Require Import VST.floyd.proofauto.
Require Import ProvedDES.verified.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Tactics for convenience *)
Ltac vst_const :=
  unfold Int.max_signed in *;
  unfold Int.max_unsigned in *;
  unfold Int.min_signed in *;
  unfold Int.iwordsize in *;
  unfold Int.zwordsize in *;
  unfold Int64.max_unsigned in *;
  unfold Int64.iwordsize' in *;
  unfold Int64.zwordsize in *;
  simpl in *; try lia.

(* functional model *)
Definition block_l (b: int64) : int64 := Int64.unsigned_bitfield_extract 32 32 b.

Definition block_r (b: int64) : int64 := Int64.unsigned_bitfield_extract 0 32 b.

Definition bit_position (i w: Z) : Z := w-i.

Definition select_bits (in_ len_in: Z) (positions : list Z) : Z :=
  fold_left
    (fun out_t p => Zbits.Zshiftin (Z.testbit in_ (bit_position p len_in)) out_t)
    positions 0.

(* API spec *)

Definition block_l_spec : ident * funspec :=
  DECLARE _block_l
    WITH b: int64
    PRE [ tulong ]
      PROP ()
      PARAMS (Vlong b)
      SEP ()
    POST [ tulong ]
      PROP ()
      RETURN (Vlong (block_l b))
      SEP ().

Definition block_r_spec : ident * funspec :=
  DECLARE _block_r
    WITH b: int64
    PRE [ tulong ]
      PROP ()
      PARAMS (Vlong b)
      SEP ()
    POST [ tulong ]
      PROP ()
      RETURN (Vlong (block_r b))
      SEP ().

Definition select_bits_spec : ident * funspec :=
  DECLARE _select_bits
    WITH in_ : Z, len_in : Z, len_out : Z,
         positions : list Z, a : val, sh : share
    PRE [ tulong, tint, tint, (tptr tint) ]
      PROP ( readable_share sh;
             0 < len_out <= Int64.zwordsize; 0 < len_in <= Int64.zwordsize;
             0 <= in_ < Int64.max_unsigned;
             Forall (fun x => 1 <= x <= len_in) positions)
      PARAMS (Vlong (Int64.repr in_);
              Vint (Int.repr len_in); Vint (Int.repr len_out); a)
      SEP (data_at sh (tarray tint len_out) (map Vint (map Int.repr positions)) a)
    POST [ tulong ]
      PROP ()
      RETURN (Vlong (Int64.repr (select_bits in_ len_in positions)))
      SEP (data_at sh (tarray tint len_out) (map Vint (map Int.repr positions)) a).

Definition Gprog :=
  ltac:(with_library prog
          [block_l_spec; block_r_spec; select_bits_spec]).

(* Proofs *)

Theorem block_l_fspec: forall b i,
    0 <= i < 32 ->
    Int64.testbit (block_l b) i = Int64.testbit b (i + 32).
Proof.
  intros.
  unfold block_l.
  rewrite Int64.bits_unsigned_bitfield_extract; vst_const.
  destruct H as [H1 H2].
  rewrite zlt_true; try lia.
  reflexivity.
Qed.

Lemma body_block_l: semax_body Vprog Gprog f_block_l block_l_spec.
Proof.
  start_function.
  forward.
  entailer!.
  f_equal.
  apply Int64.same_bits_eq.
  unfold block_l.
  intros.
  rewrite Int64.bits_shru; vst_const.
  rewrite Int64.unsigned_repr; vst_const.
  rewrite Int64.bits_unsigned_bitfield_extract; vst_const.
  destruct (zlt (i+32) Int64.zwordsize).
  - repeat rewrite zlt_true; vst_const. reflexivity.
  - repeat rewrite zlt_false; vst_const.
Qed.

Lemma body_block_r: semax_body Vprog Gprog f_block_r block_r_spec.
Proof.
  start_function.
  forward.
  entailer!.
  f_equal. unfold block_r.
  rewrite Int.unsigned_repr_eq.
  unfold "mod". simpl.
  unfold block_r.
  rewrite Int64.unsigned_bitfield_extract_by_shifts; vst_const.
  rewrite Int64.shru_shl; vst_const;
    try (unfold Int64.iwordsize; rewrite ltu64_repr_zlt; vst_const).
  rewrite Int64.sub_idem.
  rewrite Int64.shru_zero.
  rewrite Int64.unsigned_repr; vst_const.
  rewrite Int64.zero_ext_and; vst_const.
  reflexivity.
Qed.

Lemma Zshiftl_n_succ_m:
  forall n m, 0 <= m -> Z.shiftl n (Z.succ m) = Z.shiftl (Z.double n) m.
Proof.
  intros. repeat rewrite Zbits.Zshiftl_mul_two_p;
    try apply Z.le_le_succ_r; try apply H.
  rewrite two_p_S; try apply H.
  rewrite (Z.double_spec n). lia.
Qed.
  
Lemma fold_left_shiftl_init:
  forall (l : list Z) (f : Z -> bool) (init : Z), init >= 0 ->
    fold_left (fun s a => Zbits.Zshiftin (f a) s) l init =
      Z.lor (Z.shiftl init (Zlength l))
        (fold_left (fun s a => Zbits.Zshiftin (f a) s) l 0).
Proof.
  intros l. induction l.
  - intros. simpl. rewrite Z.lor_0_r. reflexivity.
  - intros. simpl.
    rewrite IHl.
    rewrite (IHl f (Zbits.Zshiftin (f a) 0)).
    rewrite Z.lor_assoc. f_equal. rewrite Zlength_cons.
    rewrite Zshiftl_n_succ_m; try apply initial_world.zlength_nonneg.
    rewrite <- Z.shiftl_lor. f_equal.
    unfold Zbits.Zshiftin.
    destruct (f a); unfold Z.succ_double; unfold Z.double; simpl.
    + destruct init eqn:E; try reflexivity.
      destruct H. simpl. reflexivity.
    + destruct init eqn:E; try reflexivity.
    + destruct (f a); simpl; lia.
    + destruct (f a); simpl; lia.
Qed.

Lemma fold_left_shiftl_range:
  forall (l : list Z) (f : Z -> bool) (i : Z),
    i >= (Zlength l) ->
    Z.testbit (fold_left (fun s a => Zbits.Zshiftin (f a) s) l 0) i = false.
Proof.
  intros l. induction l.
  - intros. simpl. rewrite Z.testbit_0_l. reflexivity.
  - intros. simpl. rewrite Zlength_cons in H.
    rewrite fold_left_shiftl_init; try (destruct (f a); simpl; lia).
    rewrite Z.lor_spec.
    rewrite Z.shiftl_spec.
    rewrite Zbits.Ztestbit_size_2.
    rewrite IHl. reflexivity.
    rewrite Z.ge_le_iff in *.
    apply Zle_succ_le. apply H.
    destruct (f a); simpl; lia.
    destruct (f a); simpl.
    lia. lia. assert (0 <= Zlength l). apply initial_world.zlength_nonneg.
    lia.
Qed.
    
Lemma fold_left_shiftl_spec:
  forall (l : list Z) (f : Z -> bool),
    forall (i : Z), 0 <= i < Zlength l ->
    Z.testbit (fold_left (fun s a => Zbits.Zshiftin (f a) s) l 0) i
    = f (Znth ((Zlength l) - i - 1) l).
Proof.
  intros l. induction l.
  - intros. unfold Zlength in H. simpl in H. lia.
  - intros. simpl.
    rewrite fold_left_shiftl_init;
      try (destruct (f a); simpl; lia).
    rewrite Z.lor_spec.
    destruct (i ?= Zlength l) eqn:E.
    + apply Z.compare_eq in E.
      rewrite E. rewrite Zlength_cons.
      replace (Z.succ (Zlength l) - Zlength l - 1) with 0.
      unfold Znth. simpl.
      rewrite Z.shiftl_spec; try apply initial_world.zlength_nonneg.
      rewrite Z.sub_diag.
      rewrite Zbits.Ztestbit_shiftin_base.
      rewrite fold_left_shiftl_range.
      rewrite orb_false_r. reflexivity.
      lia. lia.
    + destruct H as [H1 H2].
      assert (i < Zlength l). apply E.
      rewrite IHl; try lia.
      rewrite Z.shiftl_spec; try apply H1.
      rewrite Z.testbit_neg_r; try lia.
      rewrite orb_false_l. f_equal.
      rewrite Zlength_cons.
      rewrite Znth_pos_cons; try lia.
      f_equal. lia.
    + destruct H as [H1 H2].
      rewrite Zlength_cons in H2.
      apply Zlt_succ_le in H2.
      assert (i > Zlength l). apply E. lia.
Qed.  

Theorem select_bits_fspec:
  forall in_ len_in len_out (positions: list Z),
    in_ >= 0 -> len_in > 0 -> len_out = Zlength positions ->
    forall i,
      1 <= i <= len_out ->
      Z.testbit (select_bits in_ len_in positions) (bit_position i len_out) =
        Z.testbit in_ (bit_position (Znth (i-1) positions) len_in).
Proof.
  intros.
  generalize dependent i. generalize dependent len_out.
  induction positions; intros.
  - unfold Zlength in H1. simpl in H1. lia.
  - destruct (i ?= 1) eqn:E.
    + apply Z.compare_eq in E.
      rewrite E. unfold bit_position.
      rewrite Z.sub_diag. unfold Znth. simpl.
      unfold select_bits.
      rewrite H1.
      rewrite fold_left_shiftl_spec; try lia.
      unfold bit_position.
      replace (Zlength (a :: positions) - (Zlength (a :: positions) -1) -1) with 0;
        try lia.
      unfold Znth. reflexivity.
    + assert (i < 1). apply E.
      lia.
    + assert (i > 1). apply E.
      unfold select_bits. simpl.
      rewrite fold_left_shiftl_init;
        try (destruct (Z.testbit in_ (bit_position a len_in)); simpl; lia).
      unfold bit_position. 
      rewrite Z.lor_spec.
      rewrite Z.shiftl_spec; try lia.
      rewrite Zlength_cons in H1.
      assert (len_out - i - Zlength positions < 0). lia.
      rewrite Z.testbit_neg_r; try apply H4.
      rewrite orb_false_l.
      unfold select_bits in IHpositions.
      unfold bit_position in IHpositions.
      replace (len_out - i) with ((len_out-1) - (i-1)); try lia.
      rewrite IHpositions; try lia.
      rewrite Znth_pos_cons; try lia.
      reflexivity.
Qed.

Lemma body_select_bits: semax_body Vprog Gprog f_select_bits select_bits_spec.
Proof.
  start_function.
  forward. 
  forward_for_simple_bound len_out
    (EX i: Z,
        PROP ()
        LOCAL (temp _out
                 (Vlong (Int64.repr(select_bits in_ len_in (sublist 0 i positions))));
               temp _len_out (Vint (Int.repr len_out));
               temp _len_in (Vint (Int.repr len_in));
               temp _in (Vlong (Int64.repr in_));
               temp _p a
        )
        SEP (data_at sh (tarray tint len_out) (map Vint (map Int.repr positions)) a)
    )%assert.
  - entailer!.
  - forward.
    assert_PROP (Zlength positions = len_out). {
      entailer!. repeat rewrite Zlength_map. reflexivity.
    }
    forward. (* get p[i] *)
    forward.
    + entailer!; vst_const.
      assert (1 <= (Znth i positions) <= len_in). {
        apply sublist.Forall_Znth. apply H3. apply H2.
      }
      repeat rewrite Int.unsigned_repr; vst_const.
      rewrite Int.signed_repr; vst_const.
    + entailer!; vst_const. f_equal.
      apply Int64.same_bits_eq. intros.
      rewrite Int64.bits_or; vst_const.
      rewrite Int64.testbit_repr; vst_const.
      destruct (i0 ?= 0) eqn:E.
      * apply Z.compare_eq in E.
        rewrite E.
        unfold select_bits.
        rewrite fold_left_shiftl_spec;
          try (rewrite Zlength_sublist; lia).
        rewrite Zlength_sublist; try lia.
        replace (i + 1 - 0 - 0 - 1) with i; try lia.
        rewrite Znth_sublist; try lia.
        replace (i + 0) with i; try lia.
        unfold bit_position.
        rewrite Int64.bits_shl; vst_const.
        repeat rewrite Int64.unsigned_repr; vst_const.
        assert (1 <= (Znth i positions) <= len_in). {
          apply sublist.Forall_Znth. apply H3. apply H2.
        }
        rewrite Int.unsigned_repr; vst_const.
        unfold Int64.and. unfold Int64.shru.
        repeat rewrite Int64.unsigned_repr; vst_const;
          try (split; try (apply Z.shiftr_nonneg; lia);
               try (rewrite Z.shiftr_div_pow2; try lia;
                    apply Z.div_le_upper_bound; try lia)).
        rewrite <- Z.bit0_odd.
        rewrite Z.land_spec.
        replace (Z.testbit 1 0) with true; try reflexivity.
        rewrite andb_true_r.
        rewrite Z.shiftr_spec; try lia.
        rewrite Z.add_0_l.
        reflexivity.
        
        apply Z.land_nonneg. right. lia.
        replace 1 with (Z.ones 1); try reflexivity.
        rewrite Z.land_ones; try lia.
        assert (Z.shiftr in_ (len_in - Znth i positions) mod 2 ^ 1 < 2 ^ 1);
          try apply Z_mod_lt; lia.
      * assert (i0 < 0). apply E. lia.
      * assert (i0 > 0). apply E.
        rewrite Int64.bits_and; vst_const.
        rewrite Int64.bits_shru; vst_const.
        assert (1 <= (Znth i positions) <= len_in). {
          apply sublist.Forall_Znth. apply H3. apply H2.
        }
        rewrite Int64.bits_shl; vst_const.
        repeat rewrite Int.unsigned_repr; vst_const.
        repeat rewrite Int64.unsigned_repr; vst_const.
        rewrite zlt_false; try lia.
        rewrite Int64.testbit_repr; vst_const.
        rewrite (Int64.testbit_repr 1); vst_const.
        rewrite (Z.testbit_odd 1 i0).
        rewrite Z.shiftr_eq_0; try unfold Z.log2; try lia.
        simpl. rewrite andb_false_r. rewrite orb_false_r.
        destruct (i0 ?= (i+1)) eqn:E0.
        ** apply Z.compare_eq in E0.
           rewrite E0.
           unfold select_bits.
           repeat rewrite fold_left_shiftl_range;
             try (rewrite Zlength_sublist; lia).
           reflexivity.
        ** assert (i0 < i+1). apply E0.
           unfold select_bits.
           repeat rewrite fold_left_shiftl_spec;
             try repeat rewrite Zlength_sublist; try lia.
           f_equal. f_equal.
           repeat rewrite Znth_sublist; try lia.
           f_equal. lia.
        ** assert (i0 > i+1). apply E0.
           unfold select_bits.
           repeat rewrite fold_left_shiftl_range;
             try (rewrite Zlength_sublist; lia).
           reflexivity.
  - forward. entailer!.
    repeat f_equal.
    repeat rewrite initial_world.Zlength_map.
    apply sublist_same; reflexivity.
Qed.
           

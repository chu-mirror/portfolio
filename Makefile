MWEB = mweb-proto
RM = rm -rf

.SUFFIXES:
.SUFFIXES: .mw
.mw:
	@chaps=""; dir=$$PWD; \
		while [ -h $$dir/Makefile ]; do \
			if [ -d $$dir/Chapter ]; then \
				chaps="$$dir/Chapter $$chaps"; \
			fi; \
			dir=$$(dirname $$dir); \
		done; \
		chaps="$$dir/Chapter $$chaps"; \
		${MWEB} $< tangle $$chaps && cp mweb-workspace/$@ .

-include des.mk

clean:
	${RM} ${trash}

refresh:
	@for dir in ${SUB}; do \
		[ -d $$dir ] || mkdir $$dir; \
		cd $$dir && ln -sf ../Makefile Makefile && \
		make refresh && cd ..; \
	done

LATEXMK ?= latexmk
LATEXMKFLAGS ?= -xelatex -file-line-error -interaction=nonstopmode -halt-on-error
CLEAN_EXTRA ?= -e '$$clean_ext .= " nav snm vrb";'

.PHONY: all slides clean distclean

all: slides

slides: slides.pdf

slides.pdf: slides.tex
	$(LATEXMK) $(LATEXMKFLAGS) slides.tex

clean:
	$(LATEXMK) $(CLEAN_EXTRA) -c slides.tex

distclean:
	$(LATEXMK) $(CLEAN_EXTRA) -C slides.tex

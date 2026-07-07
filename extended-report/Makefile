LATEXMK ?= latexmk
REPORT_TEX := maze-extended.tex
LATEXMK_FLAGS := -pdf -interaction=nonstopmode -halt-on-error

.PHONY: all report clean distclean

all: report

report:
	$(LATEXMK) $(LATEXMK_FLAGS) $(REPORT_TEX)

clean:
	$(LATEXMK) -c $(REPORT_TEX)

distclean:
	$(LATEXMK) -C $(REPORT_TEX)

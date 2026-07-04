LATEXMK ?= latexmk
REPORT_TEX := extended-report/maze-extended.tex
LATEXMK_FLAGS := -pdf -interaction=nonstopmode -halt-on-error

.PHONY: all report clean-report distclean-report

all: report

report:
	$(LATEXMK) -cd $(LATEXMK_FLAGS) $(REPORT_TEX)

clean-report:
	$(LATEXMK) -cd -c $(REPORT_TEX)

distclean-report:
	$(LATEXMK) -cd -C $(REPORT_TEX)

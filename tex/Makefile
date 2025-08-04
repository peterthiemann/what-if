GOAL= second-class

TARGET_FILES= unicodeletters.tex agdamacros.tex
PREFIX= latex

AGDATEX= ../../agdatex/agdatex.py

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES) latex/agda-generated.tex
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode $(GOAL)
	bibtex $(GOAL)
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<

.PHONY: all type-check clean

all: $(GOAL).pdf

### agdatex

runagdatex: latex/agda-generated.tex

latex/agda-generated.tex: $(wildcard ../src/*agda) $(wildcard ../src/Simple/*.agda)
	$(AGDATEX) -v -e latex/agda-generated.tex -r ../src ../src/*.agda ../src/Simple/*.agda

### clean up

clean:
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done

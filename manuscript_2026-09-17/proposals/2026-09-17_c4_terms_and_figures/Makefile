# Please build the released arXiv manuscript from this directory.
LATEXMK ?= latexmk
.PHONY: all arxiv arxiv-package
all: arxiv
arxiv:
	MANUSCRIPT_BUILD_DIR=build_arxiv $(LATEXMK) -norc -r .latexmkrc -pdf -interaction=nonstopmode -halt-on-error main_arxiv.tex
	mkdir -p output/pdf
	cp build_arxiv/main_arxiv.pdf output/pdf/arxiv_preprint.pdf
arxiv-package: arxiv
	python3 scripts/package_arxiv.py

.PHONY: paper-build paper-clean paper-bib paper-rebuild paper-flatten paper-qeios paper-qeios-clean

paper-build:
	@if command -v latexmk >/dev/null 2>&1; then \
		cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex; \
	else \
		cd paper && pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex && \
		bibtex build/main && \
		pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex && \
		pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex; \
	fi
	@$(MAKE) paper-flatten

paper-clean:
	@if command -v latexmk >/dev/null 2>&1; then \
		cd paper && latexmk -C -outdir=build main.tex; \
	else \
		rm -f paper/build/*; \
	fi
	@rm -f paper/build/main_flat.tex

paper-bib:
	cd paper && bibtex build/main

paper-flatten:
	@flattener="$$(command -v latexpand || command -v texflatten || true)"; \
	if [ -z "$$flattener" ]; then \
		echo "missing LaTeX flattener: install latexpand or texflatten" >&2; \
		exit 1; \
	elif [ "$$(basename "$$flattener")" = "latexpand" ]; then \
		cd paper && "$$flattener" -o build/main_flat.tex main.tex; \
	else \
		cd paper && "$$flattener" main.tex > build/main_flat.tex; \
	fi

paper-rebuild: paper-clean paper-build

paper-qeios:
	./scripts/build_qeios_assets.sh

paper-qeios-clean:
	rm -rf paper/build/qeios_single

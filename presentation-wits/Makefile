all: presentation.html presentation.pdf

presentation.html: presentation.md Makefile custom.css
	docker run --rm --volume "`pwd`:/data" --user `id -u`:`id -g` pandoc/latex \
		$< \
		-t revealjs \
		--standalone \
		--output $@ \
		--metadata=date:"`date "+%B %e, %Y"`" \
		--syntax-highlighting=none \
		--katex \
		`# See reveal.js themes here: https://revealjs.com/themes/` \
		`# Use "black" for dark mode.` \
		-V theme="white" \
		`# Reveal.js options can be set form pandoc: https://github.com/jgm/pandoc/blob/master/data/templates/default.revealjs#L95` \
		`# -V center="false"` \
		-V width="1200" \
		-V height="675" \
		-V margin="0.16" \
		-V transition="none" \
		-V header-includes='<link rel="stylesheet" href="custom.css" />' \
		-V include-after='<script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"></script><script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/languages/scala.min.js"></script><script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/languages/haskell.min.js"></script><script>hljs.highlightAll();</script>' \
		-V history="true" \
		-V center="false" \
		-V navigationMode="linear" \
		-V slideNumber="true" \
		-V controls="false" \
		--slide-level=2

presentation.pdf: presentation.html
	docker run --rm --volume "`pwd`:/slides" --workdir="/slides" --user `id -u`:`id -g` astefanutti/decktape \
		$< \
		$@

talk_proposal.pdf: talk_proposal.tex
	docker run --rm --volume "`pwd`:/workdir" --user `id -u`:`id -g` texlive/texlive \
		latexmk -pdf -interaction=nonstopmode $<

.PHONY: clean

clean:
	rm -rf *.html

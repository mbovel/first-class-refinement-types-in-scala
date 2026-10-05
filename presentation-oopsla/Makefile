all: presentation.html presentation.pdf

%.html: %.md Makefile custom.css
	docker run --rm --volume "`pwd`:/data" --user `id -u`:`id -g` pandoc/latex \
		$< \
		-t revealjs \
		--standalone \
		--output $@ \
		--metadata=date:"`date "+%B %e, %Y"`" \
		--syntax-highlighting=none \
		--katex=lib/katex/ \
		-V revealjs-url=lib/reveal.js \
		`# See reveal.js themes here: https://revealjs.com/themes/` \
		`# Use "black" for dark mode.` \
		-V theme="white" \
		`# See higlight.js themes here: https://highlightjs.org/static/demo/` \
		`# Use "atom-one-dark.min.css" for dark mode. Other reasonnable light themes include xcode.css and vs.css.` \
		-V header-includes='<link rel="stylesheet" href="lib/highlight.js/styles/atom-one-light.min.css">' \
		`# Reveal.js options can be set form pandoc: https://github.com/jgm/pandoc/blob/master/data/templates/default.revealjs#L95` \
		-V center="false" \
		-V width="1200" \
		-V height="675" \
		-V margin="0.1" \
		-V transition="none" \
		-V header-includes='<link rel="stylesheet" href="custom.css" />' \
		-V include-after='<script src="lib/highlight.js/highlight.min.js"></script><script src="lib/highlight.js/languages/scala.min.js"></script><script src="lib/highlight.js/languages/haskell.min.js"></script><script src="highlightjs-coq.js"></script><script>hljs.highlightAll();</script>' \
		-V history="true" \
		-V navigationMode="linear" \
		`# "c/t" numbers slides linearly (current/total) rather than "h.v" per section.` \
		-V slideNumber="'c/t'" \
		-V controls="false" \
		--slide-level=2

%.pdf: %.html
	docker run --rm --volume "`pwd`:/slides" --workdir="/slides" --user `id -u`:`id -g` astefanutti/decktape \
		$< \
		$@

.PHONY: clean

clean:
	rm -rf *.html

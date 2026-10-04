# Vendored slide runtime

Everything `presentation.html` loads at runtime, so the deck renders with no
network access. Each deck keeps its own copy: the `Makefile` mounts only the
deck directory into the pandoc and decktape containers, so a shared directory
one level up would be invisible to the PDF export.

| Component      | Version | Source                                        |
| -------------- | ------- | --------------------------------------------- |
| reveal.js      | 5.2.1   | `npm:reveal.js` (pandoc's revealjs template default is `^5`) |
| KaTeX          | 0.18.7  | `npm:katex` (pandoc's `--katex` default is `@latest`) |
| highlight.js   | 11.9.0  | `npm:@highlightjs/cdn-assets` (same files cdnjs serves) |

Trimmed to what a current browser actually fetches. Every `@font-face` here
resolves locally to its first usable entry: KaTeX ships `.woff2` and `.woff`,
reveal.js theme fonts ship `.woff`. The formats behind those (`.ttf`, and the
IE-only `.eot`) are left out — nothing that can run reveal.js 5 falls through
to them. Also omitted: source maps, ES-module builds, and every highlight.js
grammar except Scala and Haskell. Coq highlighting is the deck's own
`highlightjs-coq.js`.

reveal.js's own `white` theme (what both decks use) is fully local. Eight of
the other bundled themes — beige, blood, league, moon, night, simple, sky,
solarized — `@import` Google Fonts and would fall back to system fonts offline.

To refresh, bump the versions in `fetch.sh` and run it from the deck directory.

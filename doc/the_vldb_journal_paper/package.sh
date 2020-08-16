#! /usr/bin/env bash

set -euo pipefail

main() {
    rm -f iconfluence.zip
    zip -r iconfluence.zip \
        figures/ \
        iconfluence_whittaker.bbl \
        iconfluence_whittaker.tex \
        invariantconfluence.sty \
        pervasives.sty \
        python.sty \
        references.bib \
        sections/ \
        svglov3.clo \
        svjour3.cls \
        tcbbreakable.code.tex \
        tcbskins.code.tex \
        tcbskinsjigsaw.code.tex \
        tcolorbox.sty \
        vldb.cls \

}

main "$@"

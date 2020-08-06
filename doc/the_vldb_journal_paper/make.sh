#! /usr/bin/env bash

set -euo pipefail

main() {
    latexmk -pdf rebuttal.tex
    latexmk -pdf iconfluence_whittaker.tex
    pdfunite rebuttal.pdf iconfluence_whittaker.pdf iconfluence_whittaker_revisions.pdf
}

main "$@"

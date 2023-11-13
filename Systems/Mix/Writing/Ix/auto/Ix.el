(TeX-add-style-hook
 "Ix"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("acmart" "authoryear" "acmsmall" "screen")))
   (TeX-run-style-hooks
    "latex2e"
    "acmart"
    "acmart10"
    "natbib"
    "tikz"
    "tikz-cd")
   (TeX-add-symbols
    "U"
    "Refl")
   (LaTeX-add-labels
    "app:RO"
    "sec:ro-syntax"
    "fig:syntax"
    "sec:ro-types"
    "fig:kinding"
    "fig:type-equiv"
    "sec:ro-terms"
    "fig:typing"
    "sec:ro-minimal"
    "fig:minimal"
    "fig:translation")
   (LaTeX-add-bibliographies))
 :latex)


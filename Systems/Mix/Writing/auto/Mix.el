(TeX-add-style-hook
 "Mix"
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
    '("SafeJ" 2)
    '("Safe" 1)
    '("Rule" 1)
    '("J" 4)
    '("Pointed" 1)
    "Fst"
    "Snd"
    "U"
    "PointedT"
    "PointedU"
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
    "fig:IxRules"
    "fig:IxDefnEq"
    "fig:translation")
   (LaTeX-add-bibliographies
    "MIx"))
 :latex)


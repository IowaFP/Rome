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
    '("New" 1)
    '("Felim" 1)
    '("SafeJ" 2)
    '("Safe" 1)
    '("Rule" 1)
    '("CaseS" 5)
    '("CaseP" 3)
    '("CaseF" 4)
    '("CaseN" 4)
    '("J" 4)
    '("Pointed" 1)
    '("Lift" 1)
    "Fst"
    "Snd"
    "U"
    "PointedT"
    "PointedU"
    "Refl")
   (LaTeX-add-labels
    "fig:syntax"
    "fig:formation"
    "fig:IxRules"
    "fig:IxDefnEq"
    "fig:translation")
   (LaTeX-add-bibliographies
    "MIx"))
 :latex)


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
    '("CaseS" 3)
    '("CaseFS" 3)
    '("CaseP" 2)
    '("CaseFZ" 2)
    '("CaseN" 3)
    '("J" 4)
    '("Pointed" 1)
    '("Lift" 1)
    '("TyPair" 3)
    '("Ixed" 1)
    '("FormJ" 2)
    '("Ix" 1)
    '("secfig" 2)
    '("SortJ" 3)
    '("Todo" 1)
    "IX"
    "Hix"
    "Nat"
    "Zero"
    "FZero"
    "Suc"
    "FSuc"
    "Fin"
    "MuIx"
    "Type"
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


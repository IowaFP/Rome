(TeX-add-style-hook
 "Ix"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "12pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "margin=1.5in")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art12"
    "geometry"
    "natbib"
    "tikz"
    "tikz-cd")
   (TeX-add-symbols
    '("FormJ" 2)
    '("Ix" 1)
    '("secfig" 2)
    '("SortJ" 3)
    "IX"
    "Hix"
    "Nat"
    "Zero"
    "FZero"
    "Suc"
    "FSuc"
    "Fin"
    "MuIx"
    "U"
    "Refl")
   (LaTeX-add-labels
    "fig:syntax"
    "app:RO"
    "sec:ro-syntax"
    "sec:ro-types"
    "fig:kinding"
    "fig:type-equiv"
    "sec:ro-terms"
    "fig:typing"
    "sec:ro-minimal"
    "fig:minimal"))
 :latex)


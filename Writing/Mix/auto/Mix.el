(TeX-add-style-hook
 "Mix"
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
    "Nat"
    "Zero"
    "Suc"
    "Fin"
    "MuIx")
   (LaTeX-add-labels
    "sec:Syntax"
    "fig:syntax"
    "sec:Kinding"
    "fig:kinding"
    "sec:Typing"
    "sec:Translation"
    "fig:translation"
    "app:RO"
    "sec:ro-syntax"
    "sec:ro-types"
    "fig:type-equiv"
    "sec:ro-terms"
    "fig:typing"
    "sec:ro-minimal"
    "fig:minimal")
   (LaTeX-add-bibliographies
    "/home/alex/Dropbox/HubersPhD/bibliography/ann-bib"))
 :latex)


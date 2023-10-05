(TeX-add-style-hook
 "template"
 (lambda ()
   (setq TeX-command-extra-options
         "--synctex=1")
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "12pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "margin=1.5in")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art12"
    "geometry"
    "tikz"
    "tikz-cd")
   (TeX-add-symbols
    "RO")
   (LaTeX-add-labels
    "sec:Introduction"
    "sec:Syntax")
   (LaTeX-add-bibliographies
    "template.bib"))
 :latex)


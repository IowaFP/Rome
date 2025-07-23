(TeX-add-style-hook
 "TN"
 (lambda ()
   (setq TeX-command-extra-options
         "-shell-escape")
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("acmart" "authoryear" "acmsmall" "screen" "review" "nonacm")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1")))
   (TeX-run-style-hooks
    "latex2e"
    "header"
    "acmart"
    "acmart10"
    "agda"
    "inputenc"
    "fontenc"
    "newunicodechar")
   (LaTeX-add-labels
    "fig:syntax-types")
   (LaTeX-add-bibliographies))
 :latex)


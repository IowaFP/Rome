(TeX-add-style-hook
 "NBE"
 (lambda ()
   (setq TeX-command-extra-options
         "-shell-escape")
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("acmart" "authoryear" "acmsmall" "screen" "review" "nonacm")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1")))
   (add-to-list 'LaTeX-verbatim-environments-local "rosi")
   (add-to-list 'LaTeX-verbatim-environments-local "haskell")
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-environments-local "code")
   (add-to-list 'LaTeX-verbatim-environments-local "codef")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
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
    "fig:syntax-types"
    "fig:type-normalization")
   (LaTeX-add-bibliographies))
 :latex)


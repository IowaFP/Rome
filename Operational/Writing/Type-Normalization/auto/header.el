(TeX-add-style-hook
 "header"
 (lambda ()
   (setq TeX-command-extra-options
         "-shell-escape")
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("ulem" "normalem") ("cleveref" "capitalize" "noabbrev")))
   (add-to-list 'LaTeX-verbatim-environments-local "codef")
   (add-to-list 'LaTeX-verbatim-environments-local "code")
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "conditionals"
    "TN"
    "ulem"
    "cleveref")
   (TeX-add-symbols
    "Root"
    "blankpage"))
 :latex)


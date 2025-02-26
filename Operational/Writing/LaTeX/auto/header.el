(TeX-add-style-hook
 "header"
 (lambda ()
   (setq TeX-command-extra-options
         "-shell-escape")
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("ulem" "normalem") ("cleveref" "capitalize" "noabbrev")))
   (TeX-run-style-hooks
    "conditionals"
    "grammar"
    "dump"
    "ulem"
    "cleveref")
   (TeX-add-symbols
    "Root"
    "blankpage")
   (LaTeX-add-environments
    '("proof" LaTeX-env-args ["argument"] 0)))
 :latex)


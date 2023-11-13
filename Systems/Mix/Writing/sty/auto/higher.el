(TeX-add-style-hook
 "higher"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("ulem" "normalem") ("cleveref" "capitalize" "noabbrev")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-environments-local "code")
   (add-to-list 'LaTeX-verbatim-environments-local "codef")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "ulem"
    "cleveref"
    "enumitem"
    "listings")
   (TeX-add-symbols
    '("Syn" ["argument"] 0)
    '("Ana" ["argument"] 0)
    '("TypeK" ["argument"] 0)
    '("Deriv" ["argument"] 0)
    '("RO" ["argument"] 0)
    '("Inj" ["argument"] 1)
    '("PrjS" ["argument"] 1)
    '("Prj" ["argument"] 1)
    '("Leqp" ["argument"] 2)
    '("KFam" 2)
    '("Sem" 1)
    '("Case" 2)
    '("rrule" 1)
    '("EqvJS" 3)
    '("EqvJ" 2)
    '("TypeJ" 3)
    '("PredJ" 2)
    '("KindJS" 4)
    '("KindJ" 3)
    '("EnvJ" 1)
    '("EntJS" 3)
    '("EntJ" 2)
    '("esrule" 2)
    '("erulec" 1)
    '("erule" 1)
    '("entsrule" 2)
    '("entrule" 1)
    '("eqrule" 1)
    '("prule" 1)
    '("krule" 1)
    '("crule" 1)
    '("labrule" 2)
    '("TLam" 3)
    '("Lam" 3)
    '("AppT" 2)
    '("ExC" 1)
    '("TyC" 1)
    '("Sing" 1)
    '("RowK" 1)
    '("ruleNvm" 1)
    '("ruleUpdated" 1)
    '("ruleAdded" 1)
    '("fixme" 1)
    '("AHFN" 1)
    '("AHRev" 1)
    '("AH" 1)
    '("RD" 1)
    '("RC" 1)
    '("RB" 1)
    '("RA" 1)
    '("ADE" 1)
    '("JHM" 1)
    '("JGM" 1)
    '("todoitems" 1)
    '("todo" 1)
    '("commentbox" 3)
    '("shade" 1)
    '("mcr" 1)
    '("mcl" 1)
    '("Inst" 2)
    '("IsType" 1)
    '("FCase" 2)
    '("FInj" 2)
    '("FPrj" 2)
    '("Unlabel" 2)
    '("LabTerm" 2)
    '("Let" 3)
    '("EllTy" 2)
    '("LabTy" 2)
    '("Lab" 1)
    '("Rowlr" 1)
    '("Row" 1)
    '("RowPlus" 2)
    '("RowPlusP" 3)
    '("trnp" 1)
    '("tr" 1)
    '("defemph" 1)
    '("appref" 1)
    '("Tuple" 1)
    '("Set" 1)
    '("E" 1)
    '("I" 1)
    '("mrule" 1)
    '("strule" 1)
    '("trule" 1)
    '("ib" 1)
    "isp"
    "rsp"
    "pto"
    "trto"
    "oleq"
    "then"
    "App"
    "Dir"
    "Left"
    "Right"
    "Concat"
    "InjS"
    "Branch"
    "Fork"
    "TLang"
    "Hole"
    "Rose"
    "Remy"
    "citeme"
    "todots"
    "ColorC"
    "ColorU"
    "ColorNvm"
    "ROmu"
    "FO"
    "SF"
    "co"
    "kay"
    "Disjoint"
    "LabK"
    "Bool"
    "Int"
    "Double"
    "List"
    "Map"
    "Fold"
    "Iter"
    "IterM"
    "IterF"
    "MapP"
    "MapS"
    "FoldP"
    "Thy"
    "Mty"
    "Sty"
    "Cty"
    "Red"
    "Reds"
    "Crash"
    "Or"
    "Ni"
    "circleit"
    "dontshow")
   (LaTeX-add-environments
    "syntaxarray"
    "syntax"
    "doublesyntaxarray"
    "doublesyntax"
    "smalle"))
 :latex)


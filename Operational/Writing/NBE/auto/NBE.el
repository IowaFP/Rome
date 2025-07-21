(TeX-add-style-hook
 "NBE"
 (lambda ()
   (setq TeX-command-extra-options
         "-shell-escape")
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("footmisc" "para") ("ulem" "normalem") ("cleveref" "capitalize" "noabbrev")))
   (add-to-list 'LaTeX-verbatim-environments-local "codef")
   (add-to-list 'LaTeX-verbatim-environments-local "code")
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-environments-local "haskell")
   (add-to-list 'LaTeX-verbatim-environments-local "rosi")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "accents"
    "amsmath"
    "amsthm"
    "centernot"
    "ifthen"
    "infer"
    "lipsum"
    "mathwidth"
    "mathrsfs"
    "mathtools"
    "multicol"
    "stmaryrd"
    "tensor"
    "xspace"
    "thmtools"
    "subfiles"
    "xcolor"
    "footmisc"
    "ulem"
    "cleveref"
    "enumitem"
    "listings")
   (TeX-add-symbols
    '("Deriv" ["argument"] 0)
    '("Fome" ["argument"] 0)
    '("Rome" ["argument"] 0)
    '("RO" ["argument"] 0)
    '("SynV" ["argument"] 1)
    '("Variant" ["argument"] 2)
    '("Record" ["argument"] 1)
    '("PlusV" ["argument"] 1)
    '("LeqV" ["argument"] 1)
    '("LeqP" ["argument"] 2)
    '("TypeK" ["argument"] 0)
    '("Normal" 1)
    '("CiteAgda" 2)
    '("Tt" 1)
    '("Cut" 1)
    '("RowIx" 4)
    '("ruleNvm" 1)
    '("ruleUpdated" 1)
    '("ruleAdded" 1)
    '("RD" 1)
    '("RC" 1)
    '("RB" 1)
    '("RA" 1)
    '("AI" 1)
    '("AM" 1)
    '("AHFn" 1)
    '("AHRev" 1)
    '("AH" 1)
    '("JGM" 1)
    '("fixme" 1)
    '("todoitems" 1)
    '("todo" 1)
    '("commentbox" 3)
    '("shade" 1)
    '("mcr" 1)
    '("mcl" 1)
    '("TypeKeyword" 1)
    '("Keyword" 1)
    '("TransV" 2)
    '("BAlg" 2)
    '("MAlg" 2)
    '("KFam" 2)
    '("Conm" 2)
    '("Con" 2)
    '("SelL" 2)
    '("Sel" 2)
    '("CaseL" 2)
    '("Case" 2)
    '("UnlabelX" 3)
    '("LabTermX" 3)
    '("Unlabel" 2)
    '("LabTerm" 2)
    '("Let" 3)
    '("AppE" 1)
    '("AppT" 2)
    '("TLam" 3)
    '("Lam" 3)
    '("ExC" 1)
    '("TyC" 1)
    '("Sing" 1)
    '("Mapp" 2)
    '("Flap" 1)
    '("Map" 1)
    '("RecTy" 1)
    '("EllTy" 2)
    '("LabTy" 2)
    '("Lab" 1)
    '("Rowlr" 1)
    '("Row" 1)
    '("Plus" 2)
    '("PlusP" 3)
    '("RowK" 1)
    '("rxrule" 1)
    '("rdrule" 1)
    '("rbrule" 1)
    '("rrule" 1)
    '("tmrule" 1)
    '("tsrule" 1)
    '("torule" 1)
    '("trrule" 1)
    '("entmrule" 1)
    '("entsrule" 1)
    '("entorule" 1)
    '("entrrule" 1)
    '("entrule" 1)
    '("emrulec" 1)
    '("errulec" 1)
    '("erulec" 1)
    '("emrule" 1)
    '("esrule" 1)
    '("eorule" 1)
    '("errule" 1)
    '("erule" 1)
    '("kmrule" 1)
    '("ksrule" 1)
    '("korule" 1)
    '("krrule" 1)
    '("kruleNF" 1)
    '("kruleNE" 1)
    '("krule" 1)
    '("crule" 1)
    '("labrule" 2)
    '("PEqvJ" 3)
    '("TEqvJ" 4)
    '("EntJ" 4)
    '("PredJ" 2)
    '("TypeJ" 5)
    '("KindJNE" 3)
    '("KindJNF" 3)
    '("KindJ" 3)
    '("TEnvJ" 2)
    '("PEnvJ" 2)
    '("KEnvJ" 1)
    '("trnp" 1)
    '("tr" 1)
    '("Note" 1)
    '("defemph" 1)
    '("secfig" 2)
    '("figref" 1)
    '("secref" 1)
    '("appref" 1)
    '("trunrule" 1)
    '("SemE" 1)
    '("SemET" 1)
    '("SemEP" 1)
    '("SemN" 1)
    '("SemPE" 1)
    '("SemP" 1)
    '("SemKE" 1)
    '("SemK" 1)
    '("SemT" 1)
    '("Sem" 1)
    '("Tuple" 1)
    '("Set" 1)
    '("E" 1)
    '("I" 1)
    '("mrule" 1)
    '("strule" 1)
    '("trule" 1)
    '("ib" 1)
    '("citeposs" 1)
    "leqnomode"
    "reqnomode"
    "ala"
    "isp"
    "rsp"
    "ran"
    "pto"
    "Maybe"
    "trto"
    "LLt"
    "nLLt"
    "Le"
    "Ri"
    "Red"
    "NRed"
    "Reds"
    "NReds"
    "RedQ"
    "RedQs"
    "NRedQ"
    "NRedQs"
    "RedT"
    "RedTs"
    "NRedT"
    "NRedTs"
    "LabK"
    "FunctorK"
    "oleq"
    "then"
    "Compl"
    "EmptyRow"
    "Bool"
    "Int"
    "Double"
    "List"
    "App"
    "In"
    "Out"
    "Fix"
    "Concat"
    "Concatl"
    "Inj"
    "Injm"
    "Prj"
    "Prjm"
    "Branch"
    "Branchl"
    "Ana"
    "Syn"
    "Fold"
    "Iter"
    "IterM"
    "IterF"
    "Fmap"
    "FmapS"
    "FmapP"
    "Reify"
    "Reflect"
    "Cata"
    "Mcata"
    "Functor"
    "MaybeFunctor"
    "Lub"
    "Glb"
    "Hook"
    "Nat"
    "Lit"
    "Add"
    "Fst"
    "Snd"
    "Const"
    "InclV"
    "ExclV"
    "LeftV"
    "RightV"
    "CombV"
    "Vals"
    "EVals"
    "Unit"
    "KeywordColor"
    "TypeKeywordColor"
    "lstfont"
    "InlineOn"
    "InlineOff"
    "Rose"
    "Remy"
    "citeme"
    "todots"
    "ColorC"
    "ColorU"
    "ColorNvm"
    "FO"
    "SF"
    "co"
    "kay"
    "Disjoint"
    "One"
    "Two"
    "Three"
    "Apart"
    "Ni"
    "codesep"
    "Norm"
    "Embed"
    "Types"
    "Terms"
    "Evidence"
    "NormalEvidence"
    "NormalRows"
    "NormalTypes"
    "NormalTerms"
    "cf"
    "veqno"
    "circleit"
    "dontshow")
   (LaTeX-add-environments
    "syntaxarray"
    "syntax"
    "doublesyntaxarray"
    "doublesyntax"
    "smalle"
    "old"))
 :latex)


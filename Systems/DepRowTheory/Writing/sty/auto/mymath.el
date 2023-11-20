(TeX-add-style-hook
 "mymath"
 (lambda ()
   (LaTeX-add-environments
    "theorem"
    "assumption"
    "prop"
    "claim"
    "defn"
    "example"))
 :latex)


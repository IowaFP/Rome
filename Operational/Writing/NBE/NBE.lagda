\documentclass[authoryear, acmsmall, screen, review, nonacm]{acmart}
\overfullrule=1mm
% \usepackage[margin=1.5in]{geometry}

\include{header.tex} 
\usepackage{agda}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}

% ACM garbage
\setcopyright{none}
\citestyle{acmauthoryear}
\settopmatter{printacmref=false, printfolios=true}
\renewcommand{\footnotetextcopyrightpermission}{} 
% Redefine the \acmDOI command to do nothing 
\pagestyle{empty}
\fancyfoot{}

%\usepackage[utf8]{inputenc}
% \numberwithin{equation}{section}
% \numberwithin{theorem}{section}

\title{Normalization By Evaluation of Types in \Rome}
\author{Alex Hubers}
\orcid{0000-0002-6237-3326}
\affiliation{
  \department{Department of Computer Science}
  \institution{The University of Iowa}
  \streetaddress{14 MacLean Hall}
  \city{Iowa City}
  \state{Iowa}
  \country{USA}}
\email{alexander-hubers@uiowa.edu}

\usepackage{newunicodechar}
\newunicodechar{∋}{$\ni$}
\newunicodechar{ε}{$\epsilon$}
\newunicodechar{·}{$\cdot$}
\newunicodechar{⊢}{$\vdash$}
\newunicodechar{⋆}{${}^\star$}
\newunicodechar{Π}{$\Pi$}
\newunicodechar{⇒}{$\Rightarrow$}
\newunicodechar{ƛ}{$\lambdabar$}
\newunicodechar{∅}{$\emptyset$}
\newunicodechar{∀}{$\forall$}
\newunicodechar{ϕ}{$\Phi$}
\newunicodechar{φ}{$\phi$}
\newunicodechar{ψ}{$\Psi$}
\newunicodechar{ρ}{$\rho$}
\newunicodechar{α}{$\alpha$}
\newunicodechar{β}{$\beta$}
\newunicodechar{μ}{$\mu$}
\newunicodechar{σ}{$\sigma$}
\newunicodechar{≡}{$\equiv$}
\newunicodechar{Γ}{$\Gamma$}
\newunicodechar{∥}{$\parallel$}
\newunicodechar{Λ}{$\Lambda$}
\newunicodechar{₂}{$_2$}
\newunicodechar{θ}{$\theta$}
\newunicodechar{Θ}{$\Theta$}
\newunicodechar{∘}{$\circ$}
\newunicodechar{Δ}{$\Delta$}
\newunicodechar{★}{$\star$}
\newunicodechar{λ}{$\lambda$}
\newunicodechar{⊧}{$\models$}
\newunicodechar{⊎}{$\uplus$}
\newunicodechar{η}{$\eta$}
\newunicodechar{⊥}{$\bot$}
\newunicodechar{Σ}{$\Sigma$}
\newunicodechar{ξ}{$\xi$}
\newunicodechar{₁}{$_1$}
\newunicodechar{ₖ}{$_k$}
\newunicodechar{₃}{$_3$}
\newunicodechar{ℕ}{$\mathbb{N}$}
\newunicodechar{ᶜ}{${}^c$}
\newunicodechar{Φ}{$\Phi$}
\newunicodechar{Ψ}{$\Psi$}
\newunicodechar{⊤}{$\top$}
\newunicodechar{κ}{$\kappa$}
\newunicodechar{τ}{$\tau$}
\newunicodechar{π}{$\pi$}
\newunicodechar{⌊}{$\lfloor$}
\newunicodechar{⌋}{$\rfloor$}
\newunicodechar{≲}{$\lesssim$}
\newunicodechar{▹}{$\triangleright$}
\newunicodechar{ℓ}{$\ell$}
\newunicodechar{υ}{$\upsilon$}

\newunicodechar{→}{$\rightarrow$}
\newunicodechar{×}{$\times$}
\newunicodechar{ω}{$\omega$}
\newunicodechar{∃}{$\exists$}
\newunicodechar{∈}{$\in$}
\newunicodechar{⇑}{$\Uparrow$}
\newunicodechar{⇓}{$\Downarrow$}
\newunicodechar{≋}{$\approx$}
\newunicodechar{ₗ}{$_l$}
\newunicodechar{ᵣ}{$_r$}
\newunicodechar{⟦}{$\llbracket$}
\newunicodechar{⟧}{$\rrbracket$}
\newunicodechar{⁻}{$^{-}$}
\newunicodechar{¹}{$^{1}$}
\newunicodechar{⦅}{$\llparenthesis$}
\newunicodechar{⦆}{$\rrparenthesis$}
\newunicodechar{─}{$\setminus$}
\newunicodechar{∷}{$\co\co$}
\newunicodechar{ₖ}{$_{k}$}
\newunicodechar{ₙ}{$_{n}$}
\newunicodechar{≟}{$\overset{?}{=}$}

\begin{document}

\maketitle

\section*{Abstract}
We describe the normalization-by-evaluation (NbE) of types in \Rome, a row calculus with recursive types, qualified types, and a novel \emph{row complement} operator. Types are normalized modulo $\beta$- and $\eta$-equivalence---that is, to $\beta\eta$-long forms. Because the type system of \Rome is a strict extension of System \Fome, type level computation for arrow kinds is isomorphic to reduction of arrow types in the STLC. Novel to this report are the reductions of $\Pi$, $\Sigma$, and row types.

\begin{code}[hide]
postulate
  bot : ∀ (X : Set) → X

open import Prelude
\end{code}

\section{The \Rome{} calculus}

For reference, \cref{fig:syntax-types} describes the syntax of kinds, predicates, and types in \Rome.

\begin{figure}[H]
\begin{gather*}
\begin{array}{r@{\hspace{5px}}l@{\qquad}r@{\hspace{5px}}l@{\qquad}r@{\hspace{5px}}l@{\qquad}r@{\hspace{5px}}l}
\text{Type variables} & \alpha \in \mathcal A & \text{Labels} & \ell \in \mathcal L
\end{array}
\\[5px]
\begin{doublesyntaxarray}
  \mcl{\text{Kinds}} & \kappa & ::= & \TypeK \mid \LabK \mid \RowK \kappa \mid \kappa \to \kappa \\
  \mcl{\text{Predicates}} & \pi, \psi & ::= & \LeqP \rho \rho \mid \PlusP \rho \rho \rho \\
  \text{Types} & \mcr{\Types \ni \phi, \tau, \upsilon, \rho, \xi} & ::= & \alpha \mid \pi \then \tau \mid \forall \alpha\co\kappa. \tau \mid \lambda \alpha\co\kappa. \tau \mid \tau \, \tau \\
               &                              &     & \mid    & \RowIx i 0 m {\LabTy {\xi_i} {\tau_i}} \mid \ell \mid \Sing{\tau} \mid \Mapp{\phi}{\rho} \mid \rho \Compl \rho \\ 
               &                              &     & \mid & \tau \to \tau \mid \Pi \mid \Sigma \mid \mu \, \phi 
\end{doublesyntaxarray}
\end{gather*}
\caption{Syntax}
\label{fig:syntax-types}
\end{figure}

\subsection{Example types}

Wand's problem and a record modifier:

\begin{rosi}
wand : forall l x y z t. x + y ~ z, {l := t} < z => #l -> Pi x -> Pi y -> t
modify : forall l t u y z1 z2. {l := t} + y ~ z1, {l := u} + y ~ z2 =>
         #l -> (t -> u) -> Pi z1 -> Pi z2
\end{rosi}

\Ni "Deriving" functor typeclass instances: 

\begin{rosi}
type Functor : (* -> *) -> *
type Functor = \f. forall a b. (a -> b) -> f a -> f b

fmapS : forall z : R[* -> *]. Pi (Functor z) -> Functor (Sigma z)
fmapP : forall z : R[* -> *]. Pi (Functor z) -> Functor (Pi z)
\end{rosi}

\Ni And a desugaring of booleans to Church encodings:

\begin{rosi}
desugar : forall y. BoolF < y, LamF < y - BoolF =>
          Pi (Functor (y - BoolF)) -> Mu (Sigma y) -> Mu (Sigma (y - BoolF))
\end{rosi}

\section{Mechanized syntax}

\subsection{Kind syntax}

Our formalization of \Rome types is \emph{intrinsic}, meaning we define the syntax of \emph{typing} and \emph{kinding judgments}, foregoing any formalization of or indexing-by untyped syntax. Arguably the only "untyped" syntax is that of kinds, which are well-formed grammatically. We give the syntax of kinds and kinding environments below.

\begin{code}
data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  R[_]  : Kind → Kind

infixr 5 _`→_
\end{code}

The kind system of \Rome defines $\star$ as the type of types; $L$ as the type of labels; $(\to)$ as the type of type operators; and $R[\kappa]$ as the type of \emph{rows} containing types at kind $\kappa$.

The syntax of kinding environments is given below. Kinding environments are isomorphic to lists of kinds.

\begin{code}
data KEnv : Set where
  ∅ : KEnv
  _,,_ : KEnv → Kind → KEnv
\end{code}

Let the metavariables $\Delta$ and $\kappa$ range over kinding environments and kinds, respectively. Correspondingly, we define \emph{generalized variables} in Agda at these names. 

\begin{code}
private
  variable
    Δ Δ₁ Δ₂ Δ₃ : KEnv
    κ κ₁ κ₂ : Kind
\end{code}

The syntax of intrinsically well-scoped De-Bruijn type variables is given below. We say that the type variable $x$ is indexed by kinding environment $\Delta$ and kind $\kappa$ to specify that $x$ has kind $\kappa$ in kinding environment $\Delta$.

\begin{code}
data TVar : KEnv → Kind → Set where
  Z : TVar (Δ ,, κ) κ
  S : TVar Δ κ₁ → TVar (Δ ,, κ₂) κ₁
\end{code}

\subsubsection{Quotienting kinds}~

\begin{minipage}[t]{0.45\textwidth}
\begin{code}
NotLabel : Kind → Set 
NotLabel ★ = ⊤
NotLabel L = ⊥
NotLabel (κ₁ `→ κ₂) = NotLabel κ₂
NotLabel R[ κ ] = NotLabel κ
\end{code}
\end{minipage}%
\hfill
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
notLabel? : ∀ κ → Dec (NotLabel κ)
notLabel? ★ = yes tt
notLabel? L = no λ ()
notLabel? (κ `→ κ₁) = notLabel? κ₁
notLabel? R[ κ ] = notLabel? κ
\end{code}
\end{minipage}

\begin{code}
Ground : Kind → Set 
ground? : ∀ κ → Dec (Ground κ)
Ground ★ = ⊤
Ground L = ⊤
Ground (κ `→ κ₁) = ⊥
Ground R[ κ ] = ⊥
\end{code}
\begin{code}[hide]
ground? ★ = yes tt
ground? L = yes tt
ground? (_ `→ _) = no (λ ())
ground? R[ _ ] = no (λ ())
\end{code}

\subsection{Type syntax}

\begin{code}
infixr 2 _⇒_
infixl 5 _·_
infixr 5 _≲_
data Pred (Ty : KEnv → Kind → Set) Δ : Kind → Set
data Type Δ : Kind → Set 

SimpleRow : (Ty : KEnv → Kind → Set) → KEnv → Kind → Set 
SimpleRow Ty Δ R[ κ ]   = List (Label × Ty Δ κ)
SimpleRow _ _ _ = ⊥

Ordered : SimpleRow Type Δ R[ κ ] → Set 
ordered? : ∀ (xs : SimpleRow Type Δ R[ κ ]) → Dec (Ordered xs)
\end{code}

\begin{code}
data Pred Ty Δ where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Ty Δ R[ κ ]) → 
       --------------------- 
       Pred Ty Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : Ty Δ R[ κ ]) →
       ----------
       Pred Ty Δ R[ κ ]  
\end{code}

\begin{code}
data Type Δ where

  ` : 
      (α : TVar Δ κ) →
      --------
      Type Δ κ

  `λ : 
      
      (τ : Type (Δ ,, κ₁) κ₂) → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
      (τ₂ : Type Δ κ₁) → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         (τ₁ : Type Δ ★) →
         (τ₂ : Type Δ ★) → 
         --------
         Type Δ ★

  `∀    :
      
         {κ : Kind} → (τ : Type (Δ ,, κ) ★) →
         -------------
         Type Δ ★

  μ     :
      
         (φ : Type Δ (★ `→ ★)) → 
         -------------
         Type Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : Pred Type Δ R[ κ₁ ]) → (τ : Type Δ ★) → 
         ---------------------
         Type Δ ★       


  ------------------------------------------------------------------
  -- Rω business

  ⦅_⦆ : (xs : SimpleRow Type Δ R[ κ ]) (ordered : True (ordered? xs)) →
        ----------------------
        Type Δ R[ κ ]

  -- labels
  lab :
    
        (l : Label) → 
        --------
        Type Δ L

  -- label constant formation
  ⌊_⌋ :
        (τ : Type Δ L) →
        ----------
        Type Δ ★

  -- Row formation
  _▹_ :
         (l : Type Δ L) → (τ : Type Δ κ) → 
         -------------------
         Type Δ R[ κ ]

  _<$>_ : 

       (φ : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
       ----------------------------------------
       Type Δ R[ κ₂ ]

  -- Record formation
  Π     :
          {notLabel : True (notLabel? κ)} →
          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :

          {notLabel : True (notLabel? κ)} →
          ----------------
          Type Δ (R[ κ ] `→ κ)

  _─_ : 
      
        Type Δ R[ κ ] → Type Δ R[ κ ] → 
        ---------------------------------
        Type Δ R[ κ ]
\end{code}

\subsubsection{The ordering predicate}~
\begin{code}
Ordered [] = ⊤
Ordered (x ∷ []) = ⊤
Ordered ((l₁ , _) ∷ (l₂ , τ) ∷ xs) = l₁ < l₂ × Ordered ((l₂ , τ) ∷ xs)

ordered? [] = yes tt
ordered? (x ∷ []) = yes tt
ordered? ((l₁ , _) ∷ (l₂ , _) ∷ xs) with l₁ <? l₂ | ordered? ((l₂ , _) ∷ xs)
... | yes p | yes q  = yes (p , q)
... | yes p | no q  = no (λ { (_ , oxs) → q oxs })
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})

cong-SimpleRow : {sr₁ sr₂ : SimpleRow Type Δ R[ κ ]} {wf₁ : True (ordered? sr₁)} {wf₂ : True (ordered? sr₂)} → 
                 sr₁ ≡ sr₂ → 
                ⦅ sr₁ ⦆ wf₁ ≡ ⦅ sr₂ ⦆ wf₂
cong-SimpleRow {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite Dec→Irrelevant (Ordered sr₁) (ordered? sr₁) wf₁ wf₂ = refl

map-overᵣ : ∀ (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) (f : Type Δ₁ κ₁ → Type Δ₁ κ₂) → 
              Ordered ρ → Ordered (map (overᵣ f) ρ)
map-overᵣ [] f oρ = tt
map-overᵣ (x ∷ []) f oρ = tt
map-overᵣ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , (map-overᵣ ((l₂ , _) ∷ ρ) f oρ)
\end{code}

\subsubsection{Flipped map operator}~

\begin{code}
-- Flapping. 
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) <$> (` (S Z))))

_??_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f ?? a = flap · f · a
\end{code}

\subsubsection{The (syntactic) complement operator}~

\begin{code}
infix 0 _∈L_

data _∈L_ : (l : Label) → SimpleRow Type Δ R[ κ ] → Set  where
  Here : ∀ {τ : Type Δ κ} {xs : SimpleRow Type Δ R[ κ ]} {l : Label} → 
         l ∈L (l , τ) ∷ xs
  There : ∀ {τ : Type Δ κ} {xs : SimpleRow Type Δ R[ κ ]} {l l' : Label} → 
          l ∈L xs → l ∈L (l' , τ) ∷ xs

_∈L?_ : ∀ (l : Label) (xs : SimpleRow Type Δ R[ κ ]) → Dec (l ∈L xs)
l ∈L? [] = no (λ { () })
l ∈L? ((l' , _) ∷ xs) with l ≟ l' 
... | yes refl = yes Here
... | no  p with l ∈L? xs 
...         | yes p = yes (There p)
...         | no  q = no λ { Here → p refl ; (There x) → q x }

_─s_ : ∀ (xs ys : SimpleRow Type Δ R[ κ ]) → SimpleRow Type Δ R[ κ ]
[] ─s ys = []
((l , τ) ∷ xs) ─s ys with l ∈L? ys 
... | yes _ = xs ─s ys
... | no  _ = (l , τ) ∷ (xs ─s ys)
\end{code}

\subsubsection{Type renaming}

\begin{code}
Renamingₖ : KEnv → KEnv → Set
Renamingₖ Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → TVar Δ₂ κ

-- lifting over binders.
liftₖ : Renamingₖ Δ₁ Δ₂ → Renamingₖ (Δ₁ ,, κ) (Δ₂ ,, κ)
liftₖ ρ Z = Z
liftₖ ρ (S x) = S (ρ x)

renₖ : Renamingₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
renPredₖ : Renamingₖ Δ₁ Δ₂ → Pred Type Δ₁ R[ κ ] → Pred Type Δ₂ R[ κ ]
renRowₖ : Renamingₖ Δ₁ Δ₂ → SimpleRow Type Δ₁ R[ κ ] → SimpleRow Type Δ₂ R[ κ ]
orderedRenRowₖ : (r : Renamingₖ Δ₁ Δ₂) → (xs : SimpleRow Type Δ₁ R[ κ ]) → Ordered xs → 
                 Ordered (renRowₖ r xs)

renₖ r (` x) = ` (r x)
renₖ r (`λ τ) = `λ (renₖ (liftₖ r) τ)
renₖ r (τ₁ · τ₂) = (renₖ r τ₁) · (renₖ r τ₂)
renₖ r (τ₁ `→ τ₂) = (renₖ r τ₁) `→ (renₖ r τ₂)
renₖ r (π ⇒ τ) = renPredₖ r π ⇒ renₖ r τ 
renₖ r (`∀ τ) = `∀ (renₖ (liftₖ r) τ)
renₖ r (μ F) = μ (renₖ r F)
renₖ r (Π {notLabel = nl}) = Π {notLabel = nl}
renₖ r (Σ {notLabel = nl}) = Σ {notLabel = nl}
renₖ r (lab x) = lab x
renₖ r ⌊ ℓ ⌋ = ⌊ (renₖ r ℓ) ⌋
renₖ r (f <$> m) = renₖ r f <$> renₖ r m
renₖ r (⦅ xs ⦆ oxs) = ⦅ renRowₖ r xs ⦆ (fromWitness (orderedRenRowₖ r xs (toWitness oxs)))
renₖ r (ρ₂ ─ ρ₁) = renₖ r ρ₂ ─ renₖ r ρ₁
renₖ r (l ▹ τ) = renₖ r l ▹ renₖ r τ

renPredₖ ρ (ρ₁ · ρ₂ ~ ρ₃) = renₖ ρ ρ₁ · renₖ ρ ρ₂ ~ renₖ ρ ρ₃
renPredₖ ρ (ρ₁ ≲ ρ₂) = (renₖ ρ ρ₁) ≲ (renₖ ρ ρ₂) 

renRowₖ r [] = [] 
renRowₖ r ((l , τ) ∷ xs) = (l , renₖ r τ) ∷ renRowₖ r xs

orderedRenRowₖ r [] oxs = tt
orderedRenRowₖ r ((l , τ) ∷ []) oxs = tt
orderedRenRowₖ r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedRenRowₖ r ((l₂ , υ) ∷ xs) oxs

weakenₖ : Type Δ κ₂ → Type (Δ ,, κ₁) κ₂
weakenₖ = renₖ S

weakenPredₖ : Pred Type Δ R[ κ₂ ] → Pred Type (Δ ,, κ₁) R[ κ₂ ]
weakenPredₖ = renPredₖ S
\end{code}

\subsubsection{Type substitution}

\begin{code}
Substitutionₖ : KEnv → KEnv → Set
Substitutionₖ Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → Type Δ₂ κ

-- lifting a substitution over binders.
liftsₖ :  Substitutionₖ Δ₁ Δ₂ → Substitutionₖ(Δ₁ ,, κ) (Δ₂ ,, κ)
liftsₖ σ Z = ` Z
liftsₖ σ (S x) = weakenₖ (σ x)

-- This is simultaneous substitution: Given subst σ and type τ, we replace *all*
-- variables in τ with the types mapped to by σ.
subₖ : Substitutionₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
subPredₖ : Substitutionₖ Δ₁ Δ₂ → Pred Type Δ₁ κ → Pred Type Δ₂ κ
subRowₖ : Substitutionₖ Δ₁ Δ₂ → SimpleRow Type Δ₁ R[ κ ] → SimpleRow Type Δ₂ R[ κ ]
orderedSubRowₖ : (σ : Substitutionₖ Δ₁ Δ₂) → (xs : SimpleRow Type Δ₁ R[ κ ]) → Ordered xs → 
                 Ordered (subRowₖ σ xs)
-- subₖ σ ε = ε
subₖ σ (` x) = σ x
subₖ σ (`λ τ) = `λ (subₖ (liftsₖ σ) τ)
subₖ σ (τ₁ · τ₂) = (subₖ σ τ₁) · (subₖ σ τ₂)
subₖ σ (τ₁ `→ τ₂) = (subₖ σ τ₁) `→ (subₖ σ τ₂)
subₖ σ (π ⇒ τ) = subPredₖ σ π ⇒ subₖ σ τ 
subₖ σ (`∀ τ) = `∀ (subₖ (liftsₖ σ) τ)
subₖ σ (μ F) = μ (subₖ σ F)
subₖ σ (Π {notLabel = nl}) = Π {notLabel = nl}
subₖ σ (Σ {notLabel = nl}) = Σ {notLabel = nl}
subₖ σ (lab x) = lab x
subₖ σ ⌊ ℓ ⌋ = ⌊ (subₖ σ ℓ) ⌋
subₖ σ (f <$> a) = subₖ σ f <$> subₖ σ a
subₖ σ (ρ₂ ─ ρ₁) = subₖ σ ρ₂ ─ subₖ σ ρ₁
subₖ σ (⦅ xs ⦆ oxs) = ⦅ subRowₖ σ xs ⦆ (fromWitness (orderedSubRowₖ σ xs (toWitness oxs)))
subₖ σ (l ▹ τ) = (subₖ σ l) ▹ (subₖ σ τ)
subRowₖ σ [] = [] 
subRowₖ σ ((l , τ) ∷ xs) = (l , subₖ σ τ) ∷ subRowₖ σ xs

orderedSubRowₖ r [] oxs = tt
orderedSubRowₖ r ((l , τ) ∷ []) oxs = tt
orderedSubRowₖ r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedSubRowₖ r ((l₂ , υ) ∷ xs) oxs

subRowₖ-isMap : ∀ (σ : Substitutionₖ Δ₁ Δ₂) (xs : SimpleRow Type Δ₁ R[ κ ]) → 
                  subRowₖ σ xs ≡ map (overᵣ (subₖ σ)) xs

subRowₖ-isMap σ [] = refl
subRowₖ-isMap σ (x ∷ xs) = cong₂ _∷_ refl (subRowₖ-isMap σ xs)

subPredₖ σ (ρ₁ · ρ₂ ~ ρ₃) = subₖ σ ρ₁ · subₖ σ ρ₂ ~ subₖ σ ρ₃
subPredₖ σ (ρ₁ ≲ ρ₂) = (subₖ σ ρ₁) ≲ (subₖ σ ρ₂) 

-- Extension of a substitution by A
extendₖ : Substitutionₖ Δ₁ Δ₂ → (A : Type Δ₂ κ) → Substitutionₖ(Δ₁ ,, κ) Δ₂
extendₖ σ A Z = A
extendₖ σ A (S x) = σ x

-- Single variable subₖstitution is a special case of simultaneous subₖstitution.
_βₖ[_] : Type (Δ ,, κ₁) κ₂ → Type Δ κ₁ → Type Δ κ₂
B βₖ[ A ] = subₖ (extendₖ ` A) B
\end{code}

\subsection{Type equivalence}

\begin{code}
infix 0 _≡t_
infix 0 _≡p_
data _≡p_ : Pred Type Δ R[ κ ] → Pred Type Δ R[ κ ] → Set
data _≡t_ : Type Δ κ → Type Δ κ → Set 

private
    variable
        ℓ ℓ₁ ℓ₂ ℓ₃ : Label
        l l₁ l₂ l₃ : Type Δ L
        ρ₁ ρ₂ ρ₃   : Type Δ R[ κ ]
        π₁ π₂    : Pred Type Δ R[ κ ]
        τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Δ κ 

data _≡r_ : SimpleRow Type Δ R[ κ ] → SimpleRow Type Δ R[ κ ] → Set where 

  eq-[] : 
    
    _≡r_  {Δ = Δ} {κ = κ} [] []
    
  eq-cons : {xs ys : SimpleRow Type Δ R[ κ ]} → 

            ℓ₁ ≡ ℓ₂ → τ₁ ≡t τ₂ → xs ≡r ys → 
            -----------------------
            ((ℓ₁ , τ₁) ∷ xs) ≡r ((ℓ₂ , τ₂) ∷ ys)

data _≡p_ where

  _eq-≲_ : 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → 
        --------------------
        τ₁ ≲ τ₂ ≡p  υ₁ ≲ υ₂

  _eq-·_~_ : 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → τ₃ ≡t υ₃ → 
        -----------------------------------
        τ₁ · τ₂ ~ τ₃ ≡p  υ₁ · υ₂ ~ υ₃

data _≡t_ where 

  -- -------------------------------------
  -- Eq. relation
    
    eq-refl : 

        ------
        τ ≡t τ 

    eq-sym : 
    
        τ₁ ≡t τ₂ →
        ----------
        τ₂ ≡t τ₁

    eq-trans : 
    
        τ₁ ≡t τ₂ → τ₂ ≡t τ₃ → 
        ---------------------
        τ₁ ≡t τ₃

  -- -------------------------------------
  -- Congruence rules

    eq-→ : 

        τ₁ ≡t τ₂ → υ₁ ≡t υ₂ →
        -----------------------
        τ₁ `→ υ₁ ≡t τ₂ `→ υ₂

    eq-∀ : 

        τ ≡t υ →
        ----------------
        `∀ τ ≡t `∀ υ

    eq-μ : 

        τ ≡t υ →
        ----------------
        μ τ ≡t μ υ

    eq-λ : ∀ {τ υ : Type (Δ ,, κ₁) κ₂} → 

        τ ≡t υ →
        ----------------
        `λ τ ≡t `λ υ

    eq-· :

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
        ---------------------
        τ₁ · τ₂ ≡t υ₁ · υ₂

    eq-<$> : ∀ {τ₁ υ₁ : Type Δ (κ₁ `→ κ₂)} {τ₂ υ₂ : Type Δ R[ κ₁ ]} → 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
        ---------------------
        τ₁ <$> τ₂ ≡t υ₁ <$> υ₂        

    eq-⌊⌋ : 

        τ ≡t υ →
        -------------
        ⌊ τ ⌋ ≡t ⌊ υ ⌋

    eq-⇒ :

         π₁ ≡p π₂ → τ₁ ≡t τ₂ →
        ------------------------
        (π₁ ⇒ τ₁) ≡t (π₂ ⇒ τ₂)

    eq-lab : 
           
           ℓ₁ ≡ ℓ₂ →
           -------------
           lab {Δ = Δ} ℓ₁ ≡t lab ℓ₂
    
    eq-row : 
        ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} {oρ₁ : True (ordered? ρ₁)} 
          {oρ₂ : True (ordered? ρ₂)} → 
  
        ρ₁ ≡r ρ₂ → 
        -------------------------------------------
        ⦅ ρ₁ ⦆ oρ₁ ≡t ⦅ ρ₂ ⦆ oρ₂

    eq-▹ : ∀ {l₁ l₂ : Type Δ L} {τ₁ τ₂ : Type Δ κ} → 
         
           l₁ ≡t l₂   →    τ₁ ≡t τ₂ → 
           ------------------------------------
           (l₁ ▹ τ₁) ≡t (l₂ ▹ τ₂)

    eq-─ : ∀ {ρ₂ ρ₁ υ₂ υ₁ : Type Δ R[ κ ]} → 
         
           ρ₂ ≡t υ₂   →    ρ₁ ≡t υ₁ → 
           ------------------------------------
           (ρ₂ ─ ρ₁) ≡t (υ₂ ─ υ₁)

  -- -------------------------------------
  -- η-laws  
         
    eq-η : ∀ {f : Type Δ (κ₁ `→ κ₂)} → 


        ----------------------------
        f ≡t `λ (weakenₖ f · (` Z))

  -- -------------------------------------
  -- Computational laws

    eq-β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) ≡t (τ₁ βₖ[ τ₂ ])

    eq-labTy : 

        l ≡t lab ℓ → 
        -------------------------------------------
        (l ▹ τ) ≡t ⦅ [ (ℓ  , τ) ] ⦆ tt

    eq-▹$ : ∀ {l} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        ---------------------------------
        (F <$> (l ▹ τ)) ≡t (l ▹ (F · τ))

    eq-<$>-─ : ∀ {F : Type Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : Type Δ R[ κ₁ ]} → 

      
      ------------------------------------------
      F <$> (ρ₂ ─ ρ₁) ≡t (F <$> ρ₂) ─ (F <$> ρ₁)

    eq-map : ∀ {F : Type Δ (κ₁ `→ κ₂)} {ρ : SimpleRow Type Δ R[ κ₁ ]} {oρ : True (ordered? ρ)} → 

         -------------------------------
         F <$> (⦅ ρ ⦆ oρ) ≡t ⦅ map (overᵣ (F ·_)) ρ ⦆ (fromWitness (map-overᵣ ρ (F ·_) (toWitness oρ)))

    eq-map-id : ∀ {κ} {τ : Type Δ R[ κ ]} → 

        ---------------------------------------- 
        (`λ {κ₁ = κ} (` Z)) <$> τ ≡t τ

    eq-map-∘ : ∀ {κ₃} {f : Type Δ (κ₂ `→ κ₃)} {g : Type Δ (κ₁ `→ κ₂)} {τ : Type Δ R[ κ₁ ]} → 

        ---------------------------------------- 
        (f <$> (g <$> τ))  ≡t (`λ (weakenₖ f · (weakenₖ g · (` Z)))) <$> τ 
    
    eq-Π : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : True (notLabel? κ)} → 

         ----------------------------
         Π {notLabel = nl} · ρ ≡t Π {notLabel = nl} <$> ρ

    eq-Σ : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : True (notLabel? κ)} → 

         ----------------------------
         Σ {notLabel = nl} · ρ ≡t Σ {notLabel = nl} <$> ρ
        
    eq-Π-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : True (notLabel? κ₂)} → 

        ----------------------------
        (Π {notLabel = nl} · ρ) · τ ≡t Π {notLabel = nl} · (ρ ?? τ)

    eq-Σ-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : True (notLabel? κ₂)} → 

        ----------------------------
        (Σ {notLabel = nl} · ρ) · τ ≡t Σ {notLabel = nl} · (ρ ?? τ)

    eq-compl : ∀ {xs ys : SimpleRow Type Δ R[ κ ]} 
                 {oxs : True (ordered? xs)} {oys : True (ordered? ys)} {ozs : True (ordered? (xs ─s ys))} → 

                 --------------------------------------------
                 (⦅ xs ⦆ oxs) ─ (⦅ ys ⦆ oys) ≡t ⦅ (xs ─s ys) ⦆ ozs
\end{code}

\subsubsection{Some admissable rules} We confirm that (i) $\Pi$ and $\Sigma$ are mapped over nested rows, and (ii) $\lambda$-bindings $\eta$-expand over $\Pi$ and $\Sigma$.

\begin{code}
eq-Π▹ : ∀ {l} {τ : Type Δ R[ κ ]}{nl : True (notLabel? κ)} → 
        (Π {notLabel = nl} · (l ▹ τ)) ≡t (l ▹ (Π {notLabel = nl} · τ))
eq-Π▹ = eq-trans eq-Π eq-▹$

eq-Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) κ₂} {nl : True (notLabel? κ₂)} → 
        Π {notLabel = nl} · (l ▹ `λ τ) ≡t `λ (Π {notLabel = nl} · (weakenₖ l ▹ τ))
\end{code}
\begin{code}[hide]
eq-Πλ = bot _
\end{code}


\section{Normal forms}


\begin{figure}
\begin{gather*}
\begin{array}{r@{\hspace{7px}}l@{\qquad\qquad}r@{\hspace{7px}}l}
  \text{Type variables} & \alpha \in \mathcal A &
  \text{Labels} & \ell \in \mathcal L
\end{array} \\
\begin{doublesyntaxarray}
  \mcl{\text{Ground Kinds}}  & \gamma   & ::= & \TypeK \mid \LabK \\
  \mcl{\text{Kinds}}         & \kappa    & ::= & \gamma \mid \kappa \to \kappa \mid  \RowK \kappa \\
  \mcl{\text{Row Literals}}   & \NormalRows \ni \Normal \rho    & ::= & \RowIx i 0 m {\LabTy {\ell_i} {\Normal {\tau_i}}} \\
  \mcl{\text{Neutral Types}} & n    & ::= & \alpha \mid n \, {\Normal \tau}  \\
  \mcl{\text{Normal Types}}  & \NormalTypes \ni \Normal \tau, \Normal \phi & ::= & n \mid \hat{\phi}^{\star} \, n \mid \Normal{\rho} \mid \Normal{\pi} \then \Normal{\tau} \mid \forall \alpha\co\kappa. \Normal{\tau} \mid \lambda \alpha\co\kappa. \Normal{\tau} \\
                             &       &     & \mid & \LabTy n {\Normal \tau} \mid \ell \mid \Sing {\Normal \tau} \mid {\Normal \tau} \Compl {\Normal \tau} \mid \KFam \Pi \TypeK \, {\Normal \tau} \mid \KFam \Sigma \TypeK \, {\Normal \tau}  \\
\end{doublesyntaxarray}
\end{gather*}
\begin{small}
\begin{gather*}
\fbox{$\KindJNF \Delta {\Normal \tau} {\kappa}$} \, \fbox{$\KindJNE \Delta {n} {\kappa}$} \\
\ib{
  \irule[\kruleNF{ne}]
    {\KindJNE \Delta n \gamma};
    {\KindJNF \Delta n \gamma}}
\isp
\ib{
  \irule[\kruleNF{$\Compl$}]
    {\KindJNF \Delta {\Normal {\tau_i}} {\RowK \kappa}}
    {\Normal{\tau_1} \notin \NormalRows \, \text{or}\, \Normal{\tau_2} \notin \NormalRows};
    {\KindJNF \Delta {\Normal{\tau_2} \Compl \Normal{\tau_1}} {\RowK \kappa}}}
\isp
\ib{
  \irule[\kruleNF{$\triangleright$}]
    {\KindJNE \Delta {n} {\LabK}}{\KindJNF \Delta {\Normal \tau} \kappa};
    {\KindJNF \Delta {\LabTy n {\Normal \tau}}{\RowK \kappa}}}
\end{gather*}
\end{small}
\caption{Normal type forms}
\label{fig:type-normalization}
\end{figure}

We define reduction on types $\tau \RedT \tau'$ by directing the type equivalence judgment $\TEqvJ \varepsilon \tau {\tau'} \kappa$ from left to right (with the exception of rule \errule{map$_\mathsf{id}$}, which reduces right-to-left).

\subsection{Mechanized syntax}

\begin{code}
data NormalType (Δ : KEnv) : Kind → Set

NormalPred : KEnv → Kind → Set 
NormalPred = Pred NormalType

NormalOrdered : SimpleRow NormalType Δ R[ κ ] → Set 
normalOrdered? : ∀ (xs : SimpleRow NormalType Δ R[ κ ]) → Dec (NormalOrdered xs)

IsNeutral IsNormal : NormalType Δ κ → Set 
isNeutral? : ∀ (τ : NormalType Δ κ) → Dec (IsNeutral τ)
isNormal? : ∀ (τ : NormalType Δ κ) → Dec (IsNormal τ)

NotSimpleRow : NormalType Δ R[ κ ] → Set 
notSimpleRows? : ∀ (τ₁ τ₂ : NormalType Δ R[ κ ]) → Dec (NotSimpleRow τ₁ or NotSimpleRow τ₂)

data NeutralType Δ : Kind → Set where
  ` : 
      (α : TVar Δ κ) → 
      ---------------------------
      NeutralType Δ κ

  _·_ : 
      
      (f : NeutralType Δ (κ₁ `→ κ)) → 
      (τ : NormalType Δ κ₁) → 
      ---------------------------
      NeutralType Δ κ

data NormalType Δ where

  ne : 

      (x : NeutralType Δ κ) → {ground : True (ground? κ)} → 
      --------------
      NormalType Δ κ

  _<$>_ : (φ : NormalType Δ (κ₁ `→ κ₂)) → NeutralType Δ R[ κ₁ ] →
          --------------------------------------------------
          NormalType Δ R[ κ₂ ]

  `λ :

      (τ : NormalType (Δ ,, κ₁) κ₂) → 
      --------------------------
      NormalType Δ (κ₁ `→ κ₂)

  _`→_ : 

      (τ₁ τ₂ : NormalType Δ ★) →
      -----------------
      NormalType Δ ★

  `∀    :
      
      (τ : NormalType (Δ ,, κ) ★) →
      --------------------------------------
      NormalType Δ ★

  μ     :
      
      (φ : NormalType Δ (★ `→ ★)) →
      -------------------------
      NormalType Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : NormalPred Δ R[ κ₁ ]) → (τ : NormalType Δ ★) → 
         ---------------------
         NormalType Δ ★       

  ------------------------------------------------------------------
  -- Rω business


  ⦅_⦆ : (ρ : SimpleRow NormalType Δ R[ κ ]) → (oρ : True (normalOrdered? ρ)) →
        ----------------------
       NormalType Δ R[ κ ]

--   -- labels
  lab :
    
      (l : Label) → 
      --------
      NormalType Δ L

  -- label constant formation
  ⌊_⌋ :
      (l : NormalType Δ L) →
      -----------------
      NormalType Δ ★

  Π  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ------------------
      NormalType Δ ★


  Σ  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ---------------
      NormalType Δ ★

  _─_ : (ρ₂ ρ₁ : NormalType Δ R[ κ ]) → {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
        NormalType Δ R[ κ ]

  _▹ₙ_ : (l : NeutralType Δ L) (τ : NormalType Δ κ) → 
         ------------------------------------
         NormalType Δ R[ κ ]
\end{code}


\begin{code}[hide]
IsNeutral (ne x) = ⊤ 
IsNeutral _ = ⊥

isNeutral? (ne x) = yes tt
isNeutral? (l ▹ₙ τ) = no λ ()
isNeutral? (`λ x) = no λ ()
isNeutral? (x `→ x₁) = no λ ()
isNeutral? (`∀ x) = no λ ()
isNeutral? (μ x) = no λ ()
isNeutral? (π ⇒ x) = no λ ()
isNeutral? (⦅ ρ ⦆ oρ) = no λ ()
isNeutral? (lab l) = no λ ()
isNeutral? ⌊ x ⌋ = no λ ()
isNeutral? (Π x) = no λ ()
isNeutral? (Σ x) = no λ ()
isNeutral? (c ─ c₁) = no λ ()
isNeutral? ((φ <$> n)) = no λ ()

IsNormal (ne x)     = ⊥
IsNormal _     = ⊤

isNormal? (ne x) = no λ ()
isNormal? (l ▹ₙ τ) = yes tt
isNormal? (`λ x) = yes tt
isNormal? (x `→ x₁) = yes tt
isNormal? (`∀ x) = yes tt
isNormal? (μ x) = yes tt
isNormal? (π ⇒ x) = yes tt
isNormal? (⦅ ρ ⦆ oρ) = yes tt
isNormal? (lab l) = yes tt
isNormal? ⌊ x ⌋ = yes tt
isNormal? (Π x) = yes tt
isNormal? (Σ x) = yes tt
isNormal? (ρ₂ ─ ρ₁) = yes tt
isNormal? ((φ <$> n)) = yes tt
\end{code}                

--------------------------------------------------------------------------------
-- Ordered predicate
\begin{code}[hide]
open IsStrictPartialOrder (SPO) renaming (trans to <-trans)
\end{code}

\begin{code}
NormalOrdered [] = ⊤
NormalOrdered ((l , _) ∷ []) = ⊤
NormalOrdered ((l₁ , _) ∷ (l₂ , τ) ∷ xs) = l₁ < l₂ × NormalOrdered ((l₂ , τ) ∷ xs)

normalOrdered? [] = yes tt
normalOrdered? ((l , τ) ∷ []) = yes tt
normalOrdered? ((l₁ , _) ∷ (l₂ , _) ∷ xs) with l₁ <? l₂ | normalOrdered? ((l₂ , _) ∷ xs)
... | yes p | yes q  = yes (p , q)
... | yes p | no q  = no (λ { (_ , oxs) → q oxs })
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})
\end{code}

\begin{code}[hide]
NormalIrrelevantOrdered : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → Irrelevant (True (normalOrdered? ρ))
NormalIrrelevantOrdered ρ = Dec→Irrelevant (NormalOrdered ρ) (normalOrdered? ρ)

cong-⦅⦆ : {sr₁ sr₂ : SimpleRow NormalType Δ R[ κ ]} {wf₁ : True (normalOrdered? sr₁)} {wf₂ : True (normalOrdered? sr₂)} → 
                 sr₁ ≡ sr₂ → 
                _≡_ {A = NormalType Δ R[ κ ]} (⦅ sr₁ ⦆ wf₁) (⦅ sr₂ ⦆ wf₂)
cong-⦅⦆ {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite NormalIrrelevantOrdered sr₁ wf₁ wf₂ = refl


inj-⦅⦆ : {sr₁ sr₂ : SimpleRow NormalType Δ R[ κ ]} 
         {wf₁ : True (normalOrdered? sr₁)} 
         {wf₂ : True (normalOrdered? sr₂)} → 
         _≡_ {A = NormalType Δ R[ κ ]} (⦅ sr₁ ⦆ wf₁) (⦅ sr₂ ⦆ wf₂) → 
         sr₁ ≡ sr₂
inj-⦅⦆ {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite NormalIrrelevantOrdered sr₁ wf₁ wf₂ = refl
                

--------------------------------------------------------------------------------
-- Ordered lists yield ordered tails

normalOrdered-tail : ∀ (x : Label × NormalType Δ κ) (ρ : SimpleRow NormalType Δ R[ κ ]) → 
               NormalOrdered (x ∷ ρ) → 
               NormalOrdered ρ 
normalOrdered-tail x [] oxρ = tt
normalOrdered-tail (l , snd₁) ((l₁ , snd₂) ∷ ρ) (_ , oxρ) = oxρ 

--------------------------------------------------------------------------------
-- Mapping over preserves ordering

normal-map-overᵣ : ∀ (ρ : SimpleRow NormalType Δ₁ R[ κ₁ ]) (f : NormalType Δ₁ κ₁ → NormalType Δ₁ κ₂) → 
                   NormalOrdered ρ → NormalOrdered (map (overᵣ f) ρ)
normal-map-overᵣ [] f oρ = tt
normal-map-overᵣ (x ∷ []) f oρ = tt
normal-map-overᵣ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , (normal-map-overᵣ ((l₂ , _) ∷ ρ) f oρ)
\end{code}

\begin{code}
NotSimpleRow (ne x) = ⊤
NotSimpleRow ((φ <$> τ)) = ⊤
NotSimpleRow (⦅ ρ ⦆ oρ) = ⊥
NotSimpleRow (τ ─ τ₁) = ⊤
NotSimpleRow (x ▹ₙ τ) = ⊤
\end{code}

\begin{code}[hide]
notSimpleRows? (ne x) _ = yes (left tt)
notSimpleRows? ((τ₁ <$> ρ)) _ = yes (left tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (ne x) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (⦅ ρ₁ ⦆ oρ₁) = no λ { (left ()) ; (right ()) }
notSimpleRows? (⦅ ρ ⦆ oρ) (ρ₁ ─ ρ₂) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (x ▹ₙ ρ₁) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) ((φ <$> _)) = yes (right tt)
notSimpleRows? (ρ₂ ─ ρ₃) _ = yes (left tt)
notSimpleRows? (x ▹ₙ ρ₂) _ = yes (left tt)
\end{code}

\subsection{Properties of normal types}

The syntax of normal types is defined precisely so as to enjoy canonical forms based on kind. We first demonstrate that neutral types and inert complements cannot occur in empty contexts.

\begin{code}
noNeutrals : NeutralType ∅ κ → ⊥

noNeutrals (n · τ) = noNeutrals n 

noComplements : ∀ {ρ₁ ρ₂ ρ₃ : NormalType ∅ R[ κ ]}
                  (nsr : True (notSimpleRows? ρ₃ ρ₂)) → 
                  ρ₁ ≡ (ρ₃ ─ ρ₂) {nsr} → 
                  ⊥
\end{code}
\begin{code}[hide]
noComplements {ρ₁ = ne x₁ ─ _} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ne x₁} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ((ρ₂ ─ ρ₃) {nsr'})} {_} {_} nsr refl = noComplements {ρ₂ = ρ₃} {ρ₂} nsr' refl
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ (l ▹ₙ ρ₂)} {_} {_} nsr refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ((φ <$> τ))} {_} {_} nsr refl = ⊥-elim (noNeutrals τ)
noComplements {ρ₁ = ((ρ₃ ─ ρ₂) {nsr'}) ─ _} {_} {_} nsr refl = noComplements {ρ₂ = ρ₂} {ρ₃} nsr' refl
noComplements {ρ₁ = (l ▹ₙ ρ₃) ─ _} {_} {_} nsr refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ((φ <$> τ)) ─ _} nsr refl = ⊥-elim (noNeutrals τ)
\end{code}

Now:

\begin{code}
arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl

row-canonicity-∅ : (ρ : NormalType ∅ R[ κ ]) → 
                    ∃[ xs ] Σ[ oxs ∈ True (normalOrdered? xs) ] 
                    (ρ ≡ ⦅ xs ⦆ oxs)
row-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
row-canonicity-∅ (⦅ ρ ⦆ oρ) = ρ , oρ , refl
row-canonicity-∅ ((ρ ─ ρ₁) {nsr}) = ⊥-elim (noComplements nsr refl)
row-canonicity-∅ (l ▹ₙ ρ) = ⊥-elim (noNeutrals l)
row-canonicity-∅ ((φ <$> ρ)) = ⊥-elim (noNeutrals ρ)

label-canonicity-∅ : ∀ (l : NormalType ∅ L) → ∃[ s ] (l ≡ lab s)
label-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
label-canonicity-∅ (lab s) = s , refl
\end{code}



\section{Semantic types}

\subsection{Renaming and substitution}

\section{Normalization by Evaluation}

\subsection{Helping evaluation}
\subsection{Evaluation}

\section{Metatheory}
\subsection{A logical relation for completeness}
\subsubsection{Properties}

\subsection{The fundamental theorem and completeness}

\subsection{A logical relation for soundness}
\subsubsection{Properties}
\subsection{The fundamental theorem and soundness}

\section{The rest of the picture}

\section{Most closely related work}
\subsubsection{\citet{ChapmanKNW19}}
\subsubsection{\citet{AllaisBM13}}


\bibliographystyle{plainnat}
\bibliography{NBE}
\end{document}
%%% Local Variables: 
%%% TeX-command-extra-options: "-shell-escape"
%%% End:
%  LocalWords:  denotational Agda Wadler dPoint sqrt subtyping coercions Intr
%  LocalWords:  RowTypes Bool eval GHC reified HillerstromL Leijen LindleyM RO
%  LocalWords:  ChapmanKNW Aydemir AbelAHPMSS AbelC AbelOV plfa HubersIMM STLC
%  LocalWords:  MorrisM denotationally DenotationalSoundness RowTheories Suc de
%  LocalWords:  ReifyingVariants RowTheory BerthomieuM CardelliMMS HarperP NatF
%  LocalWords:  XueOX GasterJ Sipser SaffrichTM Env Expr Agda's Leivant ChanW
%  LocalWords:  ThiemannW ImpredicativeSet ImpredicativeSetSucks AbelP chapman
%  LocalWords:  AltenkirchK KaposiKK Gaster XieOBS BiXOS Chlipala objTypes Bahr
%  LocalWords:  Garrigue KEnv PEnv

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
\newunicodechar{₄}{$_{4}$}
\newunicodechar{⦅}{$\llparenthesis$}
\newunicodechar{⦆}{$\rrparenthesis$}
\newunicodechar{─}{$\setminus$}
\newunicodechar{∷}{$\co\co$}
\newunicodechar{ₖ}{$_{k}$}
\newunicodechar{ₙ}{$_{n}$}
\newunicodechar{≟}{$\overset{?}{=}$}
\newunicodechar{𝒯}{$\mathcal T$}
\newunicodechar{⨾}{$\co$}
\newunicodechar{Ξ}{$\Xi$}
\newunicodechar{ξ}{$\xi$}

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

Finally, it is helpful to reflect instances of propositional equality in Agda to proofs of type-equivalence.

\begin{code}
inst : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡ τ₂ → τ₁ ≡t τ₂ 
inst refl = eq-refl
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

\subsection{Renaming}

Renaming over normal types is defined in an entirely straightforward manner.

\begin{code}
renₖNE   : Renamingₖ Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
renₖNF     : Renamingₖ Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
renRowₖNF : Renamingₖ Δ₁ Δ₂ → SimpleRow NormalType Δ₁ R[ κ ] → SimpleRow NormalType Δ₂ R[ κ ]
renPredₖNF : Renamingₖ Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
\end{code}

Care must be given to ensure that the \verb!NormalOrdered! and \verb!NotSimpleRow! predicates are preserved.

\begin{code}
orderedRenRowₖNF : (r : Renamingₖ Δ₁ Δ₂) → (xs : SimpleRow NormalType Δ₁ R[ κ ]) → NormalOrdered xs → 
                 NormalOrdered (renRowₖNF r xs)

nsrRenₖNF : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ₁ ρ₂ : NormalType Δ₁ R[ κ ]) → NotSimpleRow ρ₂ or NotSimpleRow ρ₁ → 
              NotSimpleRow (renₖNF r ρ₂) or NotSimpleRow (renₖNF r ρ₁)
nsrRenₖNF' : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ : NormalType Δ₁ R[ κ ]) → NotSimpleRow ρ → 
              NotSimpleRow (renₖNF r ρ)
\end{code}

\begin{code}[hide]
renₖNE r (` x) = ` (r x)
renₖNE ρ (τ₁ · τ₂) = renₖNE ρ τ₁ · renₖNF ρ τ₂

renₖNF ρ (ne τ {g}) = ne (renₖNE ρ τ) {g}
renₖNF ρ (`λ τ) = `λ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (τ₁ `→ τ₂) = (renₖNF ρ τ₁) `→ (renₖNF ρ τ₂)
renₖNF ρ (π ⇒ τ) = renPredₖNF ρ π ⇒ renₖNF ρ τ
renₖNF ρ (`∀ τ) = `∀ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (μ τ) = μ (renₖNF ρ τ)
renₖNF ρ (lab x) = lab x
renₖNF ρ ⌊ ℓ ⌋ = ⌊ (renₖNF ρ ℓ) ⌋
renₖNF ρ (Π τ) = Π (renₖNF ρ τ)
renₖNF ρ (Σ τ) = Σ (renₖNF ρ τ)
renₖNF r (⦅ ρ ⦆ oρ) = ⦅ renRowₖNF r ρ ⦆ (fromWitness (orderedRenRowₖNF r ρ (toWitness oρ)))
renₖNF ρ (l ▹ₙ τ) = renₖNE ρ l ▹ₙ (renₖNF ρ τ)
renₖNF r ((ρ₂ ─ ρ₁) {nsr}) = (renₖNF r ρ₂ ─ renₖNF r ρ₁) {nsr = fromWitness (nsrRenₖNF r ρ₁ ρ₂ (toWitness nsr))}
renₖNF ρ ((φ <$> x)) = (renₖNF ρ φ <$> renₖNE ρ x) 

renPredₖNF ρ (ρ₁ · ρ₂ ~ ρ₃) = (renₖNF ρ ρ₁) · (renₖNF ρ ρ₂) ~ (renₖNF ρ ρ₃)
renPredₖNF ρ (ρ₁ ≲ ρ₂) = (renₖNF ρ ρ₁) ≲ (renₖNF ρ ρ₂)

renRowₖNF _ [] = []
renRowₖNF r ((l , τ) ∷ ρ) = (l , renₖNF r τ) ∷ renRowₖNF r ρ

nsrRenₖNF' r (ne x) nsr = tt
nsrRenₖNF' r (ρ ─ ρ₁) nsr = tt
nsrRenₖNF' r (x ▹ₙ ρ) nsr = tt
nsrRenₖNF' r ((φ <$> ρ)) nsr = tt

nsrRenₖNF r ρ₁ ρ₂ (left x) = left (nsrRenₖNF' r ρ₂ x)
nsrRenₖNF r ρ₁ ρ₂ (right y) = right (nsrRenₖNF' r ρ₁ y) 

orderedRenRowₖNF r [] oxs = tt
orderedRenRowₖNF r ((l , τ) ∷ []) oxs = tt
orderedRenRowₖNF r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedRenRowₖNF r ((l₂ , υ) ∷ xs) oxs

renRowₖNF-isMap : ∀ (r : Renamingₖ Δ₁ Δ₂) (xs : SimpleRow NormalType Δ₁ R[ κ ]) → 
                  renRowₖNF r xs ≡ map (overᵣ (renₖNF r)) xs 
renRowₖNF-isMap r [] = refl
renRowₖNF-isMap r (x ∷ xs) = cong₂ _∷_ refl (renRowₖNF-isMap r xs)

weakenₖNF : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weakenₖNF = renₖNF S
weakenₖNE : NeutralType Δ κ₂ → NeutralType (Δ ,, κ₁) κ₂
weakenₖNE = renₖNE S 
weakenPredₖNF : NormalPred Δ R[ κ₂ ] → NormalPred (Δ ,, κ₁) R[ κ₂ ]
weakenPredₖNF = renPredₖNF S
\end{code}

\subsection{Embedding}

\begin{code}
⇑ : NormalType Δ κ → Type Δ κ
⇑Row : SimpleRow NormalType Δ R[ κ ] → SimpleRow Type Δ R[ κ ]
⇑NE : NeutralType Δ κ → Type Δ κ
⇑Pred : NormalPred Δ R[ κ ] → Pred Type Δ R[ κ ] 
Ordered⇑ : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → NormalOrdered ρ → 
             Ordered (⇑Row ρ)

⇑ (ne x) = ⇑NE x
⇑ (`λ τ) = `λ (⇑ τ)
⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
⇑ (`∀ τ) = `∀ (⇑ τ)
⇑ (μ τ) = μ (⇑ τ)
⇑ (lab l) = lab l
⇑ ⌊ τ ⌋ = ⌊ ⇑ τ ⌋
⇑ (Π x) = Π · ⇑ x
⇑ (Σ x) = Σ · ⇑ x
⇑ (π ⇒ τ) = (⇑Pred π) ⇒ (⇑ τ)
⇑ (⦅ ρ ⦆ oρ) = ⦅ ⇑Row ρ ⦆ (fromWitness (Ordered⇑ ρ (toWitness oρ)))
⇑ (ρ₂ ─ ρ₁) = ⇑ ρ₂ ─ ⇑ ρ₁
⇑ (l ▹ₙ τ) = (⇑NE l) ▹ (⇑ τ)
⇑ ((F <$> τ)) = (⇑ F) <$> (⇑NE τ) 

⇑Row [] = []
⇑Row ((l , τ) ∷ ρ) = ((l , ⇑ τ) ∷ ⇑Row ρ)

Ordered⇑ [] oρ = tt
Ordered⇑ (x ∷ []) oρ = tt
Ordered⇑ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) (l₁<l₂ , oρ) = l₁<l₂ , Ordered⇑ ((l₂ , _) ∷ ρ) oρ

⇑Row-isMap : ∀ (xs : SimpleRow NormalType Δ₁ R[ κ ]) → 
               ⇑Row xs ≡ map (λ { (l , τ) → l , ⇑ τ }) xs
⇑Row-isMap [] = refl
⇑Row-isMap (x ∷ xs) = cong₂ _∷_ refl (⇑Row-isMap xs)

⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)

⇑Pred (ρ₁ · ρ₂ ~ ρ₃) = (⇑ ρ₁) · (⇑ ρ₂) ~ (⇑ ρ₃)
⇑Pred (ρ₁ ≲ ρ₂) = (⇑ ρ₁) ≲ (⇑ ρ₂)
\end{code}


\section{Semantic types}

\begin{code}

--------------------------------------------------------------------------------
-- Semantic types (definition)

Row : Set → Set 
Row A = ∃[ n ](Fin n → Label × A)

--------------------------------------------------------------------------------
-- Ordered predicate on semantic rows

OrderedRow' : ∀ {A : Set} → (n : ℕ) → (Fin n → Label × A) → Set
OrderedRow' zero P = ⊤
OrderedRow' (suc zero) P = ⊤
OrderedRow' (suc (suc n)) P = (P fzero .fst < P (fsuc fzero) .fst)  × OrderedRow' (suc n) (P ∘ fsuc)

OrderedRow : ∀ {A} → Row A → Set
OrderedRow (n , P) = OrderedRow' n P

--------------------------------------------------------------------------------
-- Defining SemType Δ R[ κ ]

data RowType (Δ : KEnv) (𝒯 : KEnv → Set) : Kind → Set 
NotRow : ∀ {Δ : KEnv} {𝒯 : KEnv → Set} → RowType Δ 𝒯 R[ κ ] → Set 
notRows? : ∀ {Δ : KEnv} {𝒯 : KEnv → Set} → (ρ₂ ρ₁ : RowType Δ 𝒯 R[ κ ]) → Dec (NotRow ρ₂ or NotRow ρ₁)

data RowType Δ 𝒯 where
  _<$>_ : (φ : ∀ {Δ'} → Renamingₖ Δ Δ' → NeutralType Δ' κ₁ → 𝒯 Δ') → 
          NeutralType Δ R[ κ₁ ] → 
          RowType Δ 𝒯 R[ κ₂ ]

  _▹_ : NeutralType Δ L → 𝒯 Δ → RowType Δ 𝒯 R[ κ ]

  row : (ρ : Row (𝒯 Δ)) → OrderedRow ρ → RowType Δ 𝒯 R[ κ ]

  _─_ : (ρ₂ ρ₁ : RowType Δ 𝒯 R[ κ ]) → {nr : NotRow ρ₂ or NotRow ρ₁} →
        RowType Δ 𝒯 R[ κ ]

NotRow (x ▹ x₁) = ⊤
NotRow (row ρ x) = ⊥
NotRow (ρ ─ ρ₁) = ⊤
NotRow (φ <$> ρ) = ⊤

notRows? (x ▹ x₁) ρ₁ = yes (left tt)
notRows? (ρ₂ ─ ρ₃) ρ₁ = yes (left tt)
notRows? (φ <$> ρ) ρ₁ = yes (left tt)
notRows? (row ρ x) (x₁ ▹ x₂) = yes (right tt)
notRows? (row ρ x) (row ρ₁ x₁) = no (λ { (left ()) ; (right ()) })
notRows? (row ρ x) (ρ₁ ─ ρ₂) = yes (right tt)
notRows? (row ρ x) (φ <$> τ) = yes (right tt)

--------------------------------------------------------------------------------
-- Defining Semantic types

SemType : KEnv → Kind → Set
SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = (∀ {Δ₂} → (r : Renamingₖ Δ₁ Δ₂) (v : SemType Δ₂ κ₁) → SemType Δ₂ κ₂)
SemType Δ R[ κ ] =  RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]  

--------------------------------------------------------------------------------
-- aliases

KripkeFunction : KEnv → Kind → Kind → Set
KripkeFunctionNE : KEnv → Kind → Kind → Set
KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renamingₖ Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)
KripkeFunctionNE Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renamingₖ Δ₁ Δ₂ → NeutralType Δ₂ κ₁ → SemType Δ₂ κ₂)

--------------------------------------------------------------------------------
-- Truncating a row preserves ordering

ordered-cut : ∀ {n : ℕ} → {P : Fin (suc n) → Label × SemType Δ κ} → 
              OrderedRow (suc n , P) → OrderedRow (n , P ∘ fsuc)
ordered-cut {n = zero} oρ = tt
ordered-cut {n = suc n} oρ = oρ .snd


--------------------------------------------------------------------------------
-- Ordering is preserved by mapping

orderedOverᵣ : ∀ {n} {P : Fin n → Label × SemType Δ κ₁} → 
               (f : SemType Δ κ₁ → SemType Δ κ₂) → 
               OrderedRow (n , P) → OrderedRow (n , overᵣ f ∘ P)
orderedOverᵣ {n = zero} {P} f oρ = tt
orderedOverᵣ {n = suc zero} {P} f oρ = tt
orderedOverᵣ {n = suc (suc n)} {P} f oρ = (oρ .fst) , (orderedOverᵣ f (oρ .snd))

--------------------------------------------------------------------------------
-- Semantic row operators

_⨾⨾_ :  Label × SemType Δ κ → Row (SemType Δ κ) → Row (SemType Δ κ)

τ ⨾⨾ (n , P) =  suc n , λ { fzero    → τ 
                          ; (fsuc x) → P x }
-- the empty row                                  
εV : Row (SemType Δ κ)
εV = 0 , λ ()
\end{code}


\subsection{Renaming and substitution}

\begin{code}
renKripke : Renamingₖ Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renamingₖ Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renRow : Renamingₖ Δ₁ Δ₂ → 
         Row (SemType Δ₁ κ) → 
         Row (SemType Δ₂ κ)

orderedRenRow : ∀ {n} {P : Fin n → Label × SemType Δ₁ κ} → (r : Renamingₖ Δ₁ Δ₂) → 
                OrderedRow' n P → OrderedRow' n (λ i → (P i .fst) , renSem r (P i .snd))

nrRenSem :  ∀ (r : Renamingₖ Δ₁ Δ₂) → (ρ : RowType Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             NotRow ρ → NotRow (renSem r ρ)
nrRenSem' : ∀ (r : Renamingₖ Δ₁ Δ₂) → (ρ₂ ρ₁ : RowType Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             NotRow ρ₂ or NotRow ρ₁ → NotRow (renSem r ρ₂) or NotRow (renSem r ρ₁)

renSem {κ = ★} r τ = renₖNF r τ
renSem {κ = L} r τ = renₖNF r τ
renSem {κ = κ `→ κ₁} r F = renKripke r F
renSem {κ = R[ κ ]} r (φ <$> x) = (λ r' → φ (r' ∘ r)) <$> (renₖNE r x)
renSem {κ = R[ κ ]} r (l ▹ τ) = (renₖNE r l) ▹ renSem r τ
renSem {κ = R[ κ ]} r (row (n , P) q) = row (n , ( overᵣ (renSem r) ∘ P)) (orderedRenRow r q)
renSem {κ = R[ κ ]} r ((ρ₂ ─ ρ₁) {nr}) = (renSem r ρ₂ ─ renSem r ρ₁) {nr = nrRenSem' r ρ₂ ρ₁ nr}

nrRenSem' r ρ₂ ρ₁ (left x) = left (nrRenSem r ρ₂ x)
nrRenSem' r ρ₂ ρ₁ (right y) = right (nrRenSem r ρ₁ y)

nrRenSem r (x ▹ x₁) nr = tt
nrRenSem r (ρ ─ ρ₁) nr = tt
nrRenSem r (φ <$> ρ) nr = tt

orderedRenRow {n = zero} {P} r o = tt
orderedRenRow {n = suc zero} {P} r o = tt
orderedRenRow {n = suc (suc n)} {P} r (l₁<l₂ , o) =  l₁<l₂  , (orderedRenRow {n = suc n} {P ∘ fsuc} r o)

renRow φ (n , P) = n , overᵣ (renSem φ) ∘ P 

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ
\end{code}

\section{Normalization by Evaluation}

\begin{code}
reflect : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ

reflect {κ = ★} τ            = ne τ
reflect {κ = L} τ            = ne τ
reflect {κ = R[ κ ]} ρ       = (λ r n → reflect n) <$> ρ 
reflect {κ = κ₁ `→ κ₂} τ = λ ρ v → reflect (renₖNE ρ τ · reify v)

reifyKripke : KripkeFunction Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripkeNE : KripkeFunctionNE Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripke {κ₁ = κ₁} F = `λ (reify (F S (reflect {κ = κ₁} ((` Z)))))
reifyKripkeNE F = `λ (reify (F S (` Z)))

reifyRow' : (n : ℕ) → (Fin n → Label × SemType Δ κ) → SimpleRow NormalType Δ R[ κ ]
reifyRow' zero P    = []
reifyRow' (suc n) P with P fzero
... | (l , τ) = (l , reify τ) ∷ reifyRow' n (P ∘ fsuc)

reifyRow : Row (SemType Δ κ) → SimpleRow NormalType Δ R[ κ ]
reifyRow (n , P) = reifyRow' n P

reifyRowOrdered : ∀ (ρ : Row (SemType Δ κ)) → OrderedRow ρ →  NormalOrdered (reifyRow ρ)
reifyRowOrdered' : ∀  (n : ℕ) → (P : Fin n → Label × SemType Δ κ) → 
                      OrderedRow (n , P) →  NormalOrdered (reifyRow (n , P))

reifyRowOrdered' zero P oρ = tt
reifyRowOrdered' (suc zero) P oρ = tt
reifyRowOrdered' (suc (suc n)) P (l₁<l₂ , ih) = l₁<l₂ , (reifyRowOrdered' (suc n) (P ∘ fsuc) ih)

reifyRowOrdered (n , P) oρ = reifyRowOrdered' n P oρ

reifyPreservesNR : ∀ (ρ₁ ρ₂ : RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
                     (nr : NotRow ρ₁ or NotRow ρ₂) → NotSimpleRow (reify ρ₁) or NotSimpleRow (reify ρ₂)

reifyPreservesNR' : ∀ (ρ₁ ρ₂ : RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
                     (nr : NotRow ρ₁ or NotRow ρ₂) → NotSimpleRow (reify ((ρ₁ ─ ρ₂) {nr}))

reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} F = reifyKripke F
reify {κ = R[ κ ]} (l ▹ τ) = (l ▹ₙ (reify τ))
reify {κ = R[ κ ]} (row ρ q) = ⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered ρ q))
reify {κ = R[ κ ]} ((φ <$> τ)) =  (reifyKripkeNE φ <$> τ)
reify {κ = R[ κ ]} ((φ <$> τ) ─ ρ₂) = (reify (φ <$> τ) ─ reify ρ₂) {nsr = tt}
reify {κ = R[ κ ]} ((l ▹ τ) ─ ρ) = (reify (l ▹ τ) ─ (reify ρ)) {nsr = tt}
reify {κ = R[ κ ]} (row ρ x ─ ρ'@(x₁ ▹ x₂)) = (reify (row ρ x) ─ reify ρ') {nsr = tt}
reify {κ = R[ κ ]} ((row ρ x ─ row ρ₁ x₁) {left ()})
reify {κ = R[ κ ]} ((row ρ x ─ row ρ₁ x₁) {right ()})
reify {κ = R[ κ ]} (row ρ x ─ (φ <$> τ)) = (reify (row ρ x) ─ reify (φ <$> τ)) {nsr = tt} 
reify {κ = R[ κ ]} ((row ρ x ─ ρ'@((ρ₁ ─ ρ₂) {nr'})) {nr}) = ((reify (row ρ x)) ─ (reify ((ρ₁ ─ ρ₂) {nr'}))) {nsr = fromWitness (reifyPreservesNR (row ρ x) ρ' (right tt))}
reify {κ = R[ κ ]} ((((ρ₂ ─ ρ₁) {nr'}) ─ ρ) {nr}) = ((reify ((ρ₂ ─ ρ₁) {nr'})) ─ reify ρ) {fromWitness (reifyPreservesNR ((ρ₂ ─ ρ₁) {nr'}) ρ (left tt))}


reifyPreservesNR (x₁ ▹ x₂) ρ₂ (left x) = left tt
reifyPreservesNR ((ρ₁ ─ ρ₃) {nr}) ρ₂ (left x) = left (reifyPreservesNR' ρ₁ ρ₃ nr)
reifyPreservesNR (φ <$> ρ) ρ₂ (left x) = left tt
reifyPreservesNR ρ₁ (x ▹ x₁) (right y) = right tt
reifyPreservesNR ρ₁ ((ρ₂ ─ ρ₃) {nr}) (right y) = right (reifyPreservesNR' ρ₂ ρ₃ nr)
reifyPreservesNR ρ₁ ((φ <$> ρ₂)) (right y) = right tt

reifyPreservesNR' (x₁ ▹ x₂) ρ₂ (left x) = tt
reifyPreservesNR' (ρ₁ ─ ρ₃) ρ₂ (left x) = tt
reifyPreservesNR' (φ <$> n) ρ₂ (left x) = tt
reifyPreservesNR' (φ <$> n) ρ₂ (right y) = tt
reifyPreservesNR' (x ▹ x₁) ρ₂ (right y) = tt
reifyPreservesNR' (row ρ x) (x₁ ▹ x₂) (right y) = tt
reifyPreservesNR' (row ρ x) (ρ₂ ─ ρ₃) (right y) = tt
reifyPreservesNR' (row ρ x) (φ <$> n) (right y) = tt
reifyPreservesNR' (ρ₁ ─ ρ₃) ρ₂ (right y) = tt

--------------------------------------------------------------------------------
-- η normalization of neutral types

η-norm : NeutralType Δ κ → NormalType Δ κ 
η-norm = reify ∘ reflect

-- --------------------------------------------------------------------------------
-- -- Semantic environments

Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → SemType Δ₂ κ

idEnv : Env Δ Δ
idEnv = reflect ∘ `

extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

lifte : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
lifte {Δ₁} {Δ₂} {κ} η  = extende (weakenSem ∘ η) (idEnv Z)
\end{code}


\subsection{Helping evaluation}

\begin{code}
-----------------------
-- Semantic application

_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
F ·V V = F id V

----------------------
-- Semantic complement

_∈Row_ : ∀ {m} → (l : Label) → 
         (Q : Fin m → Label × SemType Δ κ) → 
         Set 
_∈Row_ {m = m} l Q = Σ[ i ∈ Fin m ] (l ≡ Q i .fst)

_∈Row?_ : ∀ {m} → (l : Label) → 
         (Q : Fin m → Label × SemType Δ κ) → 
         Dec (l ∈Row Q)
_∈Row?_ {m = zero} l Q = no λ { () }
_∈Row?_ {m = suc m} l Q with l ≟ Q fzero .fst
... | yes p = yes (fzero , p)
... | no  p with l ∈Row? (Q ∘ fsuc)
...        | yes (n , q) = yes ((fsuc n) , q) 
...        | no  q = no λ { (fzero , q') → p q' ; (fsuc n , q') → q (n , q') }

compl : ∀ {n m} → 
        (P : Fin n → Label × SemType Δ κ) 
        (Q : Fin m → Label × SemType Δ κ) → 
        Row (SemType Δ κ)
compl {n = zero} {m} P Q = εV
compl {n = suc n} {m} P Q with P fzero .fst ∈Row? Q 
... | yes _ = compl (P ∘ fsuc) Q 
... | no _ = (P fzero) ⨾⨾ (compl (P ∘ fsuc) Q)

-- --------------------------------------------------------------------------------
-- -- Semantic complement preserves well-ordering
lemma : ∀ {n m q} → 
          (P : Fin (suc n) → Label × SemType Δ κ)
          (Q : Fin m → Label × SemType Δ κ) → 
          (R : Fin (suc q) → Label × SemType Δ κ) → 
             OrderedRow (suc n , P) →
             compl (P ∘ fsuc) Q ≡ (suc q , R) → 
          P fzero .fst < R fzero .fst
lemma {n = suc n} {q = q} P Q R oP eq₁ with P (fsuc fzero) .fst ∈Row? Q 
lemma {κ = _} {suc n} {q = q} P Q R oP refl | no _ = oP .fst
... | yes _ = <-trans {i = P fzero .fst} {j = P (fsuc fzero) .fst} {k = R fzero .fst} (oP .fst) (lemma {n = n} (P ∘ fsuc) Q R (oP .snd) eq₁)

ordered-⨾⨾ : ∀ {n m} → 
                 (P : Fin (suc n) → Label × SemType Δ κ) 
                 (Q : Fin m → Label × SemType Δ κ) → 
                 OrderedRow (suc n , P) → 
                 OrderedRow (compl (P ∘ fsuc) Q) → OrderedRow (P fzero ⨾⨾ compl (P ∘ fsuc) Q)
ordered-⨾⨾ {n = n} P Q oP oC with compl (P ∘ fsuc) Q | inspect (compl (P ∘ fsuc)) Q
... | zero , R  | _        = tt
... | suc n , R | [[ eq ]] = lemma P Q R oP eq  , oC

ordered-compl :  ∀ {n m} → 
                 (P : Fin n → Label × SemType Δ κ) 
                 (Q : Fin m → Label × SemType Δ κ) → 
                 OrderedRow (n , P) → OrderedRow (m , Q) → OrderedRow (compl P Q)
ordered-compl {n = zero} P Q oρ₁ oρ₂ = tt
ordered-compl {n = suc n} P Q oρ₁ oρ₂ with P fzero .fst ∈Row? Q
... | yes _ = ordered-compl (P ∘ fsuc) Q (ordered-cut oρ₁) oρ₂
... | no _ = ordered-⨾⨾ P Q oρ₁ (ordered-compl (P ∘ fsuc) Q (ordered-cut oρ₁) oρ₂)

--------------------------------------------------------------------------------
-- Semantic complement on Rows
                
_─v_ : Row (SemType Δ κ) → Row (SemType Δ κ) → Row (SemType Δ κ)
(n , P) ─v (m , Q) = compl P Q

ordered─v : ∀ (ρ₂ ρ₁ : Row (SemType Δ κ)) → OrderedRow ρ₂ → OrderedRow ρ₁ → OrderedRow (ρ₂ ─v ρ₁)
ordered─v (n , P) (m , Q) oρ₂ oρ₁ = ordered-compl P Q oρ₂ oρ₁

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Semantic lifting

_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
NotRow<$> : ∀ {F : SemType Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : RowType Δ (λ Δ' → SemType Δ' κ₁) R[ κ₁ ]} → 
              NotRow ρ₂ or NotRow ρ₁ → NotRow (F <$>V ρ₂) or NotRow (F <$>V ρ₁)

F <$>V (l ▹ τ) = l ▹ (F ·V τ)
F <$>V row (n , P) q = row (n , overᵣ (F id) ∘ P) (orderedOverᵣ (F id) q)
F <$>V ((ρ₂ ─ ρ₁) {nr}) = ((F <$>V ρ₂) ─ (F <$>V ρ₁)) {NotRow<$> nr}
F <$>V (G <$> n) = (λ {Δ'} r → F r ∘ G r) <$> n

NotRow<$> {F = F} {x₁ ▹ x₂} {ρ₁} (left x) = left tt
NotRow<$> {F = F} {ρ₂ ─ ρ₃} {ρ₁} (left x) = left tt
NotRow<$> {F = F} {φ <$> n} {ρ₁} (left x) = left tt

NotRow<$> {F = F} {ρ₂} {x ▹ x₁} (right y) = right tt
NotRow<$> {F = F} {ρ₂} {ρ₁ ─ ρ₃} (right y) = right tt
NotRow<$> {F = F} {ρ₂} {φ <$> n} (right y) = right tt


-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Semantic complement on SemTypes

_─V_ : SemType Δ R[ κ ] → SemType Δ R[ κ ] → SemType Δ R[ κ ]
row ρ₂ oρ₂ ─V row ρ₁ oρ₁ = row (ρ₂ ─v ρ₁) (ordered─v ρ₂ ρ₁ oρ₂ oρ₁)
ρ₂@(x ▹ x₁) ─V ρ₁ = (ρ₂ ─ ρ₁) {nr = left tt}
ρ₂@(row ρ x) ─V ρ₁@(x₁ ▹ x₂) = (ρ₂ ─ ρ₁) {nr = right tt}
ρ₂@(row ρ x) ─V ρ₁@(_ ─ _) = (ρ₂ ─ ρ₁) {nr = right tt}
ρ₂@(row ρ x) ─V ρ₁@(_ <$> _) = (ρ₂ ─ ρ₁) {nr = right tt}
ρ@(ρ₂ ─ ρ₃) ─V ρ' = (ρ ─ ρ') {nr = left tt}
ρ@(φ <$> n) ─V ρ' = (ρ ─ ρ') {nr = left tt}

-- --------------------------------------------------------------------------------
-- -- Semantic flap

apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
apply a = λ ρ F → F ·V (renSem ρ a)

infixr 0 _<?>V_
_<?>V_ : SemType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
f <?>V a = apply a <$>V f
\end{code}

\subsection{$\Pi$ and $\Sigma$ as operators}

\begin{code}
record Xi : Set where 
  field
    Ξ★ : ∀ {Δ} → NormalType  Δ R[ ★ ] → NormalType Δ ★
    ren-★ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ ★ ]) → renₖNF ρ (Ξ★ τ) ≡  Ξ★ (renₖNF ρ τ)

open Xi
ξ : ∀ {Δ} → Xi → SemType Δ R[ κ ] → SemType Δ κ 
ξ {κ = ★} Ξ x = Ξ .Ξ★ (reify x)
ξ {κ = L} Ξ x = lab "impossible"
ξ {κ = κ₁ `→ κ₂} Ξ F = λ ρ v → ξ Ξ (renSem ρ F <?>V v)
ξ {κ = R[ κ ]} Ξ x = (λ ρ v → ξ Ξ v) <$>V x

Π-rec Σ-rec : Xi 
Π-rec = record
  {  Ξ★ = Π ; ren-★ = λ ρ τ → refl }
Σ-rec = 
  record
  { Ξ★ = Σ ; ren-★ = λ ρ τ → refl  }

ΠV ΣV : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ
ΠV = ξ Π-rec
ΣV = ξ Σ-rec

ξ-Kripke : Xi → KripkeFunction Δ R[ κ ] κ
ξ-Kripke Ξ ρ v = ξ Ξ v

Π-Kripke Σ-Kripke : KripkeFunction Δ R[ κ ] κ
Π-Kripke = ξ-Kripke Π-rec
Σ-Kripke = ξ-Kripke Σ-rec
\end{code}

\subsection{Evaluation}
\begin{code}
eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
evalPred : Pred Type Δ₁ R[ κ ] → Env Δ₁ Δ₂ → NormalPred Δ₂ R[ κ ]

evalRow        : (ρ : SimpleRow Type Δ₁ R[ κ ]) → Env Δ₁ Δ₂ → Row (SemType Δ₂ κ)
evalRowOrdered : (ρ : SimpleRow Type Δ₁ R[ κ ]) → (η : Env Δ₁ Δ₂) → Ordered ρ → OrderedRow (evalRow ρ η)

evalRow [] η = εV 
evalRow ((l , τ) ∷ ρ) η = (l , (eval τ η)) ⨾⨾ evalRow ρ η 

⇓Row-isMap : ∀ (η : Env Δ₁ Δ₂) → (xs : SimpleRow Type Δ₁ R[ κ ])  → 
                      reifyRow (evalRow xs η) ≡ map (λ { (l , τ) → l , (reify (eval τ η)) }) xs
⇓Row-isMap η [] = refl
⇓Row-isMap η (x ∷ xs) = cong₂ _∷_ refl (⇓Row-isMap η xs)

evalPred (ρ₁ · ρ₂ ~ ρ₃) η = reify (eval ρ₁ η) · reify (eval ρ₂ η) ~ reify (eval ρ₃ η)
evalPred (ρ₁ ≲ ρ₂) η = reify (eval ρ₁ η) ≲ reify (eval ρ₂ η)

eval {κ = κ} (` x) η = η x
eval {κ = κ} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval {κ = κ} (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)

eval {κ = ★} (π ⇒ τ) η = evalPred π η ⇒ eval τ η
eval {Δ₁} {κ = ★} (`∀ τ) η = `∀ (eval τ (lifte η)) 
eval {κ = ★} (μ τ) η = μ (reify (eval τ η))
eval {κ = ★} ⌊ τ ⌋ η = ⌊ reify (eval τ η) ⌋
eval (ρ₂ ─ ρ₁) η = eval ρ₂ η ─V eval ρ₁ η
eval {κ = L} (lab l) η = lab l
eval {κ = κ₁ `→ κ₂} (`λ τ) η = λ ρ v → eval τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)
eval {κ = R[ κ ] `→ κ} Π η = Π-Kripke
eval {κ = R[ κ ] `→ κ} Σ η = Σ-Kripke
eval {κ = R[ κ ]} (f <$> a) η = (eval f η) <$>V (eval a η)
eval (⦅ ρ ⦆ oρ) η = row (evalRow ρ η) (evalRowOrdered ρ η (toWitness oρ))
eval (l ▹ τ) η with eval l η 
... | ne x = (x ▹ eval τ η)
... | lab l₁ = row (1 , λ { fzero → (l₁ , eval τ η) }) tt
evalRowOrdered [] η oρ = tt
evalRowOrdered (x₁ ∷ []) η oρ = tt
evalRowOrdered ((l₁ , τ₁) ∷ (l₂ , τ₂) ∷ ρ) η (l₁<l₂ , oρ) with 
  evalRow ρ η | evalRowOrdered ((l₂ , τ₂) ∷ ρ) η oρ
... | zero , P | ih = l₁<l₂ , tt
... | suc n , P | ih₁ , ih₂ =  l₁<l₂ , ih₁ , ih₂
\end{code}

\subsection{Normalization}
\begin{code}
⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

⇓Pred : ∀ {Δ} → Pred Type Δ R[ κ ] → Pred NormalType Δ R[ κ ] 
⇓Pred π = evalPred π idEnv

⇓Row : ∀ {Δ} → SimpleRow Type Δ R[ κ ] → SimpleRow NormalType Δ R[ κ ] 
⇓Row ρ = reifyRow (evalRow ρ idEnv)

⇓NE : ∀ {Δ} → NeutralType Δ κ → NormalType Δ κ
⇓NE τ = reify (eval (⇑NE τ) idEnv)
\end{code}

\section{Metatheory}

\subsection{Stability}

\begin{code}
stability   : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → eval (⇑NE τ) (idEnv {Δ}) ≡ reflect τ
stabilityPred : ∀ (π : NormalPred Δ R[ κ ]) → evalPred (⇑Pred π) idEnv ≡ π
stabilityRow : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → reifyRow (evalRow (⇑Row ρ) idEnv) ≡ ρ
\end{code}
\begin{code}[hide]
stability     = bot _
stabilityNE   = bot _
stabilityPred = bot _
stabilityRow = bot _
\end{code}

Stability implies surjectivity and idempotency.

\begin{code}
idempotency : ∀ (τ : Type Δ κ) → (⇑ ∘ ⇓ ∘ ⇑ ∘ ⇓) τ ≡  (⇑ ∘ ⇓)  τ
idempotency τ rewrite stability (⇓ τ) = refl

surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ)
surjectivity τ = ( ⇑ τ , stability τ ) 
\end{code}

Dual to surjectivity, stability also implies that embedding is injective.
 
\begin{code}
⇑-inj : ∀ (τ₁ τ₂ : NormalType Δ κ) → ⇑ τ₁ ≡ ⇑ τ₂ → τ₁ ≡ τ₂                   
⇑-inj τ₁ τ₂ eq = trans (sym (stability τ₁)) (trans (cong ⇓ eq) (stability τ₂))
\end{code}

\subsection{A logical relation for completeness}

\begin{code}
subst-Row : ∀ {A : Set} {n m : ℕ} → (n ≡ m) → (f : Fin n → A) → Fin m → A 
subst-Row refl f = f

-- Completeness relation on semantic types
_≋_ : SemType Δ κ → SemType Δ κ → Set
_≋₂_ : ∀ {A} → (x y : A × SemType Δ κ) → Set
(l₁ , τ₁) ≋₂ (l₂ , τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
_≋R_ : (ρ₁ ρ₂ : Row (SemType Δ κ)) → Set 
(n , P) ≋R (m , Q) = Σ[ pf ∈ (n ≡ m) ] (∀ (i : Fin m) →  (subst-Row pf P) i ≋₂ Q i)

PointEqual-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
PointEqualNE-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunctionNE Δ₁ κ₁ κ₂) → Set
Uniform :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunction Δ κ₁ κ₂ → Set
UniformNE :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunctionNE Δ κ₁ κ₂ → Set

convNE : κ₁ ≡ κ₂ → NeutralType Δ R[ κ₁ ] → NeutralType Δ R[ κ₂ ]
convNE refl n = n 

convKripkeNE₁ : ∀ {κ₁'} → κ₁ ≡ κ₁' → KripkeFunctionNE Δ κ₁ κ₂ → KripkeFunctionNE Δ κ₁' κ₂
convKripkeNE₁ refl f = f

_≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} F G = 
  Uniform F × Uniform G × PointEqual-≋ {Δ₁} F G 
_≋_ {Δ₁} {R[ κ₂ ]} (_<$>_ {κ₁} φ₁ n₁) (_<$>_ {κ₁'} φ₂ n₂) = 
  Σ[ pf ∈ (κ₁ ≡ κ₁') ]  
    UniformNE φ₁
  × UniformNE φ₂
  × (PointEqualNE-≋ (convKripkeNE₁ pf φ₁) φ₂
  × convNE pf n₁ ≡ n₂)
_≋_ {Δ₁} {R[ κ₂ ]} (φ₁ <$> n₁) _ = ⊥
_≋_ {Δ₁} {R[ κ₂ ]} _ (φ₁ <$> n₁) = ⊥
_≋_ {Δ₁} {R[ κ ]} (l₁ ▹ τ₁) (l₂ ▹ τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
_≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (row ρ x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (ρ₂ ─ ρ₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (x₂ ▹ x₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (row (n , P) x₁) (row (m , Q) x₂) = (n , P) ≋R (m , Q)
_≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (ρ₂ ─ ρ₃) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (x₁ ▹ x₂) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (row ρ x₁) = ⊥
_≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (ρ₃ ─ ρ₄) = ρ₁ ≋ ρ₃ × ρ₂ ≋ ρ₄

PointEqual-≋ {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
  V₁ ≋ V₂ → F ρ V₁ ≋ G ρ V₂

PointEqualNE-≋ {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) (V : NeutralType Δ₂ κ₁) → 
  F ρ V ≋ G ρ V

Uniform {Δ₁} {κ₁} {κ₂} F = 
  ∀ {Δ₂ Δ₃} (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V₁ V₂ : SemType Δ₂ κ₁) →
  V₁ ≋ V₂ → (renSem ρ₂ (F ρ₁ V₁)) ≋ (renKripke ρ₁ F ρ₂ (renSem ρ₂ V₂))

UniformNE {Δ₁} {κ₁} {κ₂} F = 
  ∀ {Δ₂ Δ₃} (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V : NeutralType Δ₂ κ₁) →
  (renSem ρ₂ (F ρ₁ V)) ≋ F (ρ₂ ∘ ρ₁) (renₖNE ρ₂ V)

Env-≋ : (η₁ η₂ : Env Δ₁ Δ₂) → Set
Env-≋ η₁ η₂ = ∀ {κ} (x : TVar _ κ) → (η₁ x) ≋ (η₂ x)

-- extension
extend-≋ : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → 
            {V₁ V₂ : SemType Δ₂ κ} → 
            V₁ ≋ V₂ → 
            Env-≋ (extende η₁ V₁) (extende η₂ V₂)
extend-≋ p q Z = q
extend-≋ p q (S v) = p v
\end{code}
\begin{code}[hide]

refl-≋ₗ : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → V₁ ≋ V₁
refl-≋ᵣ : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → V₂ ≋ V₂
sym-≋ : ∀ {τ₁ τ₂ : SemType Δ κ}      → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
trans-≋ : ∀ {τ₁ τ₂ τ₃ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₃ → τ₁ ≋ τ₃
trans-≋ᵣ : ∀ {τ₁ τ₂ τ₃ : Row (SemType Δ κ)} → τ₁ ≋R τ₂ → τ₂ ≋R τ₃ → τ₁ ≋R τ₃

sym-≋ {κ = ★}  refl = refl
sym-≋ {κ = L}  refl = refl
sym-≋ {κ = κ `→ κ₁} 
  {F} {G} 
  (Unif-F , (Unif-G , Ext)) = 
     Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≋ (Ext ρ (sym-≋ z)))
sym-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} (eq , rel) = sym eq  , sym-≋ rel
sym-≋ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} (refl , eq-ρ) =
  refl , 
  (λ i → (sym (eq-ρ i .fst)) , (sym-≋ (eq-ρ i .snd)))
sym-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} (rel₁ , rel₂) = (sym-≋ rel₁) , (sym-≋ rel₂)
sym-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} (refl , Unif-φ₁ , Unif-φ₂ , Ext , refl) = refl  , Unif-φ₂ , Unif-φ₁ , (λ r v → sym-≋ (Ext r v) ) , refl
refl-≋ₗ q = trans-≋ q (sym-≋ q)
refl-≋ᵣ q = refl-≋ₗ (sym-≋ q)

trans-≋ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = κ₁ `→ κ₂} {F} {G} {H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≋ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≋ₗ (sym-≋ q)))
trans-≋ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} (eq-l₁ , rel-τ₁) (eq-l₂ , rel-τ₂) = trans eq-l₁ eq-l₂  , trans-≋ rel-τ₁ rel-τ₂
trans-≋ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} {row (o , R) _} (refl , rel₁) (refl , rel₂) = 
  refl , λ { i → trans (rel₁ i .fst) (rel₂ i .fst) , trans-≋ (rel₁ i .snd) (rel₂ i .snd) }
trans-≋ {κ = R[ κ ]} {ρ₂ ─ ρ₁} {ρ₄ ─ ρ₃} {ρ₆ ─ ρ₅} (rel₁ , rel₂) (rel₃ , rel₄) = (trans-≋ rel₁ rel₃) , (trans-≋ rel₂ rel₄)
trans-≋ {κ = R[ κ ]} {φ₁ <$> n₁} {φ₂ <$> n₂} {φ₃ <$> n₃} (refl , Unif-φ₁ , Unif-φ₂ , Ext₁ , refl) (refl , _ , Unif-φ₃ , Ext₂ , refl) = refl , Unif-φ₁ , Unif-φ₃ , (λ r v → trans-≋ (Ext₁ r v) (Ext₂ r v) ) , refl

trans-≋ᵣ {τ₁ = (n , P)} {τ₂ = (m , Q)} {τ₃ = (j , K)} (refl , rel₁) (refl , rel₂) = refl , (λ { i → trans (rel₁ i .fst) (rel₂ i .fst)  , trans-≋ (rel₁ i .snd) (rel₂ i .snd) })

refl-Extₗ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ F F
refl-Extₗ Ext ρ q = trans-≋ (Ext ρ q) (sym-≋ (Ext ρ (refl-≋ₗ (sym-≋ q))))

sym-Ext : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G F
sym-Ext Ext ρ q = trans-≋ (refl-≋ₗ (sym-≋ (Ext ρ (sym-≋ q)))) (sym-≋ (Ext ρ (sym-≋ q)))

refl-Extᵣ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G G
refl-Extᵣ Ext ρ q = refl-Extₗ (sym-Ext Ext) ρ q

trans-Ext : ∀ {F G H : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≋ F G → PointEqual-≋ G H → PointEqual-≋ F H
trans-Ext Ext-FG Ext-GH ρ q = trans-≋ (Ext-FG ρ q) (trans-≋ (Ext-GH ρ (sym-≋ q)) (refl-Extᵣ Ext-GH ρ q))
\end{code}

\subsubsection{Properties}~

\begin{code}
reflect-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflect τ₁ ≋ reflect τ₂
reify-≋    : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → reify V₁   ≡ reify V₂ 
reifyRow-≋ : ∀ {n} (P Q : Fin n → Label × SemType Δ κ) →  
               (∀ (i : Fin n) → P i ≋₂ Q i) → 
               reifyRow (n , P) ≡ reifyRow (n , Q)
\end{code}
\begin{code}
\end{code}
\begin{code}[hide]
reflect-≋  = bot _ 
reify-≋    = bot _ 
reifyRow-≋ = bot _ 
\end{code}

\subsection{The fundamental theorem and completeness}

\begin{code}
fundC : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : Env Δ₁ Δ₂} → 
       Env-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
fundC-pred : ∀ {π₁ π₂ : Pred Type Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
            Env-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂
fundC-Row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
            Env-≋ η₁ η₂ → ρ₁ ≡r ρ₂ → evalRow ρ₁ η₁ ≋R evalRow ρ₂ η₂
\end{code}
\begin{code}[hide]
fundC = bot _
fundC-pred = bot _
fundC-Row = bot _
\end{code}

\begin{code}
idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflect-≋ refl

completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
completeness eq = reify-≋ (fundC idEnv-≋ eq)  

completeness-row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → ρ₁ ≡r ρ₂ → ⇓Row ρ₁ ≡ ⇓Row ρ₂
\end{code}
\begin{code}[hide]
completeness-row = bot _
\end{code}

\subsection{A logical relation for soundness}
\begin{code}
infix 0 ⟦_⟧≋_
⟦_⟧≋_ : ∀ {κ} → Type Δ κ → SemType Δ κ → Set
⟦_⟧≋ne_ : ∀ {κ} → Type Δ κ → NeutralType Δ κ → Set

⟦_⟧r≋_ : ∀ {κ} → SimpleRow Type Δ R[ κ ] → Row (SemType Δ κ) → Set
⟦_⟧≋₂_ : ∀ {κ} → Label × Type Δ κ → Label × SemType Δ κ → Set
⟦ (l₁ , τ) ⟧≋₂ (l₂ , V) = (l₁ ≡ l₂) × (⟦ τ ⟧≋ V)

SoundKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set
SoundKripkeNE : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunctionNE Δ₁ κ₁ κ₂ → Set

-- τ is equivalent to neutral `n` if it's equivalent 
-- to the η and map-id expansion of n
⟦_⟧≋ne_ τ n = τ ≡t ⇑ (η-norm n)

⟦_⟧≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
⟦_⟧≋_ {κ = L} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
⟦_⟧≋_ {Δ₁} {κ = κ₁ `→ κ₂} f F = SoundKripke f F
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (row (n , P)  oρ) =
    let xs = ⇑Row (reifyRow (n , P)) in 
    (τ ≡t ⦅ xs ⦆ (fromWitness (Ordered⇑ (reifyRow (n , P)) (reifyRowOrdered' n P oρ)))) × 
    (⟦ xs ⟧r≋ (n , P))
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (l ▹ V) = (τ ≡t (⇑NE l ▹ ⇑ (reify V))) × (⟦ ⇑ (reify V) ⟧≋ V)
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ ((ρ₂ ─ ρ₁) {nr}) = (τ ≡t (⇑ (reify ((ρ₂ ─ ρ₁) {nr})))) × (⟦ ⇑ (reify ρ₂) ⟧≋ ρ₂) × (⟦ ⇑ (reify ρ₁) ⟧≋ ρ₁)
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (φ <$> n) = 
  ∃[ f ] ((τ ≡t (f <$> ⇑NE n)) × (SoundKripkeNE f φ))
⟦ [] ⟧r≋ (zero , P) = ⊤
⟦ [] ⟧r≋ (suc n , P) = ⊥
⟦ x ∷ ρ ⟧r≋ (zero , P) = ⊥
⟦ x ∷ ρ ⟧r≋ (suc n , P) =  (⟦ x ⟧≋₂ (P fzero)) × ⟦ ρ ⟧r≋ (n , P ∘ fsuc)

SoundKripke {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {v V} → 
      ⟦ v ⟧≋ V → 
      ⟦ (renₖ ρ f · v) ⟧≋ (renKripke ρ F ·V V)

SoundKripkeNE {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    ∀ {Δ₂} (r : Renamingₖ Δ₁ Δ₂) {v V} → 
      ⟦ v ⟧≋ne  V → 
      ⟦ (renₖ r f · v) ⟧≋ (F r V)
\end{code}

\subsubsection{Properties}~
\begin{code}
reflect-⟦⟧≋ : ∀ {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
             τ ≡t ⇑NE υ → ⟦ τ ⟧≋ (reflect υ)
reify-⟦⟧≋ : ∀ {τ : Type Δ κ} {V :  SemType Δ κ} → 
               ⟦ τ ⟧≋ V → τ ≡t ⇑ (reify V)
η-norm-≡t : ∀ (τ : NeutralType Δ κ) → ⇑ (η-norm τ) ≡t ⇑NE τ 
subst-⟦⟧≋ : ∀ {τ₁ τ₂ : Type Δ κ} → 
  τ₁ ≡t τ₂ → {V : SemType Δ κ} → ⟦ τ₁ ⟧≋ V → ⟦ τ₂ ⟧≋ V 
\end{code}

\subsubsection{Logical environments}~
\begin{code}
⟦_⟧≋e_ : ∀ {Δ₁ Δ₂} → Substitutionₖ Δ₁ Δ₂ → Env Δ₁ Δ₂ → Set  
⟦_⟧≋e_ {Δ₁} σ η = ∀ {κ} (α : TVar Δ₁ κ) → ⟦ (σ α) ⟧≋ (η α)

-- Identity relation
idSR : ∀ {Δ₁} →  ⟦ ` ⟧≋e (idEnv {Δ₁})
idSR α = reflect-⟦⟧≋ eq-refl
\end{code}
\begin{code}[hide]
reflect-⟦⟧≋ = bot _
reify-⟦⟧≋ = bot _
η-norm-≡t = bot _
subst-⟦⟧≋ = bot _
\end{code}
\subsection{The fundamental theorem and soundness}
\begin{code}
fundS : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)
fundSRow : ∀ {Δ₁ Δ₂ κ}(xs : SimpleRow Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subRowₖ σ xs ⟧r≋ (evalRow xs η)
fundSPred : ∀ {Δ₁ κ}(π : Pred Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η → (subPredₖ σ π) ≡p ⇑Pred (evalPred π η) 
\end{code}

\begin{code}[hide]
fundS = bot _
fundSRow = bot _
fundSPred = bot _
\end{code}

\begin{code}
--------------------------------------------------------------------------------
-- Fundamental theorem when substitution is the identity
subₖ-id : ∀ (τ : Type Δ κ) → subₖ ` τ ≡ τ 

⊢⟦_⟧≋ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≋ eval τ idEnv
⊢⟦ τ ⟧≋ = subst-⟦⟧≋ (inst (subₖ-id τ)) (fundS τ idSR)
\end{code}
\begin{code}[hide]
subₖ-id τ = bot _
\end{code}

\begin{code}
--------------------------------------------------------------------------------
-- Soundness claim  

soundness :  ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 
soundness τ = reify-⟦⟧≋ (⊢⟦ τ ⟧≋)

 --------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ τ₂ then the embedding of τ₁ is equivalent to τ₂

embed-≡t : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ τ₂) → ⇑ τ₁ ≡t τ₂
embed-≡t {τ₁ = τ₁} {τ₂} refl = eq-sym (soundness τ₂) 

--------------------------------------------------------------------------------
-- Soundness implies the converse of completeness, as desired

Completeness⁻¹ : ∀ {Δ κ} → (τ₁ τ₂ : Type Δ κ) → ⇓ τ₁ ≡ ⇓ τ₂ → τ₁ ≡t τ₂
Completeness⁻¹ τ₁ τ₂ eq = eq-trans (soundness τ₁) (embed-≡t eq)
\end{code}

\section{The rest of the picture}

In the remainder of the development, we intrinsically represent terms as typing judgments indexed by normal types. We then give a typed reduction relation on terms and show progress.

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

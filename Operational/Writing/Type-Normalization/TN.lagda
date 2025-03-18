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

\title{Type Normalization in \Rome}
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

\begin{document}

\maketitle

\section{Introduction}
We describe the normalization-by-evaluation (NBE) of types in \Rome. Types are normalized modulo $\beta$- and $\eta$-equivalence---that is, to $\beta\eta$-long forms. Because the type system of \Rome is a strict extension of System \Fome, type level computation for arrow kinds is isomorphic to reduction of arrow types in the STLC. Novel to this report are the reductions of $\Pi$, $\Sigma$, and label bound terms. 

\section{Syntax of kinds}
Our formalization of \Rome types is \emph{intrinsic}, meaning we define the syntax of \emph{typing} and \emph{kinding judgments}, foregoing any description of untyped syntax. The syntax of types is indexed by kinding environments and kinds, defined below.

\begin{code}
data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  R[_]  : Kind → Kind

infixr 5 _`→_
\end{code}

The kind system of \Rome defines $\star$ as the type of types; $L$ as the type of labels; $(\to)$ as the type of type operators; and $R[\kappa]$ as the type of \emph{rows} containing types at kind $\kappa$. As shorthand, we write $R^{n}[\kappa]$ to denote $n$ repeated applications of $R$ to the type $\kappa$--e.g., $R^3[\kappa]$ is shorthand for $R[ R[ R[ \kappa ]]]$.

The syntax of kinding environments is given below. Kinding environments are isomorphic to lists of kinds.

\begin{code}
data KEnv : Set where
  ε : KEnv
  _,,_ : KEnv → Kind → KEnv
\end{code}

Let the metavariables $\Delta$ and $\kappa$ range over kinding environments and kinds, respectively. Correspondingly, we define \emph{generalized variables} in Agda at these names. 

\begin{code}
private
  variable
    Δ Δ₁ Δ₂ Δ₃ : KEnv
    κ κ₁ κ₂ : Kind
\end{code}

The syntax of intrinsically well-scoped De-Bruijn type variables is given below. We say that the kind variable $x$ is indexed by kinding environment $\Delta$ and kind $\kappa$ to specify that $x$ has kind $\kappa$ in kinding environment $\Delta$.

\begin{code}
data KVar : KEnv → Kind → Set where
  Z : KVar (Δ ,, κ) κ
  S : KVar Δ κ₁ → KVar (Δ ,, κ₂) κ₁
\end{code}

\section{Syntax of types}

\Rome is a qualified type system with predicates of the form $\rho_1 \lesssim \rho_2$ and $\rho_1 \cdot \rho_2 \sim \rho_3$ for row-kinded types $\rho_1$, $\rho_2$, and $\rho_3$. Because predicates occur in types and types occur in predicates, the syntax of well-kinded types and well-kinded predicates are mutually recursive. The syntax for each is given below. we describe (in this order) the syntactic components belonging to System $\Fome$, qualified type systems, and system \RO.

\begin{code}[hide]
open import Data.String using (String)
Label = String

infixl 1 _·_
infixr 2 _⇒_
\end{code}

\begin{code}
data Pred (Δ : KEnv) : Kind → Set
data Type Δ : Kind → Set 
data Type Δ where

  ` : 
    (α : KVar Δ κ) →
    Type Δ κ

  `λ : 
    (τ : Type (Δ ,, κ₁) κ₂) → 
    Type Δ (κ₁ `→ κ₂)

  _·_ :   
    (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
    (τ₂ : Type Δ κ₁) → 
    Type Δ κ₂

  _`→_ : 
    (τ₁ : Type Δ ★) →
    (τ₂ : Type Δ ★) → 
    Type Δ ★

  `∀    :  
    (τ : Type (Δ ,, κ) ★) →
    Type Δ ★

  μ     :  
    (F : Type Δ (★ `→ ★)) → 
    Type Δ ★
\end{code}

The first three constructors are analogous to the terms of the STLC. the constructor \verb!`→! classifies term functions; the constructor \verb!`∀! classifies type-in-term quantification; and the constructor \verb!μ! classifies recursive terms. Note that \verb!μ! could be further generalized to kind \verb!κ `→ ★!; however, we found that kind \verb!★ `→ ★! was sufficient for our needs while simplifying both presentation and mechanization.

The syntax of qualified types is given below.

\begin{code}
  _⇒_ : 
    (π : Pred Δ R[ κ₁ ]) → (τ : Type Δ ★) → 
    Type Δ ★  
\end{code}

The type \verb!π ⇒ τ! states that \verb!τ! is \emph{qualified} by the predicate \verb!π!---that is, the type variables bound in \verb!τ! are restricted in instantiation to just those that satisfy the predicate \verb!π!. This is completely analogous to identical syntax used in Haskell to introduce typeclass qualification. Predicates are defined below (after the presentation of type syntax).

We now describe the syntax exclusive to \Rome, beginning with label kind introduction and elimination. Labels are first-class entities in \Rome, and may be represented by both constants and variables. 

\begin{code}
  lab :
    (l : Label) → 
    Type Δ L

  ⌊_⌋ :
    (τ : Type Δ L) →
    Type Δ ★
\end{code}

Label constants in \Rome are constructed from the type \verb!Label!; in our mechanization, \verb!Label! is a type synonym for \verb!String!, but one could choose any other candidate with decidable equality. Types at label kind \verb!L! may be cast to \emph{label singletons} by the \verb!⌊_⌋! constructor. This makes labels first-class entities: for example, as the type \verb!⌊ lab "l" ⌋! has kind $\star$, it can be inhabited by a term.

Types at row kind are constructed by one of the following three constructors.

\begin{code}
  ε : 
    Type Δ R[ κ ]

  _▹_ :
    (l : Type Δ L) → (τ : Type Δ κ) → 
    Type Δ R[ κ ]

  _<$>_ : 
    (f : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
    Type Δ R[ κ₂ ]
\end{code}

Rows in \Rome are either the empty row \verb!ε!, a labeled row \verb!(l ▹ τ)!, or a row mapping \verb!f <$> τ!. The row mapping \verb!f <$> (l ▹ τ)! describes the lifting of the function \verb!f! over row \verb!(l ▹ τ)!, which we will define to equal \verb!(l ▹ f τ)! in the case where the right hand applicand is a labeled row. We will show that rows in Rome (that is, types at row kind) reduce to either the empty row \verb!ε! or a labeled row \verb!(l ▹ τ)! after normalization. There are two important consequences of this canonicity: firstly, we treat row mapping \verb!_<$>_! as having latent computation to perform (there are no normal types with form \verb!f <$> τ! except when \verb!τ! is a neutral variable). The second consequence is that we do not permit the formation of rows with more than one label-type association. Such rows are instead formed as type variables with predicates specifying the shape of the row.

Rows in \Rome are eliminated by the \verb!Π! and \verb!Σ! constructors.

\begin{code}
  Π     :
          Type Δ (R[ κ ] `→ κ)

  Σ     :
          Type Δ (R[ κ ] `→ κ)
\end{code}

Given a type $\rho$ at row kind, $\Pi \rho$ constructs a record with label-type associations from \verb!ρ! and $\Sigma \rho$ constructs a variant that has label and type from \verb!ρ!. We choose to represent \verb!Π! and \verb!Σ! as type constants at kind \verb!(R[ κ ] `→ κ)!; we will show that many applications of \verb!Π! and \verb!Σ! induce type reductions, and hence it is convenient to group such reductions with type application.

The syntax of predicates is given below. The predicate $\LeqP {\rho_1} {\rho_2}$ states that label-to-type mappings in $\rho_1$ are a subset of those in $\rho_2$; the predicate $\RowPlusP {\rho_1} {\rho_2} {\rho_3}$ states that the combination of mappings in $\rho_1$ and $\rho_2$ equals $\rho_3$.

\begin{code}
data Pred Δ where
  _·_~_ : 
    (ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]) → 
    Pred Δ R[ κ ]

  _≲_ : 
    (ρ₁ ρ₂ : Type Δ R[ κ ]) →
    Pred Δ R[ κ ]  
\end{code}

\citet{HubersM23} implicitly define two type-level row lifting operators, \emph{left mapping} \verb!<$>! and \emph{right mapping} \verb!<?>!, but the latter is superfluous. We appeal to the kinds of these operators for their intuition: left mapping \verb!f <$> ρ! lifts a function at arrow kind \verb!f : κ₁ → κ₂! into a function at kind \verb!R[ κ₁ ] → R[ κ₂ ]! and then applies it to \verb!ρ : R[ κ₂ ]!. We may define right mapping (named \emph{flap} and written \verb!<?>!, after similar Haskell operators) of row function $f : R[ \kappa_1 \to \kappa_2 ]$ over type $\tau : \kappa_1$ using left mapping under the following identity:

\[
f\, \verb!<?>!\, \tau = (\lambda\, g.\, g \, \tau) \, \verb!<$>!\, f
\]

\Ni which we encode in Agda as follows:

\begin{code}
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) <$> (` (S Z))))

_<?>_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f <?> a = flap · f · a
\end{code}

\Ni (We choose to define \verb!_<?>_! as the application of \verb!flap! to inputs \verb!f! and \verb!a! so that we needn't pollute the definition with weakenings of its arguments.)





\subsection{Type renaming}

We closely follow \citet{plfa22} and \citet{ChapmanKNW19}  in defining a \emph{type renaming} as a function from type variables in one kinding environment to type variables in another. This is the \emph{parallel renaming and substitution} approach for which weakening and single variable substitution are special cases. The code we establish now will be mimicked again for both normal types and for terms; many names are reused, and so we find it helpful to index duplicate names by a suffix. The suffix $_k$ specifies that this definition describes the \verb!Type! syntax.

\begin{code}
Renamingₖ : KEnv → KEnv → Set
Renamingₖ Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → KVar Δ₂ κ
\end{code}

\Ni We will let the metavariable $\rho$ range over both renamings and types at row kind.

Lifting can be thought of as the weakening of a renaming, and permits renamings to be pushed under binders.

\begin{code}
liftₖ : Renamingₖ Δ₁ Δ₂ → Renamingₖ (Δ₁ ,, κ) (Δ₂ ,, κ)
liftₖ ρ Z = Z
liftₖ ρ (S x) = S (ρ x)
\end{code}

We define renaming as a function that translates a kinding derivation in kinding environment \verb!Δ₁! to environment \verb!Δ₂! provided a renaming from \verb!Δ₁! to \verb!Δ₂!. The definition proceeds by induction on the input kinding derivation. In the variable case, we use $\rho$ to rename variable $x$. In the \verb!`λ! and \verb!`∀! cases, we must lift the renaming $\rho$ over the type variable introduced by these binders. The rest of the cases are effectively just congruence over the type structure.

\begin{code}
renₖ : Renamingₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
renPredₖ : Renamingₖ Δ₁ Δ₂ → Pred Δ₁ R[ κ ] → Pred Δ₂ R[ κ ]

renₖ ρ (` x)      = ` (ρ x)
renₖ ρ (`λ τ)     = `λ (renₖ (liftₖ ρ) τ)
renₖ ρ (π ⇒ τ)    = renPredₖ ρ π ⇒ renₖ ρ τ 
renₖ ρ (`∀ τ)     = `∀ (renₖ (liftₖ ρ) τ)
renₖ ρ ε          = ε
renₖ ρ (τ₁ · τ₂)  = (renₖ ρ τ₁) · (renₖ ρ τ₂)
renₖ ρ (τ₁ `→ τ₂) = (renₖ ρ τ₁) `→ (renₖ ρ τ₂)
renₖ ρ (μ F)      = μ (renₖ ρ F)
renₖ ρ Π          = Π 
renₖ ρ Σ          = Σ
renₖ ρ (lab x)    = lab x
renₖ ρ (l ▹ τ)    = renₖ ρ l ▹ renₖ ρ τ
renₖ ρ ⌊ ℓ ⌋      = ⌊ (renₖ ρ ℓ) ⌋
renₖ ρ (f <$> m)  = renₖ ρ f <$> renₖ ρ m
\end{code}

As \verb!Type! and \verb!Pred! are mutually inductive, we must define \verb!renPredₖ! as mutually recursive to \verb!renₖ!. Its definition is completely unsuprising.

\begin{code}
renPredₖ ρ (ρ₁ · ρ₂ ~ ρ₃) = renₖ ρ ρ₁ · renₖ ρ ρ₂ ~ renₖ ρ ρ₃
renPredₖ ρ (ρ₁ ≲ ρ₂) = (renₖ ρ ρ₁) ≲ (renₖ ρ ρ₂)
\end{code}

Finally, weakening is a special case of renaming.

\begin{code}
weakenₖ : Type Δ κ₂ → Type (Δ ,, κ₁) κ₂
weakenₖ = renₖ S
\end{code}

\subsection{Type substitution}

We wish to give both a declarative and algorithmic treatment of type equivalence. For the latter, we will normalize types to normal forms, meaning types are equivalent iff their normal forms are definitionally equal. For the former, we must define $\beta$-substitution syntactically so that we can express $\beta$-equivalence of types declaratively. In our development, $\beta$-reduction is a special case of substitution.

We define a substitution as a function mapping type variables in context $\Delta_1$ to types in context $\Delta_2$.

\begin{code}
Substitutionₖ : KEnv → KEnv → Set
Substitutionₖ Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → Type Δ₂ κ
\end{code}

Substitutions must be lifted over binders, just as is done for renamings. 

\begin{code}
liftsₖ :  Substitutionₖ Δ₁ Δ₂ → Substitutionₖ(Δ₁ ,, κ) (Δ₂ ,, κ)
liftsₖ σ Z = ` Z
liftsₖ σ (S x) = weakenₖ (σ x)
\end{code}

Substitution is defined inductively over types in a similar fashion to renaming. Note that this is
\emph{simultaneous} substitution and renaming---The variable case translates type variable \verb!x! to the type $\sigma \, \tau$, for which the substitution \verb!σ! also performs a renaming from environment $\Delta_1$ to $\Delta_2$. The rest of the cases (as with renaming) are either congruences over the type structure or congruences plus lifting of the substitution. Again, substitution over predicates is defined mutually recursively.

\begin{code}
subₖ : Substitutionₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
subPredₖ : Substitutionₖ Δ₁ Δ₂ → Pred Δ₁ κ → Pred Δ₂ κ
subₖ σ ε = ε
subₖ σ (` x) = σ x
subₖ σ (`λ τ) = `λ (subₖ (liftsₖ σ) τ)
subₖ σ (τ₁ · τ₂) = (subₖ σ τ₁) · (subₖ σ τ₂)
subₖ σ (τ₁ `→ τ₂) = (subₖ σ τ₁) `→ (subₖ σ τ₂)
subₖ σ (π ⇒ τ) = subPredₖ σ π ⇒ subₖ σ τ 
subₖ σ (`∀ τ) = `∀ (subₖ (liftsₖ σ) τ)
subₖ σ (μ F) = μ (subₖ σ F)
subₖ σ (Π) = Π
subₖ σ Σ = Σ
subₖ σ (lab x) = lab x
subₖ σ (l ▹ τ) = subₖ σ l ▹ subₖ σ τ
subₖ σ ⌊ ℓ ⌋ = ⌊ (subₖ σ ℓ) ⌋
subₖ σ (f <$> a) = subₖ σ f <$> subₖ σ a

subPredₖ σ (ρ₁ · ρ₂ ~ ρ₃) = subₖ σ ρ₁ · subₖ σ ρ₂ ~ subₖ σ ρ₃
subPredₖ σ (ρ₁ ≲ ρ₂) = (subₖ σ ρ₁) ≲ (subₖ σ ρ₂) 
\end{code}

We define the extension of a substitution $\sigma$ by the type $\tau$ functionally. If we had chosen to represent a \verb!Substitutionₖ! as a list, extension would be done by the \verb!cons! constructor. In a De-Bruijn representation, the most recently appended variable is zero---hence an extension here maps the zero variable to \verb!τ! in the \verb!Z! case and maps each variable \verb!(S x)! to its value in \verb!σ! at predecessor \verb!x!.

\begin{code}
extendₖ : Substitutionₖ Δ₁ Δ₂ → (τ : Type Δ₂ κ) → Substitutionₖ (Δ₁ ,, κ) Δ₂
extendₖ σ τ Z = τ
extendₖ σ τ (S x) = σ x
\end{code}

Finally, $\beta$-substitution is simply a special case of substitution. Note that the constructor \verb!`! has type \verb!KVar Δ κ → Type Δ κ!, making it a substitution. It is in fact an identity substitution, which fixes the meaning of its type variables, hence it is the substitution we choose to extend when defining $\beta$-substitution.

\begin{code}
_βₖ[_] : Type (Δ ,, κ₁) κ₂ → Type Δ κ₁ → Type Δ κ₂
τ₁ βₖ[ τ₂ ] = subₖ (extendₖ ` τ₂) τ₁
\end{code}

\section{Type equivalence}

We define type and predicate equivalence mutually recursively. You may think of type equivalence also as a sort of small-step relation on types, as we include rules to equate $\beta$-equivalent and $\eta$-equivalent types, as well as a number of computational steps a row kinded type may take.

\begin{code}
infix 0 _≡t_
infix 0 _≡p_
data _≡p_ : Pred Δ R[ κ ] → Pred Δ R[ κ ] → Set
data _≡t_ : Type Δ κ → Type Δ κ → Set 
\end{code}

Unless otherwise quantified, let the metavariable \verb!l! range over types with label kind, let \verb!π! range over predicates, and let \verb!τ! and \verb!υ! range over types:

\begin{code}
private
    variable
        l l₁ l₂ l₃ : Type Δ L
        ρ₁ ρ₂ ρ₃   : Type Δ R[ κ ]
        π₁ π₂    : Pred Δ R[ κ ]
        τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Δ κ 
\end{code}

The rules for predicate equivalence are uninteresting: two predicates are considered equivalent when their component types are equivalent.

\begin{code}
data _≡p_ where
  _eq-≲_ : 
        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → 
        τ₁ ≲ τ₂ ≡p  υ₁ ≲ υ₂

  _eq-·_~_ : 
        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → τ₃ ≡t υ₃ → 
        τ₁ · τ₂ ~ τ₃ ≡p  υ₁ · υ₂ ~ υ₃
\end{code}

The first three rules for type equivalence state that it is an equivalence relation.

\begin{code}
data _≡t_ where 
  eq-refl : 
    τ ≡t τ 

  eq-sym : 
    τ₁ ≡t τ₂ →
    τ₂ ≡t τ₁

  eq-trans : 
    τ₁ ≡t τ₂ → τ₂ ≡t τ₃ →
    τ₁ ≡t τ₃
\end{code}

Type equivalence is congruent over the total structure of types, including $\lambda$-bindings (hence you may view type normalization as being \emph{call-by-value}). We omit the other eight congruence rules.

\begin{code}
  eq-λ : ∀ {τ υ : Type (Δ ,, κ₁) κ₂} → 
    τ ≡t υ →
    `λ τ ≡t `λ υ
\end{code}
\begin{code}[hide]
  eq-→ : 
    τ₁ ≡t τ₂ → υ₁ ≡t υ₂ →
    τ₁ `→ υ₁ ≡t τ₂ `→ υ₂

  eq-∀ : 
    τ ≡t υ →
    `∀ τ ≡t `∀ υ

  eq-μ : 
    τ ≡t υ →
    μ τ ≡t μ υ

  eq-· :
    τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
    τ₁ · τ₂ ≡t υ₁ · υ₂

  eq-<$> : ∀ {τ₁ υ₁ : Type Δ (κ₁ `→ κ₂)} {τ₂ υ₂ : Type Δ R[ κ₁ ]} → 
    τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
    τ₁ <$> τ₂ ≡t υ₁ <$> υ₂        

  eq-⌊⌋ : 
      τ ≡t υ →
      ⌊ τ ⌋ ≡t ⌊ υ ⌋

  eq-▹ :
       l₁ ≡t l₂ → τ₁ ≡t τ₂ →
      (l₁ ▹ τ₁) ≡t (l₂ ▹ τ₂)

  eq-⇒ :
       π₁ ≡p π₂ → τ₁ ≡t τ₂ →
      (π₁ ⇒ τ₁) ≡t (π₂ ⇒ τ₂)
\end{code}

We have one $\eta$-equivalence rule. It is henceforth useful to view the following rules as directed left-to-right, as normal forms are produced on the right-hand side.

\begin{code}
  eq-η : ∀ {f : Type Δ (κ₁ `→ κ₂)} → 
    f ≡t `λ (weakenₖ f · (` Z))
\end{code}

The rules that remain as \emph{computational}---these are precisely the rules we would use to define small-step reduction of types. We begin with the $\beta$-equivalence rule, which states that lambda abstractions applied to arguments are equivalent to their beta reduction.


\begin{code}
  eq-β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 
    ((`λ τ₁) · τ₂) ≡t (τ₁ βₖ[ τ₂ ])
\end{code}

The next two rules specify the computational behavior of mapping over rows. Rule (\verb!eq-<$>ε!) states that mapping over the empty row $\epsilon$ should yield the empty row; rule \verb!eq-▹$! states that mapping over a labeled row should push the left applicand into the body of the row.

\begin{code}
  eq-<$>ε : {F : Type Δ (κ₁ `→ κ₂)} → 
    (F <$> ε) ≡t ε

  eq-▹$ : ∀ {l} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 
    (F <$> (l ▹ τ)) ≡t (l ▹ (F · τ))
\end{code}

We wish to establish that normal forms of types at row kind are either the empty row \verb!ε! or labeled rows. This is, of course, not the case for types in general. For example, the type \verb!Π · (l ▹ τ)! has row kind when $\tau$ has row kind \verb!R[ κ ]!. In this case, rule \verb!eq-Π▹! pushes the $\Pi$ over the label so that a canonical form is restored.

\begin{code}
  eq-Π▹ : ∀ {l} {τ : Type Δ R[ κ ]} → 
    Π · (l ▹ τ) ≡t (l ▹ (Π · τ))
\end{code}

\Ni The application of $\Pi$ and $\Sigma$ to a type $\tau$ at nested-row kind is in fact just the mapping of $\Pi$ and $\Sigma$ over $\tau$:

\begin{code}
  eq-Π : ∀ {τ : Type Δ R[ R[ κ ] ]} → 
    Π · τ ≡t Π <$> τ
\end{code}

Likewise to rows, we wish to show that normal forms of types at arrow kind are canonically $\lambda$-bound. However, the type \verb!Π · (l ▹ `λ τ)! has arrow kind! Rule \verb!eq-Πλ! pushes the $\lambda$ outwards in order to restore canonicity and so that application of \verb!Π · (l ▹ `λ τ)! to an applicand is simply $\beta$-reduction.

\begin{code}
  eq-Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) κ₂} → 
    Π · (l ▹ `λ τ) ≡t `λ (Π · (weakenₖ l ▹ τ))
\end{code}

Finally, in many cases (such as record concatenation and variant branching) it is necessary to reassociate the application $(\Pi\, \rho)\, \tau$ inward so that $\Pi$ (or $\Sigma$) are the outermost syntax. We observe the following reassociation identity:

\begin{code}
  eq-Π-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} → 
    (Π · ρ) · τ ≡t Π · (ρ <?> τ)
\end{code}

The definition of \verb!_≡t_! concludes by repeating the last four rules, replacing each $\Pi$ with $\Sigma$. As a final aside, it might be thought that we could have rid ourselves of the syntax for mapping by elaborating types at kind \verb!R[ κ₁ → κ₂]!. For example, the type \verb!(l ▹ λ x : κ₁. τ)! could perhaps have its $\lambda$ binding pushed outside to yield \verb!λ x : κ₁. (l ▹ τ)!. However, this would not be kind-preserving (the latter has kind \verb!κ₁ → R[ κ₂ ]!), and therefore such a translation would induce a normalization that does not preserve kinds. We believe it would be possible but complicated to consider a kind-changing translation.

\section{Normal Types}

As is common in other \emph{normalization by evaluation} approaches, we separate \emph{neutral types} from \emph{normal types.} These two definitions are defined mutually inductively with the data type for normal predicates:
\begin{code}[hide]
infixr 1 _▹_
\end{code}
\begin{code}
data NormalType (Δ : KEnv) : Kind → Set
data NormalPred (Δ : KEnv) : Kind → Set
data NeutralType Δ : Kind → Set
\end{code}

A type is neutral if it is (respectively) (i) a variable, (ii) the application of a variable to an argument, or (iii) the mapping of a normal function type over a neutral row type. Intuitively, neutral forms are forms for which computation is "stuck" waiting on a variable to be substituted for a canonical form. Note that this third neutral form (row mapping) is novel to our development, and, in comparison to application, inverts the normal/neutral expectation of its arguments. It captures the stuck nature of a type such as \verb!(l ▹ λ x. M) <$> ρ!---that is, we are unable to map a function over a type variable.

\begin{code}
data NeutralType Δ where
  ` : 
    (α : KVar Δ κ) → 
    NeutralType Δ κ

  _·_ :     
    (f : NeutralType Δ (κ₁ `→ κ)) → 
    (τ : NormalType Δ κ₁) → 
    NeutralType Δ κ

  _<$>_ : 
    (F : NormalType Δ (κ₁ `→ κ₂)) → (τ : NeutralType Δ R[ κ₁ ]) → 
    NeutralType Δ (R[ κ₂ ])
\end{code}

A predicate is normal if its component types are each normal.

\begin{code}
data NormalPred Δ where
  _·_~_ : 
    (ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]) → 
    NormalPred Δ R[ κ ]

  _≲_ : 
    (ρ₁ ρ₂ : NormalType Δ R[ κ ]) →
    NormalPred Δ R[ κ ]  
\end{code}

Because we consider the normalization of types modulo $\eta$-equivalence, we wish to restrict our normal types to $\eta$-long form. This can be done by restricting the construction of normal-neutral types to just ground kind.  This also ensures a canonical form for arrow-kinded normal types, as neutral types at arrow-kind cannot be promoted to normal types. We define a \verb!Ground! predicate on types that maps all non-arrow kinds to the unit type \verb!⊤! and maps the arrow kind to \verb!⊥!. (In other words, \verb!Ground κ! is trivially inhabitable so long as $\kappa \neq \kappa_1 \to \kappa_2$.)

\begin{code}[hide]
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit hiding (_≟_) public
open import Data.Empty public
\end{code}
\begin{code}
Ground : Kind → Set 
Ground ★ = ⊤
Ground L = ⊤
Ground (κ `→ κ₁) = ⊥
Ground R[ κ ] = ⊤
\end{code}

\Ni It is easy to show that this predicate is decidable.

\begin{code}
ground? : ∀ κ → Dec (Ground κ)
ground? ★ = yes tt
ground? L = yes tt
ground? (_ `→ _) = no (λ ())
ground? R[ _ ] = yes tt
\end{code}

Now we may restrict the \verb!ne! constructor to promoting just neutral types at ground kind by adding the (implicit) requirement that \verb!ne! only be used when \verb!Ground κ! is satisfied. To make this evidence easy to populate when $\kappa$ is known, we employ a well-known proof-by-reflection trick (see \citet{plfa22}) and require evidence of the form \verb!True (ground? κ)!.

\begin{code}[hide]
open import Relation.Nullary.Decidable using (True ; toWitness ; fromWitness)
\end{code}
\begin{code}
data NormalType Δ where
  ne : 
    (x : NeutralType Δ κ) → {ground : True (ground? κ)} → 
    NormalType Δ κ

\end{code}

Likewise, to ensure canonical forms of rows, we restrict \verb!Π! and \verb!Σ! to formation at kind \verb!★! and \verb!L!. The constructors for record types are given below.

\begin{code}
  Π  : 
    (ρ : NormalType Δ R[ ★ ]) →
    NormalType Δ ★

  ΠL  : 
    (ρ : NormalType Δ R[ L ]) →
    NormalType Δ L
\end{code}

The rest of the \verb!NormalType! syntax is identical to the \verb!Type! syntax with the exception that we remove the \verb!`! constructor for variables and \verb!Π! and \verb!Σ! constructors at arbitrary kind. We choose not to omit this syntax, as our proofs of canonicity follow from knowing the totality of \verb!NormalType! constructors.

\begin{code}
  -- Fω
  `λ :
    (τ : NormalType (Δ ,, κ₁) κ₂) → 
    NormalType Δ (κ₁ `→ κ₂)

  _`→_ : 
    (τ₁ τ₂ : NormalType Δ ★) →
    NormalType Δ ★

  `∀    :
    {κ : Kind} → (τ : NormalType (Δ ,, κ) ★) →
    NormalType Δ ★

  μ     :
    (F : NormalType Δ (★ `→ ★)) →
    NormalType Δ ★

  -- Qualified types
  _⇒_ : 
    (π : NormalPred Δ R[ κ₁ ]) → (τ : NormalType Δ ★) → 
    NormalType Δ ★       

  -- Rω
  ε : 
    NormalType Δ R[ κ ]


  _▹_ :  
    (l : NormalType Δ L) → 
    (τ : NormalType Δ κ) → 
    NormalType Δ R[ κ ]

  lab :   
    (l : Label) → 
    NormalType Δ L

  ⌊_⌋ :
    (l : NormalType Δ L) →
    NormalType Δ ★
  Σ  : 
    (ρ : NormalType Δ R[ ★ ]) →
    NormalType Δ ★

  ΣL  : 
    (ρ : NormalType Δ R[ L ]) →
    NormalType Δ L
\end{code}

\subsection{Renaming}
We define renaming over \verb!NormalType!s in the same fashion as defined over \verb!Type!s. Note that we use the suffix \verb!ₖNF! now to denote functions which operate on \verb!NormalType! syntax. Definitions are unsurprising and omitted.

\begin{code}
renₖNE     : Renamingₖ Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
renₖNF     : Renamingₖ Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
weakenₖNF  : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weakenₖNE  : NeutralType Δ κ₂ → NeutralType (Δ ,, κ₁) κ₂
\end{code}
\begin{code}[hide]
renPredₖNF : Renamingₖ Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]

renₖNE ρ (` x) = ` (ρ x)
renₖNE ρ (τ₁ · τ₂) = renₖNE ρ τ₁ · renₖNF ρ τ₂
renₖNE ρ (F <$> τ) = renₖNF ρ F <$> (renₖNE ρ τ)

renₖNF ρ ε   = ε
renₖNF ρ (ne τ {g}) = ne (renₖNE ρ τ) {g}
renₖNF ρ (l ▹ τ) = (renₖNF ρ l) ▹ (renₖNF ρ τ)
renₖNF ρ (`λ τ) = `λ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (τ₁ `→ τ₂) = (renₖNF ρ τ₁) `→ (renₖNF ρ τ₂)
renₖNF ρ (π ⇒ τ) = renPredₖNF ρ π ⇒ renₖNF ρ τ
renₖNF ρ (`∀ τ) = `∀ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (μ τ) = μ (renₖNF ρ τ)
renₖNF ρ (lab x) = lab x
renₖNF ρ ⌊ ℓ ⌋ = ⌊ (renₖNF ρ ℓ) ⌋
renₖNF ρ (Π τ) = Π (renₖNF ρ τ)
renₖNF ρ (ΠL τ) = ΠL (renₖNF ρ τ)
renₖNF ρ (Σ τ) = Σ (renₖNF ρ τ)
renₖNF ρ (ΣL τ) = ΣL (renₖNF ρ τ)

renPredₖNF ρ (ρ₁ · ρ₂ ~ ρ₃) = (renₖNF ρ ρ₁) · (renₖNF ρ ρ₂) ~ (renₖNF ρ ρ₃)
renPredₖNF ρ (ρ₁ ≲ ρ₂) = (renₖNF ρ ρ₁) ≲ (renₖNF ρ ρ₂)

weakenₖNF = renₖNF S
weakenₖNE = renₖNE S 
\end{code}


\subsection{Properties of normal types}
We use Agda to confirm the desired canonicity properties. First, we wish for arrow kinds to be canonically formed by $\lambda$-abstractions. This can be shown easily by induction on arrow-kinded \verb!f!.

\begin{code}[hide]
import Data.Sum as Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open Sum using (_or_ ; left ; right)
import Data.Product as Product
  renaming (proj₁ to fst ; proj₂ to snd) 
open Product 
  using (_×_ ; fst ; snd ; _,_ ; Σ-syntax ; ∃ ; ∃-syntax) 
  public
open import Relation.Binary.PropositionalEquality as Eq public
\end{code}
\begin{code}
arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl
\end{code}

Second, we wish for types at row kind to be canonically either (i) a labeled type \verb!(l ▹ τ)!, (ii) a neutral type, or (iii) the empty row \verb!ε!. The \verb!row-canonicity! lemma below states precisely this. Note that we permit row-kinded types to be neutral because we do not $\eta$-expand arrow-kinded rows. Recall our discussion above that such an expansion would not be kind-preserving. This means arrow-kinded rows must be permitted to be canonically neutral.

\begin{code}
row-canonicity : (ρ : NormalType Δ R[ κ ]) →  
  ∃[ l ] (Σ[ τ ∈ NormalType Δ κ ] ((ρ ≡ (l ▹ τ)))) or 
  Σ[ τ ∈ NeutralType Δ R[ κ ] ] (ρ ≡ ne τ) or 
  ρ ≡ ε 
row-canonicity (l ▹ τ) = left (l , τ , refl)
row-canonicity (ne τ) = right (left (τ , refl))
row-canonicity ε = right (right refl)
\end{code}
\subsection{Type embeddings}

We establish an embedding back from normal types to types below. The embedding is written \verb!⇑! because its type is converse to our definition of normalization, written \verb!⇓!. We will show in later sections precisely that \verb!⇑! is right-inverse to \verb!⇓!.

\begin{code}
⇑ : NormalType Δ κ → Type Δ κ
⇑NE : NeutralType Δ κ → Type Δ κ
⇑Pred : NormalPred Δ R[ κ ] → Pred Δ R[ κ ] 
\end{code}

Much of the embedding is defined by using like-for-like constructors and recursing on the subdata.

\begin{code}
⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)
⇑NE (F <$> τ) = (⇑ F) <$> (⇑NE τ) 

⇑Pred (ρ₁ · ρ₂ ~ ρ₃) = (⇑ ρ₁) · (⇑ ρ₂) ~ (⇑ ρ₃)
⇑Pred (ρ₁ ≲ ρ₂) = (⇑ ρ₁) ≲ (⇑ ρ₂)

⇑ ε   = ε
⇑ (ne x) = ⇑NE x
⇑ (l ▹ τ) = (⇑ l) ▹ (⇑ τ)
⇑ (`λ τ) = `λ (⇑ τ)
⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
⇑ (`∀ τ) = `∀ (⇑ τ)
⇑ (μ τ) = μ (⇑ τ)
⇑ (lab l) = lab l
⇑ ⌊ τ ⌋ = ⌊ ⇑ τ ⌋
⇑ (π ⇒ τ) = (⇑Pred π) ⇒ (⇑ τ)
\end{code}

\Ni An exception is made for record and variant constructors, which we must reconstruct as applications:

\begin{code}
⇑ (Π x) = Π · ⇑ x
⇑ (ΠL x) = Π · ⇑ x
⇑ (Σ x) = Σ · ⇑ x
⇑ (ΣL x) = Σ · ⇑ x
\end{code}

\section{Semantic types}

We next define \verb!SemType Δ κ!, the semantic interpretation of types. \verb!SemType!s are defined by induction on the kind $\kappa$ and mutually-recursively with \verb!KripkeFunction!s, the interpretation of type functions.

\begin{code}[hide]
open import Data.Maybe using (Maybe ; just ; nothing) public
\end{code}
\begin{code}
SemType : KEnv → Kind → Set
KripkeFunction : KEnv → Kind → Kind → Set
\end{code}

Type functions are interpreted as Kripke function spaces because they must permit arbitrary and intermediate renaming. That is, they are functions at "any world."
\begin{code}
KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renamingₖ Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)
SemType Δ₁ (κ₁ `→ κ₂) = KripkeFunction Δ₁ κ₁ κ₂
\end{code}

\Ni We interpret \verb!★! and \verb!L! kinded types as their normal forms.

\begin{code}
SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
\end{code}

\Ni We interpret rows as either \verb!nothing! (the empty row), \verb!just (left x)! for neutral \verb!x!, or \verb!just (right (l , τ))! for normal \verb!l! and \verb!τ!. This corresponds directly with rows having these exact normal forms. (In general, we should expect a bijection between the types \verb!NormalType Δ κ! and \verb!SemType Δ κ!.)

\begin{code}
SemType Δ R[ κ ] = Maybe 
  ((NeutralType Δ R[ κ ]) or 
  (NormalType Δ L × SemType Δ κ))
\end{code}

\subsection{Renaming \& substitution}
Renaming is defined over semantic types in an obvious fashion. Definitions are again surprising and omitted. Substitution is unnecessary, as type functions are interpreted into an Agda function space.


\begin{code}
renSem : Renamingₖ Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
\end{code}

\begin{code}[hide]
open import Function
renKripke : Renamingₖ Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem {κ = ★} ρ τ = renₖNF ρ τ
renSem {κ = L} ρ τ = renₖNF ρ τ
renSem {κ = κ `→ κ₁} ρ F = renKripke ρ F
renSem {κ = R[ κ ]} ρ (just (left x)) = just (left (renₖNE ρ x))
renSem {κ = R[ κ ]} ρ (just (right (l , τ))) = just (right (renₖNF ρ l , renSem ρ τ))
renSem {κ = R[ κ ]} ρ nothing = nothing

weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ
\end{code}

\subsection{Normalization by evaluation}

Our \emph{normalization by evaluation} proceeds in a standard fashion. We will define \verb!reflect!, which maps neutral types to semantic types, and \verb!reify!, which maps semantic types to normal types. We then write an evaluator that takes a \verb!Type! into the semantic domain. During this process, function applications (and other forms of computation) are reduced. We finally reify the semantic type back to a normal form.

Reflection and reification are defined mutually recursively. We define the type synonym \verb!reifyKripke!, the reification of types at arrow kind, for repeated use later.

\begin{code}
reflect : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reifyKripke : KripkeFunction Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
\end{code}

Reflection of neutral types at ground kind leaves the type undisturbed. 
\begin{code}
reflect {κ = ★} τ            = ne τ
reflect {κ = L} τ            = ne τ
reflect {κ = R[ κ ]} τ       = just (left τ)
\end{code}

\Ni Reflection of neutral types at arrow kind are effectively $\eta$-expanded into a Kripke function. Note here that is necessary to reify the input \verb!v! back to a normal type.

\begin{code}
reflect {κ = κ₁ `→ κ₂} τ     = λ ρ v → reflect (renₖNE ρ τ · reify v)
\end{code}

\Ni Reification similarly leaves ground types undisturbed. Semantic types at $\star$ and label kind are already in normal form; semantic types at row kind must be 
translated from their semantic constructors to their \verb!NormalType! constructors. This process simply exhibits (half of) the bijection between the canonical 
forms of row kinded normal types and the semantic domain at row kind.

\begin{code}
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = R[ κ ]} (just (left x)) = ne x
reify {κ = R[ κ ]} (just (right (l , τ))) = l ▹ (reify τ)
reify {κ = R[ κ ]} nothing = ε
\end{code}

Semantic functions must be reified from Agda functions back into \verb!NormalType! syntax. This is done by reifying the
 application of semantic function \verb!F! to the reflection of the $\eta$-expanded variable \verb!` Z!.

\begin{code}
reify {κ = κ₁ `→ κ₂} F = reifyKripke F
reifyKripke {κ₁ = κ₁} F = `λ (reify (F S (reflect {κ = κ₁} (` Z))))
\end{code}

Observe that neutral types can be forced into $\eta$-long form simply by composing reification and reflection. This will prove helpful later, as the neutral type former \verb!ne! has the same 
type except restricted to ground kind, but we will need to be able to promote from neutral to normal type at \emph{all} kinds.

\begin{code}
η-norm : NeutralType Δ κ → NormalType Δ κ 
η-norm = reify ∘ reflect
\end{code}

Towards writing an evaluator, we define a semantic environment as function mapping kinding variables to semantic types.

\begin{code}
Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ
\end{code}

\Ni Environment extension and lifting can be written in a straightforward manner.
\begin{code}
extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
lifte : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
\end{code}

\begin{code}[hide]
extende η V Z     = V
extende η V (S x) = η x

lifte {Δ₁} {Δ₂} {κ} η  = extende η' V -- extende η' V
  where
    η' : Env Δ₁ (Δ₂ ,, κ)
    η' {κ'} v = (weakenSem {Δ = Δ₂} {κ₁ = κ'} {κ₂ = κ}) (η v)

    V  : SemType (Δ₂ ,, κ) κ
    V = reflect {κ = κ} (` Z)
\end{code}

The identity environment now maps type variables to semantic types. Unlike in \citet{ChapmanKNW19}, this environment can no longer be truly said to be an identity: type variables are de facto put into $\eta$-long form during reflection. However this change is mandatory for normalization, so we cannot define an environment that does not.

\begin{code}
idEnv : Env Δ Δ
idEnv = reflect ∘ `
\end{code}

\subsection{Helping evaluation}

In aid of writing an evaluator, we found it helpful to develop \emph{semantic} notions of the syntax introduced by \Rome. For example, we define a type synonym for application, which is simply Agda application within the identity renaming.

\begin{code}
_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
F ·V V = F id V
\end{code}

We can further define the constructors of the three canonical forms of row-kinded types:

\begin{code}
_▹V_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
_▹V_ {κ = κ} ℓ τ = just (right (ℓ , τ))

ne-R : NeutralType Δ R[ κ ] → SemType Δ R[ κ ]
ne-R = just ∘ left

εV : SemType Δ R[ κ ] 
εV = nothing
\end{code}



\Ni The definition of semantic row mapping varies by the shape of the row \verb!V! over which we are lifting. If \verb!V! is neutral, so too must the mapping of \verb!F! over !V! be neutral. Hence we reify \verb!F! to normal form and leave its mapping in neutral form. If \verb!V! is a labeled row \verb!(l ▹ τ)!, we push the application of \verb!F! over \verb!τ!. Finally, if \verb!V! is the empty row, its mapping is empty.

\begin{code}
_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
_<$>V_ {κ₁ = κ₁} {κ₂} F (just (left x)) = ne-R (reifyKripke F <$> x)
_<$>V_ {κ₁ = κ₁} {κ₂} F (just (right (l , τ))) = (l ▹V (F ·V τ))
_<$>V_ {κ₁ = κ₁} {κ₂} F nothing = εV
\end{code}

Although the flap operator \verb!_<?>_! is expressible as a special case of row mapping, we nevertheless find it a useful abstraction. It is defined below in terms of semantic row mapping; we find it likewise helpful to give a type synonym \verb!apply! to the left hand side of this equation.

\begin{code}
apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
apply a = λ ρ F → F ·V (renSem ρ a)

infixr 0 _<?>V_
_<?>V_ : SemType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
f <?>V a = apply a <$>V f
\end{code}

Much of the latent computation in \Rome occurs under an outermost $\Pi$ and $\Sigma$ syntax. To this end, we chose to represent $\Pi$ and $\Sigma$ as arrow-kinded type-constants, 
meaning they will evaluate into Agda functions. This provides an opportunity to concisely abstract their reduction logic. We define a semantic combinator for the $\Pi$ type constant below. 
The first two equations state that record types at $\star$ and label kind may be formed provided normal bodies; the third equation pushes the $\lambda$-binding of $F$ outside of the record type; 
the fourth equation states that application \emph{is} mapping at nested row kind.

\begin{code}
ΠV : SemType Δ R[ κ ] → SemType Δ κ 
ΠV {κ = ★} x = Π (reify x)
ΠV {κ = L} x = ΠL (reify x)
ΠV {κ = κ₁ `→ κ₂} F = λ ρ v → ΠV (renSem ρ F <?>V v)
ΠV {κ = R[ κ ]} x = (λ ρ v → ΠV v) <$>V x
\end{code} 

\Ni We omit the definition of \verb!ΣV!, as it differs only in naming.

\begin{code}[hide]
ΣV : SemType Δ R[ κ ] → SemType Δ κ 
ΣV {κ = ★} x = Σ (reify x)
ΣV {κ = L} x = ΣL (reify x)
ΣV {κ = κ₁ `→ κ₂} F = λ ρ v → ΣV (renSem ρ F <?>V v)
ΣV {κ = R[ κ ]} x = (λ ρ v → ΣV v) <$>V x
\end{code}[hide]

\subsection{Evaluation}

Evaluation reflects a \verb!Type! to the semantic domain, after which reification places the type in normal form. 
Evaluation is defined by induction on the type structure. 

\begin{code}
eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
evalPred : Pred Δ₁ R[ κ ] → Env Δ₁ Δ₂ → NormalPred Δ₂ R[ κ ] 
\end{code}

\Ni As we have no semantic space for predicates, evaluation of predicates simply places 
the predicate's component types into normal form.

\begin{code}
evalPred (ρ₁ · ρ₂ ~ ρ₃) η = reify (eval ρ₁ η) · reify (eval ρ₂ η) ~ reify (eval ρ₃ η)
evalPred (ρ₁ ≲ ρ₂) η = reify (eval ρ₁ η) ≲ reify (eval ρ₂ η)
\end{code}

\Ni We evaluate variables to their image in the environment $\eta$. Applications defer to the semantic combinator \verb!_·V_!; recall that the left-hand applicand $\tau_1$ evaluates to a Kripke \verb!KripkeFunction!, so
evaluation of $\tau_1 · \tau_2$ is simply application in the Agda function space. 


\begin{code}
eval {κ = κ} (` x) η = η x
eval {κ = κ} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
\end{code}

The next four cases are congruent over the type structure. Note that in the \verb!`∀! case, 
we must lift the environment over the newly bound type variable, and in the \verb!μ! case,
we must make sure to reify the evaluation of $\tau$ as $\tau$ evaluates to a Kripke function $\mu$ expects a \verb!NormalType!.


\begin{code}
eval {κ = ★} (π ⇒ τ) η = evalPred π η ⇒ eval τ η
eval {κ = κ} (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)
eval {κ = ★} (`∀ τ) η = `∀ (eval τ (lifte η))
eval {κ = ★} (μ τ) η = μ (reify (eval τ η))
eval {κ = ★} ⌊ τ ⌋ η = ⌊ eval τ η ⌋
\end{code} 

\Ni Label constants have no recursive subdata and so need no further evaluation. 

\begin{code}
eval {κ = L} (lab l) η = lab l
\end{code} 

\Ni Type-level functions evaluate their bodies in an extended environment. 

\begin{code}
eval {κ = κ₁ `→ κ₂} (`λ τ) η = λ ρ v → eval τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)
\end{code} 

\Ni The type constants $\Pi$ and $\Sigma$ evaluate directly to their Kripke combinators; observe that the renaming \verb!ρ! is ignored as both \verb!ΠV! and \verb!ΣV! have no free variables. 
The mapping application \verb!f <$> a! and labeled row \verb!(l ▹ τ)! evaluate to their semantic combinator.
Finally, the empty row evaluates to \verb!nothing!.

\begin{code}
eval {κ = κ₁ `→ κ₂} Π η = λ ρ v → ΠV v
eval {κ = κ₁ `→ κ₂} Σ η = λ ρ v → ΣV v
eval {κ = R[ κ₂ ]} (f <$> a) η = (eval f η) <$>V (eval a η)
eval {κ = _} (l ▹ τ) η = (eval l η) ▹V (eval τ η) 
eval ε η = nothing
\end{code}

We define normalization as the composition of reification and evaluation in the identity environment.

\begin{code}
⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

⇓NE : ∀ {Δ} → NeutralType Δ κ → NormalType Δ κ
⇓NE τ = reify (eval (⇑NE τ) idEnv)
\end{code}

It is helpful in future proofs to name the re-abstraction of a normal type back to its
semantic form: 


\begin{code}
⇈ : NormalType Δ κ → SemType Δ κ 
⇈ τ = eval (⇑ τ) idEnv
\end{code}



\section{Completeness}

\subsection{A logical relation}
\subsection{The fundamental theorem \& completeness}

\section{Soundness}
\subsection{A logical relation}
\subsection{The fundamental theorem \& soundness}

\section{Stability}

\section{Remark}

\subsection{Comparison to \citet{ChapmanKNW19}}
Our mechanization has closely resembled that of \citet{ChapmanKNW19}. Our definition of semantic types, however, has differed, as our normalization is with respect to both $\beta$- and $\eta$-equivalence, whereas Chapman et al's is simply $\beta$-equivalence. Changing this definition simplifies some things and complicates others. The definition of semantic types is simpler: whereas Chapman et al permit function types to be interpreted as \verb!NeutralType!s, ours must be interpreted into solely Kripke function spaces. This complicates the definitions of \verb!reify! and \verb!reflect!, which must become mutually recursive, as we are unable to reflect neutral types at arrow kind to neutral types. We will show later that some of Chapman et al's metatheory relies on neutral forms to not be disturbed by normalization. This complicates the definition of term-level, normality-preserving substitution.


\bibliographystyle{plainnat}
\bibliography{TN}
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

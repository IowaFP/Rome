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

\newunicodechar{→}{$\rightarrow$}
\newunicodechar{×}{$\times$}

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

Rows in \Rome are either the empty row \verb!ε!, a labeled row \verb!(l ▹ τ)!, or a row mapping \verb!f <$> τ!.  We will show that rows in Rome (that is, types at row kind) reduce to either the empty row \verb!ε! or a labeled row \verb!(l ▹ τ)! after normalization. There are two important consequences of this canonicity: firstly, we treat row mapping \verb!_<$>_! as having latent computation to perform (there are no normal types with form \verb!f <$> τ! except when \verb!τ! is a neutral variable). The second consequence is that we do not permit the formation of rows with more than one label-type association. Such rows are instead formed as type variables with predicates specifying the shape of the row.

Rows in \Rome are eliminated by the \verb!Π! and \verb!Σ! constructors.

\begin{code}
  Π     :
          Type Δ (R[ κ ] `→ κ)

  Σ     :
          Type Δ (R[ κ ] `→ κ)
\end{code}

Given a type $\rho$ at row kind, $\Pi \rho$ constructs a record with label-type associations from \verb!ρ! and $\Sigma \rho$ constructs a variant that has label and type from \verb!ρ!. We choose to represent \verb!Π! and \verb!Σ! as type constants at kind \verb!(R[ κ ] `→ κ)!; we will show that many applications of \verb!Π! and \verb!Σ! induce type reductions, and hence it is convenient to group such reductions with type application.

Finally, the syntax of predicates is given below. The predicate $\LeqP {\rho_1} {\rho_2}$ states that label-to-type mappings in $\rho_1$ are a subset of those in $\rho_2$; the predicate $\RowPlusP {\rho_1} {\rho_2} {\rho_3}$ states that the combination of mappings in $\rho_1$ and $\rho_2$ equals $\rho_3$.\footnote{I do not know if I should generalize this description to be row-theory agnostic or if I should specialize it to a specific row theory.}

\begin{code}
data Pred Δ where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]) → 
       Pred Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : Type Δ R[ κ ]) →
       Pred Δ R[ κ ]  
\end{code}

\subsection{Type renaming}

We closely follow PLFA and SFFP (citations needed) in defining a \emph{type renaming} as a function from type variables in one kinding environment to type variables in another. This is the \emph{parallel renaming and substitution} approach (citation needed) for which weakening and single variable substitution are special cases. The code we establish now will be mimicked again for both normal types and for terms; many names are reused, and so we find it helpful to index duplicate names by a suffix. The suffix $_k$ specifies that this definition describes the \verb!Type! syntax.

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

We define renaming as a function that translates a kinding derivation in kinding environment \verb!Δ₁! to environment \verb!Δ₂! provided a renaming from \verb!Δ₁! to \verb!Δ₂!. The definition proceeds by induction on the input kinding derivation; we describe only the interesting cases, omitting the cases which are effectively just congruence over the type structure. In the variable case, we use $\rho$ to rename variable $x$. In the \verb!`λ! and \verb!`∀! cases, we must lift the renaming $\rho$ over the type variable introduced by these binders.

\begin{code}
renₖ : Renamingₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
renPredₖ : Renamingₖ Δ₁ Δ₂ → Pred Δ₁ R[ κ ] → Pred Δ₂ R[ κ ]

renₖ ρ (` x) = ` (ρ x)
renₖ ρ (`λ τ) = `λ (renₖ (liftₖ ρ) τ)
renₖ ρ (π ⇒ τ) = renPredₖ ρ π ⇒ renₖ ρ τ 
renₖ ρ (`∀ τ) = `∀ (renₖ (liftₖ ρ) τ)
\end{code}

\begin{code}[hide]
renₖ ρ ε  = ε
renₖ ρ (τ₁ · τ₂) = (renₖ ρ τ₁) · (renₖ ρ τ₂)
renₖ ρ (τ₁ `→ τ₂) = (renₖ ρ τ₁) `→ (renₖ ρ τ₂)
renₖ ρ (μ F) = μ (renₖ ρ F)
renₖ ρ (Π ) = Π 
renₖ ρ Σ = Σ
renₖ ρ (lab x) = lab x
renₖ ρ (l ▹ τ) = renₖ ρ l ▹ renₖ ρ τ
renₖ ρ ⌊ ℓ ⌋ = ⌊ (renₖ ρ ℓ) ⌋
renₖ ρ (f <$> m) = renₖ ρ f <$> renₖ ρ m
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

\section{Normal Types}

\section{Semantic types}

\subsection{Renaming \& substitution}

\subsection{Normalization by evaluation}

\section{Completeness}

\subsection{Type Equivalence}
\subsection{A logical relation}
\subsection{The fundamental theorem \& completeness}

\section{Soundness}
\subsection{A logical relation}
\subsection{The fundamental theorem \& soundness}

\section{Stability}

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

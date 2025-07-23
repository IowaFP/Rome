\documentclass[authoryear, acmsmall, screen, review, nonacm]{acmart} % % use acmtog for two-column
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
We describe the normalization-by-evaluation (NbE) of types in \Rome, a row calculus with recursive types, qualified types, and a novel \emph{row complement} operator. Types are normalized to $\beta\eta$-long forms modulo a type equivalence relation. Because the type system of \Rome is a strict extension of System \Fome, much of the type reduction is isomorphic to reduction of terms in the STLC. Novel to this report are the reductions of row, record, and variant types.

\section{The \Rome{} calculus}

For reference, \cref{fig:syntax-types} describes the syntax of kinds, predicates, and types in \Rome. We forego further description to the next section.

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

\subsection{Example types and the need for reduction}
% Add motivation for where this incurs type normalization. Show "hidden" maps and hidden reductions. How does $(\Pi\, (\ell \triangleright f)) \, \tau$ reduce?
We will write Rome types in programs in the slightly-altered syntax of \emph{Rosi}, our experimental implementation of \Rome. 
Wand's problem:

\begin{rosi}
wand : forall l x y z t. x + y ~ z, {l := t} < z => #l -> Pi x -> Pi y -> t
\end{rosi}

Here we can simulate the deriving of functor typeclass instances: given a record of \verb!fmap! instances, I can give you a \verb!Functor! instance for $\Sigma\, z$.

\begin{rosi}
type Functor : (* -> *) -> *
type Functor = \f. forall a b. (a -> b) -> f a -> f b

fmapS : forall z : R[* -> *]. Pi (Functor z) -> Functor (Sigma z)
\end{rosi}

Let's first elaborate this type by rendering an implicit map explicit.

\begin{rosi}
fmapS : forall z : R[* -> *]. Pi (Functor z) -> Functor (Sigma z)
\end{rosi}

\Ni And a desugaring of booleans to Church encodings:

\begin{rosi}
desugar : forall y. BoolF < y, LamF < y - BoolF =>
          Pi (Functor (y - BoolF)) -> Mu (Sigma y) -> Mu (Sigma (y - BoolF))
\end{rosi}

\section{Type Reduction}
\subsection{Normal forms}

By directing the type equivalence relation we define computation on types. This serves as a sort of specification on the shape normal forms of types ought to have. Our grammar for normal types must be carefully crafted so as to be neither too "large" nor too "small". In particular, we wish our normalization algorithm to be \emph{stable}, which implies surjectivity. Hence if the normal syntax is too large---i.e., it produces junk types---then these junk types will have pre-images in the domain of normalization. Inversely, if the normal syntax is too small, then there will be types whose normal forms cannot be expressed. \Cref{fig:type-normalization} specifies the syntax and typing of normal types, given as reference. We describe the syntax in more depth by describing its intrinsic mechanization.

\begin{figure}[H]
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
  \mcl{\text{Normal Types}}  & \NormalTypes \ni \Normal \tau, \Normal \phi & ::= & n \mid \Mapp {\hat{\phi}} {n} \mid \Normal{\rho} \mid \Normal{\pi} \then \Normal{\tau} \mid \forall \alpha\co\kappa. \Normal{\tau} \mid \lambda \alpha\co\kappa. \Normal{\tau} \\
                             &       &     & \mid & \LabTy n {\Normal \tau} \mid \ell \mid \Sing {\Normal \tau} \mid {\Normal \tau} \Compl {\Normal \tau} \mid \Pi \, {\Normal \tau} \mid \Sigma \, {\Normal \tau}  \\
\end{doublesyntaxarray}
\end{gather*}
\caption{Normal type forms}
\label{fig:type-normalization}
\end{figure}

\subsection{Metatheory}
\subsubsection{Canonicity of normal types}

The syntax of normal types is defined precisely so as to enjoy canonical forms
based on kind.
\subsubsection{Completeness of normalization}
\subsubsection{Soundness of normalization}
\subsubsection{Decidability of type conversion}

\section{Normalization by Evaluation (NbE)}
\begin{code}[hide]
postulate
  bot : ∀ (X : Set) → X
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars
open import Rome.Types.Syntax
open import Rome.Types.Normal.Syntax
open import Rome.Types.Semantic.Syntax
open import Rome.Prelude
\end{code}

\subsection{The semantic domain}

\subsection{Reflection \& reification}

\subsection{Evaluation}

\subsection{Normalization}
\begin{code}
-- ⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
-- ⇓ τ = reify (eval τ idEnv)
\end{code}

\section{Mechanizing Metatheory}

\subsection{Stability}

\begin{code}
-- stability   : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
-- stabilityNE : ∀ (τ : NeutralType Δ κ) → eval (⇑NE τ) (idEnv {Δ}) ≡ reflect τ
-- stabilityPred : ∀ (π : NormalPred Δ R[ κ ]) → evalPred (⇑Pred π) idEnv ≡ π
-- stabilityRow : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → reifyRow (evalRow (⇑Row ρ) idEnv) ≡ ρ
\end{code}
\begin{code}[hide]
-- stability     = bot _
-- stabilityNE   = bot _
-- stabilityPred = bot _
-- stabilityRow = bot _
\end{code}

Stability implies surjectivity and idempotency.

\begin{code}
-- idempotency : ∀ (τ : Type Δ κ) → (⇑ ∘ ⇓ ∘ ⇑ ∘ ⇓) τ ≡  (⇑ ∘ ⇓)  τ
-- idempotency τ rewrite stability (⇓ τ) = refl

-- surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ)
-- surjectivity τ = ( ⇑ τ , stability τ ) 
\end{code}

Dual to surjectivity, stability also implies that embedding is injective.
 
\begin{code}
-- ⇑-inj : ∀ (τ₁ τ₂ : NormalType Δ κ) → ⇑ τ₁ ≡ ⇑ τ₂ → τ₁ ≡ τ₂                   
-- ⇑-inj τ₁ τ₂ eq = trans (sym (stability τ₁)) (trans (cong ⇓ eq) (stability τ₂))
\end{code}

\subsection{A logical relation for completeness}

\begin{code}
-- subst-Row : ∀ {A : Set} {n m : ℕ} → (n ≡ m) → (f : Fin n → A) → Fin m → A 
-- subst-Row refl f = f

-- -- Completeness relation on semantic types
-- _≋_ : SemType Δ κ → SemType Δ κ → Set
-- _≋₂_ : ∀ {A} → (x y : A × SemType Δ κ) → Set
-- (l₁ , τ₁) ≋₂ (l₂ , τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
-- _≋R_ : (ρ₁ ρ₂ : Row (SemType Δ κ)) → Set 
-- (n , P) ≋R (m , Q) = Σ[ pf ∈ (n ≡ m) ] (∀ (i : Fin m) →  (subst-Row pf P) i ≋₂ Q i)

-- PointEqual-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
-- PointEqualNE-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunctionNE Δ₁ κ₁ κ₂) → Set
-- Uniform :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunction Δ κ₁ κ₂ → Set
-- UniformNE :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunctionNE Δ κ₁ κ₂ → Set

-- _≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
-- _≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
-- _≋_ {Δ₁} {κ = κ₁ `→ κ₂} F G = 
--   Uniform F × Uniform G × PointEqual-≋ {Δ₁} F G 
-- _≋_ {Δ₁} {R[ κ₂ ]} (_<$>_ {κ₁} φ₁ n₁) (_<$>_ {κ₁'} φ₂ n₂) = 
--   Σ[ pf ∈ (κ₁ ≡ κ₁') ]  
--     UniformNE φ₁
--   × UniformNE φ₂
--   × (PointEqualNE-≋ (convKripkeNE₁ pf φ₁) φ₂
--   × convNE pf n₁ ≡ n₂)
-- _≋_ {Δ₁} {R[ κ₂ ]} (φ₁ <$> n₁) _ = ⊥
-- _≋_ {Δ₁} {R[ κ₂ ]} _ (φ₁ <$> n₁) = ⊥
-- _≋_ {Δ₁} {R[ κ ]} (l₁ ▹ τ₁) (l₂ ▹ τ₂) = l₁ ≡ l₂ × τ₁ ≋ τ₂
-- _≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (row ρ x₃) = ⊥
-- _≋_ {Δ₁} {R[ κ ]} (x₁ ▹ x₂) (ρ₂ ─ ρ₃) = ⊥
-- _≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (x₂ ▹ x₃) = ⊥
-- _≋_ {Δ₁} {R[ κ ]} (row (n , P) x₁) (row (m , Q) x₂) = (n , P) ≋R (m , Q)
-- _≋_ {Δ₁} {R[ κ ]} (row ρ x₁) (ρ₂ ─ ρ₃) = ⊥
-- _≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (x₁ ▹ x₂) = ⊥
-- _≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (row ρ x₁) = ⊥
-- _≋_ {Δ₁} {R[ κ ]} (ρ₁ ─ ρ₂) (ρ₃ ─ ρ₄) = ρ₁ ≋ ρ₃ × ρ₂ ≋ ρ₄

-- PointEqual-≋ {Δ₁} {κ₁} {κ₂} F G = 
--   ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
--   V₁ ≋ V₂ → F ρ V₁ ≋ G ρ V₂

-- PointEqualNE-≋ {Δ₁} {κ₁} {κ₂} F G = 
--   ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) (V : NeutralType Δ₂ κ₁) → 
--   F ρ V ≋ G ρ V

-- Uniform {Δ₁} {κ₁} {κ₂} F = 
--   ∀ {Δ₂ Δ₃} (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V₁ V₂ : SemType Δ₂ κ₁) →
--   V₁ ≋ V₂ → (renSem ρ₂ (F ρ₁ V₁)) ≋ (renKripke ρ₁ F ρ₂ (renSem ρ₂ V₂))

-- UniformNE {Δ₁} {κ₁} {κ₂} F = 
--   ∀ {Δ₂ Δ₃} (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V : NeutralType Δ₂ κ₁) →
--   (renSem ρ₂ (F ρ₁ V)) ≋ F (ρ₂ ∘ ρ₁) (renₖNE ρ₂ V)

-- Env-≋ : (η₁ η₂ : Env Δ₁ Δ₂) → Set
-- Env-≋ η₁ η₂ = ∀ {κ} (x : TVar _ κ) → (η₁ x) ≋ (η₂ x)
\end{code}

\subsubsection{Properties}~

\begin{code}
-- reflect-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflect τ₁ ≋ reflect τ₂
-- reify-≋    : ∀ {V₁ V₂ : SemType Δ κ}     → V₁ ≋ V₂ → reify V₁   ≡ reify V₂ 
-- reifyRow-≋ : ∀ {n} (P Q : Fin n → Label × SemType Δ κ) →  
--                (∀ (i : Fin n) → P i ≋₂ Q i) → 
--                reifyRow (n , P) ≡ reifyRow (n , Q)
\end{code}
\begin{code}[hide]
-- reflect-≋  = bot _ 
-- reify-≋    = bot _ 
-- reifyRow-≋ = bot _ 
\end{code}

\subsection{The fundamental theorem and completeness}

\begin{code}
-- fundC : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : Env Δ₁ Δ₂} → 
--        Env-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
-- fundC-pred : ∀ {π₁ π₂ : Pred Type Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
--             Env-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂
-- fundC-Row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
--             Env-≋ η₁ η₂ → ρ₁ ≡r ρ₂ → evalRow ρ₁ η₁ ≋R evalRow ρ₂ η₂
\end{code}
\begin{code}[hide]
-- fundC = bot _
-- fundC-pred = bot _
-- fundC-Row = bot _
\end{code}

\begin{code}
-- idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
-- idEnv-≋ x = reflect-≋ refl

-- completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
-- completeness eq = reify-≋ (fundC idEnv-≋ eq)  

-- completeness-row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → ρ₁ ≡r ρ₂ → ⇓Row ρ₁ ≡ ⇓Row ρ₂
\end{code}
\begin{code}[hide]
-- completeness-row = bot _
\end{code}

\subsection{A logical relation for soundness}
\begin{code}
-- infix 0 ⟦_⟧≋_
-- ⟦_⟧≋_ : ∀ {κ} → Type Δ κ → SemType Δ κ → Set
-- ⟦_⟧≋ne_ : ∀ {κ} → Type Δ κ → NeutralType Δ κ → Set

-- ⟦_⟧r≋_ : ∀ {κ} → SimpleRow Type Δ R[ κ ] → Row (SemType Δ κ) → Set
-- ⟦_⟧≋₂_ : ∀ {κ} → Label × Type Δ κ → Label × SemType Δ κ → Set
-- ⟦ (l₁ , τ) ⟧≋₂ (l₂ , V) = (l₁ ≡ l₂) × (⟦ τ ⟧≋ V)

-- SoundKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set
-- SoundKripkeNE : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunctionNE Δ₁ κ₁ κ₂ → Set

-- -- τ is equivalent to neutral `n` if it's equivalent 
-- -- to the η and map-id expansion of n
-- ⟦_⟧≋ne_ τ n = τ ≡t ⇑ (η-norm n)

-- ⟦_⟧≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
-- ⟦_⟧≋_ {κ = L} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
-- ⟦_⟧≋_ {Δ₁} {κ = κ₁ `→ κ₂} f F = SoundKripke f F
-- ⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (row (n , P)  oρ) =
--     let xs = ⇑Row (reifyRow (n , P)) in 
--     (τ ≡t ⦅ xs ⦆ (fromWitness (Ordered⇑ (reifyRow (n , P)) (reifyRowOrdered' n P oρ)))) × 
--     (⟦ xs ⟧r≋ (n , P))
-- ⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (l ▹ V) = (τ ≡t (⇑NE l ▹ ⇑ (reify V))) × (⟦ ⇑ (reify V) ⟧≋ V)
-- ⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ ((ρ₂ ─ ρ₁) {nr}) = (τ ≡t (⇑ (reify ((ρ₂ ─ ρ₁) {nr})))) × (⟦ ⇑ (reify ρ₂) ⟧≋ ρ₂) × (⟦ ⇑ (reify ρ₁) ⟧≋ ρ₁)
-- ⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (φ <$> n) = 
--   ∃[ f ] ((τ ≡t (f <$> ⇑NE n)) × (SoundKripkeNE f φ))
-- ⟦ [] ⟧r≋ (zero , P) = ⊤
-- ⟦ [] ⟧r≋ (suc n , P) = ⊥
-- ⟦ x ∷ ρ ⟧r≋ (zero , P) = ⊥
-- ⟦ x ∷ ρ ⟧r≋ (suc n , P) =  (⟦ x ⟧≋₂ (P fzero)) × ⟦ ρ ⟧r≋ (n , P ∘ fsuc)

-- SoundKripke {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
--     ∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {v V} → 
--       ⟦ v ⟧≋ V → 
--       ⟦ (renₖ ρ f · v) ⟧≋ (renKripke ρ F ·V V)

-- SoundKripkeNE {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
--     ∀ {Δ₂} (r : Renamingₖ Δ₁ Δ₂) {v V} → 
--       ⟦ v ⟧≋ne  V → 
--       ⟦ (renₖ r f · v) ⟧≋ (F r V)
\end{code}

\subsubsection{Properties}~
\begin{code}
-- reflect-⟦⟧≋ : ∀ {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
--              τ ≡t ⇑NE υ → ⟦ τ ⟧≋ (reflect υ)
-- reify-⟦⟧≋ : ∀ {τ : Type Δ κ} {V :  SemType Δ κ} → 
--                ⟦ τ ⟧≋ V → τ ≡t ⇑ (reify V)
-- η-norm-≡t : ∀ (τ : NeutralType Δ κ) → ⇑ (η-norm τ) ≡t ⇑NE τ 
-- subst-⟦⟧≋ : ∀ {τ₁ τ₂ : Type Δ κ} → 
--   τ₁ ≡t τ₂ → {V : SemType Δ κ} → ⟦ τ₁ ⟧≋ V → ⟦ τ₂ ⟧≋ V 
\end{code}

\subsubsection{Logical environments}~
\begin{code}
-- ⟦_⟧≋e_ : ∀ {Δ₁ Δ₂} → Substitutionₖ Δ₁ Δ₂ → Env Δ₁ Δ₂ → Set  
-- ⟦_⟧≋e_ {Δ₁} σ η = ∀ {κ} (α : TVar Δ₁ κ) → ⟦ (σ α) ⟧≋ (η α)

-- Identity relation
-- idSR : ∀ {Δ₁} →  ⟦ ` ⟧≋e (idEnv {Δ₁})
-- idSR α = reflect-⟦⟧≋ eq-refl
\end{code}
\begin{code}[hide]
-- reflect-⟦⟧≋ = bot _
-- reify-⟦⟧≋ = bot _
-- η-norm-≡t = bot _
-- subst-⟦⟧≋ = bot _
-- \end{code}
-- \subsection{The fundamental theorem and soundness}
-- \begin{code}
-- fundS : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
--           ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)
-- fundSRow : ∀ {Δ₁ Δ₂ κ}(xs : SimpleRow Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
--           ⟦ σ ⟧≋e η  → ⟦ subRowₖ σ xs ⟧r≋ (evalRow xs η)
-- fundSPred : ∀ {Δ₁ κ}(π : Pred Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
--           ⟦ σ ⟧≋e η → (subPredₖ σ π) ≡p ⇑Pred (evalPred π η) 
\end{code}

\begin{code}[hide]
-- fundS = bot _
-- fundSRow = bot _
-- fundSPred = bot _
\end{code}

\begin{code}
--------------------------------------------------------------------------------
-- Fundamental theorem when substitution is the identity
-- subₖ-id : ∀ (τ : Type Δ κ) → subₖ ` τ ≡ τ 

-- ⊢⟦_⟧≋ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≋ eval τ idEnv
-- ⊢⟦ τ ⟧≋ = subst-⟦⟧≋ (inst (subₖ-id τ)) (fundS τ idSR)
\end{code}
\begin{code}[hide]
-- subₖ-id τ = bot _
\end{code}

\begin{code}
--------------------------------------------------------------------------------
-- Soundness claim  

-- soundness :  ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 
-- soundness τ = reify-⟦⟧≋ (⊢⟦ τ ⟧≋)

 --------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ τ₂ then the embedding of τ₁ is equivalent to τ₂

-- embed-≡t : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ τ₂) → ⇑ τ₁ ≡t τ₂
-- embed-≡t {τ₁ = τ₁} {τ₂} refl = eq-sym (soundness τ₂) 

--------------------------------------------------------------------------------
-- Soundness implies the converse of completeness, as desired

-- Completeness⁻¹ : ∀ {Δ κ} → (τ₁ τ₂ : Type Δ κ) → ⇓ τ₁ ≡ ⇓ τ₂ → τ₁ ≡t τ₂
-- Completeness⁻¹ τ₁ τ₂ eq = eq-trans (soundness τ₁) (embed-≡t eq)
\end{code}


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

module Simple.StackBasedBigStep where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; map; take)
open import Data.List.Properties using (length-++; ++-identityʳ; ++-assoc)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Bool using (Bool; true; false) renaming (T to 𝕋)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _<_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (<ᵇ⇒<; +-suc; +-identityʳ; n≤1+n; m≤m+n) renaming (≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import Data.Fin using (Fin; zero; suc; fromℕ; fromℕ<; inject≤)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; proj₁ ; proj₂; Σ; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; const; _∘_)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; dcong)

{-
** The problem

If we pass stack arguments to a heap closure, then we need to ensure that the
callers' stack does not get corrupted. Corruption can only happen in the presence of
references.

As an example, suppose we pass a stack reference r which contains another stack reference.
That is r : ref 2 (ref 2 Int). On the local stack, we allocate a new reference as in
x = ref 2 (42)
and overwrite the content of r with it
r := x
Now the callers' stack contains a reference to the current stackframe, which becomes
invalid after return from the heap closure (as this return pops the stack).

** Design alternatives

1. Disallow passing stack references to heap closures.
   A well-formedness constraint on function types can help: if the function is heap, then its arguments and results must be heap, too.

2. If we pass a stack reference to a heap function, then it should not be written to.
   To this end, we might introduce a type of read-only references as a supertype of read-write references such that ref 2 T <: roref 2 T' where T' is a read-only supertype of T.
   Writing to a stack reference could happen indirectly via a stack closure, so we'd have to have a simple effect that all writeable references are on the heap.

   (on the other hand, references to primitive type are ok as we cannot introduce backpointers through this avenue.)

** Here we choose option 1.

-}


--

Ident = String
Address = ℕ

open import Qualifiers
open import Auxiliary

-- well-formed types

--! QType {
data Type (q : Qual) : Set
record QType : Set where
  inductive
  constructor mkQ
  field
    q-of  : Qual
    t-of  : Type q-of
open QType public

data Type q where
  Unit  : Type q
  Base  : Type q
  Fun   : (S₁ : QType) → (S₂ : QType)
        → q-of S₁ ≤ q → q-of S₂ ≤ q → Type q
  Ref   : (S : QType) → q-of S ≤ q → Type q

syntax mkQ q t = t ^ q
--! }

-- variables
--! Variables
record Var : Set where
  constructor X
  field
    ident : Ident
    q-var : Qual
open Var public

x≢⇒s≢ : ∀ {s s′ : Ident}{q : Qual} → X s q ≢ X s′ q → s ≢ s′
x≢⇒s≢ xneq refl = xneq refl

-- expressions
--! Expr
data Expr  : Set where
  unit     : Expr
  cst      : ℕ → Expr
  var      : Var → Expr
  lam      : Qual → Var → Expr → Qual → Expr
  app      : Expr → Expr → Expr
  seq      : Expr → Expr → Expr
  ref      : Qual → Expr → Expr
  deref    : Expr → Expr
  setref   : Expr → Expr → Expr

-- values and run-time environments
--! Values {
data Val   : Set
record Stack : Set
data Env   : Set where
  ∅        : Env
  ⟨_≔_,_⟩  : Ident → Val → Env → Env
  ⟨_⇒_,_⟩  : Ident → Address → Env → Env

data Val where
  unit  : Val
  cst   : ℕ → Val
  clos  : (q : Qual) (𝓔 : Env) (𝓢 : Stack) (x : Var) (e : Expr)
         (qᵣ : Qual) → Val
  ref   : (q : Qual) (ℓ : Address) → Val

record Stack where
  inductive; constructor mkS
  field
    vars  : List Val
    refs  : List Val

Heap = List Val
--! }
open Stack public

data _∋_⇒_ : Env → Var → Address → Set where

  here   : ∀ {𝓔}{s}{i} → ⟨ s ⇒ i , 𝓔 ⟩ ∋ X s 𝟚 ⇒ i
  there  : ∀ {𝓔}{x}{i}{s}{j} → 𝓔 ∋ x ⇒ i → ⟨ s ⇒ j , 𝓔 ⟩ ∋ x ⇒ i
  skip   : ∀ {𝓔}{x}{i}{s}{v} → 𝓔 ∋ x ⇒ i → ⟨ s ≔ v , 𝓔 ⟩ ∋ x ⇒ i

clos-stack-env : Val → Maybe (Env × Stack)
clos-stack-env unit = nothing
clos-stack-env (cst x) = nothing
clos-stack-env (clos q 𝓔 𝓢 x e x₁) = just (𝓔 , 𝓢)
clos-stack-env (ref q ℓ) = nothing

variable
  𝓔 𝓔′ : Env
  𝓗 𝓗′ 𝓗″ 𝓗‴ : Heap
  𝓢 𝓢′ 𝓢″ 𝓢‴ 𝓢⁗ 𝓢₁ 𝓢₂ 𝓢₃ 𝓢ᶜ : Stack
  𝓛 : List (List Val)
  s s′ : Ident
  v v′ v″ v₀ v₁ v₂ : Val
  vs vs′ : List Val
  x x′ : Var
  e e₁ e₂ e′ : Expr
  n ℓ : ℕ

-- push an argument on the stack

push : Stack → Val → Stack
push (mkS vars refs) v = mkS (vars ++ [ v ]) refs

push-refs-≡ : push 𝓢 v .refs ≡ 𝓢 .refs
push-refs-≡ = refl

-- allocate a reference on the stack

push-refs : Stack → List Val → Stack
push-refs (mkS vv rr) vs = mkS vv (rr ++ vs)

salloc : Stack → Val → Stack × ℕ
salloc (mkS vars₁ refs₁) v = mkS vars₁ (refs₁ ++ [ v ]) , length refs₁


𝓢∅ : Stack
𝓢∅ = mkS [] []

--! StackExtension
_≼ₛ_ : Stack → Stack → Set
𝓢₁ ≼ₛ 𝓢₂ = 𝓢₁ .vars ≼ 𝓢₂ .vars
          × length (𝓢₁ .refs) ≤ℕ length (𝓢₂ .refs)

≼ₛ-bot : (𝓢 : Stack) → 𝓢∅ ≼ₛ 𝓢
≼ₛ-bot 𝓢 = (𝓢 .vars , refl) , z≤n

≼ₛ-refl : 𝓢 ≼ₛ 𝓢
≼ₛ-refl = ([] , (++-identityʳ _)) , ≤ℕ-refl

≼ₛ-trans : 𝓢₁ ≼ₛ 𝓢₂ → 𝓢₂ ≼ₛ 𝓢₃ → 𝓢₁ ≼ₛ 𝓢₃
≼ₛ-trans ((vs , refl) , ≤-12) ((vs₁ , refl) , ≤-23) = ((vs ++ vs₁) , (sym (++-assoc _ vs vs₁))) , ≤ℕ-trans ≤-12 ≤-23

≼ₛ-push : 𝓢 ≼ₛ push 𝓢 v
≼ₛ-push {𝓢 = 𝓢}{v = v} = ([ v ] , refl) , ≤ℕ-refl

≼ₛ-salloc : 𝓢 ≼ₛ salloc 𝓢 v .proj₁
≼ₛ-salloc {𝓢 = 𝓢} = ([] , (++-identityʳ _)) , ≤ℕ-trans (m≤m+n _ 1) (≡⇒≤ (sym (length-++ (𝓢 .refs))))

≼ₛ-extend : ∀ vs → 𝓢 ≼ₛ mkS (𝓢 .vars) (𝓢 .refs ++ vs)
≼ₛ-extend {𝓢} vs = ([] , ++-identityʳ _) , (≤ℕ-trans (m≤m+n _ (length vs)) (≡⇒≤ (sym (length-++ (𝓢 .refs)))))

-- typing

--! Contexts
data Ctx : Set where
  ∅         : Ctx
  _,_⦂_[_]  :  (Γ : Ctx) (x : Var) (S : QType)
               (S≡x : q-of S ≡ q-var x) → Ctx

variable
  Γ Γ′ Γ″ Γ‴ : Ctx
  T T₁ T₂ : Type q
  S S′ S₀ S₁ S₂ S₃ S₄ : QType

--! ContextLookup
data _∋_⦂_ : Ctx → Var → QType → Set where
  here   : ∀ {S≡x} → (Γ , x ⦂ S [ S≡x ]) ∋ x ⦂ S
  there  : ∀ {S≡x} → Γ ∋ x ⦂ S → x ≢ x′
         → (Γ , x′ ⦂ S′ [ S≡x ]) ∋ x ⦂ S


-- lower bounds for qualifiers

q-val : Val → Qual
q-val unit = 𝟙
q-val (clos q _ _ _ _ _) = q
q-val (cst x) = 𝟙
q-val (ref q _) = q


module _ (q : Qual) where

  data q-Bound : Ctx → Set where

    qb-∅ : q-Bound ∅

    qb-add : ∀ {S≡x} → q-of S ≤ q → q-Bound Γ → q-Bound (Γ , x ⦂ S [ S≡x ])

  data q-Bounded : Ctx → Ctx → Set where

    qb-∅ : q-Bounded ∅ ∅

    qb-keep : ∀ {S≡x} → q-of S ≤ q → q-Bounded Γ Γ′ → q-Bounded (Γ , x ⦂ S [ S≡x ]) (Γ′ , x ⦂ S [ S≡x ])

    qb-drop : ∀ {S≡x} → q-Bounded Γ Γ′ → (∀ {x′} {S′} → Γ′ ∋ x′ ⦂ S′ → x′ ≢ x)  → q-Bounded (Γ , x ⦂ S [ S≡x ]) (Γ′)


  data q-Bounded-Env : Env → Env → Set where

    qbe-∅ : q-Bounded-Env ∅ ∅

    qbe-keep : q-Bounded-Env 𝓔 𝓔′ → q-Bounded-Env ⟨ s ≔ v , 𝓔 ⟩ ⟨ s ≔ v , 𝓔′ ⟩

    qbe-drop : ∀ {a} → q-Bounded-Env 𝓔 𝓔′ → q-Bounded-Env ⟨ s ⇒ a , 𝓔 ⟩ (case q of λ { 𝟙 → 𝓔′ ; 𝟚 → ⟨ s ⇒ a , 𝓔′ ⟩ })


is-bounded : q-Bounded q Γ Γ′ → q-Bound q Γ′
is-bounded qb-∅ = qb-∅
is-bounded (qb-keep x qbdd) = qb-add x (is-bounded qbdd)
is-bounded (qb-drop qbdd _) = is-bounded qbdd

𝟚-bounded-env : q-Bounded-Env 𝟚 𝓔 𝓔′ → 𝓔 ≡ 𝓔′
𝟚-bounded-env qbe-∅ = refl
𝟚-bounded-env (qbe-keep qbe) = trans ((cong₂ ⟨_≔_, _ ⟩) refl refl) ((cong ⟨ _ ≔ _ ,_⟩) (𝟚-bounded-env qbe))
𝟚-bounded-env (qbe-drop qbe) = trans ((cong₂ ⟨_⇒_, _ ⟩) refl refl) ((cong ⟨ _ ⇒ _ ,_⟩) (𝟚-bounded-env qbe))


𝟙-bound⇒∀𝟚∉ : q-Bound 𝟙 Γ → (∀ s S → ¬ (Γ ∋ X s 𝟚 ⦂ S))
𝟙-bound⇒∀𝟚∉ qb-∅ s S ()
𝟙-bound⇒∀𝟚∉ (qb-add {S≡x = ()} ≤-refl qbd) s S here
𝟙-bound⇒∀𝟚∉ (qb-add x qbd) s S (there x∈ x₁) = 𝟙-bound⇒∀𝟚∉ qbd s S x∈

--! SubtypingRelation {
data _<⦂′_ {q₁ q₂ : Qual} {qsub : q₁ ≤ q₂}
           : Type q₁ → Type q₂ → Set

data _<⦂_ : QType → QType → Set where

  SQual  : (qsub : q₁ ≤ q₂)
         → _<⦂′_ {qsub = qsub} T₁  T₂
         → (T₁ ^ q₁) <⦂ (T₂ ^ q₂)

data _<⦂′_ {q₁ q₂ qsub} where

  SUnit  : Unit <⦂′ Unit

  SBase  : Base <⦂′ Base

  SFun   : ∀ {cq₁ cq₂ cq₃ cq₄}
         → S₃ <⦂ S₁
         → S₂ <⦂ S₄
         → Fun S₁ S₂ cq₁ cq₂ <⦂′ Fun S₃ S₄ cq₃ cq₄

  SRef   : ∀ {cq₁ cq₂}
         → S₁ <⦂ S₂
         → S₂ <⦂ S₁
         → Ref S₁ cq₁ <⦂′ Ref S₂ cq₂
--! }

q-of-mono : S₁ <⦂ S₂ → q-of S₁ ≤ q-of S₂
q-of-mono (SQual q1≤q2 _) = q1≤q2


<⦂-refl : S <⦂ S
<⦂′-refl : ∀ {T : Type q} → _<⦂′_ {qsub = ≤-refl} T  T

<⦂-refl {mkQ q T} = SQual ≤-refl <⦂′-refl

<⦂′-refl {T = Unit} = SUnit
<⦂′-refl {T = Base} = SBase
<⦂′-refl {T = Fun S₁ S₂ cq₁ cq₂} = SFun <⦂-refl <⦂-refl
<⦂′-refl {T = Ref S x} = SRef <⦂-refl <⦂-refl

<⦂-trans : S₁ <⦂ S₂ → S₂ <⦂ S₃ → S₁ <⦂ S₃
<⦂′-trans : ∀ {T₁ : Type q₁}{T₂ : Type q₂}{T₃ : Type q₃}{qsub₁ : q₁ ≤ q₂}{qsub₂ : q₂ ≤ q₃}
  → _<⦂′_ {qsub = qsub₁} T₁ T₂ → _<⦂′_ {qsub = qsub₂} T₂ T₃ → _<⦂′_ {qsub = ≤-trans qsub₁ qsub₂} T₁ T₃

<⦂-trans (SQual qsub T₁<⦂T₂) (SQual qsub₁ T₂<⦂T₃) = SQual (≤-trans qsub qsub₁) (<⦂′-trans T₁<⦂T₂ T₂<⦂T₃)

<⦂′-trans (SUnit) (SUnit) = SUnit
<⦂′-trans (SBase) (SBase) = SBase
<⦂′-trans (SFun <⦂-arg₁ <⦂-res₁) (SFun <⦂-arg₂ <⦂-res₂) = SFun (<⦂-trans <⦂-arg₂ <⦂-arg₁) (<⦂-trans <⦂-res₁ <⦂-res₂)
<⦂′-trans (SRef S₁<⦂S₂ S₂<⦂S₁) (SRef S₂<⦂S₃ S₃<⦂S₂) = SRef (<⦂-trans S₁<⦂S₂ S₂<⦂S₃) (<⦂-trans S₃<⦂S₂ S₂<⦂S₁)

<⦂-antisym : S₁ <⦂ S₂ → S₂ <⦂ S₁ → S₁ ≡ S₂
<⦂′-antisym : ∀ {T₁ T₂ : Type q} → _<⦂′_ {qsub = ≤-refl} T₁ T₂ → _<⦂′_ {qsub = ≤-refl} T₂ T₁ → T₁ ≡ T₂

<⦂-antisym (SQual qsub T₁<⦂T₂) (SQual qsub₁ T₂<⦂T₁)
  with ≤-antisym qsub qsub₁
<⦂-antisym (SQual ≤-refl T₁<⦂T₂) (SQual ≤-refl T₂<⦂T₁) | refl
  = cong (mkQ _) (<⦂′-antisym T₁<⦂T₂ T₂<⦂T₁)

<⦂′-antisym (SUnit) (SUnit) = refl
<⦂′-antisym (SBase) (SBase) = refl
<⦂′-antisym (SFun S₁<⦂S₂ S₁<⦂S₃) (SFun S₂<⦂S₁ S₂<⦂S₂)
  with refl ← <⦂-antisym S₂<⦂S₁ S₁<⦂S₂
  with refl ← <⦂-antisym S₁<⦂S₃ S₂<⦂S₂
  = cong₂ (Fun _ _) ≤-irrelevant ≤-irrelevant
<⦂′-antisym (SRef S₁<⦂S₂ _) (SRef  S₂<⦂S₁ _)
  with refl ← <⦂-antisym S₁<⦂S₂ S₂<⦂S₁
  = cong (Ref _) ≤-irrelevant


-- typing

--! TypingRules {
data _⊢_⦂_ : Ctx → Expr → QType → Set where

  TUnit    : Γ ⊢ unit ⦂ (Unit ^ q)

  TBase    : Γ ⊢ cst n ⦂ (Base ^ q)

  TVar     : Γ ∋ x ⦂ S
           → Γ ⊢ var x ⦂ S

  TAbs     : ∀ {S≡x}
           → (Γ′ , x ⦂ S₁ [ S≡x ]) ⊢ e ⦂ S₂
           → q-Bounded q Γ Γ′
           → let q₁ = q-of S₁; q₂ = q-of S₂
           in {cq₁ : q₁ ≤ q}
           → {cq₂ : q₂ ≤ q}
           → Γ ⊢ lam q x e q₂ ⦂ (Fun S₁ S₂ cq₁ cq₂ ^ q)

  TApp     : ∀ {cq₁ cq₂}
           → Γ ⊢ e₁ ⦂ (Fun S₁ S₂ cq₁ cq₂ ^ 𝟚)
           → Γ ⊢ e₂ ⦂ S₁
           → Γ ⊢ app e₁ e₂ ⦂ S₂

  TSub     : Γ ⊢ e ⦂ S
           → S <⦂ S′
           → Γ ⊢ e ⦂ S′

  TSeq     : Γ ⊢ e₁ ⦂ (Unit ^ 𝟚)
           → Γ ⊢ e₂ ⦂ S
           → Γ ⊢ seq e₁ e₂ ⦂ S

  TRef     : ∀ {cq : q-of S ≤ q}
           → Γ ⊢ e ⦂ S
           → Γ ⊢ ref q e ⦂ (Ref S cq ^ q)

  TDeref   : ∀ {cq : q-of S ≤ q}
           → Γ ⊢ e ⦂ (Ref S cq ^ q)
           → Γ ⊢ deref e ⦂ S

  TSetref  : ∀ {cq : q-of S ≤ q}
           → Γ ⊢ e₁ ⦂ (Ref S cq ^ q)
           → Γ ⊢ e₂ ⦂ S
           → Γ ⊢ setref e₁ e₂ ⦂ (Unit ^ 𝟙)
--! }


-- heap & stack typing

_↓′_ : List Val → ℕ → Maybe Val
[] ↓′ i = nothing
(x ∷ xs) ↓′ zero = just x
(x ∷ xs) ↓′ (suc i) = xs ↓′ i

↓′-[] : (i : ℕ) → [] ↓′ i ≡ nothing
↓′-[] i = refl

_↓ᵥ_ : Stack → ℕ → Maybe Val
𝓢 ↓ᵥ i = 𝓢 .vars ↓′ i

_↓ᵣ_ : Stack → ℕ → Maybe Val
𝓢 ↓ᵣ i = 𝓢 .refs ↓′ i

↓′-mono : ∀ {v} i → just v ≡ vs ↓′ i → just v ≡ (vs ++ vs′) ↓′ i
↓′-mono {x₁ ∷ vs} {vs′} {i} zero vs↓≡ = vs↓≡
↓′-mono {x₁ ∷ vs} {vs′} {i} (suc x) vs↓≡ = ↓′-mono {vs} {vs′} {i} x vs↓≡

↓ᵥ-mono : ∀ {v}{i : ℕ} → 𝓢 ≼ₛ 𝓢′ →  just v ≡ 𝓢 ↓ᵥ i → just v ≡ 𝓢′ ↓ᵥ i
↓ᵥ-mono {𝓢 = 𝓢} {v = v} {i = i} ((fst , refl) , snd) 𝓢↓≡ = ↓′-mono {vs = 𝓢 .vars} {v = v} i 𝓢↓≡

↓′-last : ∀ vs → just v ≡ (vs ++ [ v ]) ↓′ (length vs)
↓′-last [] = refl
↓′-last (_ ∷ vs) = ↓′-last vs


variable
  a a′  : Address
  va va′ : Val ⊎ Address

-- (H,∅)(x 1) = v
data Access : Env → Var → Val → Set where

  here   : Access ⟨ s ≔ v , 𝓔 ⟩ (X s 𝟙) v
  there  : Access 𝓔 x v → X s′ 𝟙 ≢ x → Access ⟨ s′ ≔ v′ , 𝓔 ⟩ x v
  skip   : Access 𝓔 x v → X s′ 𝟚 ≢ x → Access ⟨ s′ ⇒ a′ , 𝓔 ⟩ x v

data StackAccess : Env → Var → Address → Set where

  here   : StackAccess ⟨ s ⇒ a , 𝓔 ⟩ (X s 𝟚) a
  there  : StackAccess 𝓔 x a → X s′ 𝟚 ≢ x → StackAccess ⟨ s′ ⇒ a′ , 𝓔 ⟩ x a
  skip   : StackAccess 𝓔 x a → X s′ 𝟙 ≢ x → StackAccess ⟨ s′ ≔ v′ , 𝓔 ⟩ x a

data GenAccess : Env → Var → (Val ⊎ Address) → Set where

  on-heap   : Access 𝓔 (X s 𝟙) v → GenAccess 𝓔 (X s 𝟙) (inj₁ v)
  on-stack  : StackAccess 𝓔 (X s 𝟚) a → GenAccess 𝓔 (X s 𝟚) (inj₂ a)

access-unique : Access 𝓔 x v → Access 𝓔 x v′ → v ≡ v′
access-unique here here = refl
access-unique here (there acc′ x) = ⊥-elim (x refl)
access-unique (there acc x) here = ⊥-elim (x refl)
access-unique (there acc x) (there acc′ x₁) = access-unique acc acc′
access-unique (skip acc x) (skip acc′ x₁) = access-unique acc acc′

stack-access-unique : StackAccess 𝓔 x a → StackAccess 𝓔 x a′ → a ≡ a′
stack-access-unique here here = refl
stack-access-unique here (there sa′ x) = ⊥-elim (x refl)
stack-access-unique (there sa x) here = ⊥-elim (x refl)
stack-access-unique (there sa x) (there sa′ x₁) = stack-access-unique sa sa′
stack-access-unique (skip sa x) (skip sa′ x₁) = stack-access-unique sa sa′

gen-access-unique : GenAccess 𝓔 x va → GenAccess 𝓔 x va′ → va ≡ va′
gen-access-unique (on-heap x) (on-heap x₁) = cong inj₁ (access-unique x x₁)
gen-access-unique (on-stack x) (on-stack x₁) = cong inj₂ (stack-access-unique x x₁)


-- heap and stack types

Typeof : Qual → Set
Typeof 𝟙 = Type 𝟙               -- heap types
Typeof 𝟚 = QType                -- stack types

_^^_ : (q : Qual) → Typeof q → QType
𝟙 ^^ T = T ^ 𝟙
𝟚 ^^ S = S

q-^^-≤ : {S : Typeof q} → q-of (q ^^ S) ≤ q
q-^^-≤ {𝟙} = ≤-refl
q-^^-≤ {𝟚} = ≤-top

HSType = (q : Qual) → List (Typeof q)

-- heap type

HType = List (Type 𝟙)

-- stack type

SType = List QType

variable
  Σₕₛ Σₕₛ′ Σₕₛ″ : HSType
  Σₕ Σₕ′ Σₕ″ : HType
  Σₛ Σₛ′ Σₛ″ : SType
  Σₓ Σₓ′ Σₓ″ : List (Typeof q)

extend-Σ : HSType → (q : Qual) → Typeof q → HSType
extend-Σ Σₕₛ 𝟙 T 𝟙 = Σₕₛ 𝟙 ++ [ T ]
extend-Σ Σₕₛ 𝟙 T 𝟚 = Σₕₛ 𝟚
extend-Σ Σₕₛ 𝟚 T 𝟙 = Σₕₛ 𝟙
extend-Σ Σₕₛ 𝟚 T 𝟚 = Σₕₛ 𝟚 ++ [ T ]


adjust-stack : HSType → List QType → HSType
adjust-stack Σₕₛ Σₛ 𝟙 = Σₕₛ 𝟙
adjust-stack Σₕₛ Σₛ 𝟚 = Σₛ


---- heap/stack typing extension
-- combined h/s typing

_≼ₕₛ_ : HSType → HSType → Set
Σₕₛ ≼ₕₛ Σₕₛ′ = ∀ q → ∃[ qts ] Σₕₛ q ++ qts ≡  Σₕₛ′ q

≼ₕₛ-refl : Σₕₛ ≼ₕₛ Σₕₛ
≼ₕₛ-refl {Σₕₛ} q = [] , ++-identityʳ (Σₕₛ q)

≼ₕₛ-trans : Σₕₛ ≼ₕₛ Σₕₛ′ →  Σₕₛ′ ≼ₕₛ Σₕₛ″ →  Σₕₛ ≼ₕₛ Σₕₛ″
≼ₕₛ-trans { Σₕₛ} Σ≼ Σ≼″ q
  with Σ≼ q | Σ≼″ q
... | qts1 , eq1 | qts2 , eq2
  rewrite sym eq2 = (qts1 ++ qts2) , trans (sym (++-assoc (Σₕₛ q) qts1 qts2)) (cong (_++ qts2) eq1)

≼ₕₛ-extend-Σ : ∀ q₁ S₁ → Σₕₛ ≼ₕₛ extend-Σ Σₕₛ q₁ S₁
≼ₕₛ-extend-Σ 𝟙 S₁ 𝟙 = [ S₁ ] , refl
≼ₕₛ-extend-Σ 𝟙 S₁ 𝟚 = [] , (++-identityʳ _)
≼ₕₛ-extend-Σ 𝟚 S₁ 𝟙 = [] , (++-identityʳ _)
≼ₕₛ-extend-Σ 𝟚 S₁ 𝟚 = [ S₁ ] , refl

≼ₕₛ-adjust : ∀ {Σ₁ Σ₂ : HSType} → Σ₁ ≼ₕₛ Σ₂ → Σ₁ ≼ₕₛ adjust-stack Σ₂ (Σ₁ 𝟚)
≼ₕₛ-adjust ≼Σ₁ 𝟙 = ≼Σ₁ 𝟙
≼ₕₛ-adjust {Σ₁} ≼Σ₁ 𝟚 = [] , ++-identityʳ (Σ₁ 𝟚)

-- ≼ₕₛ-adjust-[] : ∀ {Σ₁ Σ₂ : HSType} → adjust-stack Σ₁ [] ≼ₕₛ Σ₂ → Σ₁ ≼ₕₛ adjust-stack Σ₂ (Σ₁ 𝟚)
-- ≼ₕₛ-adjust-[] ≼Σ₁ 𝟙 = ≼Σ₁ 𝟙
-- ≼ₕₛ-adjust-[] {Σ₁} ≼Σ₁ 𝟚 = [] , ++-identityʳ (Σ₁ 𝟚)

≼ₕₛ⇒length : Σₕₛ ≼ₕₛ Σₕₛ′ → ∀ q → length (Σₕₛ q) ≤ℕ length (Σₕₛ′ q)
≼ₕₛ⇒length {Σₕₛ} Σ≼ q
  with Σ≼ q
... | qts , eq
  with length-≤ (Σₕₛ q) qts
... | r
  rewrite eq
  = r

≼ₕₛ-lookup-aux : ∀ {a}{A : Set a} (xs ys zs : List A)
  → (eq : xs ++ ys ≡ zs)
  → (i : Fin (length xs))
  → lookup (xs ++ ys) (inject≤ i (length-≤ xs ys)) ≡ lookup zs (inject≤ i (subst (λ xx → length xs ≤ℕ length xx) eq (length-≤ xs ys)))
≼ₕₛ-lookup-aux xs ys zs refl i = refl

≼ₕₛ-lookup : (Σ≼ : Σₕₛ ≼ₕₛ Σₕₛ′) → ∀ q → (i : Fin (length (Σₕₛ q))) → lookup (Σₕₛ q) i ≡ lookup (Σₕₛ′ q) (inject≤ i (≼ₕₛ⇒length Σ≼ q))
≼ₕₛ-lookup {Σₕₛ = Σₕₛ}{Σₕₛ′} Σ≼ q i
  using qts , eq ← Σ≼ q
  = trans (lookup-++ (Σₕₛ q) qts i) (≼ₕₛ-lookup-aux (Σₕₛ q) qts (Σₕₛ′ q) eq i)

---- value typing & environment agreement

--! NewFrame
new-frame? : Qual → Stack → Stack
new-frame? 𝟙 𝓢 = 𝓢∅
new-frame? 𝟚 𝓢 = 𝓢

--! Choose
choose : (q : Qual) → HType → SType → List (Typeof q)
choose 𝟙 Σₕ Σₛ = Σₕ
choose 𝟚 Σₕ Σₛ = Σₛ

--! ValueTyping {
data ⟨_,_⟩⊢[_⦂_] (Σₕ : HType) (Σₛ : SType)
                 : Val → QType → Set

record ⟨_,_,_⟩⊨_/_ (Σₕ : HType) (Σₛ : SType) (Γ : Ctx)
                   (𝓔 : Env) (𝓢 : Stack) : Set where
  inductive
  constructor mk-⊨
  field
    ⊨-heap   : ∀ {s}{T} → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙)
             → ∃[ v ] Access 𝓔 (X s 𝟙) v
                    × ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
    ⊨-stack  : ∀ {s}{S} → Γ ∋ X s 𝟚 ⦂ S
             → ∃[ a ] StackAccess 𝓔 (X s 𝟚) a
                    × ∃[ v ] just v ≡ (𝓢 ↓ᵥ a)
                    × ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ]
open ⟨_,_,_⟩⊨_/_ public

-- value typing

data ⟨_,_⟩⊢[_⦂_] Σₕ Σₛ where

  TVUnit  : ⟨ Σₕ , Σₛ ⟩⊢[ unit ⦂ (Unit ^ q) ]

  TVCst   : ⟨ Σₕ , Σₛ ⟩⊢[ cst n ⦂ (Base ^ q) ]

  TVClos  : ∀ {S₁≤x}
          → (∀⊨𝓔 : ∀ 𝓢′ → (𝓢≼ : 𝓢 ≼ₛ 𝓢′)
                        → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢′)
          → (𝓢≡ : 𝓢 ≡ new-frame? q 𝓢)
          → (qbd : q-Bound q Γ)
          → (⊢e : (Γ , x ⦂ S₁ [ S₁≤x ]) ⊢ e ⦂ S₂)
          → let q₂ = q-of S₂ in
          let q₁ = q-of S₁
          in (cq₁ : q₁ ≤ q)
          → (cq₂ : q₂ ≤ q)
          → (<⦂S : (Fun S₁ S₂ cq₁ cq₂ ^ q) <⦂ S)
          → ⟨ Σₕ , Σₛ ⟩⊢[ clos q 𝓔 𝓢 x e q₂ ⦂ S ]

  TVRef   : ∀ {T : Typeof q}
          → let Σᵣ = choose q Σₕ Σₛ
          in (ℓ< : ℓ < length Σᵣ)
          → (lkup≡ : lookup Σᵣ (fromℕ< ℓ<) ≡ T)
          → (<⦂S : (Ref (q ^^ T) q-^^-≤ ^ q) <⦂ S)
          → ⟨ Σₕ , Σₛ ⟩⊢[ ref q ℓ ⦂ S ]
--! }

rename-bounded′ : q-Bounded q Γ Γ′ → Γ′ ∋ x ⦂ S → Γ ∋ x ⦂ S
rename-bounded′ (qb-keep x qbdd) (here) = here
rename-bounded′ (qb-keep x qbdd) (there x∈ x≢) = there (rename-bounded′ qbdd x∈) x≢
rename-bounded′ (qb-drop qbdd f) x∈ = there (rename-bounded′ qbdd x∈) (f x∈)

restrict′ : ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → q-Bounded q Γ Γ′ → ⟨ Σₕ , Σₛ , Γ′ ⟩⊨ 𝓔 / new-frame? q 𝓢
restrict′ {q = 𝟚} ⊨𝓔 qbdd =
  mk-⊨ (λ x∈ → ⊨-heap ⊨𝓔 (rename-bounded′ qbdd x∈))
       (λ x∈ → ⊨-stack ⊨𝓔 (rename-bounded′ qbdd x∈))
restrict′ {q = 𝟙} ⊨𝓔 qbdd =
  mk-⊨ (λ x∈ → ⊨-heap ⊨𝓔 (rename-bounded′ qbdd x∈))
       (λ{ x∈ → ⊥-elim (𝟙-bound⇒∀𝟚∉ (is-bounded qbdd) _ _ x∈)})


𝟙-value : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ] → S <⦂ mkQ 𝟙 T → q-val v ≡ 𝟙
𝟙-value TVUnit S<⦂ = refl
𝟙-value TVCst S<⦂ = refl
𝟙-value (TVClos ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ (SQual ≤-refl x₁)) (SQual ≤-refl x) = refl
𝟙-value (TVRef ℓ< lkup≡ (SQual ≤-refl x₁)) (SQual ≤-refl x) = refl

𝟙-value-no-stack : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ] → q-of S ≡ 𝟙 → ⟨ Σₕ , [] ⟩⊢[ v ⦂ S ]
𝟙-env-no-stack : ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → q-Bound 𝟙 Γ →  ⟨ Σₕ , [] , Γ ⟩⊨ 𝓔 / 𝓢

𝟙-value-no-stack TVUnit qs≡𝟙 = TVUnit
𝟙-value-no-stack TVCst qs≡𝟙 = TVCst
𝟙-value-no-stack (TVClos {q = 𝟙} ∀⊨𝓔 refl qbd ⊢e cq₁ cq₂ (SQual ≤-refl x)) refl = TVClos (λ 𝓢′ 𝓢≼ → 𝟙-env-no-stack (∀⊨𝓔 𝓢′ 𝓢≼) qbd) refl qbd ⊢e cq₁ cq₂ (SQual ≤-refl x)
𝟙-value-no-stack (TVRef {𝟙} ℓ< lkup≡ <⦂S) refl = TVRef ℓ< lkup≡ <⦂S
𝟙-value-no-stack (TVRef {𝟚} ℓ< lkup≡ (SQual () x)) refl

𝟙-env-no-stack ⊨𝓔 qbd = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , acc , 𝟙-value-no-stack ⊢v refl)
                             λ x∈ → contradiction x∈ (𝟙-bound⇒∀𝟚∉ qbd _ _)

⊨-adjust-≼ₛ : 𝓢 ≼ₛ 𝓢′
  → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢′

⊨-adjust-≼ₛ {𝓢 = 𝓢}{𝓢′ = 𝓢′} 𝓢≼ₛ𝓢′ ⊨𝓔 =
  mk-⊨ (λ x∈ → ⊨-heap ⊨𝓔 x∈)
       (λ x∈ → let a , sa , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , sa , v , (↓ᵥ-mono {𝓢 = 𝓢}{𝓢′ = 𝓢′} 𝓢≼ₛ𝓢′ eq) , ⊢v)

-- a heap value can be typed with any stack type

⊢ᵥ-adjust-𝟙 : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ] →  ⟨ Σₕ , Σₛ′ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
⊨-adjust-𝟙 : q-Bound 𝟙 Γ → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢′ → ⟨ Σₕ , Σₛ′ , Γ ⟩⊨ 𝓔 / 𝓢′

⊢ᵥ-adjust-𝟙 TVUnit = TVUnit
⊢ᵥ-adjust-𝟙 TVCst = TVCst
⊢ᵥ-adjust-𝟙 (TVClos {q = 𝟙} ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S) = TVClos (λ 𝓢′ 𝓢≼ → ⊨-adjust-𝟙 qbd (∀⊨𝓔 𝓢′ 𝓢≼)) 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S
⊢ᵥ-adjust-𝟙 (TVClos {q = 𝟚} ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ (SQual () x))
⊢ᵥ-adjust-𝟙 (TVRef {𝟙} ℓ< lkup≡ <⦂S) = TVRef ℓ< lkup≡ <⦂S
⊢ᵥ-adjust-𝟙 (TVRef {𝟚} ℓ< lkup≡ (SQual () x))

⊨-adjust-𝟙 qbd ⊨𝓔 = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , acc , ⊢ᵥ-adjust-𝟙 ⊢v)
                         (λ {s} {S} x∈ → contradiction x∈ (𝟙-bound⇒∀𝟚∉ qbd s S))


-- extension for value types and agreement

⊨-extend : Σₕ ≼ Σₕ′ → Σₛ ≼ Σₛ′ → 𝓢 ≼ₛ 𝓢′ → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → ⟨ Σₕ′ , Σₛ′ , Γ ⟩⊨ 𝓔 / 𝓢′
⊢ᵥ-extend : Σₕ ≼ Σₕ′ → Σₛ ≼ Σₛ′ → 𝓢 ≼ₛ 𝓢′ → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ] → ⟨ Σₕ′ , Σₛ′ ⟩⊢[ v ⦂ S ]

⊨-extend {𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼Σₕ ≼Σₛ ≼𝓢 ⊨𝓔 = mk-⊨ (λ x → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x in v , acc , ⊢ᵥ-extend {𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼Σₕ ≼Σₛ ≼𝓢 ⊢v)
                         (λ x → let a , sacc , v , jv≡ , ⊢v = ⊨-stack ⊨𝓔 x in a , sacc , v , ↓ᵥ-mono{𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼𝓢 jv≡ , ⊢ᵥ-extend {𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼Σₕ ≼Σₛ ≼𝓢 ⊢v)
⊢ᵥ-extend ≼Σₕ ≼Σₛ ≼𝓢 TVUnit = TVUnit
⊢ᵥ-extend ≼Σₕ ≼Σₛ ≼𝓢 TVCst = TVCst
⊢ᵥ-extend ≼Σₕ ≼Σₛ ≼𝓢 (TVClos ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S)
  = TVClos (λ 𝓢′₁ 𝓢≼ → ⊨-extend {𝓢 = 𝓢′₁} ≼Σₕ ≼Σₛ (≼ₛ-refl {𝓢′₁}) (∀⊨𝓔 _ 𝓢≼)) 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S
⊢ᵥ-extend {Σₕ = Σₕ} {Σₛ = Σₛ} ≼Σₕ@(qts , eq) ≼Σₛ ≼𝓢 (TVRef {q = 𝟙} ℓ< lkup≡ <⦂S) = TVRef (≤ℕ-trans ℓ< (≼⇒length ≼Σₕ)) (trans (lookup-from-i′ Σₕ ℓ< eq) lkup≡) <⦂S
⊢ᵥ-extend {Σₕ = Σₕ} {Σₛ = Σₛ} ≼Σₕ ≼Σₛ@(qts , eq) ≼𝓢 (TVRef {q = 𝟚} ℓ< lkup≡ <⦂S) = TVRef (≤ℕ-trans ℓ< (≼⇒length ≼Σₛ)) (trans (lookup-from-i′ Σₛ ℓ< eq) lkup≡) <⦂S



-- heap typing


--! HeapTyping {
_⊢[_⦂_] : HType → Val → Type 𝟙 → Set
Σₕ ⊢[ v ⦂ T ] = ⟨ Σₕ , [] ⟩⊢[ v ⦂ (T ^ 𝟙)]

_⊢ₕ_ : HType → Heap → Set
Σₕ ⊢ₕ 𝓗 = Pointwise (Σₕ ⊢[_⦂_]) 𝓗 Σₕ
--! }

⊢ₕ-length-aux : ∀ {q} {Σᵣ} {vs : List Val} → Pointwise (λ x y → ⟨ Σₕ , Σₛ ⟩⊢[ x ⦂ (q ^^ y) ]) vs Σᵣ → length Σᵣ ≡ length vs
⊢ₕ-length-aux [] = refl
⊢ₕ-length-aux (x∼y ∷ pws) = cong suc (⊢ₕ-length-aux pws)

⊢ₕ-length : Σₕ ⊢ₕ 𝓗 → length Σₕ ≡ length 𝓗
⊢ₕ-length ⊢𝓗 = ⊢ₕ-length-aux ⊢𝓗




-- stack typing

--! StackTyping
_,_⊢ₛ_ : HType → SType → Stack → Set
Σₕ , Σₛ ⊢ₛ 𝓢 = Pointwise ⟨ Σₕ , Σₛ ⟩⊢[_⦂_] (𝓢 .refs) Σₛ

⊢ₛ-length : Σₕ , Σₛ ⊢ₛ 𝓢 → length Σₛ ≡ length (𝓢 .refs)
⊢ₛ-length ⊢𝓢 = ⊢ₕ-length-aux ⊢𝓢


⊨-adjust-≼ₕ :
  Σₕ ≼ Σₕ′
  → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → ⟨ Σₕ′ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢

⊢ᵥ-adjust-≼ₕ :
  Σₕ ≼ Σₕ′
  → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ]
  → ⟨ Σₕ′ , Σₛ ⟩⊢[ v ⦂ S ]
⊢ᵥ-adjust-≼ₕ ≼Σ TVUnit = TVUnit
⊢ᵥ-adjust-≼ₕ ≼Σ TVCst = TVCst
⊢ᵥ-adjust-≼ₕ ≼Σ (TVClos ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S) = TVClos (λ 𝓢′ 𝓢≼ → ⊨-adjust-≼ₕ ≼Σ (∀⊨𝓔 𝓢′ 𝓢≼)) 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S
⊢ᵥ-adjust-≼ₕ {Σₕ = Σₕ} ≼Σ (TVRef {𝟙} ℓ< lkup≡ <⦂S)
  with ≼Σ in eq
... | qts , eq1  
  = TVRef (≤ℕ-trans ℓ< (≼⇒length ≼Σ)) (trans (lookup-from-i′ Σₕ ℓ< eq1) lkup≡) <⦂S
⊢ᵥ-adjust-≼ₕ ≼Σ (TVRef {𝟚} ℓ< lkup≡ <⦂S) = TVRef ℓ< lkup≡ <⦂S

⊨-adjust-≼ₕ ≼Σ ⊨𝓔
  = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , acc , ⊢ᵥ-adjust-≼ₕ ≼Σ ⊢v)
         (λ x∈ → let a , sa , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , sa , v , eq , ⊢ᵥ-adjust-≼ₕ ≼Σ ⊢v)



⊢ₛ-adjust-aux-≼ₕ : ∀ {vs : List Val} {Σᵣ : List QType}
  → Σₕ ≼ Σₕ′
  → Pointwise ⟨ Σₕ , Σₛ ⟩⊢[_⦂_] vs Σᵣ
  → Pointwise ⟨ Σₕ′ , Σₛ ⟩⊢[_⦂_] vs Σᵣ
⊢ₛ-adjust-aux-≼ₕ ≼Σ [] = []
⊢ₛ-adjust-aux-≼ₕ ≼Σ (x∼y ∷ pws) = ⊢ᵥ-adjust-≼ₕ ≼Σ x∼y ∷ ⊢ₛ-adjust-aux-≼ₕ ≼Σ pws


⊢ₛ-adjust-≼ₕ :
  Σₕ ≼ Σₕ′
  → Σₕ , Σₛ ⊢ₛ 𝓢
  → Σₕ′ , Σₛ ⊢ₛ 𝓢
⊢ₛ-adjust-≼ₕ ≼Σ ⊢𝓢 = ⊢ₛ-adjust-aux-≼ₕ ≼Σ ⊢𝓢



⊢ₛ-adjust-push : ∀ {vs}
  → Σₕ , Σₛ ⊢ₛ 𝓢
  → Σₕ , Σₛ ⊢ₛ mkS (𝓢 .vars ++ vs) (𝓢 .refs)
⊢ₛ-adjust-push {𝓢 = 𝓢} ⊢𝓢 = ⊢𝓢


⊨-adjust-push-update : ∀ {S₁≤x} s
  → ⟨ Σₕ , Σₛ ⟩⊢[ v₀ ⦂ S ]
  → (⊨𝓔   : ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢)
  → ⟨ Σₕ , Σₛ , (Γ , X s 𝟚 ⦂ S [ S₁≤x ]) ⟩⊨ ⟨ s ⇒ length (𝓢 .vars) , 𝓔 ⟩ / mkS (𝓢 .vars ++ [ v₀ ]) (𝓢 .refs)

⊨-adjust-push-update  {v₀ = v₀}{𝓢 = 𝓢} s ⊢v₀ ⊨𝓔
  = mk-⊨ (λ{ (there x∈ x≢) → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , skip acc (x≢ ∘ sym) , ⊢v })
         (λ{ here → length (𝓢 .vars) , here , v₀ , ↓′-last (𝓢 .vars) , ⊢v₀
           ; (there x∈ x≢) → let a , acc , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , there acc (x≢ ∘ sym) , v , ↓′-mono {vs = 𝓢 .vars} {vs′ = [ v₀ ]} a eq , ⊢v })

-- value typing extends

⊨-extend-Σ : Σₕ ≼ Σₕ′ → Σₛ ≼ Σₛ′ → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → ⟨ Σₕ′ , Σₛ′ , Γ ⟩⊨ 𝓔 / 𝓢

[⦂]-≼ₕₛ :  Σₕ ≼ Σₕ′ → Σₛ ≼ Σₛ′ → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ] → ⟨ Σₕ′ , Σₛ′ ⟩⊢[ v ⦂ S ]
[⦂]-≼ₕₛ Σ≼ₕ Σ≼ₛ TVUnit = TVUnit
[⦂]-≼ₕₛ Σ≼ₕ Σ≼ₛ TVCst = TVCst
[⦂]-≼ₕₛ Σ≼ₕ Σ≼ₛ (TVClos ∀⊨𝓔 𝓢≡ qbd ⊢e σ?≡ cq₂ <⦂S) = TVClos (λ 𝓢′ 𝓢≼ → ⊨-extend-Σ Σ≼ₕ Σ≼ₛ (∀⊨𝓔  𝓢′ 𝓢≼)) 𝓢≡ qbd ⊢e σ?≡ cq₂ <⦂S
[⦂]-≼ₕₛ {Σₕ = Σₕ} {Σₛ = Σₛ} Σ≼ₕ@(qts , eq) Σ≼ₛ (TVRef {q = 𝟙} ℓ< lkup≡ <⦂S) = TVRef (≤ℕ-trans ℓ< (≼⇒length Σ≼ₕ)) (trans (lookup-from-i′ Σₕ ℓ< eq) lkup≡) <⦂S
[⦂]-≼ₕₛ {Σₕ = Σₕ} {Σₛ = Σₛ} Σ≼ₕ Σ≼ₛ@(qts , eq) (TVRef {q = 𝟚} ℓ< lkup≡ <⦂S) = TVRef (≤ℕ-trans ℓ< (≼⇒length Σ≼ₛ)) (trans (lookup-from-i′ Σₛ ℓ< eq) lkup≡) <⦂S


-- agreement extends


⊨-extend-Σ Σ≼ₕ Σ≼ₛ ⊨Γ = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨Γ x∈ in v , acc , [⦂]-≼ₕₛ Σ≼ₕ Σ≼ₛ ⊢v)
                             (λ x∈ → let a , sa , v , eq , ⊢v = ⊨-stack ⊨Γ x∈ in a , sa , v , eq , [⦂]-≼ₕₛ Σ≼ₕ Σ≼ₛ ⊢v)


-- heap typing extends (needed?)




⊨-extend-𝟙 : ∀ {S₁≤x} s T
  → (⊢v : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙)])
  → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → ⟨ Σₕ , Σₛ , (Γ , X s 𝟙 ⦂ (T ^ 𝟙) [ S₁≤x ]) ⟩⊨ ⟨ s ≔ v , 𝓔 ⟩ / 𝓢
⊨-extend-𝟙 {v = v} s T ⊢v ⊨𝓔 =
  mk-⊨ (λ{ here → v , here , ⊢v
       ; (there x∈ x≢) → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , there acc (x≢ ∘ sym) , ⊢v})
       (λ{ (there x∈ x≢) → let a , sa , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , (skip sa (x≢ ∘ sym)) , v , eq , ⊢v})


⊨𝓔-stack-𝟙 : q-Bound 𝟙 Γ → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → ⟨ Σₕ , Σₛ′ , Γ ⟩⊨ 𝓔 / 𝓢
⊢v-stack-𝟙 : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ] → ⟨ Σₕ , Σₛ′ ⟩⊢[ v ⦂ (T ^ 𝟙) ]

⊢v-stack-𝟙 TVUnit = TVUnit
⊢v-stack-𝟙 TVCst = TVCst
⊢v-stack-𝟙 (TVClos {q = 𝟙} ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S) = TVClos (λ 𝓢′ 𝓢≼ → ⊨𝓔-stack-𝟙 qbd (∀⊨𝓔 𝓢′ 𝓢≼)) 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S
⊢v-stack-𝟙 (TVClos {q = 𝟚} ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ (SQual () x))
⊢v-stack-𝟙 (TVRef {𝟙} ℓ< lkup≡ <⦂S) = TVRef ℓ< lkup≡ <⦂S
⊢v-stack-𝟙 (TVRef {𝟚} ℓ< lkup≡ (SQual () x))

⊨𝓔-stack-𝟙 qbd ⊨𝓔 = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , acc , ⊢v-stack-𝟙 ⊢v)
                         (λ {s} {S} x∈ → contradiction x∈ (𝟙-bound⇒∀𝟚∉ qbd s S))

access-soundness : ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) → Access 𝓔 (X s 𝟙) v → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
access-soundness Γ⊨ x∈ access
  with ⊨-heap Γ⊨ x∈
... | v , acc′ , ⊢v
  rewrite access-unique access acc′ = ⊢v

¬x𝟙∈𝟚 : ¬ (Γ ∋ X s 𝟙 ⦂ mkQ 𝟚 T)
¬x𝟙∈𝟚 (there x∈ x≢) = ¬x𝟙∈𝟚 x∈

genaccess-soundness : ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → Γ ∋ x ⦂ (T ^ q) → GenAccess 𝓔 x (inj₁ v) → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ q) ]
genaccess-soundness {q = 𝟙} ⊨𝓔 x∈ (on-heap acc) = access-soundness ⊨𝓔 x∈ acc
genaccess-soundness {q = 𝟚} ⊨𝓔 x∈ (on-heap acc) = contradiction x∈ ¬x𝟙∈𝟚

genaccess-soundness-𝟚 : ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢 → Γ ∋ x ⦂ (T ^ q) → GenAccess 𝓔 x (inj₂ a) → ∀ v → just v ≡ 𝓢 ↓ᵥ a → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ q) ]
genaccess-soundness-𝟚 ⊨𝓔 x∈ (on-stack sa) v eq
  with ⊨-stack ⊨𝓔 x∈
... | a , sa′ , v′ , eq′ , ⊢v
  rewrite stack-access-unique sa sa′ | sym eq
  with eq′
... | refl = ⊢v



<⦂-val-lift : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S₁ ] → S₁ <⦂ S₂ → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S₂ ]
<⦂-val-lift TVUnit (SQual _ SUnit) = TVUnit
<⦂-val-lift TVCst  (SQual _ SBase) = TVCst
<⦂-val-lift (TVClos ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ <⦂S₁) S₁<⦂S₂ = TVClos ∀⊨𝓔 𝓢≡ qbd ⊢e cq₁ cq₂ (<⦂-trans <⦂S₁ S₁<⦂S₂)
<⦂-val-lift (TVRef ℓ< lkup≡ <⦂S₁) S₁<⦂S₂ = TVRef ℓ< lkup≡ (<⦂-trans <⦂S₁ S₁<⦂S₂)


-- operational semantics

-- operations on references: deref and update

data read : List Val → ℕ → Val → Set where

  read0 : read (v ∷ vs) zero v
  read1 : read vs n v → read (v′ ∷ vs) (suc n) v

data sread : Stack → ℕ → Val → Set where

  sread0 : read (𝓢 .refs) ℓ v → sread 𝓢 ℓ v

data write : List Val → ℕ → Val → List Val → Set where

  write0 : write (v′ ∷ vs) zero v (v ∷ vs)
  write1 : write vs n v vs′ → write (v′ ∷ vs) (suc n) v (v′ ∷ vs′)

data swrite : Stack → ℕ → Val → Stack → Set where

  swrite0 : ∀{vars} → write vs ℓ v vs′ → swrite (mkS vars vs) ℓ v (mkS vars vs′)

length-write : write vs ℓ v vs′ → length vs ≡ length vs′
length-write write0 = refl
length-write (write1 wr) = cong suc (length-write wr)

≼ₛ-swrite : swrite 𝓢 ℓ v 𝓢′ → 𝓢 ≼ₛ 𝓢′
≼ₛ-swrite (swrite0 wr) = ([] , ++-identityʳ _) , ≡⇒≤ (length-write wr)

{-unused-}
swrite-≼ₛ : swrite 𝓢 ℓ v 𝓢′ → 𝓢′ ≼ₛ 𝓢
swrite-≼ₛ (swrite0 wr) = ([] , ++-identityʳ _) , ≡⇒≤ (sym (length-write wr))

typed-read-aux : ∀ {q}{T : Typeof q}{Σᵣ : List (Typeof q)}
  → Pointwise (λ v T → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (q ^^ T) ] ) 𝓗 Σᵣ
  → {ℓ : ℕ}
  → (ℓ< : ℓ < length Σᵣ)
  → (lkup≡ : lookup Σᵣ (fromℕ< ℓ<) ≡ T)
  → read 𝓗 ℓ v
  → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (q ^^ T) ]
typed-read-aux (x∼y ∷ pws) {zero} ℓ< refl read0 = x∼y
typed-read-aux (x∼y ∷ pws) {suc ℓ} (s≤s ℓ<) lkup≡ (read1 rd) = typed-read-aux pws {ℓ} ℓ< lkup≡ rd

typed-read : Σₕ ⊢ₕ 𝓗
  → (ℓ< : ℓ < length Σₕ)
  → (lkup≡ : lookup Σₕ (fromℕ< ℓ<) ≡ T)
  → read 𝓗 ℓ v
  → ⟨ Σₕ , [] ⟩⊢[ v ⦂ (T ^ 𝟙) ]
typed-read {Σₕ = Σₕ} ⊢𝓗 ℓ< lkup≡ xread = typed-read-aux {Σᵣ = Σₕ}  ⊢𝓗 ℓ< lkup≡ xread 

typed-sread : Σₕ , Σₛ ⊢ₛ 𝓢
  → (ℓ< : ℓ < length Σₛ)
  → (lkup≡ : lookup Σₛ (fromℕ< ℓ<) ≡ S)
  → sread 𝓢 ℓ v
  → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ]
typed-sread {Σₛ = Σₛ} ⊢𝓢 ℓ< lkup≡ (sread0 xread) = typed-read-aux {Σᵣ = Σₛ} ⊢𝓢 ℓ< lkup≡ xread

typed-write-aux : ∀ {q}{T : Typeof q}{Σᵣ}
  → Pointwise (λ w T → ⟨ Σₕ , Σₛ ⟩⊢[ w ⦂ (q ^^ T) ] ) 𝓗 Σᵣ
  → {ℓ : ℕ}
  → (ℓ< : ℓ < length Σᵣ)
  → (lkup≡ : lookup Σᵣ (fromℕ< ℓ<) ≡ T)
  → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (q ^^ T) ]
  → write 𝓗 ℓ v 𝓗′
  → Pointwise (λ w T → ⟨ Σₕ , Σₛ ⟩⊢[ w ⦂ (q ^^ T) ] ) 𝓗′ Σᵣ
typed-write-aux (x∼y ∷ pws) {zero} ℓ< refl ⊢v write0 = ⊢v ∷ pws
typed-write-aux (x∼y ∷ pws) {suc ℓ} (s≤s ℓ<) lkup≡ ⊢v (write1 xwrite) = x∼y ∷ typed-write-aux pws ℓ< lkup≡ ⊢v xwrite

typed-write : ∀ {T : Type 𝟙}
  → Σₕ ⊢ₕ 𝓗
  → (ℓ< : ℓ < length Σₕ)
  → (lkup≡ : lookup Σₕ (fromℕ< ℓ<) ≡ T)
  → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
  → write 𝓗 ℓ v 𝓗′
  → Σₕ ⊢ₕ 𝓗′
typed-write {Σₕ = Σₕ} ⊢𝓗 ℓ< lkup≡ ⊢v xwrite = typed-write-aux {Σᵣ = Σₕ} ⊢𝓗 ℓ< lkup≡ (⊢ᵥ-adjust-𝟙 ⊢v) xwrite

typed-swrite : ∀ {S}
  → Σₕ , Σₛ ⊢ₛ 𝓢
  → (ℓ< : ℓ < length Σₛ)
  → (lkup≡ : lookup Σₛ (fromℕ< ℓ<) ≡ S)
  → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ]
  → swrite 𝓢 ℓ v 𝓢′
  → Σₕ , Σₛ ⊢ₛ 𝓢′
typed-swrite {Σₛ = Σₛ} ⊢𝓢 ℓ< lkup≡ ⊢v (swrite0 xwrite) = typed-write-aux {Σᵣ = Σₛ} ⊢𝓢 ℓ< lkup≡ ⊢v xwrite

⊢𝓗-extend-𝟙-aux : ∀ {Σᵣ} → (T : Type 𝟙) (⊢v : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ])
  → (⊢𝓗    : Pointwise (λ v T → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ T ^ 𝟙 ]) 𝓗 Σᵣ)
  → Pointwise (λ v T′ → ⟨ Σₕ ++ [ T ] , Σₛ ⟩⊢[ v ⦂ (T′ ^ 𝟙)] ) (𝓗 ++ v ∷ []) (Σᵣ ++ [ T ])
⊢𝓗-extend-𝟙-aux T ⊢v [] = ([⦂]-≼ₕₛ ([ T ] , refl) ≼-refl ⊢v) ∷ []
⊢𝓗-extend-𝟙-aux T ⊢v (x∼y ∷ ⊢𝓗) = [⦂]-≼ₕₛ ([ T ] , refl) ≼-refl x∼y ∷ (⊢𝓗-extend-𝟙-aux T ⊢v ⊢𝓗)

⊢𝓗-extend-𝟙 : (T : Type 𝟙) (⊢v : ⟨ Σₕ , [] ⟩⊢[ v ⦂ mkQ 𝟙 T ]) (⊢𝓗 : Σₕ ⊢ₕ 𝓗)
  → Pointwise (λ v T′ → ⟨ Σₕ ++ [ T ] , [] ⟩⊢[ v ⦂ (T′ ^ 𝟙)] ) (𝓗 ++ v ∷ []) (Σₕ ++ [ T ])
⊢𝓗-extend-𝟙 T ⊢v ⊢𝓗 = ⊢𝓗-extend-𝟙-aux T ⊢v ⊢𝓗

⊢𝓢-extend-𝟙-aux : ∀ {Σᵣ} {xs : List Val} → (T : Type 𝟙)
  → (⊢𝓢 : Pointwise (λ v S → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ]) xs Σᵣ)
  → Pointwise (λ v S → ⟨ Σₕ ++ [ T ] , Σₛ ⟩⊢[ v ⦂ S ]) xs Σᵣ
⊢𝓢-extend-𝟙-aux T [] = []
⊢𝓢-extend-𝟙-aux T (x∼y ∷ ⊢𝓢) = [⦂]-≼ₕₛ ([ T ] , refl) ≼-refl x∼y ∷ (⊢𝓢-extend-𝟙-aux T ⊢𝓢)

⊢𝓢-extend-𝟙 : (T : Type 𝟙) → (⊢𝓢 : Σₕ , Σₛ ⊢ₛ 𝓢) → (Σₕ ++ [ T ]) , Σₛ ⊢ₛ 𝓢
⊢𝓢-extend-𝟙 T ⊢𝓢 = ⊢𝓢-extend-𝟙-aux T ⊢𝓢



⊢𝓢-extend-𝟚-aux : ∀ {Σᵣ : List QType} {xs : List Val}
  → (S : QType) (⊢v : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ])
  → (⊢𝓢 : Pointwise (λ v S′ → ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S′ ]) xs Σᵣ)
  → Pointwise (λ v S′ → ⟨ Σₕ , Σₛ ++ [ S ] ⟩⊢[ v ⦂ S′ ] ) (xs ++ [ v ]) (Σᵣ ++ [ S ])
⊢𝓢-extend-𝟚-aux S ⊢v [] = [⦂]-≼ₕₛ ≼-refl ([ S ] , refl) ⊢v ∷ []
⊢𝓢-extend-𝟚-aux S ⊢v (x∼y ∷ pws) = [⦂]-≼ₕₛ ≼-refl ([ S ] , refl) x∼y ∷ ⊢𝓢-extend-𝟚-aux S ⊢v pws

⊢𝓢-extend-𝟚 : (S : QType)
  → (⊢v : ⟨ Σₕ , Σₛ ⟩⊢[ v ⦂ S ])
  → (⊢𝓢 : Σₕ , Σₛ ⊢ₛ 𝓢)
  → Pointwise (λ v T′ → ⟨ Σₕ , Σₛ ++ [ S ] ⟩⊢[ v ⦂ T′ ]) (𝓢 .refs ++ [ v ]) (Σₛ ++ [ S ])
⊢𝓢-extend-𝟚 S ⊢v ⊢𝓢 =  ⊢𝓢-extend-𝟚-aux S ⊢v ⊢𝓢





∣_∣ʰ = length

∣_∣ˢ : Stack → ℕ
∣_∣ˢ = length ∘ vars

_⊕_ : Env → (Var × Val × Address) → Env
𝓔 ⊕ (X s 𝟙 , v , a) = ⟨ s ≔ v , 𝓔 ⟩
𝓔 ⊕ (X s 𝟚 , v , a) = ⟨ s ⇒ a , 𝓔 ⟩

_⊕ₛ_ : Stack → (Var × Val) → Stack
𝓢 ⊕ₛ (X s 𝟙 , v) = 𝓢
𝓢 ⊕ₛ (X s 𝟚 , v) = push 𝓢 v

valloc : Stack → Val → Stack × ℕ
valloc 𝓢 v = push 𝓢 v , ∣ 𝓢 ∣ˢ

{-
alloc-length : ∀ 𝓢 → ∣ alloc 𝓢 v .proj₁ ∣ˢ ≡ suc ∣ 𝓢 ∣ˢ
alloc-length {v = v} 𝓢 = trans (length-++ (𝓢 .head) {[ v ]}) (trans (+-suc (∣ 𝓢 ∣ˢ) zero) (cong suc (+-identityʳ ∣ 𝓢 ∣ˢ)))
-}

restore-frame? : Qual → Stack → Stack → Stack
restore-frame? 𝟙 𝓢₁ 𝓢₂ = 𝓢₁
restore-frame? 𝟚 𝓢₁ 𝓢₂ = 𝓢₂

decode : Val ⊎ Address → Stack → Maybe Val
decode (inj₁ v) 𝓢 = just v
decode (inj₂ a) 𝓢 = 𝓢 ↓ᵥ a

-- H,S ⊢ c ⇓q s c ⊣ S
data _,_,_⊢_⇓[_]_⊣_,_
  : Env → Heap → Stack → Expr → Qual → Val → Heap → Stack → Set
  where

--! RuleEUnit
  EUnit  :
        𝓔 , 𝓗 , 𝓢 ⊢ unit ⇓[ q ] unit ⊣ 𝓗 , 𝓢

--! RuleEVar
  EVar :
        GenAccess 𝓔 x va
       → just v ≡ decode va 𝓢
         ------------------------------------
       → 𝓔 , 𝓗 , 𝓢 ⊢ var x ⇓[ q ] v ⊣ 𝓗 , 𝓢

--! RuleEAbs
  EAbs : ∀ {𝓢ᶜ}
       → q₁ ≤ q
       → q₂ ≤ q
       → 𝓢ᶜ ≡ new-frame? q₁ 𝓢
       → q-Bounded-Env q₁ 𝓔 𝓔′
         -------------------------------------------------------------
       → 𝓔 , 𝓗 , 𝓢 ⊢ lam q₁ x e q₂ ⇓[ q ]
                      clos q₁ 𝓔′ 𝓢ᶜ x e q₂ ⊣ 𝓗 , 𝓢
       
--! RuleEApp
  EApp : q₂ ≤ q₀
       → 𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ]
                      clos q 𝓔′ 𝓢ᶜ (X s q₁) e q₂ ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q₁ ] v₂ ⊣ 𝓗″ , 𝓢″
       → let 𝓢ₙ = new-frame? q 𝓢″
       in (𝓔′ ⊕ (X s q₁ , v₂ , ∣ 𝓢ₙ ∣ˢ)) , 𝓗″ ,
          𝓢ₙ ⊕ₛ (X s q₁ , v₂) ⊢ e ⇓[ q₀ ] v ⊣ 𝓗‴ , 𝓢‴
       → 𝓢⁗ ≡ restore-frame? q 𝓢″ 𝓢‴
        ---------------------------------------------------------
       → 𝓔 , 𝓗 , 𝓢 ⊢ app e₁ e₂ ⇓[ q₀ ] v ⊣ 𝓗‴ , 𝓢⁗
  
--! RuleERef
  ERef :  q₁ ≤ q
      → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q₁ ] v ⊣ 𝓗′ , 𝓢′
      → (case q₁ of λ where
          𝟙 → 𝓢″ ≡ 𝓢′ × n ≡ ∣ 𝓗′ ∣ʰ × 𝓗″ ≡ 𝓗′ ++ [ v ]
          𝟚 → 𝓗″ ≡ 𝓗′ × (𝓢″ , n) ≡ salloc 𝓢′ v)
        --------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ ref q₁ e ⇓[ q ] ref q₁ n ⊣ 𝓗″ , 𝓢″

--! RuleEDeref
  EDeref :
        𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ 𝟚 ] ref q₁ ℓ ⊣ 𝓗′ , 𝓢′
      → case q₁ of (λ{ 𝟙 → read 𝓗′ ℓ v ; 𝟚 → sread 𝓢′ ℓ v })
        ----------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ deref e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′

--! RuleESetref
  ESetref :
        𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ] ref q₁ ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q₁ ] v ⊣ 𝓗″ , 𝓢″
      → case q₁ of (λ{ 𝟙 → write 𝓗″ ℓ v 𝓗‴ × 𝓢‴ ≡ 𝓢″
                     ; 𝟚 → 𝓗‴ ≡ 𝓗″ × swrite 𝓢″ ℓ v 𝓢‴ })
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ setref e₁ e₂ ⇓[ q ] unit ⊣ 𝓗‴ , 𝓢‴

--! RuleESeq
  ESeq :
         𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ] v₁ ⊣ 𝓗′ , 𝓢′
      →  𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
         ---------------------------------------------------------
      →  𝓔 , 𝓗 , 𝓢 ⊢ seq e₁ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″

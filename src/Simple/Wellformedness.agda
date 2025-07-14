module Simple.Wellformedness where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; foldr)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; [] ; _∷_; ++⁺)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; fromℕ<; inject≤)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using () renaming (≤-trans to ≤ℕ-trans)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; -,_; proj₁ ; proj₂; ∃-syntax; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)

open import Qualifiers
open import Auxiliary
open import Simple.StackBasedBigStep


-- wellformed values and environments

data Heap-Env : Env → Set where

  hpe-∅ : Heap-Env ∅

  hpe-keep : Heap-Env 𝓔 → Heap-Env ⟨ s ≔ v , 𝓔 ⟩

data Wellformed-Env (𝓢 : Stack) : Env → Set

record Wellformed (𝓢 : Stack) (v : Val) : Set where
  constructor WFV
  inductive
  field
    wfv : ∀ {𝓔}{𝓢ᶜ} → clos-stack-env v ≡ just (𝓔 , 𝓢ᶜ) → (q-val v ≡ 𝟙 → 𝓢ᶜ ≡ 𝓢∅ × Heap-Env 𝓔) × 𝓢ᶜ ≼ₛ 𝓢 × Wellformed-Env 𝓢ᶜ 𝓔 × Wellformed-Env 𝓢 𝓔

data Wellformed-Env 𝓢 where

  wf-∅ : Wellformed-Env 𝓢 ∅
  wf-ext-𝟙 : q-val v ≡ 𝟙 → Wellformed 𝓢 v → Wellformed-Env 𝓢 𝓔 → Wellformed-Env 𝓢 ⟨ s ≔ v , 𝓔 ⟩
  wf-ext-𝟚 : just v ≡ (𝓢 ↓ᵥ a) → Wellformed 𝓢 v → Wellformed-Env 𝓢 𝓔 → Wellformed-Env 𝓢 ⟨ s ⇒ a , 𝓔 ⟩

record Wellformed-List (𝓢 : Stack) (vs : List Val) : Set where
  constructor WFL
  field
    wfl : ∀ {ℓ} → (ℓ< : ℓ < length vs) → Wellformed 𝓢 (lookup vs (fromℕ< ℓ<))

record Wellformed-Heap (𝓢 : Stack) (𝓗 : Heap) : Set where
  constructor WFH
  field
    wfl : Wellformed-List 𝓢 𝓗
    wfh : ∀ {ℓ} (ℓ< : ℓ < length 𝓗) → q-val (lookup 𝓗 (fromℕ< ℓ<)) ≡ 𝟙


wfe-ext-≼ₛ : 𝓢 ≼ₛ 𝓢′ → Wellformed-Env 𝓢 𝓔 → Wellformed-Env 𝓢′ 𝓔
wfv-ext-≼ₛ : 𝓢 ≼ₛ 𝓢′ → Wellformed 𝓢 v → Wellformed 𝓢′ v

wfe-ext-≼ₛ 𝓢≼ wf-∅ = wf-∅
wfe-ext-≼ₛ 𝓢≼ (wf-ext-𝟙 qv≡ wfv wfe) = wf-ext-𝟙 qv≡ (wfv-ext-≼ₛ 𝓢≼ wfv) (wfe-ext-≼ₛ 𝓢≼ wfe)
wfe-ext-≼ₛ {𝓢 = 𝓢}{𝓢′ = 𝓢′} 𝓢≼ (wf-ext-𝟚 acc≡ wfv wfe) = wf-ext-𝟚 (↓ᵥ-mono {𝓢 = 𝓢}{𝓢′ = 𝓢′} 𝓢≼ acc≡) (wfv-ext-≼ₛ 𝓢≼ wfv) (wfe-ext-≼ₛ 𝓢≼ wfe)

wfv-ext-≼ₛ {𝓢 = 𝓢}{𝓢′ = 𝓢′} 𝓢≼ (WFV  wfv) = WFV (λ {𝓔} {𝓢ᶜ} c2se≡ → let qfun , 𝓢ᶜ≼ , wfe0 , wfe = wfv c2se≡ in qfun , (≼ₛ-trans{𝓢₁ = 𝓢ᶜ}{𝓢₂ = 𝓢}{𝓢₃ = 𝓢′} 𝓢ᶜ≼ 𝓢≼) , wfe0 , (wfe-ext-≼ₛ 𝓢≼ wfe))

wfl-ext-≼ₛ : 𝓢 ≼ₛ 𝓢′ → Wellformed-List 𝓢 vs → Wellformed-List 𝓢′ vs
wfl-ext-≼ₛ {𝓢 = 𝓢} 𝓢≼ (WFL wfl) = WFL (λ ℓ< → wfv-ext-≼ₛ 𝓢≼ (wfl ℓ<))

wfh-ext-≼ₛ : 𝓢 ≼ₛ 𝓢′ → Wellformed-Heap 𝓢 𝓗 → Wellformed-Heap 𝓢′ 𝓗
wfh-ext-≼ₛ 𝓢≼ (WFH wfl wfh) = WFH (wfl-ext-≼ₛ 𝓢≼ wfl) (λ {ℓ} ℓ< → wfh {ℓ} ℓ<)

heap-env⇒𝟙-bounded-env : Heap-Env 𝓔 → q-Bounded-Env 𝟙 𝓔 𝓔
heap-env⇒𝟙-bounded-env hpe-∅ = qbe-∅
heap-env⇒𝟙-bounded-env (hpe-keep hpenv) = qbe-keep (heap-env⇒𝟙-bounded-env hpenv)

𝟙-bounded⇒heap-env : q-Bounded-Env 𝟙 𝓔 𝓔′ → Heap-Env 𝓔′
𝟙-bounded⇒heap-env qbe-∅ = hpe-∅
𝟙-bounded⇒heap-env (qbe-keep qbe) = hpe-keep (𝟙-bounded⇒heap-env qbe)
𝟙-bounded⇒heap-env (qbe-drop qbe) = 𝟙-bounded⇒heap-env qbe


𝟙-bounded-val-wfv : q-val v ≡ 𝟙 → Wellformed 𝓢 v → Wellformed 𝓢′ v
𝟙-bounded-env-wfe : q-Bounded-Env 𝟙 𝓔 𝓔′ → Wellformed-Env 𝓢 𝓔 → Wellformed-Env 𝓢′ 𝓔′

𝟙-bounded-env-wfe qbe-∅ wf-∅ = wf-∅
𝟙-bounded-env-wfe (qbe-keep qbd) (wf-ext-𝟙 qv≡ wfv wfe) = wf-ext-𝟙 qv≡ (𝟙-bounded-val-wfv qv≡ wfv) (𝟙-bounded-env-wfe qbd wfe)
𝟙-bounded-env-wfe (qbe-drop qbd) (wf-ext-𝟚 x x₁ wfe) = 𝟙-bounded-env-wfe qbd wfe

𝟙-bounded-val-wfv {unit} qv≡ (WFV wfv) = WFV λ ()
𝟙-bounded-val-wfv {cst x} qv≡ (WFV wfv) = WFV λ()
𝟙-bounded-val-wfv {clos q 𝓔 𝓢 x e x₁} {𝓢′ = 𝓢′} refl (WFV wfv)
  with wfv refl
... | qfun , 𝓢ᶜ≼ , wfe0 , wfe
  with refl , hp-env ← qfun refl = WFV (λ{ refl → qfun , ≼ₛ-bot 𝓢′ , wfe0 , (𝟙-bounded-env-wfe (heap-env⇒𝟙-bounded-env hp-env) wfe)})
𝟙-bounded-val-wfv {ref q ℓ} qv≡ (WFV wfv) = WFV λ()

wfe-push : ∀ s → Wellformed 𝓢 v → Wellformed-Env 𝓢 𝓔 → Wellformed-Env (push 𝓢 v) ⟨ s ⇒ ∣ 𝓢 ∣ˢ , 𝓔 ⟩
wfe-push {𝓢 = 𝓢} s wfv wfe = wf-ext-𝟚 (↓′-last (𝓢 .vars)) (wfv-ext-≼ₛ (≼ₛ-push {𝓢 = 𝓢}) wfv) (wfe-ext-≼ₛ (≼ₛ-push {𝓢 = 𝓢}) wfe)

wfh-wfh : Wellformed-Heap 𝓢 𝓗 → Wellformed-Heap 𝓢′ 𝓗
wfh-wfh (WFH (WFL wfl) wfh) = WFH (WFL (λ {ℓ} ℓ< → 𝟙-bounded-val-wfv (wfh ℓ<) (wfl ℓ<))) (λ {ℓ} ℓ< → wfh ℓ<)

acc-qbe :  q-Bounded-Env 𝟙 𝓔 𝓔′ → Access 𝓔 (X s 𝟙) v → Access 𝓔′ (X s 𝟙) v
acc-qbe qbe-∅ ()
acc-qbe (qbe-keep qbe) here = here
acc-qbe (qbe-keep qbe) (there acc x) = there (acc-qbe qbe acc) x
acc-qbe (qbe-drop qbe) (skip acc x) = acc-qbe qbe acc

⊨-qbe : q-Bounded-Env 𝟙 𝓔 𝓔′ → q-Bound 𝟙 Γ′ → ⟨ Σₕ , Σₛ , Γ′ ⟩⊨ 𝓔 / 𝓢∅ → ⟨ Σₕ , Σₛ , Γ′ ⟩⊨ 𝓔′ / 𝓢∅
⊨-qbe qbe qdb ⊨𝓔 = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , acc-qbe qbe acc , ⊢v)
                         λ x∈ → contradiction x∈ (𝟙-bound⇒∀𝟚∉ qdb _ _)

wf-access : Wellformed-Env 𝓢 𝓔 → Access 𝓔 (X s 𝟙) v → Wellformed 𝓢 v
wf-access (wf-ext-𝟙 qv≡ wfv wfe) here = wfv
wf-access (wf-ext-𝟙 qv≡ wfv wfe) (there acc x) = wf-access wfe acc
wf-access (wf-ext-𝟚 x x₁ wfe) (skip acc x₂) = wf-access wfe acc

wf-saccess : Wellformed-Env 𝓢 𝓔 → StackAccess 𝓔 (X s 𝟚) a → (dec≡  : just v ≡ (𝓢 ↓ᵥ a)) → Wellformed 𝓢 v
wf-saccess (wf-ext-𝟙 qv≡ x wfe) (skip sacc x₁) dec≡ = wf-saccess wfe sacc dec≡
wf-saccess (wf-ext-𝟚 x wfv wfe) here dec≡
  with trans dec≡ (sym x)
... | refl = wfv
wf-saccess (wf-ext-𝟚 x x₁ wfe) (there sacc x₂) dec≡ = wf-saccess wfe sacc dec≡

-- heap access

wf-hread : Wellformed-List 𝓢 𝓗 → read 𝓗 ℓ v → Wellformed 𝓢 v
wf-hread (WFL wfl) read0 = wfl (s≤s z≤n)
wf-hread (WFL wfl) (read1 rd) = wf-hread (WFL (λ ℓ< → wfl (s≤s ℓ<))) rd

wfh-hread : Wellformed-Heap 𝓢 𝓗 → read 𝓗 ℓ v → Wellformed 𝓢 v
wfh-hread (WFH wfl wfh) rd = wf-hread wfl rd

-- stack access

Wellformed-Stack : Stack → Set
Wellformed-Stack 𝓢 = Wellformed-List 𝓢 (𝓢 .refs)

wfs-push : Wellformed-Stack 𝓢 → Wellformed-Stack (push 𝓢 v)
wfs-push {𝓢 = 𝓢}{v = v} wfs rewrite sym (push-refs-≡ {𝓢 = 𝓢}{v = v}) = wfl-ext-≼ₛ (≼ₛ-push {𝓢 = 𝓢}) wfs

wf-sread : Wellformed-Stack 𝓢 → sread 𝓢 ℓ v → Wellformed 𝓢 v
wf-sread wfl (sread0 rd) = wf-hread wfl rd

wfs0 : Wellformed-Stack 𝓢∅
wfs0 = WFL (λ())

wfl-add : Wellformed 𝓢 v → Wellformed-List 𝓢 vs → Wellformed-List 𝓢 (vs ++ [ v ])
wfl-add {v = v}{vs = vs} wfv wfl = WFL (aux wfv wfl)
  where aux : ∀ {𝓢} →  Wellformed 𝓢 v → Wellformed-List 𝓢 vs → ∀ {ℓ} (ℓ< : ℓ < length (vs ++ [ v ])) → Wellformed 𝓢 (lookup (vs ++ [ v ]) (fromℕ< ℓ<))
        aux {𝓢 = 𝓢} wfv (WFL wfl) ℓ<
          with <-decomp vs v ℓ<
        ... | inj₁ ℓ<< rewrite lookup-from-i′ vs {[ v ]} ℓ<< refl = wfl ℓ<<
        ... | inj₂ ℓ≡  rewrite lookup-last v vs | ℓ≡ = subst (Wellformed 𝓢) (sym (lookup-last v vs)) wfv

wfh-add : q-val v ≡ 𝟙 → Wellformed 𝓢 v → Wellformed-Heap 𝓢 𝓗 → Wellformed-Heap 𝓢 (𝓗 ++ [ v ])
wfh-add {v = v}{𝓗 = 𝓗} qv≡ wfv (WFH wfl wfh) = WFH (wfl-add wfv wfl) (aux v qv≡ wfh)
  where aux : (v : Val) (qv≡ : q-val v ≡ 𝟙)
            → ( {ℓ : ℕ} (ℓ< : ℓ < length 𝓗) → q-val (lookup 𝓗 (fromℕ< ℓ<)) ≡ 𝟙)
            → ( {ℓ : ℕ} (ℓ< : ℓ < length (𝓗 ++ [ v ])) → q-val (lookup (𝓗 ++ [ v ]) (fromℕ< ℓ<)) ≡ 𝟙)
        aux v qv≡ wfh ℓ<
          with <-decomp 𝓗 v ℓ<
        ... | inj₁ ℓ<< rewrite lookup-from-i′ 𝓗 {[ v ]} ℓ<< refl = wfh ℓ<<
        ... | inj₂ ℓ≡  rewrite ℓ≡ = trans (cong q-val (lookup-last v 𝓗)) qv≡


wfl-add-𝟚 : Wellformed 𝓢 v → Wellformed-Stack 𝓢 → Wellformed-Stack (salloc 𝓢 v .proj₁)
wfl-add-𝟚 {𝓢 = 𝓢}{v = v} wfv wfs = wfl-add wfv⁺ wfs⁺
  where
    𝓢⁺ : Stack
    𝓢⁺ = salloc 𝓢 v .proj₁
    wfv⁺ : Wellformed 𝓢⁺ v
    wfv⁺ = wfv-ext-≼ₛ (≼ₛ-salloc {𝓢 = 𝓢}) wfv
    wfs⁺ : Wellformed-List 𝓢⁺ (𝓢 .refs)
    wfs⁺ = wfl-ext-≼ₛ (≼ₛ-salloc {𝓢 = 𝓢}) wfs

wfl-write : Wellformed 𝓢 v → write 𝓗 ℓ v 𝓗′ → Wellformed-List 𝓢 𝓗 → Wellformed-List 𝓢 𝓗′
wfl-write {ℓ = zero}  wfv write0 (WFL wfl) = WFL (λ{ {zero} ℓ< → wfv ; {suc ℓ} ℓ< → wfl {suc ℓ} ℓ<})
wfl-write {ℓ = suc ℓ} wfv (write1 hwrite) (WFL wfl)
  with wfl-write wfv hwrite (WFL (λ ℓ< → wfl (s≤s ℓ<)))
... | WFL wfl′ = WFL (λ{ {zero} ℓ< → wfl (s≤s z≤n) ; {suc ℓ} (s≤s ℓ<) → wfl′ ℓ< })

wfh-write : q-val v ≡ 𝟙 → Wellformed 𝓢 v → write 𝓗 ℓ v 𝓗′ → Wellformed-Heap 𝓢 𝓗 → Wellformed-Heap 𝓢 𝓗′
wfh-write {ℓ = zero} qv≡ wfv write0 (WFH (WFL wfl) wfh) = WFH (WFL (λ{ {zero} ℓ< → wfv ; {suc ℓ} ℓ< → wfl {suc ℓ} ℓ<}))
                                                              (λ{ {zero} ℓ< → qv≡ ; {suc ℓ} ℓ< → wfh {suc ℓ} ℓ< })
wfh-write {v = v}{ℓ = suc ℓ} qv≡ wfv (write1 wr) (WFH (WFL wfl) wfh)
  with wfh-write {v = v} qv≡ wfv wr (WFH (WFL λ ℓ< → wfl (s≤s ℓ<)) λ ℓ< → wfh (s≤s ℓ<))
... | WFH (WFL wfl′) wfh′ = WFH (WFL (λ{ {zero} ℓ< → wfl (s≤s z≤n) ; {suc ℓ} (s≤s ℓ<) → wfl′ ℓ< }))
                                (λ{ {zero} ℓ< → wfh (s≤s z≤n) ; {suc ℓ} (s≤s ℓ<) → wfh′ ℓ<})



module Simple.Soundness where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; foldr)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; [] ; _∷_; ++⁺)
open import Data.List.Properties using (++-identityʳ)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; fromℕ<; inject≤)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
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

open import Simple.Wellformedness


-- assumptions and results for the soundness theorem

record Assumption (Σₕ : HType) (Σₛ : SType) (𝓗 : Heap) (𝓢 : Stack) (Γ : Context) (𝓔 : Env) (S : QType) (q : Qual) : Set where
  field
    ↓⊢𝓗 : Σₕ ⊢ₕ 𝓗
    ↓⊢𝓢 : Σₕ , Σₛ ⊢ₛ 𝓢
    ↓⊨𝓔 : ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢
    ↓S≤-q : q-of S ≤ q
    ↓𝓔-wft : Wellformed-Env 𝓢 𝓔



record Result (Σₕ : HType) (Σₛ : SType) (v : Val) (S : QType) (𝓗′ : Heap) (𝓢 𝓢′ : Stack) : Set where
  field
    ↑Σₕ′ : HType
    ↑Σₛ′ : SType
    ↑Σ≼ₕ : Σₕ ≼ ↑Σₕ′
    ↑Σ≼ₛ : Σₛ ≼ ↑Σₛ′
    ↑⊢v   : ⟨ ↑Σₕ′ , ↑Σₛ′ ⟩⊢[ v ⦂ S ]
    ↑⊢𝓗  : ↑Σₕ′ ⊢ₕ 𝓗′
    ↑⊢𝓢   : ↑Σₕ′ , ↑Σₛ′ ⊢ₛ 𝓢′
    ↑𝓢≼   : 𝓢 ≼ₛ 𝓢′
    ↑cls  : Wellformed 𝓢′ v
    ↑wf-𝓗 : Wellformed-Heap 𝓢′ 𝓗′
    ↑wf-𝓢  : Wellformed-Stack 𝓢′

open Result

---- soundness theorem of evaluation

eval-soundness :
    Σₕ ⊢ₕ 𝓗
  → Σₕ , Σₛ ⊢ₛ 𝓢
  → ⟨ Σₕ , Σₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → Wellformed-Env 𝓢 𝓔
  → Wellformed-Heap 𝓢 𝓗
  → Wellformed-Stack 𝓢
  → q-of S ≤ q
  → Γ ⊢ e ⦂ S
  → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → Result Σₕ Σₛ v S 𝓗′ 𝓢 𝓢′

-- subsumption

eval-soundness {𝓢 = 𝓢} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TSub ⊢e <⦂S) ⇓
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 (≤-trans (q-of-mono <⦂S) ≤-q) ⊢e ⇓
... | ih = record
             { ↑Σₕ′ = ↑Σₕ′ ih
             ; ↑Σ≼ₕ = ↑Σ≼ₕ ih
             ; ↑Σₛ′ = ↑Σₛ′ ih
             ; ↑Σ≼ₛ = ↑Σ≼ₛ ih 
             ; ↑⊢v = <⦂-val-lift (↑⊢v ih) <⦂S
             ; ↑⊢𝓗 = ↑⊢𝓗 ih
             ; ↑⊢𝓢 = ↑⊢𝓢 ih
             ; ↑𝓢≼ = ↑𝓢≼ ih
             ; ↑cls = ↑cls ih
             ; ↑wf-𝓗 = ih .↑wf-𝓗
             ; ↑wf-𝓢 = ih .↑wf-𝓢
             }

-- lambda abstraction

eval-soundness {Σₕ = Σₕ}{Σₛ = Σₛ}{𝓢 = 𝓢} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TAbs {q = 𝟙} ⊢e qbdd {wf₁}{wf₂}) (EAbs wfc₁ wfc₂ refl qbe)
  = record
      { ↑Σₕ′ = Σₕ
      ; ↑Σ≼ₕ = ≼-refl
      ; ↑Σₛ′ = Σₛ
      ; ↑Σ≼ₛ = ≼-refl
      ; ↑⊢v = TVClos (λ 𝓢′ 𝓢≼ → ⊨-adjust-≼ₛ 𝓢≼ (⊨-qbe qbe (is-bounded qbdd) (restrict′ ⊨𝓔 qbdd))) refl (is-bounded qbdd) ⊢e wf₁ wf₂ <⦂-refl
      ; ↑⊢𝓗 = ⊢𝓗
      ; ↑⊢𝓢 = ⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-refl {𝓢}
      ; ↑cls = WFV λ{ refl → (λ{ refl → refl , 𝟙-bounded⇒heap-env qbe}) , ≼ₛ-bot 𝓢 , 𝟙-bounded-env-wfe qbe 𝓔-wft , 𝟙-bounded-env-wfe qbe 𝓔-wft }
      ; ↑wf-𝓗 = wf-𝓗
      ; ↑wf-𝓢 = wf-𝓢
      }
eval-soundness {Σₕ = Σₕ}{Σₛ = Σₛ}{𝓢 = 𝓢} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-refl (TAbs {q = 𝟚} ⊢e qbdd {wf₁}{wf₂}) (EAbs ≤-refl wfc₂ refl qbe)
  rewrite 𝟚-bounded-env qbe
  = record
      { ↑Σₕ′ = Σₕ
      ; ↑Σ≼ₕ = ≼-refl
      ; ↑Σₛ′ = Σₛ
      ; ↑Σ≼ₛ = ≼-refl
      ; ↑⊢v = TVClos (λ 𝓢′ 𝓢≼ → ⊨-adjust-≼ₛ 𝓢≼ (restrict′ ⊨𝓔 qbdd)) refl (is-bounded qbdd) ⊢e wf₁ wf₂ <⦂-refl
      ; ↑⊢𝓗 = ⊢𝓗
      ; ↑⊢𝓢 = ⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-refl {𝓢}
      ; ↑cls = WFV λ{ refl → (λ()) , ≼ₛ-refl {𝓢} , 𝓔-wft , 𝓔-wft } 
      ; ↑wf-𝓗 = wf-𝓗
      ; ↑wf-𝓢 = wf-𝓢
      }

-- application

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TApp ⊢e ⊢e₁) (EApp {𝓢 = 𝓢}{q = 𝟙} {q₁ = 𝟙}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″} q₂≤q ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft  wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = ↑Σₕ′₁ ; ↑Σₛ′ = ↑Σₛ′₁ ; ↑Σ≼ₕ = ↑Σ≼ₕ₁ ; ↑Σ≼ₛ = ↑Σ≼ₛ₁ ; ↑⊢v = TVClos {x = X s _} {S₁≤x = S₁≤x} ∀⊨𝓔 refl qbd ⊢e₂ wf₁ ≤-refl (SQual qsub (SFun {S₃ = S₃}{S₁ = S₁@ (T₁ ^ 𝟙)}{S₂ = S₂@ (T₂ ^ 𝟙)}{S₄ = S₄} S₁<⦂S₂ S₃<⦂S₄)) ; ↑⊢𝓗 = ↑⊢𝓗₁ ; ↑⊢𝓢 = ↑⊢𝓢₁ ; ↑𝓢≼ = ↑𝓢≼₁ ; ↑cls = ↑cls₁ ; ↑wf-𝓗 = ↑wf-𝓗₁ ; ↑wf-𝓢 = ↑wf-𝓢₁ }
  with eval-soundness (↑⊢𝓗 ih) (↑⊢𝓢 ih)
                      (⊨-extend (↑Σ≼ₕ ih) (↑Σ≼ₛ ih) (↑𝓢≼ ih) ⊨𝓔)
                      (wfe-ext-≼ₛ (↑𝓢≼ ih) 𝓔-wft)
                      (↑wf-𝓗 ih)
                      (↑wf-𝓢 ih)
                      (≤-trans (q-of-mono S₁<⦂S₂) wf₁)
                      ⊢e₁ ⇓₁
... | ih₁@record { ↑Σₕ′ = Σₕ″ ; ↑Σₛ′ = Σₛ″ ; ↑Σ≼ₕ = Σ≼ₕ″ ; ↑Σ≼ₛ = Σ≼ₛ″ ; ↑⊢v = ⊢varg ; ↑⊢𝓗 = ⊢𝓗″ ; ↑⊢𝓢 = ⊢𝓢″ ; ↑𝓢≼ = 𝓢≼″ }
  using ⊨𝓔″ ← ∀⊨𝓔 (mkS [] []) (≼ₛ-refl {mkS [] []})
  using ⊨𝓔″+arg ← ⊨-extend-𝟙 {S₁≤x = S₁≤x} s T₁ (<⦂-val-lift ⊢varg S₁<⦂S₂) (⊨-extend-Σ Σ≼ₕ″ Σ≼ₛ″ ⊨𝓔″)
  using WFV wfv ← ↑cls ih
  using qfun , 𝓢ᶜ≼ , wfe0 , wfe ← wfv refl
  with eval-soundness ⊢𝓗″ []
                      (⊨-adjust-𝟙 (qb-add ≤-refl qbd) ⊨𝓔″+arg)
                      (let qvarg≡𝟙 = (𝟙-value ⊢varg S₁<⦂S₂) in wf-ext-𝟙 qvarg≡𝟙 (𝟙-bounded-val-wfv qvarg≡𝟙 (↑cls ih₁)) wfe0)
                      (wfh-wfh (↑wf-𝓗 ih₁))
                      wfs0
                      q₂≤q
                      ⊢e₂ ⇓₂
... | ih₂
  = record
      { ↑Σₕ′ = ↑Σₕ′ ih₂
      ; ↑Σₛ′ = Σₛ″
      ; ↑Σ≼ₕ = ≼-trans (↑Σ≼ₕ ih) (≼-trans Σ≼ₕ″ (↑Σ≼ₕ ih₂))
      ; ↑Σ≼ₛ = ≼-trans (↑Σ≼ₛ ih) Σ≼ₛ″
      ; ↑⊢v = <⦂-val-lift (⊢ᵥ-adjust-𝟙 (↑⊢v ih₂)) S₃<⦂S₄
      ; ↑⊢𝓗 = ↑⊢𝓗 ih₂
      ; ↑⊢𝓢 = ⊢ₛ-adjust-≼ₕ{𝓢 = 𝓢″} (↑Σ≼ₕ ih₂) ⊢𝓢″
      ; ↑𝓢≼ = ≼ₛ-trans{𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢″} (↑𝓢≼ ih) (↑𝓢≼ ih₁)
      ; ↑cls = 𝟙-bounded-val-wfv (𝟙-value (↑⊢v ih₂) <⦂-refl) (↑cls ih₂)
      ; ↑wf-𝓗 = wfh-wfh (↑wf-𝓗 ih₂)
      ; ↑wf-𝓢 = ih₁ .↑wf-𝓢
      }

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TApp ⊢e ⊢e₁) (EApp {𝓢 = 𝓢}{q = 𝟚} {q₁ = 𝟙}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″}{𝓢‴ = 𝓢‴} q₂≤q ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft  wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = ↑Σₕ′₁ ; ↑Σₛ′ = ↑Σₛ′₁ ; ↑Σ≼ₕ = ↑Σ≼ₕ₁ ; ↑Σ≼ₛ = ↑Σ≼ₛ₁ ; ↑⊢v = TVClos {𝓢 = 𝓢ᶜ} {x = X s _} {S₁≤x = refl} ∀⊨𝓔 𝓢≡ qbd ⊢e₂ wf₁ wf₂ (SQual qsub (SFun {S₃ = S₃}{S₁ = S₁@ (T₁ ^ 𝟙)}{S₂ = S₂}{S₄ = S₄} S₁<⦂S₂ S₃<⦂S₄)) ; ↑⊢𝓗 = ↑⊢𝓗₁ ; ↑⊢𝓢 = ↑⊢𝓢₁ ; ↑𝓢≼ = ↑𝓢≼₁ ; ↑cls = ↑cls₁ ; ↑wf-𝓗 = ↑wf-𝓗₁ ; ↑wf-𝓢 = ↑wf-𝓢₁ }
  with eval-soundness (↑⊢𝓗 ih) (↑⊢𝓢 ih)
                      (⊨-extend (↑Σ≼ₕ ih) (↑Σ≼ₛ ih) (↑𝓢≼ ih) ⊨𝓔)
                      (wfe-ext-≼ₛ (↑𝓢≼ ih) 𝓔-wft)
                      (↑wf-𝓗 ih)
                      (↑wf-𝓢 ih)
                      (q-of-mono S₁<⦂S₂)
                      ⊢e₁ ⇓₁
... | ih₁@record { ↑Σₕ′ = Σₕ″ ; ↑Σₛ′ = Σₛ″ ; ↑Σ≼ₕ = Σ≼ₕ″ ; ↑Σ≼ₛ = Σ≼ₛ″ ; ↑⊢v = ⊢varg ; ↑⊢𝓗 = ⊢𝓗″ ; ↑⊢𝓢 = ⊢𝓢″ ; ↑𝓢≼ = 𝓢≼″ }
  using WFV wfv ← ↑cls ih
  using qfun , 𝓢ᶜ≼ , wfe0 , wfe ← wfv refl
  using ⊨𝓔″ ← ∀⊨𝓔 𝓢″ (≼ₛ-trans{𝓢₁ = 𝓢ᶜ}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢″} 𝓢ᶜ≼ (𝓢≼″))
  using ⊨𝓔″+arg ← ⊨-extend {𝓢 = 𝓢″}{𝓢′ = 𝓢″} Σ≼ₕ″ Σ≼ₛ″ (≼ₛ-refl {𝓢″}) ⊨𝓔″
  with eval-soundness ⊢𝓗″ ⊢𝓢″
                      (⊨-extend-𝟙 s T₁ (<⦂-val-lift ⊢varg S₁<⦂S₂) ⊨𝓔″+arg)
                      (wf-ext-𝟙 (𝟙-value ⊢varg S₁<⦂S₂) (↑cls ih₁) (wfe-ext-≼ₛ 𝓢≼″ wfe))
                      (↑wf-𝓗 ih₁)
                      (↑wf-𝓢 ih₁)
                      q₂≤q
                      ⊢e₂ ⇓₂
... | ih₂
  = record
      { ↑Σₕ′ = ih₂ .↑Σₕ′
      ; ↑Σₛ′ = ih₂ .↑Σₛ′
      ; ↑Σ≼ₕ = ≼-trans (↑Σ≼ₕ ih) (≼-trans Σ≼ₕ″ (↑Σ≼ₕ ih₂))
      ; ↑Σ≼ₛ = ≼-trans (↑Σ≼ₛ ih) (≼-trans (↑Σ≼ₛ ih₁) (↑Σ≼ₛ ih₂))
      ; ↑⊢v = <⦂-val-lift (ih₂ .↑⊢v) S₃<⦂S₄
      ; ↑⊢𝓗 = ih₂ .↑⊢𝓗
      ; ↑⊢𝓢 = ih₂ .↑⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-trans {𝓢₁ = 𝓢} {𝓢₂ = 𝓢′}{𝓢₃ = 𝓢‴} (ih .↑𝓢≼) (≼ₛ-trans {𝓢₁ = 𝓢′} {𝓢₂ = 𝓢″}{𝓢₃ = 𝓢‴} (ih₁ .↑𝓢≼) (ih₂ .↑𝓢≼))
      ; ↑cls = ih₂ .↑cls
      ; ↑wf-𝓗 = ih₂ .↑wf-𝓗
      ; ↑wf-𝓢 = ih₂ .↑wf-𝓢
      }

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TApp ⊢e ⊢e₁) (EApp {𝓢 = 𝓢}{q = 𝟚} {q₁ = 𝟚}{𝓢′ = 𝓢′}{v₂ = v₂}{𝓢″ = 𝓢″}{𝓢‴ = 𝓢‴} q₂≤q ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft  wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = ↑Σₕ′₁ ; ↑Σₛ′ = ↑Σₛ′₁ ; ↑Σ≼ₕ = ↑Σ≼ₕ₁ ; ↑Σ≼ₛ = ↑Σ≼ₛ₁ ; ↑⊢v = TVClos {𝓢 = 𝓢ᶜ} {x = X s _} {S₁≤x = S₁≤x} ∀⊨𝓔 𝓢≡ qbd ⊢e₂ wf₁ wf₂ (SQual qsub (SFun {S₃ = S₃}{S₁ = S₁}{S₂ = S₂}{S₄ = S₄} S₁<⦂S₂ S₃<⦂S₄)) ; ↑⊢𝓗 = ↑⊢𝓗₁ ; ↑⊢𝓢 = ↑⊢𝓢₁ ; ↑𝓢≼ = ↑𝓢≼₁ ; ↑cls = ↑cls₁ ; ↑wf-𝓗 = ↑wf-𝓗₁ ; ↑wf-𝓢 = ↑wf-𝓢₁ }
  with eval-soundness (↑⊢𝓗 ih) (↑⊢𝓢 ih)
                      (⊨-extend (↑Σ≼ₕ ih) (↑Σ≼ₛ ih) (↑𝓢≼ ih) ⊨𝓔)
                      (wfe-ext-≼ₛ (↑𝓢≼ ih) 𝓔-wft)
                      (↑wf-𝓗 ih)
                      (↑wf-𝓢 ih)
                      ≤-top
                      ⊢e₁ ⇓₁
... | ih₁@record { ↑Σₕ′ = Σₕ″ ; ↑Σₛ′ = Σₛ″ ; ↑Σ≼ₕ = Σ≼ₕ″ ; ↑Σ≼ₛ = Σ≼ₛ″ ; ↑⊢v = ⊢varg ; ↑⊢𝓗 = ⊢𝓗″ ; ↑⊢𝓢 = ⊢𝓢″ ; ↑𝓢≼ = 𝓢≼″ }
  using WFV wfv ← ↑cls ih
  using qfun , 𝓢ᶜ≼𝓢′ , wfe0 , wfe ← wfv refl
  using ⊨𝓔″ ← ∀⊨𝓔 𝓢″ (≼ₛ-trans{𝓢₁ = 𝓢ᶜ}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢″} 𝓢ᶜ≼𝓢′ (𝓢≼″))
  using ⊨𝓔″+arg ← ⊨-extend {𝓢 = 𝓢″}{𝓢′ = 𝓢″} Σ≼ₕ″ Σ≼ₛ″ (≼ₛ-refl {𝓢″}) ⊨𝓔″
  with eval-soundness ⊢𝓗″
                      (⊢ₛ-adjust-push {𝓢 = 𝓢″} {vs = [ v₂ ]}⊢𝓢″)
                      (⊨-adjust-push-update s (<⦂-val-lift ⊢varg S₁<⦂S₂) ⊨𝓔″+arg ) -- (⊨-extend-𝟙 s T₁ (<⦂-val-lift ⊢varg S₁<⦂S₂) ⊨𝓔″+arg)
                      (wfe-push s (ih₁ .↑cls) (wfe-ext-≼ₛ 𝓢≼″ wfe)) -- (wf-ext-𝟙 (𝟙-value ⊢varg S₁<⦂S₂) (↑cls ih₁) (wfe-ext-≼ₛ 𝓢≼″ wfe))
                      (wfh-wfh (↑wf-𝓗 ih₁))
                      (wfs-push (↑wf-𝓢 ih₁))
                      q₂≤q
                      ⊢e₂
                      ⇓₂
... | ih₂
  = record
      { ↑Σₕ′ = ih₂ .↑Σₕ′
      ; ↑Σₛ′ = ih₂ .↑Σₛ′
      ; ↑Σ≼ₕ = ≼-trans (ih .↑Σ≼ₕ) (≼-trans (ih₁ .↑Σ≼ₕ) (ih₂ .↑Σ≼ₕ))
      ; ↑Σ≼ₛ = ≼-trans (ih .↑Σ≼ₛ) (≼-trans (ih₁ .↑Σ≼ₛ) (ih₂ .↑Σ≼ₛ))
      ; ↑⊢v = <⦂-val-lift (ih₂ .↑⊢v) S₃<⦂S₄
      ; ↑⊢𝓗 = ih₂ .↑⊢𝓗
      ; ↑⊢𝓢 = ih₂ .↑⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-trans {𝓢₁ = 𝓢} {𝓢₂ = 𝓢′} {𝓢₃ = 𝓢‴} (ih .↑𝓢≼) (≼ₛ-trans {𝓢₁ = 𝓢′} {𝓢₂ = 𝓢″} {𝓢₃ = 𝓢‴} (ih₁ .↑𝓢≼) (≼ₛ-trans{𝓢₁ = 𝓢″}{𝓢₂ = push 𝓢″ v₂}{𝓢₃ = 𝓢‴} (≼ₛ-push {𝓢 = 𝓢″}) (ih₂ .↑𝓢≼)))
      ; ↑cls = ih₂ .↑cls
      ; ↑wf-𝓗 = ih₂ .↑wf-𝓗
      ; ↑wf-𝓢 = ih₂ .↑wf-𝓢
      }

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TApp ⊢e ⊢e₁) (EApp {𝓢 = 𝓢}{q = 𝟙} {q₁ = 𝟚}{𝓢′ = 𝓢′}{v₂ = v₂}{𝓢″ = 𝓢″}{𝓢‴ = 𝓢‴} q₂≤q ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft  wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = ↑Σₕ′₁ ; ↑Σₛ′ = ↑Σₛ′₁ ; ↑Σ≼ₕ = ↑Σ≼ₕ₁ ; ↑Σ≼ₛ = ↑Σ≼ₛ₁ ; ↑⊢v = TVClos {𝓢 = 𝓢ᶜ} {x = X s _} {S₁≤x = S₁≤x} ∀⊨𝓔 refl qbd ⊢e₂ ≤-refl ≤-refl (SQual qsub (SFun {S₃ = S₃}{S₁ = S₁}{S₂ = S₂}{S₄ = S₄} S₁<⦂S₂ S₃<⦂S₄)) ; ↑⊢𝓗 = ↑⊢𝓗₁ ; ↑⊢𝓢 = ↑⊢𝓢₁ ; ↑𝓢≼ = ↑𝓢≼₁ ; ↑cls = ↑cls₁ ; ↑wf-𝓗 = ↑wf-𝓗₁ ; ↑wf-𝓢 = ↑wf-𝓢₁ }
  with eval-soundness (↑⊢𝓗 ih) (↑⊢𝓢 ih)
                      (⊨-extend (↑Σ≼ₕ ih) (↑Σ≼ₛ ih) (↑𝓢≼ ih) ⊨𝓔)
                      (wfe-ext-≼ₛ (↑𝓢≼ ih) 𝓔-wft)
                      (↑wf-𝓗 ih)
                      (↑wf-𝓢 ih)
                      ≤-top
                      ⊢e₁ ⇓₁
... | ih₁@record { ↑Σₕ′ = Σₕ″ ; ↑Σₛ′ = Σₛ″ ; ↑Σ≼ₕ = Σ≼ₕ″ ; ↑Σ≼ₛ = Σ≼ₛ″ ; ↑⊢v = ⊢varg ; ↑⊢𝓗 = ⊢𝓗″ ; ↑⊢𝓢 = ⊢𝓢″ ; ↑𝓢≼ = 𝓢≼″ }
  using WFV wfv ← ↑cls ih
  using qfun , 𝓢ᶜ≼ , wfe0 , wfe ← wfv refl
  with refl , hpe-𝓔′ ← qfun refl
  using ⊨𝓔″ ← ∀⊨𝓔 𝓢∅ (≼ₛ-refl {𝓢∅})
  using ⊨𝓔‴ ← ⊨-extend-Σ Σ≼ₕ″ Σ≼ₛ″ ⊨𝓔″
--   using ⊨𝓔″+arg ← 𝟙-env-no-stack (⊨-extend {𝓢 = 𝓢∅}{𝓢′ = 𝓢∅} Σ≼ₕ″ {!!} (≼ₛ-refl {𝓢∅}) ⊨𝓔″) qbd
  with eval-soundness {Σₛ = []}
                      ⊢𝓗″
                      []
                      (⊨-adjust-push-update s (𝟙-value-no-stack (<⦂-val-lift ⊢varg S₁<⦂S₂) refl) (𝟙-env-no-stack ⊨𝓔‴ qbd))
                      (wfe-push{𝓢 = 𝓢∅} s (𝟙-bounded-val-wfv (𝟙-value ⊢varg S₁<⦂S₂) (ih₁ .↑cls)) (𝟙-bounded-env-wfe (heap-env⇒𝟙-bounded-env hpe-𝓔′) wfe))
                      (wfh-wfh (↑wf-𝓗 ih₁))
                      (WFL (λ{ ()}))
                      ≤-bot
                      ⊢e₂
                      ⇓₂
... | ih₂
  = record
      { ↑Σₕ′ = ih₂ .↑Σₕ′
      ; ↑Σₛ′ = ih₁ .↑Σₛ′
      ; ↑Σ≼ₕ = ≼-trans (ih .↑Σ≼ₕ) (≼-trans (ih₁ .↑Σ≼ₕ) (ih₂ .↑Σ≼ₕ))
      ; ↑Σ≼ₛ = ≼-trans (ih .↑Σ≼ₛ) (ih₁ .↑Σ≼ₛ)
      ; ↑⊢v =  <⦂-val-lift (⊢ᵥ-adjust-𝟙 (ih₂ .↑⊢v)) S₃<⦂S₄
      ; ↑⊢𝓗 = ih₂ .↑⊢𝓗
      ; ↑⊢𝓢 = ⊢ₛ-adjust-≼ₕ{𝓢 = 𝓢″} (ih₂ .↑Σ≼ₕ) (ih₁ .↑⊢𝓢)
      ; ↑𝓢≼ = ≼ₛ-trans {𝓢₁ = 𝓢} {𝓢₂ = 𝓢′} {𝓢₃ = 𝓢″} (ih .↑𝓢≼) (ih₁ .↑𝓢≼)
      ; ↑cls = 𝟙-bounded-val-wfv (𝟙-value (ih₂ .↑⊢v) <⦂-refl) (ih₂ .↑cls)
      ; ↑wf-𝓗 = wfh-wfh (ih₂ .↑wf-𝓗)
      ; ↑wf-𝓢 = ih₁ .↑wf-𝓢
      }


-- unit / constants

eval-soundness {Σₕ} {Σₛ = Σₛ} {𝓢 = 𝓢} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q TUnit EUnit
  = record
      { ↑Σₕ′ = Σₕ
      ; ↑Σₛ′ = Σₛ
      ; ↑Σ≼ₕ = ≼-refl
      ; ↑Σ≼ₛ = ≼-refl
      ; ↑⊢v = TVUnit
      ; ↑⊢𝓗 = ⊢𝓗
      ; ↑⊢𝓢 = ⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-refl {𝓢}
      ; ↑cls = WFV (λ ())
      ; ↑wf-𝓗 = wf-𝓗
      ; ↑wf-𝓢 = wf-𝓢
      }

-- variables


eval-soundness {Σₕ = Σₕ}{Σₛ = Σₛ} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-bottop (TVar x) (EVar {𝓢 = 𝓢} (on-heap acc) refl)
  = let ⊢v = access-soundness ⊨𝓔 x acc in
    record
      { ↑Σₕ′ = Σₕ
      ; ↑Σₛ′ = Σₛ
      ; ↑Σ≼ₕ = ≼-refl
      ; ↑Σ≼ₛ = ≼-refl
      ; ↑⊢v = ⊢v
      ; ↑⊢𝓗 = ⊢𝓗
      ; ↑⊢𝓢 = ⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-refl {𝓢}
      ; ↑cls = wf-access 𝓔-wft acc
      ; ↑wf-𝓗 = wf-𝓗
      ; ↑wf-𝓢 = wf-𝓢
      }
eval-soundness {Σₕ = Σₕ}{Σₛ = Σₛ} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-refl (TVar x∈) (EVar {𝓢 = 𝓢} (on-heap acc) refl)
  = let ⊢v = genaccess-soundness ⊨𝓔 x∈ (on-heap acc) in
    record
      { ↑Σₕ′ = Σₕ
      ; ↑Σₛ′ = Σₛ
      ; ↑Σ≼ₕ = ≼-refl
      ; ↑Σ≼ₛ = ≼-refl
      ; ↑⊢v = ⊢v
      ; ↑⊢𝓗 = ⊢𝓗
      ; ↑⊢𝓢 = ⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-refl {𝓢}
      ; ↑cls = wf-access 𝓔-wft acc
      ; ↑wf-𝓗 = wf-𝓗
      ; ↑wf-𝓢 = wf-𝓢
      }
eval-soundness {Σₕ = Σₕ}{Σₛ = Σₛ} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TVar x∈) (EVar {𝓢 = 𝓢} (on-stack sacc) dec≡)
  = let ⊢v = genaccess-soundness-𝟚 ⊨𝓔 x∈ (on-stack sacc) _ dec≡ in
    record
      { ↑Σₕ′ = Σₕ
      ; ↑Σₛ′ = Σₛ
      ; ↑Σ≼ₕ = ≼-refl
      ; ↑Σ≼ₛ = ≼-refl
      ; ↑⊢v = ⊢v
      ; ↑⊢𝓗 = ⊢𝓗
      ; ↑⊢𝓢 = ⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-refl {𝓢}
      ; ↑cls = wf-saccess 𝓔-wft sacc dec≡
      ; ↑wf-𝓗 = wf-𝓗
      ; ↑wf-𝓢 = wf-𝓢
      }

-- sequence

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TSeq ⊢e ⊢e₁) (ESeq {𝓢 = 𝓢}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″} ⇓ ⇓₁)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-refl ⊢e ⇓
... | ih
  with eval-soundness (↑⊢𝓗 ih) (↑⊢𝓢 ih) (⊨-extend (↑Σ≼ₕ ih) (↑Σ≼ₛ ih) (↑𝓢≼ ih) ⊨𝓔) (wfe-ext-≼ₛ (↑𝓢≼ ih) 𝓔-wft) (↑wf-𝓗 ih) (↑wf-𝓢 ih) ≤-q ⊢e₁ ⇓₁
... | ih₁
  = record
      { ↑Σₕ′ = ↑Σₕ′ ih₁
      ; ↑Σₛ′ = ↑Σₛ′ ih₁
      ; ↑Σ≼ₕ = ≼-trans (↑Σ≼ₕ ih) (↑Σ≼ₕ ih₁) 
      ; ↑Σ≼ₛ = ≼-trans (↑Σ≼ₛ ih) (↑Σ≼ₛ ih₁)
      ; ↑⊢v = ↑⊢v ih₁
      ; ↑⊢𝓗 = ih₁ .↑⊢𝓗
      ; ↑⊢𝓢 = ih₁ .↑⊢𝓢
      ; ↑𝓢≼ = ≼ₛ-trans {𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢″} (ih .↑𝓢≼) (ih₁ .↑𝓢≼)
      ; ↑cls = ih₁ .↑cls
      ; ↑wf-𝓗 = ↑wf-𝓗 ih₁
      ; ↑wf-𝓢 = ↑wf-𝓢 ih₁
      }

-- reference

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TRef {S = S} {wf = ≤-refl} ⊢e) (ERef {q = 𝟙}{𝓢 = 𝓢}{𝓢′ = 𝓢′} ≤-refl ⇓ (refl , refl , refl))
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-refl ⊢e ⇓
... | ih
  rewrite sym (⊢ₕ-length (ih .↑⊢𝓗))
  = let T = t-of S in
    record
      { ↑Σₕ′ = ih .↑Σₕ′ ++ [ T ]
      ; ↑Σₛ′ = ih .↑Σₛ′
      ; ↑Σ≼ₕ = ≼-trans (ih .↑Σ≼ₕ) ([ T ] , refl)
      ; ↑Σ≼ₛ = ih .↑Σ≼ₛ
      ; ↑⊢v = TVRef (length-< T (ih .↑Σₕ′) []) (lookup-last T (ih .↑Σₕ′)) <⦂-refl
      ; ↑⊢𝓗 = ⊢𝓗-extend-𝟙 T (⊢v-stack-𝟙 (↑⊢v ih)) (↑⊢𝓗 ih)
      ; ↑⊢𝓢 = ⊢𝓢-extend-𝟙 {𝓢 = 𝓢′} T (ih .↑⊢𝓢)
      ; ↑𝓢≼ = ih .↑𝓢≼
      ; ↑cls = WFV (λ ())
      ; ↑wf-𝓗 = wfh-add (𝟙-value (ih .↑⊢v) <⦂-refl) (↑cls ih) (↑wf-𝓗 ih)
      ; ↑wf-𝓢 = ↑wf-𝓢 ih
      }

eval-soundness {q = 𝟚} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TRef {S = S} {wf = ≤-bottop} ⊢e) (ERef {q₁ = q₁} {q = q} {𝓢 = 𝓢} {𝓢′ = 𝓢′} x ⇓ (refl , refl))
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-bottop ⊢e ⇓
... | ih
  rewrite sym (⊢ₛ-length {𝓢 = 𝓢′} (ih .↑⊢𝓢))
 = record
     { ↑Σₕ′ = ih .↑Σₕ′
     ; ↑Σₛ′ = ih .↑Σₛ′ ++ [ S ]
     ; ↑Σ≼ₕ = ih .↑Σ≼ₕ
     ; ↑Σ≼ₛ = ≼-trans (ih .↑Σ≼ₛ) ([ S ] , refl)
     ; ↑⊢v = TVRef (length-< S (ih .↑Σₛ′) []) (lookup-last S (ih .↑Σₛ′)) <⦂-refl
     ; ↑⊢𝓗 = ih .↑⊢𝓗
     ; ↑⊢𝓢 = ⊢𝓢-extend-𝟚 {𝓢 = 𝓢′} S (ih .↑⊢v) (ih .↑⊢𝓢)
     ; ↑𝓢≼ = ≼ₛ-trans {𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = salloc 𝓢′ _ .proj₁} (ih .↑𝓢≼) (≼ₛ-salloc{𝓢 = 𝓢′})
     ; ↑cls = WFV (λ ())
     ; ↑wf-𝓗 = wfh-ext-≼ₛ (≼ₛ-salloc{𝓢 = 𝓢′}) (↑wf-𝓗 ih)
     ; ↑wf-𝓢 = wfl-add-𝟚 (↑cls ih) (↑wf-𝓢 ih)
     }

eval-soundness {q = 𝟚} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TRef {S = S@ (mkQ 𝟙 T)} {wf = ≤-refl} ⊢e) (ERef {q₁ = q₁} {q = q} {𝓢 = 𝓢} {𝓢′ = 𝓢′} x ⇓ (refl , refl , refl))
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-refl ⊢e ⇓
... | ih
  rewrite sym (⊢ₕ-length (ih .↑⊢𝓗))
  = record
      { ↑Σₕ′ = ih .↑Σₕ′ ++ [ T ]
      ; ↑Σₛ′ = ih .↑Σₛ′
      ; ↑Σ≼ₕ = ≼-trans (ih .↑Σ≼ₕ) ([ T ] , refl)
      ; ↑Σ≼ₛ = ih .↑Σ≼ₛ
      ; ↑⊢v = TVRef (length-< T (ih .↑Σₕ′) []) (lookup-last T (ih .↑Σₕ′)) <⦂-refl
      ; ↑⊢𝓗 = ⊢𝓗-extend-𝟙 T (⊢v-stack-𝟙 (↑⊢v ih)) (↑⊢𝓗 ih)
      ; ↑⊢𝓢 = ⊢𝓢-extend-𝟙 {𝓢 = 𝓢′} T (ih .↑⊢𝓢)
      ; ↑𝓢≼ = ih .↑𝓢≼
      ; ↑cls = WFV (λ ())
      ; ↑wf-𝓗 = wfh-add (𝟙-value (ih .↑⊢v) <⦂-refl) (↑cls ih) (↑wf-𝓗 ih)
      ; ↑wf-𝓢 = ↑wf-𝓢 ih
      }

eval-soundness {q = 𝟚} ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TRef {S = S@ (mkQ 𝟚 T)} {wf = ≤-refl} ⊢e) (ERef {q₁ = q₁} {q = q} {𝓢 = 𝓢} {𝓢′ = 𝓢′} x ⇓ (refl , refl))
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-refl ⊢e ⇓
... | ih
  rewrite sym (⊢ₛ-length {𝓢 = 𝓢′} (ih .↑⊢𝓢))
  = record
      { ↑Σₕ′ = ih .↑Σₕ′
      ; ↑Σₛ′ = ih .↑Σₛ′ ++ [ S ]
      ; ↑Σ≼ₕ = ih .↑Σ≼ₕ
      ; ↑Σ≼ₛ = ≼-trans (ih .↑Σ≼ₛ) ([ S ] , refl)
      ; ↑⊢v = TVRef (length-< S (ih .↑Σₛ′) []) (lookup-last S (ih .↑Σₛ′)) <⦂-refl
      ; ↑⊢𝓗 = ih .↑⊢𝓗
      ; ↑⊢𝓢 = ⊢𝓢-extend-𝟚 {𝓢 = 𝓢′} S (ih .↑⊢v) (ih .↑⊢𝓢)
      ; ↑𝓢≼ = ≼ₛ-trans {𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = salloc 𝓢′ _ .proj₁} (ih .↑𝓢≼) (≼ₛ-salloc{𝓢 = 𝓢′})
      ; ↑cls = WFV (λ ())
      ; ↑wf-𝓗 = wfh-ext-≼ₛ (≼ₛ-salloc{𝓢 = 𝓢′}) (↑wf-𝓗 ih)
      ; ↑wf-𝓢 = wfl-add-𝟚 (↑cls ih) (↑wf-𝓢 ih)
      }

-- dereference

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TDeref {wf = wf} ⊢e) (EDeref {q₁ = 𝟙} ⇓ hread)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = _ ; ↑Σₛ′ = _ ; ↑Σ≼ₕ = _ ; ↑Σ≼ₛ = _ ; ↑⊢v = (TVRef ℓ< lkup≡ (SQual ≤-cls (SRef S<⦂ <⦂S))) ; ↑⊢𝓗 = ⊢𝓗′ ; ↑⊢𝓢 = ⊢𝓢′ ; ↑𝓢≼ = _ ; ↑cls = _ }
  with refl ← <⦂-antisym S<⦂ <⦂S
  = record
      { ↑Σₕ′ = ih .↑Σₕ′
      ; ↑Σₛ′ = ih .↑Σₛ′
      ; ↑Σ≼ₕ = ih .↑Σ≼ₕ
      ; ↑Σ≼ₛ = ih .↑Σ≼ₛ
      ; ↑⊢v = ⊢v-stack-𝟙 (typed-read ⊢𝓗′ ℓ< lkup≡ hread)
      ; ↑⊢𝓗 = ⊢𝓗′
      ; ↑⊢𝓢 = ⊢𝓢′
      ; ↑𝓢≼ = ih .↑𝓢≼
      ; ↑cls = wfh-hread (↑wf-𝓗 ih) hread
      ; ↑wf-𝓗 = ih .↑wf-𝓗
      ; ↑wf-𝓢 = ih .↑wf-𝓢
      }
eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TDeref {wf = wf} ⊢e) (EDeref {q₁ = 𝟚} ⇓ xread)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = Σₕ′ ; ↑Σₛ′ = Σₛ′ ; ↑Σ≼ₕ = Σ≼ₕ ; ↑Σ≼ₛ = Σ≼ₛ ; ↑⊢v = TVRef ℓ< lkup≡ (SQual qsub (SRef S<⦂ <⦂S)) ; ↑⊢𝓗 = ⊢𝓗′ ; ↑⊢𝓢 = ⊢𝓢′ ; ↑𝓢≼ = 𝓢≼ ; ↑cls = cls ; ↑wf-𝓗 = wf-𝓗′ ; ↑wf-𝓢 = wf-𝓢′ }
  with refl ← <⦂-antisym S<⦂ <⦂S
  = record
      { ↑Σₕ′ = Σₕ′
      ; ↑Σₛ′ = Σₛ′
      ; ↑Σ≼ₕ = Σ≼ₕ
      ; ↑Σ≼ₛ = Σ≼ₛ
      ; ↑⊢v = typed-sread ⊢𝓢′ ℓ< lkup≡ xread
      ; ↑⊢𝓗 = ⊢𝓗′
      ; ↑⊢𝓢 = ⊢𝓢′
      ; ↑𝓢≼ = 𝓢≼
      ; ↑cls = wf-sread wf-𝓢′ xread
      ; ↑wf-𝓗 = wf-𝓗′
      ; ↑wf-𝓢 = wf-𝓢′
      }


-- setref

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TSetref ⊢e ⊢e₁) (ESetref {𝓢 = 𝓢}{q₁ = 𝟙}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″} ⇓ ⇓₁ (hwrite , refl))
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = _ ; ↑Σₛ′ = _ ; ↑Σ≼ₕ = _ ; ↑Σ≼ₛ = _ ; ↑⊢v = (TVRef ℓ< lkup≡ (SQual qsub (SRef <⦂S S<⦂))) ; ↑⊢𝓗 = _ ; ↑⊢𝓢 = _ ; ↑𝓢≼ = _ ; ↑cls = _ ; ↑wf-𝓗 = _ ; ↑wf-𝓢 = _ }
  with eval-soundness (ih .↑⊢𝓗) (ih .↑⊢𝓢) (⊨-extend (↑Σ≼ₕ ih) (↑Σ≼ₛ ih) (↑𝓢≼ ih) ⊨𝓔) (wfe-ext-≼ₛ (↑𝓢≼ ih) 𝓔-wft) (↑wf-𝓗 ih) (↑wf-𝓢 ih) (q-of-mono S<⦂) ⊢e₁ ⇓₁
... | ih₁
  with refl ← <⦂-antisym  S<⦂ <⦂S
  = record
              { ↑Σₕ′ = ih₁ .↑Σₕ′
              ; ↑Σₛ′ = ih₁ .↑Σₛ′
              ; ↑Σ≼ₕ = ≼-trans (ih .↑Σ≼ₕ) (ih₁ .↑Σ≼ₕ)
              ; ↑Σ≼ₛ = ≼-trans (ih .↑Σ≼ₛ) (ih₁ .↑Σ≼ₛ)
              ; ↑⊢v = TVUnit
              ; ↑⊢𝓗 = typed-write (ih₁ .↑⊢𝓗)
                                   (≤ℕ-trans ℓ< (≼⇒length (ih₁ .↑Σ≼ₕ)))
                                   (trans (trans (cong (lookup (ih₁ .↑Σₕ′)) (fromℕ-inject≤ (≼⇒length (ih₁ .↑Σ≼ₕ)) ℓ<)) (sym (≼-lookup (ih₁ .↑Σ≼ₕ) _))) lkup≡)
                                   (ih₁ .↑⊢v)
                                   hwrite
              ; ↑⊢𝓢 = ih₁ .↑⊢𝓢
              ; ↑𝓢≼ = ≼ₛ-trans{𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢″} (ih .↑𝓢≼) (ih₁ .↑𝓢≼)
              ; ↑cls = WFV (λ())
              ; ↑wf-𝓗 = wfh-write (𝟙-value (ih₁ .↑⊢v) <⦂-refl ) (ih₁ .↑cls) hwrite (ih₁ .↑wf-𝓗)
              ; ↑wf-𝓢 = ih₁ .↑wf-𝓢
              }

eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-q (TSetref ⊢e ⊢e₁) (ESetref {𝓢 = 𝓢}{q₁ = 𝟚}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″}{𝓢‴ = 𝓢‴} ⇓ ⇓₁ (refl , stwrite))
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊨𝓔 𝓔-wft wf-𝓗 wf-𝓢 ≤-top ⊢e ⇓
... | ih@record { ↑Σₕ′ = _ ; ↑Σₛ′ = _ ; ↑Σ≼ₕ = _ ; ↑Σ≼ₛ = _ ; ↑⊢v = (TVRef ℓ< lkup≡ (SQual qsub (SRef <⦂S S<⦂))) ; ↑⊢𝓗 = _ ; ↑⊢𝓢 = _ ; ↑𝓢≼ = _ ; ↑cls = _ ; ↑wf-𝓗 = _ ; ↑wf-𝓢 = _ }
  with eval-soundness (ih .↑⊢𝓗) (ih .↑⊢𝓢) (⊨-extend (↑Σ≼ₕ ih) (↑Σ≼ₛ ih) (↑𝓢≼ ih) ⊨𝓔) (wfe-ext-≼ₛ (↑𝓢≼ ih) 𝓔-wft) (↑wf-𝓗 ih) (↑wf-𝓢 ih) ≤-top ⊢e₁ ⇓₁
... | ih₁
  with refl ← <⦂-antisym  S<⦂ <⦂S
  using 𝓢″≼ₛ𝓢‴ ← ≼ₛ-swrite stwrite
  with swrite0 xwrite ← stwrite
  = record
              { ↑Σₕ′ = ih₁ .↑Σₕ′
              ; ↑Σₛ′ = ih₁ .↑Σₛ′
              ; ↑Σ≼ₕ = ≼-trans (ih .↑Σ≼ₕ) (ih₁ .↑Σ≼ₕ)
              ; ↑Σ≼ₛ = ≼-trans (ih .↑Σ≼ₛ) (ih₁ .↑Σ≼ₛ)
              ; ↑⊢v = TVUnit
              ; ↑⊢𝓗 = ih₁ .↑⊢𝓗
              ; ↑⊢𝓢 = typed-swrite (ih₁ .↑⊢𝓢)
                                   (≤ℕ-trans ℓ< (≼⇒length (ih₁ .↑Σ≼ₛ)))
                                   (trans (trans (cong (lookup (ih₁ .↑Σₛ′)) (fromℕ-inject≤ (≼⇒length (ih₁ .↑Σ≼ₛ)) ℓ<)) (sym (≼-lookup (ih₁ .↑Σ≼ₛ) _))) lkup≡)
                                   (ih₁ .↑⊢v)
                                   stwrite 
              ; ↑𝓢≼ = ≼ₛ-trans{𝓢₁ = 𝓢}{𝓢₂ = 𝓢″}{𝓢₃ = 𝓢‴} (≼ₛ-trans{𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢″} (ih .↑𝓢≼) (ih₁ .↑𝓢≼)) 𝓢″≼ₛ𝓢‴
              ; ↑cls = WFV (λ())
              ; ↑wf-𝓗 = wfh-ext-≼ₛ 𝓢″≼ₛ𝓢‴ (ih₁ .↑wf-𝓗)
              ; ↑wf-𝓢 = let r = wfl-write (ih₁ .↑cls) xwrite (ih₁ .↑wf-𝓢) in wfl-ext-≼ₛ (≼ₛ-swrite stwrite) r
              }

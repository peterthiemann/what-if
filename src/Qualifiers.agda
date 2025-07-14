module Qualifiers where

open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)

-- qualifiers
data Qual : Set where
  𝟙 𝟚 : Qual

variable
  q q₀ q₁ q₂ q₃ q₄ q′ q₁′ q₂′ : Qual


data _≤_ : Qual → Qual → Set where
  ≤-bottop  : 𝟙 ≤ 𝟚
  ≤-refl : q ≤ q

≤-bot : 𝟙 ≤ q
≤-bot {𝟙} = ≤-refl
≤-bot {𝟚} = ≤-bottop

≤-top : q ≤ 𝟚
≤-top {𝟙} = ≤-bottop
≤-top {𝟚} = ≤-refl

≤-antisym : q₁ ≤ q₂ → q₂ ≤ q₁ → q₁ ≡ q₂
≤-antisym ≤-refl ≤-refl = refl

≤-trans : q₁ ≤ q₂ → q₂ ≤ q₃ → q₁ ≤ q₃
≤-trans ≤-bottop ≤-refl = ≤-bottop
≤-trans ≤-refl ≤-bottop = ≤-bottop
≤-trans ≤-refl ≤-refl = ≤-refl

≤-irrelevant : {p₁ p₂ : q₁ ≤ q₂} → p₁ ≡ p₂
≤-irrelevant {p₁ = ≤-bottop} {≤-bottop} = refl
≤-irrelevant {p₁ = ≤-refl} {≤-refl} = refl

¬2≤1 : ¬ (𝟚 ≤ 𝟙)
¬2≤1 ()

≤⇒≡ : q ≤ 𝟙 → q ≡ 𝟙
≤⇒≡ ≤-refl = refl

_⊔_ : Qual → Qual → Qual
𝟙 ⊔ q₂ = q₂
𝟚 ⊔ q₂ = 𝟚

_≤ᵇ_ : Qual → Qual → Bool
𝟙 ≤ᵇ q₂ = true
𝟚 ≤ᵇ 𝟙 = false
𝟚 ≤ᵇ 𝟚 = true

≤-sound : q₁ ≤ q₂ → q₁ ≤ᵇ q₂ ≡ true
≤-sound {𝟙} ≤-refl = refl
≤-sound {𝟚} ≤-refl = refl
≤-sound ≤-bottop = refl

≤-complete : q₁ ≤ᵇ q₂ ≡ true → q₁ ≤ q₂
≤-complete {𝟙} {𝟙} ≤b = ≤-refl
≤-complete {𝟙} {𝟚} ≤b = ≤-bottop
≤-complete {𝟚} {𝟚} ≤b = ≤-refl

≤ᵇ-top : q ≤ᵇ 𝟚 ≡ true
≤ᵇ-top = ≤-sound ≤-top

≤ᵇ-mon : q₁ ≤ q₂ → q₂ ≤ᵇ q ≡ true → q₁ ≤ᵇ q ≡ true
≤ᵇ-mon q1≤q2 q2≤bq = ≤-sound (≤-trans q1≤q2 (≤-complete q2≤bq))

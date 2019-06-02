module Main where

  open import TwoPoint
  open import NbE (⊑ᴸᴴ-Preorder)
  open import Data.Empty
  open import Relation.Nullary

  -- the bool type is isomorphic to unit + unit
  Bool : Type
  Bool = 𝟙 + 𝟙

  -- true is the left injection
  True : ∀ {Γ} → Nf Bool Γ
  True = inl unit

  -- false is the right injection
  False : ∀ {Γ} → Nf Bool Γ
  False = inr unit

  open import Relation.Binary.PropositionalEquality
  open import Data.Sum

  -- lemmas about the shape of the context
  -- this are very concrete to the proof we have
  -- future work amounts to generalize this
  private
    lemma₁ : ∀ {a b} → ¬ (Ne (a ⇒ b) (Ø `, (〈 H 〉 Bool)))
    lemma₁ (var (su ()))
    lemma₁ (n ∙ _) = lemma₁ n

    lemma₂ : ∀ {a b} → ¬ (Ne (a + b) (Ø `, (〈 H 〉 Bool)))
    lemma₂ (var (su ()))
    lemma₂ (n ∙ _) = lemma₁ n

    lemma₃ : ∀ {a} → ¬ (Ne (〈 L 〉 a) (Ø `, (〈 H 〉 Bool)))
    lemma₃ (var (su ()))
    lemma₃ (n ∙ _)    = lemma₁ n
    lemma₃ (⊑ᴸᴴ-L ↑ n) = lemma₃ n


  -- main lemma
  lemma : (n : Nf (〈 H 〉 Bool ⇒ 〈 L 〉 Bool) Ø)
        → (n ≡ `λ (η True)) ⊎ (n ≡ `λ (η False))
  lemma (`λ (η (inl unit)))         = inj₁ refl
  lemma (`λ (η (inl (case n _ _)))) = ⊥-elim (lemma₂ n)
  lemma (`λ (η (inr unit)))         = inj₂ refl
  lemma (`λ (η (inr (case n _ _)))) = ⊥-elim (lemma₂ n)
  lemma (`λ (η (case n _ _)))       = ⊥-elim (lemma₂ n)
  lemma (`λ (n ≫= _))     = ⊥-elim (lemma₃ n)
  lemma (`λ (case n _ _)) = ⊥-elim (lemma₂ n)
  lemma (case n _ _)      = ⊥-elim (emptyNe n)


  -- the main theorem stating that a term that
  -- receives a secret and produces a public output
  -- it is equivalent to a constant function
  main : (n : Term (〈 H 〉 Bool ⇒ 〈 L 〉 Bool) Ø)
       → (norm n ≡ `λ (η True)) ⊎ (norm n ≡ `λ (η False))
  main n = lemma (norm n)

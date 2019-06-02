module Main where

  open import TwoPoint
  open import NbE (⊑ᴸᴴ-Preorder)
  open import Data.Empty
  open import Relation.Nullary
  open import Function using (_∋_)

  -- the bool type is isomorphic to unit + unit
  Bool : Type
  Bool = 𝟙 + 𝟙

  -- true is the left injection
  True : ∀ {Γ} → Nf Bool Γ
  True = inl unit

  true : ∀ {Γ} → Term Bool Γ
  true = inl unit

  -- false is the right injection
  False : ∀ {Γ} → Nf Bool Γ
  False = inr unit

  false : ∀ {Γ} → Term Bool Γ
  false = inr unit

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


  -- we model the complete proof by assuming a lot of stuff
  -- which we label as future work.
  -- everything seems fairly reasonable or is standard from the
  -- literature.
  module FutureWork where

    import Relation.Binary as B

    -- βη convertibility relation (only the case needed for the proof)
    -- it is obviously very incomplete
    data _≈_ : ∀ {Γ} {a} → Term a Γ → Term a Γ → Set where
      ≈-cong  : ∀ {Γ} {a b} {f₁ f₂ : Term (a ⇒ b) Γ} {t₁ t₂ : Term a Γ}
                → f₁ ≈ f₂ → t₁ ≈ t₂ → (f₁ ∙ t₁) ≈ (f₂ ∙ t₂)

    -- βη convertibility is an equivalence relation
    postulate
      ≈-refl  : ∀ {Γ} {a} → B.Reflexive (_≈_ {Γ = Γ} {a = a})
      ≈-sym   : ∀ {Γ} {a} → B.Symmetric (_≈_ {Γ = Γ} {a = a})
      ≈-trans : ∀ {Γ} {a} → B.Transitive (_≈_ {Γ = Γ} {a = a})

    postulate

      -- nbe is consistent
      nbe-consitency : ∀ {Γ} {a} → (t : Term a Γ) → t ≈ qNf (norm t)

      -- constant functions applied return constant results
      λtrue          : ∀ {ℓ} {Γ} {a} → (e : Term a Γ)
                     → ((`λ (Term (〈 ℓ 〉 Bool) (Γ `, a) ∋ η true)) ∙ e) ≈ (η true)

      λfalse         : ∀ {ℓ} {Γ} {a} → (e : Term a Γ)
                     → ((`λ (Term (〈 ℓ 〉 Bool) (Γ `, a) ∋ η false)) ∙ e) ≈ (η false)

    -- propositional equality implies βη convertibility
    ≡⇒≈ : ∀ {Γ} {a} {t₁ t₂ : Term a Γ} → t₁ ≡ t₂ → t₁ ≈ t₂
    ≡⇒≈ refl = ≈-refl

    -- noninterference like property for λ-sec
    ni : ∀ (t : Term (〈 H 〉 Bool ⇒ 〈 L 〉 Bool) Ø)
         → (a₁ a₂ : Term (〈 H 〉 Bool) Ø)
         → (t ∙ a₁) ≈ (t ∙ a₂)
    ni t a₁ a₂ with main t
    ni t a₁ a₂ | inj₁ ctrue  with ≈-trans (nbe-consitency t) (≡⇒≈ (cong qNf ctrue))
    ... | p with ≈-cong {t₁ = a₁} {t₂ = a₁} p ≈-refl | ≈-cong {t₁ = a₂} {t₂ = a₂} p ≈-refl
    ... | pp | qq  with ≈-trans pp (λtrue a₁) | ≈-trans qq (λtrue a₂)
    ... | s1 | s2  = ≈-trans s1 (≈-sym s2)
    ni t a₁ a₂ | inj₂ cfalse with ≈-trans (nbe-consitency t) (≡⇒≈ (cong qNf cfalse))
    ... | p with ≈-cong {t₁ = a₁} {t₂ = a₁} p ≈-refl | ≈-cong {t₁ = a₂} {t₂ = a₂} p ≈-refl
    ... | pp | qq  with ≈-trans pp (λfalse a₁) | ≈-trans qq (λfalse a₂)
    ... | s1 | s2  = ≈-trans s1 (≈-sym s2)

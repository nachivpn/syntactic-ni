import Relation.Binary as RB
open import Level
module NbE (Pre : RB.Preorder 0ℓ 0ℓ 0ℓ)where

  -- handy synonyms
  Label = RB.Preorder.Carrier Pre
  _⊑_   = RB.Preorder._∼_ Pre

  module TypeModule where

    -- types of λ-sec
    data Type  : Set where
      𝟙     :                 Type            -- unit
      𝕓     :                 Type            -- base (abstract) type
      _⇒_   : (a b : Type)  → Type            -- function
      _+_   : (a b : Type)  → Type            -- sums
      〈_〉_   : (ℓ : Label) (a : Type) → Type  -- security monad

    infixr 10 _⇒_

    -- Ctx as a snoc list of types
    data Ctx : Set where
      Ø    : Ctx
      _`,_ : Ctx → Type → Ctx

  open TypeModule public

  module Weakening where

    -- Weakening over contexts Γ ⊆ Δ to be read as:
    -- Γ is weaker (contains possibly more types) than Δ
    -- Δ is thinner (contains possibly less types) than Γ
    data _⊆_ : Ctx → Ctx → Set where
      base : Ø ⊆ Ø
      keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
      drop : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ Δ

    -- Weakenings form a preorder relation
    ⊆-refl : RB.Reflexive _⊆_
    ⊆-refl {Ø}      = base
    ⊆-refl {Γ `, T} = keep ⊆-refl

    ⊆-trans : RB.Transitive _⊆_
    ⊆-trans base q = q
    ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
    ⊆-trans (keep p) (drop q) = drop (⊆-trans p q)
    ⊆-trans (drop p) q        = drop (⊆-trans p q)

  open Weakening public

  module Variable where

    -- De Bruijn index into a context
    -- type τ appears in context Γ
    data _∈_ : Type → Ctx → Set where
      ze : ∀ {Γ a}   → a ∈ (Γ `, a)
      su : ∀ {Γ a S} → a ∈ Γ → a ∈ (Γ `, S)

    wkenⱽ : ∀ {a} {Γ Δ} → Γ ⊆ Δ → a ∈ Δ → a ∈ Γ
    wkenⱽ (keep e) ze     = ze
    wkenⱽ (keep e) (su v) = su (wkenⱽ e v)
    wkenⱽ (drop e) v      = su (wkenⱽ e v)

  open Variable public

  module TermModule where

    -- intrinsically-typed terms of λ-sec
    -- a Term τ Γ is to be read as a typing judgement
    -- Γ ⊢ t : τ
    data Term : Type → Ctx → Set where
      -- unit

      unit  : ∀ {Γ} ----------
                    → Term 𝟙 Γ

      -- λ-calculus
      `λ    : ∀ {Γ} {a b} → Term b (Γ `, a)
                          -----------------
                          → Term (a ⇒ b) Γ

      var   : ∀ {Γ} {a} → a ∈ Γ
                        ----------
                        → Term a Γ

      _∙_   : ∀ {Γ} {a b} → Term (a ⇒ b) Γ → Term a Γ
                          ---------------------------
                          →         Term b Γ

      -- security monad
      _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Term (〈 ℓᴸ 〉 a ) Γ
                               -----------------------------
                               →      Term (〈 ℓᴴ 〉 a) Γ

      η     : ∀ {ℓ} {Γ} {a} → Term a Γ
                            ------------------
                            → Term (〈 ℓ 〉 a) Γ

      _≫=_ : ∀ {ℓ} {Γ} {a b}  → Term (〈 ℓ 〉 a) Γ → Term (〈 ℓ 〉 b) (Γ `, a)
                               -------------------------------------------
                               →             Term (〈 ℓ 〉 b) Γ

      -- sums
      inl   : ∀ {Γ} {a b} → Term a Γ
                          ----------------
                          → Term (a + b) Γ

      inr   : ∀ {Γ} {a b} → Term b Γ
                          ----------------
                          → Term (a + b) Γ

      case  : ∀ {Γ} {a b c} → Term (a + b) Γ → Term c (Γ `, a) → Term c (Γ `, b)
                            ----------------------------------------------------
                            →                    Term c Γ


    -- terms can be weakened
    wkenTm : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Term a Δ → Term a Γ
    wkenTm e unit = unit
    wkenTm e (`λ t)    = `λ (wkenTm (keep e) t)
    wkenTm e (var x)   = var (wkenⱽ e x)
    wkenTm e (t ∙ t₁)  = wkenTm e t ∙ wkenTm e t₁
    wkenTm e (η t)     = η (wkenTm e t)
    wkenTm e (t ≫= k) = wkenTm e t ≫= wkenTm (keep e) k
    wkenTm e (x ↑ t)   = x ↑ wkenTm e t
    wkenTm e (inl t) = inl (wkenTm e t)
    wkenTm e (inr t) = inr (wkenTm e t)
    wkenTm e (case t t₁ t₂) = case (wkenTm e t) (wkenTm (keep e) t₁) (wkenTm (keep e) t₂)

  open TermModule public

  module NormalForm where

  -- intrinsically typed representation of
  -- normal and neutral forms of λ-sec
  mutual

    data Ne : Type → Ctx → Set where
      var   : ∀ {Γ} {a} → a ∈ Γ
                        --------
                        → Ne a Γ

      _∙_   : ∀ {Γ} {a b} → Ne (a ⇒ b) Γ → Nf a Γ
                          -----------------------
                          →         Ne b Γ

      _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Ne (〈 ℓᴸ 〉 a) Γ
                               --------------------------
                               →     Ne (〈 ℓᴴ 〉 a) Γ

    data Nf : Type → Ctx → Set where
      -- unit
      unit  : ∀ {Γ} --------
                    → Nf 𝟙 Γ

      -- λ-calculus with base
      `λ    : ∀ {Γ} {a b} → Nf b (Γ `, a)
                          --------------
                          → Nf (a ⇒ b) Γ

      𝕓     : ∀ {Γ}       → Ne 𝕓 Γ
                          --------
                          → Nf 𝕓 Γ

      -- security monad
      η     : ∀ {ℓ} {Γ}  {a}   → Nf a Γ
                               ---------------
                               → Nf (〈 ℓ 〉 a) Γ
      _≫=_ : ∀ {ℓ} {Γ} {a b} → Ne (〈 ℓ 〉 a) Γ → Nf (〈 ℓ 〉 b) (Γ `, a)
                              ---------------------------------------
                              →             Nf (〈 ℓ 〉 b) Γ

      -- sums
      inl   : ∀ {Γ} {a b} → Nf a Γ
                          --------------
                          → Nf (a + b) Γ

      inr   : ∀ {Γ} {a b} → Nf b Γ
                          --------------
                          → Nf (a + b) Γ

      case  : ∀ {Γ} {a b c} → Ne (a + b) Γ → Nf c (Γ `, a) → Nf c (Γ `, b)
                            ----------------------------------------------
                            →                  Nf c Γ

  -- normal forms and neutrals can be weakened
  mutual
    wkenNf : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Nf T Δ → Nf T Γ
    wkenNf e unit      = unit
    wkenNf e (`λ n)    = `λ (wkenNf (keep e) n)
    wkenNf e (η m)     = η (wkenNf e m)
    wkenNf e (𝕓 n)     = 𝕓 (wkenNe e n)
    wkenNf e (x ≫= m) = (wkenNe e x) ≫= wkenNf (keep e) m
    wkenNf e (inl n)   = inl (wkenNf e n)
    wkenNf e (inr n)   = inr (wkenNf e n)
    wkenNf e (case x n₁ n₂) = case (wkenNe e x) (wkenNf (keep e) n₁) (wkenNf (keep e) n₂)
    wkenNe : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Ne T Δ → Ne T Γ
    wkenNe e (var x) = var (wkenⱽ e x)
    wkenNe e (n ∙ x) = (wkenNe e n) ∙ (wkenNf e x)
    wkenNe e (c ↑ n) = c ↑ wkenNe e n


  -- normal forms and terms are a subset of
  -- terms (can be embedded back into terms)
  mutual
    -- a normal form
    qNf : ∀ {a} {Γ} → Nf a Γ → Term a Γ
    qNf unit = unit
    qNf (`λ n) = `λ (qNf n)
    qNf (𝕓 x)  = qNe x
    qNf (η n)  = η (qNf n)
    qNf (x ≫= n) = (qNe x) ≫= (qNf n)
    qNf (inl n) = inl (qNf n)
    qNf (inr n) = inr (qNf n)
    qNf (case n c₁ c₂) = case (qNe n) (qNf c₁) (qNf c₂)

    qNe : ∀ {a} {Γ} → Ne a Γ → Term a Γ
    qNe (var x) = var x
    qNe (t ∙ u) = (qNe t) ∙ (qNf u)
    qNe (c ↑ t) = c ↑ (qNe t)

  open NormalForm public

  open import Data.Product
  open import Data.Unit hiding (_≤_)
  open import Data.Sum
    using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
  open import Function using (_∘_)

  -- machinery to evaluate terms in λ-sec
  module Presheaf where

    -- a presheaf is something of type Ctx → Set
    -- for instance Term, Nf, Ne
    -- and a function to weaken it
    record 𝒫 : Set₁ where
      field
        In   : Ctx → Set
        Wken : ∀ {Δ Γ} (Γ⊆Δ : Γ ⊆ Δ) → (In Δ → In Γ)

    open 𝒫

    -- natural transformation between presheaves
    _→∙_ : 𝒫 → 𝒫 → Set
    (P →∙ Q) = ∀ {Γ} → P .In Γ → Q .In Γ

    -- presheaves are closed under product
    _×ᴾ_ : 𝒫 → 𝒫 → 𝒫
    In (P ×ᴾ Q) Γ                 = (In P Γ) × (In Q Γ)
    Wken (P ×ᴾ Q) Γ⊆Δ (fst , snd) = (Wken P Γ⊆Δ fst) , (Wken Q Γ⊆Δ snd)

    -- presheaves are closed under function
    _⇒ᴾ_ :  𝒫 → 𝒫 → 𝒫
    In (P ⇒ᴾ Q) Γ             = ∀ {Δ} → Δ ⊆ Γ → P .In Δ → Q .In Δ
    (P ⇒ᴾ Q) .Wken Γ⊆Δ₁ f Δ⊆Γ = f (⊆-trans Δ⊆Γ  Γ⊆Δ₁)

    -- presheaves are closed under sums
    _+ᴾ_ :  𝒫 → 𝒫 → 𝒫
    In (P +ᴾ Q) Γ    = (In P Γ) ⊎ (In Q Γ)
    (P +ᴾ Q) .Wken Γ⊆Δ = [ inj₁ ∘ Wken P Γ⊆Δ , inj₂ ∘ Wken Q Γ⊆Δ  ]′ 

    -- the unit presheaf that ignores the context
    𝟙ᴾ : 𝒫
    𝟙ᴾ = record { In = λ _ → ⊤ ; Wken = λ {Δ} {Γ} Γ⊆Δ _ → tt }

  open Presheaf
  open 𝒫

  module CoverMonad where

    -- the cover security monad allow us to
    -- interpret the security monad of λ-sec
    -- in the semantics.
    -- it is indexed by the security label
    data 𝒞 (A : 𝒫) (ℓ : Label) : Ctx → Set where
      return : ∀ {Γ}       → A .In Γ → 𝒞 A ℓ Γ
      bind   : ∀ {Γ} {a}   → Ne (〈 ℓ 〉 a) Γ → 𝒞 A ℓ (Γ `, a) → 𝒞 A ℓ Γ
      branch : ∀ {Γ} {a b} → Ne (a + b) Γ →  𝒞 A ℓ (Γ `, a) →  𝒞 A ℓ (Γ `, b)
                           → 𝒞 A ℓ Γ

    -- the cover monad can be weakened
    wken𝒞 : ∀ {ℓ} {A} {Γ Δ} → Γ ⊆ Δ → 𝒞 A ℓ Δ → 𝒞 A ℓ Γ
    wken𝒞 {A = A} e (return x) = return (Wken A e x)
    wken𝒞 e (bind x m)         = bind   (wkenNe e x) (wken𝒞 (keep e) m)
    wken𝒞 e (branch x m₁ m₂)   =
      branch (wkenNe e x) (wken𝒞 (keep e) m₁) (wken𝒞 (keep e) m₂)

    -- the cover monad is a presheaf
    𝒞ᴾ : Label → 𝒫 → 𝒫
    𝒞ᴾ ℓ A = record { In = 𝒞 A ℓ ; Wken = wken𝒞 }

    -- we show that 𝒞 is a monad over presheaves
    -- by implementing fmap and join
    -- we do not prove the laws
    map𝒞  : ∀ {ℓ} {A B} → (A →∙ B) → (𝒞ᴾ ℓ A →∙ 𝒞ᴾ ℓ B)
    map𝒞 f (return x) = return (f x)
    map𝒞 f (bind x m) = bind x (map𝒞 f m)
    map𝒞 f (branch x c₁ c₂) = branch x (map𝒞 f c₁) (map𝒞 f c₂)

    join𝒞 : ∀ {ℓ} {A} → 𝒞ᴾ ℓ (𝒞ᴾ ℓ A) →∙ 𝒞ᴾ ℓ A
    join𝒞 (return x) = x
    join𝒞 (bind f m) = bind f (join𝒞 m)
    join𝒞 (branch x c₁ c₂) = branch x (join𝒞 c₁) (join𝒞 c₂)

    mapExp𝒞  : ∀ {ℓ} {A B} → (A ⇒ᴾ B) →∙ (𝒞ᴾ ℓ A ⇒ᴾ 𝒞ᴾ ℓ B)
    mapExp𝒞 f e (return x) = return (f e x)
    mapExp𝒞 f e (bind x m) = bind x (mapExp𝒞 f (drop e) m)
    mapExp𝒞 f e (branch x c₁ c₂) =
      branch x (mapExp𝒞 f (drop e) c₁) (mapExp𝒞 f (drop e) c₂)

    bindExp𝒞 : ∀ {ℓ} {A B} → (A ⇒ᴾ 𝒞ᴾ ℓ B) →∙ (𝒞ᴾ ℓ A ⇒ᴾ 𝒞ᴾ ℓ B)
    bindExp𝒞 f e m = join𝒞 (mapExp𝒞 f e m)

    -- we can also implement a semantic version
    -- of λ-sec ↑
    up𝒞 : ∀ {ℓᴸ ℓᴴ} {A} → ℓᴸ ⊑ ℓᴴ → (𝒞ᴾ ℓᴸ A →∙ 𝒞ᴾ ℓᴴ A)
    up𝒞 L⊑H (return x)  = return x
    up𝒞 L⊑H (bind n k)  = bind (L⊑H ↑ n) (up𝒞 L⊑H k)
    up𝒞 L⊑H (branch x c₁ c₂) = branch x (up𝒞 L⊑H c₁) (up𝒞 L⊑H c₂)

  open CoverMonad public

  module DecMonad where

    -- the decision monad for coproducts
    data 𝒟 (A : 𝒫) : Ctx → Set where
      return : ∀ {Γ} → A .In Γ → 𝒟 A Γ
      branch : ∀ {Γ} {a b}
        → Ne (a + b) Γ
        → (c₁ : 𝒟 A (Γ `, a)) → (c₂ :  𝒟 A (Γ `, b))
        ---------------------------------------------
        → 𝒟 A Γ

    -- 𝒟 can be weakened
    wken𝒟 : ∀ {A} {Γ Δ} → Γ ⊆ Δ → 𝒟 A Δ → 𝒟 A Γ
    wken𝒟 {A} e (return x)   = return (Wken A e x)
    wken𝒟 e (branch x c₁ c₂) =
      branch (wkenNe e x) (wken𝒟 (keep e) c₁) (wken𝒟 (keep e) c₂)

    -- 𝒟 is a presheaf
    𝒟ᴾ : 𝒫 → 𝒫
    𝒟ᴾ A = record { In = 𝒟 A ; Wken = wken𝒟 }

    -- we show that 𝒟 is a monad over presheaves
    -- by implementing fmap and join
    -- we do not prove the laws
    map𝒟  : ∀ {A B} → (A →∙ B) → (𝒟ᴾ A →∙ 𝒟ᴾ B)
    map𝒟 f (return x) = return (f x)
    map𝒟 f (branch x c₁ c₂) = branch x (map𝒟 f c₁) (map𝒟 f c₂)

    join𝒟 : ∀ {A} → 𝒟ᴾ (𝒟ᴾ A) →∙ 𝒟ᴾ A
    join𝒟 (return x) = x
    join𝒟 (branch x m m₁) = branch x (join𝒟 m) (join𝒟 m₁)

    mapExp𝒟  : ∀ {A B} → (A ⇒ᴾ B) →∙ (𝒟ᴾ A ⇒ᴾ 𝒟ᴾ B)
    mapExp𝒟 f e (return x) =
      return (f e x)
    mapExp𝒟 f e (branch x c₁ c₂) =
      branch x (mapExp𝒟 f (drop e) c₁) (mapExp𝒟 f (drop e) c₂)

    bindExp𝒟 : ∀ {A B} → (A ⇒ᴾ 𝒟ᴾ B) →∙ (𝒟ᴾ A ⇒ᴾ 𝒟ᴾ B)
    bindExp𝒟 f e m = join𝒟 (mapExp𝒟 f e m)

  open DecMonad

  -- we glue together the machinery to
  -- normalize λ-sec terms
  module Interpretation where

    -- Term is a presheaf
    Termᴾ : Type → 𝒫
    Termᴾ τ = record { In = Term τ ; Wken = wkenTm }

    -- Nf is a presheaf
    Nfᴾ : Type → 𝒫
    Nfᴾ τ = record { In = Nf τ ; Wken = wkenNf }

    -- Ne is a presheaf
    Neᴾ : Type → 𝒫
    Neᴾ τ = record { In = Ne τ ; Wken = wkenNe }

    -- the presheaf for base type
    𝕓ᴾ : 𝒫
    𝕓ᴾ = record { In   = Nf 𝕓 ; Wken = wkenNf }

    -- interpretation of a λ-sec type 
    -- as a presheaf
    ⟦_⟧ : Type → 𝒫
    ⟦ 𝟙  ⟧        = 𝟙ᴾ
    ⟦ 𝕓 ⟧         = 𝕓ᴾ
    ⟦ a ⇒ b ⟧     = ⟦ a ⟧ ⇒ᴾ  ⟦ b ⟧
    ⟦ (〈 ℓ 〉 a) ⟧  = 𝒞ᴾ ℓ ⟦ a ⟧
    ⟦ a + b ⟧     = 𝒟ᴾ (⟦ a ⟧ +ᴾ ⟦ b ⟧)

    -- interpretation of Ctx (list of types)
    -- as a presheaf
    ⟦_⟧ₑ : Ctx → 𝒫
    ⟦ Ø ⟧ₑ      = 𝟙ᴾ
    ⟦ Γ `, a ⟧ₑ = ⟦ Γ ⟧ₑ ×ᴾ ⟦ a ⟧

  open Interpretation public

  module DecMonadOps where

    run𝒟Nf : ∀ {a : Type} → 𝒟ᴾ (Nfᴾ a) →∙ (Nfᴾ a)
    run𝒟Nf (return x) = x
    run𝒟Nf (branch x m m₁) = case x (run𝒟Nf m) (run𝒟Nf m₁)

    run𝒟 : ∀ {a : Type} → 𝒟ᴾ ⟦ a ⟧ →∙ ⟦ a ⟧
    run𝒟 {𝟙}      _ = tt
    run𝒟 {𝕓}      m = run𝒟Nf m
    run𝒟 {a + b}  m = join𝒟 m
    run𝒟 {a ⇒ b}  m = λ e x → run𝒟 {b} (run𝒟⇒ m e (return x))
      where
      run𝒟⇒ : 𝒟ᴾ ⟦ a ⇒ b ⟧ →∙ (𝒟ᴾ ⟦ a ⟧ ⇒ᴾ 𝒟ᴾ ⟦ b ⟧)
      run𝒟⇒ (return f) e x = mapExp𝒟 f e x
      run𝒟⇒ (branch n c₁ c₂) e x =
        branch (wkenNe e n)
          (run𝒟⇒ c₁ (keep e) (wken𝒟 (drop ⊆-refl) x))
          (run𝒟⇒ c₂ (keep e) (wken𝒟 (drop ⊆-refl) x))
    run𝒟 {〈 ℓ 〉 a} m = run𝒟𝒞 m
      where
      run𝒟𝒞 : 𝒟ᴾ (𝒞ᴾ ℓ ⟦ a ⟧) →∙ (𝒞ᴾ ℓ ⟦ a ⟧)
      run𝒟𝒞 (return x) = x
      run𝒟𝒞 (branch x c₁ c₂) = branch x (run𝒟𝒞 c₁) (run𝒟𝒞 c₂)

  open DecMonadOps

  module NbE where

    open 𝒫

    -- lookup a De Brujin index in the context
    lookup : ∀ {a Γ} → a ∈ Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    lookup ze     (_ , v) = v
    lookup (su v) (γ , _) = lookup v γ

    -- evaluate (map) a term into a `function` (morphism)
    -- between the interpretation of its context to the interpretation
    -- of its type
    eval : ∀ {a Γ} → Term a Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    -- unit
    eval unit _ = tt

    -- λ-calculus
    eval {Γ = Γ} (`λ t) γ     = λ e u → eval t (Wken ⟦ Γ ⟧ₑ e γ , u)
    eval (var x) γ            = lookup x γ
    eval (t ∙ u) γ            = (eval t γ) ⊆-refl (eval u γ)

    -- security monad
    eval (c ↑ t) γ            = up𝒞 c (eval t γ)
    eval (η t) γ              = return (eval t γ)
    eval {Γ = Γ} (t ≫= m) γ  =
      bindExp𝒞 (λ e a → eval m (Wken ⟦ Γ ⟧ₑ e γ , a)) ⊆-refl (eval t γ)

    -- sums
    eval (inl t) γ            = return (inj₁ (eval t γ))
    eval (inr t) γ            = return (inj₂ (eval t γ))
    eval {a} {Γ} (case {_} {b} {c} t t₁ t₂) {Δ} γ =
      run𝒟 {a} (mapExp𝒟 match ⊆-refl (eval t γ))
      where
      match : ((⟦ b ⟧ +ᴾ ⟦ c ⟧) ⇒ᴾ ⟦ a ⟧) .In Δ
      match e (inj₁ x) = eval t₁ ((Wken ⟦ Γ ⟧ₑ e γ) , x)
      match e (inj₂ y) = eval t₂ ((Wken ⟦ Γ ⟧ₑ e γ) , y)

    -- reify a value from the interpretation back into a
    -- normal form of λ-sec
    mutual

      reifyVal : ∀ {a} → ⟦ a ⟧ →∙ Nfᴾ a
      reifyVal {𝟙} x      = unit
      reifyVal {𝕓} x      = x
      reifyVal {a ⇒ b} f  = `λ (reifyVal (f (drop ⊆-refl) (reflect {a} (var ze))))
      reifyVal {〈 a 〉 ℓ} m = reifyVal𝒞 m
      reifyVal {a + b}  m = run𝒟Nf (map𝒟 reifySum m)

      reifyVal𝒟 : ∀ {a} → 𝒟ᴾ ⟦ a ⟧ →∙ Nfᴾ a
      reifyVal𝒟 {a} m = run𝒟Nf {a} (map𝒟 reifyVal m)

      reifySum : ∀ {a b} → (⟦ a ⟧ +ᴾ ⟦ b ⟧) →∙ Nfᴾ (a + b)
      reifySum {a} {b} = [ inl ∘ reifyVal {a} , inr ∘ reifyVal {b} ]′

      reifyVal𝒞 : ∀ {a} {ℓ} → 𝒞ᴾ ℓ ⟦ a ⟧ →∙ Nfᴾ (〈 ℓ 〉 a)
      reifyVal𝒞 (return x) = η (reifyVal x)
      reifyVal𝒞 (bind x m) = x ≫= reifyVal𝒞 m
      reifyVal𝒞 (branch x c₁ c₂) = case x (reifyVal𝒞 c₁) (reifyVal𝒞 c₂)

      -- reflect maps a neutral into the semantic
      -- is needed for the function type
      reflect : ∀ {a} → Neᴾ a →∙ ⟦ a ⟧
      reflect {𝟙}      n = tt
      reflect {𝕓}      n = 𝕓 n
      reflect {a ⇒ b}  n = λ e v → reflect ((wkenNe e n) ∙ (reifyVal v))
      reflect {〈 ℓ 〉 a} n =  bind n (return (reflect {a} (var ze)))
      reflect {a + b}  n =
        branch n
          (return (inj₁ (reflect {a} (var ze))))
          (return (inj₂ (reflect {b} (var ze))))

    -- the identity substitution
    idSubst :  ∀ Γ → ⟦ Γ ⟧ₑ .In Γ
    idSubst Ø        = tt
    idSubst (Γ `, T) = Wken ⟦ Γ ⟧ₑ (drop ⊆-refl) (idSubst Γ) , reflect {T} (var ze)

    -- reify a morphism in the interpretation
    -- back to a normal form
    reify : ∀{a Γ} → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧) → Nf a Γ
    reify {a} {Γ} f = reifyVal (f (idSubst Γ))

    -- normalization is the composition of
    -- eval and reify
    norm : ∀ {a} → Termᴾ a →∙ Nfᴾ a
    norm t = reify (eval t)

  open NbE public

  module Neutrality where

    open import Data.Empty
    open import Relation.Nullary

    -- neutrality shows that is impossible
    -- to have a neutral term in the empty
    -- context
    emptyNe : ∀ {a} → ¬ (Ne a Ø)
    emptyNe (var ())
    emptyNe (x ∙ _) = emptyNe x
    emptyNe (x ↑ n) = emptyNe n

  open Neutrality public

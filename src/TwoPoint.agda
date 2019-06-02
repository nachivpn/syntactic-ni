module TwoPoint where
-- classic two point lattice for IFC
-- note that our development only uses
-- the fact that is a preorder

  open import Level
  open import Data.Product
  import Relation.Binary as B
  import Relation.Binary.Lattice as L
  import Relation.Binary.PropositionalEquality as P

  -- Low and High labels
  data LH : Set where
    L H : LH

  -- 'can flow to' relation
  data _⊑ᴸᴴ_ : LH → LH → Set where
    ⊑ᴸᴴ-H : ∀ {ℓ} → ℓ ⊑ᴸᴴ H
    ⊑ᴸᴴ-L : L ⊑ᴸᴴ L

  ⊑ᴸᴴ-refl : B.Reflexive _⊑ᴸᴴ_
  ⊑ᴸᴴ-refl {L} = ⊑ᴸᴴ-L
  ⊑ᴸᴴ-refl {H} = ⊑ᴸᴴ-H

  ⊑ᴸᴴ-trans : B.Transitive _⊑ᴸᴴ_
  ⊑ᴸᴴ-trans a ⊑ᴸᴴ-H = ⊑ᴸᴴ-H
  ⊑ᴸᴴ-trans a ⊑ᴸᴴ-L = a

  _≡ᴸᴴ_ : LH → LH → Set
  _≡ᴸᴴ_ = P._≡_

  -- 'can flow to' is a preorder
  ⊑ᴸᴴ-IsPreorder : B.IsPreorder _≡ᴸᴴ_ _⊑ᴸᴴ_
  ⊑ᴸᴴ-IsPreorder = record { isEquivalence = P.isEquivalence
                         ; reflexive     = λ {P.refl → ⊑ᴸᴴ-refl}
                         ; trans         = ⊑ᴸᴴ-trans }



  ⊑ᴸᴴ-antisym : B.Antisymmetric _≡ᴸᴴ_ _⊑ᴸᴴ_
  ⊑ᴸᴴ-antisym ⊑ᴸᴴ-H ⊑ᴸᴴ-H = P.refl
  ⊑ᴸᴴ-antisym ⊑ᴸᴴ-L p    = P.refl

  -- 'can flow to' is a partial order
  ⊑ᴸᴴ-IsPartialOrder : B.IsPartialOrder _≡ᴸᴴ_ _⊑ᴸᴴ_
  ⊑ᴸᴴ-IsPartialOrder =
    record { isPreorder = ⊑ᴸᴴ-IsPreorder
           ; antisym    = ⊑ᴸᴴ-antisym }


  -- lattice join operation
  _⊔ᴸᴴ_ : LH → LH → LH
  L ⊔ᴸᴴ q = q
  H ⊔ᴸᴴ q = H

  ⊑ᴸᴴ-⊔ᴸᴴ-Supremum : L.Supremum _⊑ᴸᴴ_ _⊔ᴸᴴ_
  ⊑ᴸᴴ-⊔ᴸᴴ-Supremum L L = ⊑ᴸᴴ-L , ⊑ᴸᴴ-L , (λ _ _ x → x)
  ⊑ᴸᴴ-⊔ᴸᴴ-Supremum L H = ⊑ᴸᴴ-H , ⊑ᴸᴴ-H , (λ _ _ x → x)
  ⊑ᴸᴴ-⊔ᴸᴴ-Supremum H y = ⊑ᴸᴴ-H , ⊑ᴸᴴ-H , (λ _ x _ → x)

  -- 'can flow to' forms a join semilattice
  ⊑ᴸᴴ-IsJoinSemilattice : L.IsJoinSemilattice _≡ᴸᴴ_ _⊑ᴸᴴ_ _⊔ᴸᴴ_
  ⊑ᴸᴴ-IsJoinSemilattice =
    record { isPartialOrder = ⊑ᴸᴴ-IsPartialOrder
           ; supremum       = ⊑ᴸᴴ-⊔ᴸᴴ-Supremum }

  -- 'can flow to' preorder
  ⊑ᴸᴴ-Preorder : B.Preorder 0ℓ 0ℓ 0ℓ
  ⊑ᴸᴴ-Preorder = record { Carrier = LH
    ; _≈_ = _≡ᴸᴴ_
    ; _∼_ = _⊑ᴸᴴ_
    ; isPreorder = ⊑ᴸᴴ-IsPreorder }

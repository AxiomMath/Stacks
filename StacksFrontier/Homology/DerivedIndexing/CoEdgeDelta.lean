module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.EffaceableFamily

/-!
# The co-edge morphism of a composite as a morphism of δ-families

Let `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞` be left exact functors between abelian categories, `𝒜` with
enough injectives. The higher right derived functors `R ⁱ(Q ∘ P)` form an effaceable δ-functor,
and `Q ∘ R ⁱP` is a δ-family: the δ-functor `R ⁱP` followed by the additive functor `Q`. The
canonical identification `R ⁰(Q ∘ P) = Q ∘ P = Q ∘ R ⁰P` therefore extends uniquely to a family
of natural transformations

`R ⁱ(Q ∘ P) ⟶ Q ∘ R ⁱP`

commuting with the connecting morphisms. This is the co-edge morphism `H ⁱ ⟶ E₂^{0,i}` of the
Grothendieck spectral sequence of `(P, Q)` (the edge morphism of [Stacks, Tag 015N] is a
morphism of δ-families extending the degree-zero identification, hence equals this one).

## Main definitions

* `Stacks.DerivedIndexing.plusDelta`: the higher right derived functors `R ⁱF`, in the
  `ℤ`-indexing of `CategoryTheory.Functor.rightDerivedPlus`, as a δ-functor.
* `Stacks.DerivedIndexing.coEdge`: the co-edge morphism `R ⁱ(Q ∘ P) ⟶ Q ∘ R ⁱP`.

## Main results

* `Stacks.DerivedIndexing.canonicalδ_comp_coEdge`: the co-edge morphism commutes with the
  connecting morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace Stacks.DerivedIndexing

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C]

/-- **The higher right derived functors `R ⁱF` as a δ-functor**, in the `ℤ`-indexing, with the
connecting morphisms of the distinguished triangles of short exact sequences. -/
abbrev plusDelta (F : A ⥤ B) [F.Additive] : DeltaFunctor A B :=
  rightDerivedPlusDeltaFunctor F (derivedDeltaFunctorStructure F) (canonicalδ F) (fun _ _ ↦ rfl)

/-- The higher right derived functors vanish on injective objects in positive degrees, so they
form an effaceable δ-functor. -/
instance effaceable_plusDelta (F : A ⥤ B) [F.Additive] : (plusDelta F).Effaceable :=
  DeltaFunctor.Effaceable.of_isZero_injective _ fun n I _ ↦
    (isZero_rightDerivedPlus_obj_iff F (rfl : ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ)) I).2
      (F.isZero_rightDerived_obj_injective_succ n I)

variable (P : A ⥤ B) (Q : B ⥤ C) [P.Additive] [Q.Additive] [PreservesFiniteLimits P]
  [PreservesFiniteLimits Q]

/-- The identification `R ⁰(Q ∘ P) = Q ∘ P = Q ∘ R ⁰P` of left exact functors. -/
def coEdgeZero : (P ⋙ Q).rightDerivedPlus 0 ⟶ P.rightDerivedPlus 0 ⋙ Q :=
  haveI := comp_preservesFiniteLimits P Q
  (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (P ⋙ Q)).hom ≫
    Functor.whiskerRight (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso P).inv Q

/-- **The co-edge morphism `R ⁱ(Q ∘ P) ⟶ Q ∘ R ⁱP`**: the extension of the degree-zero
identification to a family of natural transformations commuting with the connecting
morphisms. -/
def coEdge (n : ℕ) : (P ⋙ Q).rightDerivedPlus n ⟶ P.rightDerivedPlus n ⋙ Q :=
  (DeltaFunctor.DeltaFamily.postcomp (plusDelta P) Q).liftFamily (plusDelta (P ⋙ Q))
    (coEdgeZero P Q) n

/-- In degree zero the co-edge morphism is the identification `R ⁰(Q ∘ P) = Q ∘ R ⁰P`. -/
theorem coEdge_zero : coEdge P Q 0 = coEdgeZero P Q := rfl

/-- **The co-edge morphism commutes with the connecting morphisms**: for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, the connecting morphism of `R ⁱ(Q ∘ P)` followed by the co-edge
morphism is the co-edge morphism followed by `Q` of the connecting morphism of `R ⁱP`. -/
@[reassoc]
theorem canonicalδ_comp_coEdge {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    canonicalδ (P ⋙ Q) hS n ≫ (coEdge P Q (n + 1)).app S.X₁ =
      (coEdge P Q n).app S.X₃ ≫ Q.map (canonicalδ P hS n) :=
  (DeltaFunctor.DeltaFamily.postcomp (plusDelta P) Q).δ_comp_liftFamily
    (F := plusDelta (P ⋙ Q)) (coEdgeZero P Q) hS n

end Stacks.DerivedIndexing

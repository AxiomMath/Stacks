module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Right derived functors along an exact functor preserving injectives

Let `P : A ⥤ B` be an exact additive functor between abelian categories which preserves
injective objects, and let `Q : B ⥤ D` be additive. Then `P` carries an injective resolution of
`X` to an injective resolution of `P X`, so `Rⁿ Q (P X) = Rⁿ (Q ∘ P) (X)`, naturally in `X`. If
moreover `Q ∘ P` is identified with `E ∘ F` for an additive `F` and an exact `E`, then
`Rⁿ Q ∘ P ≅ E ∘ Rⁿ F`.

## Main definitions

* `Stacks.Cohomology.RightDerivedEdgeIso.edgeIsoOfExact`: the edge morphism
  `Rⁿ Q ∘ P ⟶ Rⁿ (Q ∘ P)` as a natural isomorphism, for exact `P` preserving injectives.
* `Stacks.Cohomology.RightDerivedEdgeIso.rightDerivedIsoOfExactOfIso`: the natural isomorphism
  `P ⋙ Rⁿ Q ≅ Rⁿ F ⋙ E` attached to `P ⋙ Q ≅ F ⋙ E`, for exact `P` preserving injectives and
  exact `E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedEdgeIso

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasInjectiveResolutions B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [P.PreservesInjectiveObjects] (Q : B ⥤ D) [Q.Additive]

/-- For `P` exact and preserving injectives, the edge morphism `Rⁿ Q ∘ P ⟶ Rⁿ (Q ∘ P)` is an
isomorphism. -/
instance isIso_edge_of_exact (n : ℕ) : IsIso (RightDerivedEdge.edge P Q n) := by
  have : ∀ X : A, IsIso ((RightDerivedEdge.edge P Q n).app X) := fun X ↦
    isIso_edge_app P Q X n fun q hq _ ↦ P.isZero_rightDerived_of_exact X q hq
  exact NatIso.isIso_of_isIso_app _

/-- **The edge morphism along an exact functor preserving injectives is an isomorphism**:
`Rⁿ Q ∘ P ≅ Rⁿ (Q ∘ P)`, naturally. -/
def edgeIsoOfExact (n : ℕ) : P ⋙ Q.rightDerived n ≅ (P ⋙ Q).rightDerived n :=
  asIso (RightDerivedEdge.edge P Q n)

/-- The forward morphism of `edgeIsoOfExact P Q n` is the edge morphism. -/
@[simp]
lemma edgeIsoOfExact_hom (n : ℕ) :
    (edgeIsoOfExact P Q n).hom = RightDerivedEdge.edge P Q n :=
  rfl

variable {D' : Type u₄} [Category.{v₄} D'] [Abelian D'] (F : A ⥤ D') [F.Additive]
  (E : D' ⥤ D) [E.Additive] [E.PreservesHomology]

/-- **Right derived functors commute with an exact change of categories.** If `P` is exact and
preserves injectives, `E` is exact and `P ⋙ Q ≅ F ⋙ E`, then `P ⋙ Rⁿ Q ≅ Rⁿ F ⋙ E`, naturally. -/
def rightDerivedIsoOfExactOfIso (e : P ⋙ Q ≅ F ⋙ E) (n : ℕ) :
    P ⋙ Q.rightDerived n ≅ F.rightDerived n ⋙ E :=
  edgeIsoOfExact P Q n ≪≫ Functor.rightDerivedIsoOfNatIso e n ≪≫ Functor.rightDerivedCompIso F E n

end Stacks.Cohomology.RightDerivedEdgeIso

end

module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge

/-!
# The co-edge morphism of a composite in degree zero

Let `P : A ⥤ B` and `Q : B ⥤ D` be additive functors between abelian categories with enough
injectives, `Q` left exact. In degree zero the co-edge morphism
`R⁰(Q ∘ P) X ⟶ Q (R⁰ P X)` of `Stacks.Cohomology.RightDerivedCoEdge.secondEdge` is compatible with
the canonical maps out of `(Q ∘ P) X` and `P X`.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.toRightDerivedZero_comp_secondEdge`: the canonical map
  `(Q ∘ P) X ⟶ R⁰(Q ∘ P) X` followed by the co-edge morphism is `Q` of the canonical map
  `P X ⟶ R⁰ P X`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  [HasInjectiveResolutions A] (P : A ⥤ B) [P.Additive] (Q : B ⥤ D) [Q.Additive]
  [PreservesFiniteLimits Q]

omit [HasInjectiveResolutions A] [PreservesFiniteLimits Q] in
/-- The canonical map into the degree-zero cycles of `Q ∘ P` applied to an injective resolution
factors through `Q` of the canonical map for `P`. -/
public theorem toRightDerivedZero'_comp {X : A} (I : InjectiveResolution X) :
    I.toRightDerivedZero' (P ⋙ Q) =
      Q.map (I.toRightDerivedZero' P) ≫
        mapCycles Q ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0 := by
  refine (cancel_mono (HomologicalComplex.iCycles _ 0)).1 ?_
  refine (I.toRightDerivedZero'_comp_iCycles (P ⋙ Q)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (Q.map (I.toRightDerivedZero' P) ≫ ·)
    (mapCycles_i Q ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0).symm)
  refine Eq.trans ?_ (Q.map_comp _ _)
  exact congrArg Q.map (I.toRightDerivedZero'_comp_iCycles P).symm

/-- **The co-edge morphism in degree zero**: the canonical map `(Q ∘ P) X ⟶ R⁰(Q ∘ P) X`
followed by the co-edge morphism is `Q` applied to the canonical map `P X ⟶ R⁰ P X`. -/
public theorem toRightDerivedZero_comp_secondEdge (X : A) :
    (P ⋙ Q).toRightDerivedZero.app X ≫ (secondEdge P Q 0).app X =
      Q.map (P.toRightDerivedZero.app X) := by
  have h := secondEdge_app_eq P Q 0 (injectiveResolution X)
  rw [InjectiveResolution.toRightDerivedZero_eq (injectiveResolution X) (P ⋙ Q),
    InjectiveResolution.toRightDerivedZero_eq (injectiveResolution X) P,
    toRightDerivedZero'_comp]
  refine (Category.assoc _ _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Q.map_comp _ _).symm
  refine congrArg (Q.map ((injectiveResolution X).toRightDerivedZero' P) ≫ ·) ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  exact h.trans (Q.map_comp _ _).symm

end Stacks.Cohomology.RightDerivedCoEdge

end

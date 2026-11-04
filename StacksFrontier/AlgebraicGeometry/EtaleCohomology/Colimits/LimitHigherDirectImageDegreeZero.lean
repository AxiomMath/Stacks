module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.HigherBaseChangeDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDimensionShift

/-!
# Higher direct images along a limit in degree zero

The direct image of abelian sheaves on small étale sites along a morphism of schemes is left
exact, so it is identified with its degree-zero right derived functor. This file records that
identification as a natural isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.directImageZeroIso` — `f_* ≅ R⁰f_*`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.directImageZeroIso_hom_naturality` — the
  identification is natural.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)

/-- The identification `T ≅ R⁰T` of the left exact direct image of abelian sheaves along a
morphism of schemes with its degree-zero right derived functor:
`Stacks.RightDerivedPlus.rightDerivedZeroUnit` followed by the comparison of the two indexings. -/
def directImageZeroIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtalePushforwardAb f).obj F ≅ ((smallEtalePushforwardAb f).rightDerived 0).obj F :=
  haveI : PreservesFiniteLimits (smallEtalePushforwardAb f) :=
    have := (smallEtaleAdjunctionAb f).rightAdjoint_preservesLimits
    inferInstance
  haveI := Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit (smallEtalePushforwardAb f) F
  asIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb f) F) ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb f) 0).symm.app F

/-- The components of `Stacks.EtaleCohomology.LimitHigherDirectImage.directImageZeroIso`. -/
theorem directImageZeroIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (directImageZeroIso f F).hom =
      Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb f) F ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb f) 0).inv.app F :=
  rfl

/-- `Stacks.EtaleCohomology.LimitHigherDirectImage.directImageZeroIso` is natural. -/
theorem directImageZeroIso_hom_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G) :
    (smallEtalePushforwardAb f).map φ ≫ (directImageZeroIso f G).hom =
      (directImageZeroIso f F).hom ≫ ((smallEtalePushforwardAb f).rightDerived 0).map φ := by
  rw [directImageZeroIso_hom, directImageZeroIso_hom,
    reassoc_of% Stacks.DerivedFunctor.rightDerivedZeroUnit_naturality, Category.assoc]
  exact congrArg (_ ≫ ·)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb f) 0).inv.naturality φ)

end Stacks.EtaleCohomology.LimitHigherDirectImage

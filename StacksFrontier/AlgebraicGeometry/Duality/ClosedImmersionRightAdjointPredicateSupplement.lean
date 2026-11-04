module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicate
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedAtModel
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherentAnyModel

/-!
# `D⁺_QCoh` and the conclusion of [Stacks, Tag 0A9X]

The bounded-below part `D⁺_QCoh(𝒪_Z)` of the quasi-coherent derived category of a scheme, and,
for a closed immersion `i : Z ⟶ W`, the property of a candidate right adjoint of `Ri_*` that it
agrees on `D⁺_QCoh(𝒪_W)` with `R𝓗om_{𝒪_W}(𝒪_Z, -)`, both at a given model of the derived category.

## Main definitions

* `Stacks.Duality.isBoundedBelowQuasiCoherentAtModel`: the bounded-below objects of `D_QCoh(𝒪_Z)`.
* `Stacks.Duality.quasiCoherentDerivedCategoryPlusAtModel`: the category `D⁺_QCoh(𝒪_Z)`.
* `Stacks.Duality.IsDerivedSheafHomRightAdjointAtModel`: the conclusion of [Stacks, Tag 0A9X] for
  one closed immersion and one candidate right adjoint.

## References

* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe w u

namespace Stacks.Duality

attribute [local instance] HasDerivedCategory.standard in
/-- The bounded-below objects of `D_QCoh(𝒪_Z)`, as a property of its objects. -/
abbrev isBoundedBelowQuasiCoherentAtModel (Z : Scheme.{u}) [HasDerivedCategory.{w} Z.Modules] :
    ObjectProperty (quasiCoherentDerivedCategory Z) :=
  fun K => DerivedCategoryB.IsBoundedBelow K.obj

/-- `D⁺_QCoh(𝒪_Z)`: the bounded-below objects of the quasi-coherent derived category of a
scheme, as a category, at the model of the derived category given by the instance parameter. -/
abbrev quasiCoherentDerivedCategoryPlusAtModel (Z : Scheme.{u}) [HasDerivedCategory.{w} Z.Modules] :
    Type (u + 1) :=
  ObjectProperty.FullSubcategory (isBoundedBelowQuasiCoherentAtModel Z)

attribute [local instance] HasDerivedCategory.standard in
/-- **The conclusion of [Stacks, Tag 0A9X] for one closed immersion `i : Z ⟶ W` and one
candidate right adjoint `a` of `Ri_*`:** on the bounded-below part of `D_QCoh(𝒪_W)` the functor
`a` agrees with the right derived functor of sheaf Hom with exact support of
[Stacks, Tag 0A76], that is, with `R𝓗om_{𝒪_W}(𝒪_Z, -)`.

Both sides are compared after the fully faithful inclusion into the ambient `D(𝒪_Z)`. -/
def IsDerivedSheafHomRightAdjointAtModel {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    [instZ : HasDerivedCategory.{w} Z.Modules] [instW : HasDerivedCategory.{w} W.Modules]
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z) : Prop :=
  Nonempty
    ((ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel W) ⋙ a ⋙
        (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
          (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι) ≅
      (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel W) ⋙
        (DerivedCategoryB.derivedCategoryB (A := W.Modules)
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι ⋙
        (@Stacks.Duality.AnyModel.derivedSheafHomExactSupport
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i) instW instZ)))

end Stacks.Duality

end

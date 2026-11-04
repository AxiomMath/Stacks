module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IndependenceOfDerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Relatively perfect objects on an algebraic space

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
flat and locally of finite presentation. An object `E` of `D(𝒪_X)` is *perfect relative to `Y`*,
or *`Y`-perfect*, if `E` is pseudo-coherent (Stacks 08FT) and `E` locally has finite Tor
dimension as an object of `D(f⁻¹𝒪_Y)` (Stacks 08FZ). This is [Stacks, Tag 0DKN].

The derived tensor product against which finite Tor dimension is measured is *the* derived tensor
product of each slice of the small étale site of `X`, ringed by `f⁻¹𝒪_Y`: the one constructed by
Stacks 06YU from K-flat resolutions, `Stacks.SheafOfModules.canonicalDerivedTensorProduct`. The
notion does not depend on this choice: for every family of derived tensor products on the slices
the two notions agree.

## Main definitions

* `AlgebraicGeometry.Space.IsRelativelyPerfect`: the objects of `D(𝒪_X)` perfect relative to `Y`.

## Main results

* `AlgebraicGeometry.Space.isRelativelyPerfect_iff_isPerfectRelativeTo`: relative perfectness
  agrees with `AlgebraicGeometry.Space.IsPerfectRelativeTo` measured against *any* family of
  derived tensor products on the slices.
* `AlgebraicGeometry.Space.isRelativelyPerfect_iff_isPerfectRelativeToCanonical`: it agrees with
  `AlgebraicGeometry.Space.IsPerfectRelativeToCanonical`.

## Implementation notes

The only instance arguments are the derived categories `D(𝒪_X)`, `D(f⁻¹𝒪_Y)` and those of the
slices of `(X_étale, f⁻¹𝒪_Y)`, the standing convention for unbounded derived categories in this
development. Sheafification and local bijectivity on the slices of the small étale site are the
instances `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over_addCommGrpCat` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`, and the composition of
the sheaf condition with `forget₂ RingCat AddCommGrpCat` there is Mathlib's
`CategoryTheory.hasSheafCompose_of_preservesMulticospan`; additivity of the slice
tensor bifunctors is `Stacks.SheafOfModules.Tensor.sheafTensor_additive` and
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive`, and the existence of their total
complexes is `Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor`.

The slices of `AlgebraicGeometry.Space.inverseImageRingedSite` are
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, whose objects live one universe above their
morphisms and sections; Stacks 06YU and Stacks 06YS hold in that generality, so the canonical
derived tensor product exists on each of them.

Flatness and local finite presentation of `f` are hypotheses of the definition which do not enter
the formula.

## References

* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u d e

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is flat and locally of
finite presentation. An object `E` of `D(𝒪_X)` is *perfect relative to `Y`*, or *`Y`-perfect*,
if `E` is pseudo-coherent and `E` locally has finite Tor dimension as an object of `D(f⁻¹𝒪_Y)`.

`E` is read as an object of `D(f⁻¹𝒪_Y)` through restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`, and
finite Tor dimension on the slice of `(X_étale, f⁻¹𝒪_Y)` over `U` is measured against the derived
tensor product of that slice constructed by Stacks 06YU. -/
@[stacks 0DKN "Y-perfect objects: pseudo-coherent, and locally of finite tor dimension over \
f⁻¹𝒪_Y for the derived tensor product of 06YU; independent of that choice by \
isRelativelyPerfect_iff_isPerfectRelativeTo"]
def IsRelativelyPerfect
    (_hflat : IsFlat B S hS f.hom)
    (_hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E ∧
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E)

/-- **Relative perfectness does not depend on the derived tensor products.** An object of
`D(𝒪_X)` is perfect relative to `Y` if and only if it satisfies
`AlgebraicGeometry.Space.IsPerfectRelativeTo` for an arbitrary family `T` of derived tensor
products on the slices of `(X_étale, f⁻¹𝒪_Y)`. -/
theorem isRelativelyPerfect_iff_isPerfectRelativeTo
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsRelativelyPerfect B S hS f hflat hlfp E ↔ IsPerfectRelativeTo B S hS f hflat hlfp T E :=
  and_congr_right fun _ =>
    Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_congr _ T _

/-- Relative perfectness is `AlgebraicGeometry.Space.IsPerfectRelativeToCanonical`. -/
theorem isRelativelyPerfect_iff_isPerfectRelativeToCanonical
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsRelativelyPerfect B S hS f hflat hlfp E ↔
      IsPerfectRelativeToCanonical B S hS f hflat hlfp E :=
  Iff.rfl

end AlgebraicGeometry.Space

end

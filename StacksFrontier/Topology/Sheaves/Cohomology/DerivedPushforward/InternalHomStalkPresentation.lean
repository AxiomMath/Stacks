module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoefficientPointInclusion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnePointModules
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk

/-!
# The point of a ringed space, presented as a one-point ringed space over it

`Stacks.Cohomology.DerivedInternalHomStalk.StalkPresentation X x` presents the point `x` as a
one-point ringed space `Y = {x}` with structure sheaf `𝒪_{X,x}`, with the inclusion `Y ⟶ X`, an
identification `D(𝒪_Y) ≌ D(𝒪_{X,x})`, and two compatibilities of that identification — with
derived pullback along `Y ⟶ X`, and with the derived internal hom of `Y`.

For an arbitrary ringed space `X` and an arbitrary point `x` this file produces the one-point
ringed space, the inclusion, the flatness of the inclusion, and the derived identification
`D(𝒪_Y) ≌ D(𝒪_{X,x})` given by the one-point description of modules;
`stalkPresentationOfCompatibilities` assembles a `StalkPresentation X x` from the two
compatibilities `StalkPullbackComparison` and `InternalHomComparison` at that identification.
A presentation at the stalk identification is
`Stacks.Cohomology.DerivedInternalHomStalk.pointStalkPresentation`.

The space is `Stacks.AssociatedSheaf.coefficientPoint`, the skyscraper one-point ringed space, and
the inclusion is `Stacks.AssociatedSheaf.fromCoefficientPoint`.  The identification is the
one-point description of sheaves of modules, `Stacks.AssociatedSheaf.onePointEquivalence`, carried
to unbounded derived categories by `Dualizing.mapDerivedCategoryEquivalenceOfEquivalence`.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomStalk.pointSpace`: the one-point ringed space
  `Y = ({x}, 𝒪_{X,x})`.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointHom`: the inclusion `Y ⟶ X`.
* `Stacks.Cohomology.DerivedInternalHomStalk.stalkRingEquiv`: the two spellings of `𝒪_{X,x}` — the
  `CommRingCat`-valued stalk of the structure sheaf, and the `RingCat`-valued stalk of the sheaf of
  rings underlying it, which is the one the stalk functor on sheaves of modules produces — agree.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointModulesEquiv`: `Mod(𝒪_Y) ≌ Mod(𝒪_{X,x})`.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointDerivedEquiv`: **the identification
  `D(𝒪_Y) ≌ D(𝒪_{X,x})`.**
* `Stacks.Cohomology.DerivedInternalHomStalk.StalkPullbackComparison` and
  `Stacks.Cohomology.DerivedInternalHomStalk.InternalHomComparison`: the two compatibilities at
  `pointDerivedEquiv`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomStalk.stalkPresentationOfCompatibilities`: **a
  `StalkPresentation X x` from the two compatibilities**, for every ringed space `X` and
  every point `x`.

## Implementation notes

*The two spellings of the stalk ring.*  `StalkPresentation.equiv` lands in
`D(ModuleCat (stalkRing X x))`, and `stalkRing X x` is the `RingCat`-valued stalk of
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, while `coefficientPoint` is indexed by a
`CommRingCat` and so by the `CommRingCat`-valued stalk `X.presheaf.stalk x`.  The two differ by
`SemilinearStalk.commStalkRingEquiv`, the comparison coming from the fact that
`forget₂ CommRingCat RingCat` preserves the filtered colimit computing a stalk.  Rather than
transport the space, which would mean rebuilding the inclusion and its flatness, the comparison is
absorbed into the identification: `pointModulesEquiv` is the one-point description followed by
restriction of scalars along `stalkRingEquiv`.  So `pointHom` is `fromCoefficientPoint` with no
transport, and `base_pt` and `stalkMap_isIso` are that file's lemmas applied verbatim.

*Additivity.*  `Dualizing.mapDerivedCategoryEquivalenceOfEquivalence` wants both directions of
`pointModulesEquiv` additive.  Neither is additive by construction, but an equivalence preserves
binary products, so `CategoryTheory.Functor.additive_of_preserves_binary_products` gives the
functor and `CategoryTheory.Equivalence.inverse_additive` then gives the inverse.

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Cohomology.DerivedInternalHomStalk

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback and the derived internal hom name the structure sheaf of a ringed space
-- differently, by `structureSheafRing` and by `Stacks.SheafOfModules.Tensor.ringSheaf`; the two
-- are the same sheaf of rings by `rfl`, and the statements below mix them.
-- `structureSheafRing` is `@[instance_reducible]`, so it is already unfolded both by instance
-- search and at `implicit` transparency, but its reduct stops at an explicit-constructor
-- projection while `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`;
-- these two Mathlib definitions are the gap between them.  This is the list
-- `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk` carries, and it
-- is needed here for the same reason: `StalkPullbackComparison` and the `stalkIso` field it is
-- handed to compose the derived pullback, named at the first spelling, with functors named at
-- the second.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

/-! ### The one-point ringed space over `X` at `x` -/

/-- **The one-point ringed space `Y = ({x}, 𝒪_{X,x})`**: the skyscraper one-point ringed space with
value the stalk of the structure sheaf at `x`. -/
abbrev pointSpace : RingedSpace.{u, u} := coefficientPoint (X.presheaf.stalk x)

/-- **The inclusion `Y ⟶ X`** of the one-point ringed space at `x`, acting on sections by taking
germs at `x`.  This is `Stacks.AssociatedSheaf.fromCoefficientPoint`. -/
abbrev pointHom : pointSpace X x ⟶ X := fromCoefficientPoint X x

/-- The one-point space has only its point. -/
theorem pointSpace_unique_pt (p : (pointSpace X x).carrier) : p = PUnit.unit := rfl

/-- The inclusion sends the point to `x`. -/
theorem pointHom_base_pt :
    (ConcreteCategory.hom (pointHom X x).hom.base) PUnit.unit = x :=
  fromCoefficientPoint_base_pt X x

/-! ### The identification `D(𝒪_Y) ≌ D(𝒪_{X,x})` -/

/-- **The two spellings of the local ring `𝒪_{X,x}` agree.**  The `RingCat`-valued stalk of the
sheaf of rings underlying the structure sheaf — the spelling the stalk functor on sheaves of
modules produces, and the one `stalkRing` names — is the `CommRingCat`-valued stalk of the
structure sheaf, because `forget₂ CommRingCat RingCat` preserves the filtered colimit computing a
stalk. -/
abbrev stalkRingEquiv : stalkRing X x ≃+* ToType (X.presheaf.stalk x) :=
  SemilinearStalk.commStalkRingEquiv X.presheaf x

/-- **Sheaves of modules on the one-point space are modules over `𝒪_{X,x}`.**  The one-point
description `Stacks.AssociatedSheaf.onePointEquivalence`, followed by restriction of scalars along
`stalkRingEquiv` to reach the spelling of the local ring that `StalkPresentation` is stated at. -/
def pointModulesEquiv :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (pointSpace X x) ≌
      ModuleCat.{u} (stalkRing X x) :=
  (onePointEquivalence (ToType (X.presheaf.stalk x))).symm.trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (stalkRingEquiv X x))

/-- `pointModulesEquiv` is additive: an equivalence preserves binary products. -/
instance pointModulesEquiv_functor_additive : (pointModulesEquiv X x).functor.Additive :=
  (pointModulesEquiv X x).functor.additive_of_preserves_binary_products

/-- The inverse of `pointModulesEquiv` is additive, the functor being so. -/
instance pointModulesEquiv_inverse_additive : (pointModulesEquiv X x).inverse.Additive :=
  inferInstance

/-- **The identification `D(𝒪_Y) ≌ D(𝒪_{X,x})`**, the field `StalkPresentation.equiv` asks for:
`pointModulesEquiv` carried to unbounded derived categories.  Both directions are exact, being
equivalences, so each induces a functor on derived categories and the two remain inverse. -/
def pointDerivedEquiv :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
        (pointSpace X x)) ≌
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (pointModulesEquiv X x)

/-! ### The two compatibilities, and the assembly -/

/-- **The first compatibility**: derived pullback along the inclusion `Y ⟶ X`, read
through `pointDerivedEquiv`, is the derived stalk at `x`.  See the implementation notes. -/
abbrev StalkPullbackComparison :=
  derivedPullbackFunctor (pointHom X x) ⋙ (pointDerivedEquiv X x).functor ≅ derivedStalk X x

/-- **The second compatibility**: `pointDerivedEquiv` carries the derived internal hom
of `Y` to `RHom` over `𝒪_{X,x}`.  See the implementation notes. -/
abbrev InternalHomComparison :=
  Functor.uncurry.obj (Stacks.SheafOfModules.derivedSheafHom (pointSpace X x).sheaf) ⋙
      (pointDerivedEquiv X x).functor ≅
    (pointDerivedEquiv X x).functor.op.prod (pointDerivedEquiv X x).functor ⋙
      stalkDerivedHom X x

/-- **A presentation of the point from the two compatibilities.**  Every other field of
`StalkPresentation X x` is constructed here, for an arbitrary ringed space `X` and an arbitrary
point `x`: the one-point ringed space is `pointSpace`, the inclusion is `pointHom`, its flatness is
`Stacks.AssociatedSheaf.isIso_stalkMap_fromCoefficientPoint`, and the identification
`D(𝒪_Y) ≌ D(𝒪_{X,x})` is `pointDerivedEquiv`. -/
def stalkPresentationOfCompatibilities (stalkIso : StalkPullbackComparison X x)
    (homIso : InternalHomComparison X x) :
    StalkPresentation X x where
  space := pointSpace X x
  pt := PUnit.unit
  unique_pt := pointSpace_unique_pt X x
  hom := pointHom X x
  base_pt := pointHom_base_pt X x
  stalkMap_isIso := inferInstance
  equiv := pointDerivedEquiv X x
  stalkIso := stalkIso
  homIso := homIso

end Stacks.Cohomology.DerivedInternalHomStalk

end

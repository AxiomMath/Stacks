module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleQuasicoherentDerivedChain

/-!
# The four categories of Stacks 0H06 are triangulated, and the equivalences between them exact

Stacks 0H06 asserts *canonical exact equivalences between the following triangulated categories*

1. `D_QCoh(𝒪_F)`,
2. `D_QCoh(F_{affine,étale}, 𝒪_F)`,
3. `D_QCoh(F_{affine}, 𝒪_F)`, and
4. `QC(F_{affine}, 𝒪_F)`,

for `F` an algebraic space over a scheme `S`.  The categories and the three equivalences between
them are built in `StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleQuasicoherentDerivedChain.lean`
as plain categories and plain equivalences.  This file supplies the two things the source's
wording asks for on top of that: each of (1)–(4) is a *full triangulated subcategory* of the
derived category it sits in, and each of the three equivalences is *exact*, i.e. its functor
commutes with the translation and carries distinguished triangles to distinguished triangles.

## Main results

* `AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedAffineEtaleChain`: each of
  (1)–(4) is a full triangulated subcategory, as the four
  `CategoryTheory.ObjectProperty.IsTriangulated` facts for the object properties cutting them
  out.
* `AlgebraicGeometry.Space.commShiftQuasicoherentDerivedAffineEtaleChartEquivalence`,
  `AlgebraicGeometry.Space.commShiftAffineEtaleChartQuasicoherentDerivedChaoticEquivalence`,
  `AlgebraicGeometry.Space.commShiftAffineEtaleChartChaoticQuasicoherentQCEquivalence`: the
  three equivalences `(1) ≌ (2)`, `(2) ≌ (3)`, `(3) ≌ (4)` commute with the translation `[1]`.
  These are instances, so they are the shift-compatibility that every statement about the
  exactness of one of the equivalences is read over, here and downstream.
* `AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedAffineEtaleChartEquivalence`,
  `AlgebraicGeometry.Space.isTriangulated_affineEtaleChartQuasicoherentDerivedChaoticEquivalence`
  and
  `AlgebraicGeometry.Space.isTriangulated_affineEtaleChartChaoticQuasicoherentQCEquivalence`:
  the three equivalences carry distinguished triangles to distinguished triangles.
* `AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedAffineEtaleChainEquivalences`: the
  three together, which with the shift-compatibilities above is the exactness the tag asserts.
* `AlgebraicGeometry.Space.isTriangulatedEquivalence_quasicoherentDerivedAffineEtaleChain`: the
  same exactness in Mathlib's bundled form, each of the three being a
  `CategoryTheory.Equivalence.IsTriangulated`.

## Main definitions

* `CategoryTheory.ObjectProperty.commShiftOfCompι` and
  `CategoryTheory.ObjectProperty.isTriangulated_of_compι`: a functor into a full triangulated
  subcategory commutes with the translation and is triangulated as soon as the ambient functor
  it covers does, which is how all three equivalences here are handled.

## The argument

Nothing here repeats the construction of the equivalences; the triangulated structure is
transported, in the order (4), (3), (2), (1), along the identifications already proved.

* (4) `QC(F_{affine}, 𝒪_F)` is a triangulated subcategory outright: that is Stacks 0GYW,
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isTriangulated`.
* (3) is the same subcategory of `D(F_{affine}, 𝒪_F)` as (4), by Stacks 0GZR in the form
  `AlgebraicGeometry.Space.isQC_iff_hasQuasicoherentCohomology_affineEtaleChartChaotic`, so it
  inherits the structure.
* (2) is the subcategory of Stacks 0GZS, by
  `AlgebraicGeometry.Space.isCartesianPushforward_affineEtale_iff`, and that one is the preimage
  of (4) under the triangulated functor `Rε_*`
  (`Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward_isTriangulated`).  The
  preimage of a triangulated subcategory under a triangulated functor is triangulated, so (2)
  needs no weak Serre class of its own.
* (1) is the preimage of (2) under the derived functor of restriction to the affine charts,
  which is exact; the identification of the two object properties is
  `AlgebraicGeometry.Space.derivedCategoryB_inverseImage_affineEtaleRestrictionEquivalence`,
  the degree-zero input being
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModulePushforward_iff`.

Taking the preimages rather than the weak Serre classes is what keeps all four unconditional at
the module universe of the chain: the extension clause of Stacks 03M1 is available outright only
at the module universe of the schemes
(`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_schemeUniverse`), whereas the
chain is read at module universe `max (u + 1) w`.

For the equivalences, each of the three functors is an `CategoryTheory.ObjectProperty.lift` of
the ambient functor it covers — of the identity for `(3) ≌ (4)`, of `Rε_*` for `(2) ≌ (3)`, of
the derived restriction for `(1) ≌ (2)` — so `CategoryTheory.ObjectProperty.commShiftOfCompι`
and `CategoryTheory.ObjectProperty.isTriangulated_of_compι` apply with the identification of the
composite with `ObjectProperty.ι` that the chain already proves.

## Implementation notes

`CategoryTheory.Functor.IsTriangulated` reads a functor's preservation of distinguished triangles
over a `CategoryTheory.Functor.CommShift` structure, which it takes as an instance.  The three
shift-compatibilities here are therefore declared as instances rather than as plain definitions:
a statement that one of the equivalences preserves distinguished triangles is then read over the
compatibility registered for it, and not over one introduced inside that statement's own type.

The `CategoryTheory.HasDerivedCategory` instance on `𝒪_F`-modules that the statements about (1)
mention is the standard model, which is what
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` is defined against; as in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleQuasicoherentDerivedChain.lean` it is
introduced by a `letI` in each statement and proof that needs it rather than as an instance of
this file.

The ambient-universe instances on sheaves of modules are removed exactly as in the chain file,
for the same reason: their module universe is stated as a `max` pattern that `max (u + 1) w`
does not match syntactically.

## References

* [Stacks Project, Tag 0H06](https://stacks.math.columbia.edu/tag/0H06)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
-/

@[expose] public section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.QuasiCoherentCohomology
open Stacks.ModulesOnACategory.ChaoticComparison

universe u w v v' u'

namespace CategoryTheory.ObjectProperty

section Transport

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

open ZeroObject in
/-- **The preimage of a full triangulated subcategory under a triangulated functor is a full
triangulated subcategory.**

The ambient functor comes first, so that the two categories and their structure are read off
its type rather than guessed.  Its shift-compatibility and triangulatedness are explicit
arguments rather than instances: for a functor between derived categories taken at two
different models of the localization they are not on the instance path, while both are
available as named results. -/
theorem isTriangulated_inverseImage_of_commShift (G : C ⥤ D) (hG : G.CommShift ℤ)
    (hGt : letI := hG; G.IsTriangulated) (Q : ObjectProperty D)
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms] :
    (Q.inverseImage G).IsTriangulated :=
  let := hG
  have := hGt
  { exists_zero := ⟨0, isZero_zero C, Q.prop_of_isZero (G.map_isZero (isZero_zero C))⟩
    isStableUnderShiftBy n := ⟨fun X hX =>
      Q.prop_of_iso ((G.commShiftIso n).symm.app X) (Q.le_shift n _ hX)⟩
    ext₂' T hT h₁ h₃ := (Q.inverseImage G).le_isoClosure _
      (Q.ext_of_isTriangulatedClosed₂ _ (G.map_distinguished T hT) h₁ h₃) }

end Transport

section Lift

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  (Q : ObjectProperty D) [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]

/-- **A functor into a full triangulated subcategory commutes with the translation as soon as the
ambient functor it covers does.**

The ambient functor `G` and its shift-compatibility are explicit arguments, and so is the
identification `F ⋙ Q.ι = G`: a derived category of modules on a site has several names (the
modules over the restricted structure sheaf, the modules over the ring sheaf of the restricted
ringed site, …) which are the same category but not the same expression, so the shift of `G` is
in general available only for one of them, and an instance argument would be looked for at the
name `F` happens to carry. -/
@[instance_reducible]
noncomputable def commShiftOfCompι (F : C ⥤ Q.FullSubcategory) (G : C ⥤ D) (hG : G.CommShift ℤ)
    (e : F ⋙ Q.ι = G) : F.CommShift ℤ :=
  letI := hG
  Functor.CommShift.ofComp (eqToIso e) ℤ

omit [Q.IsClosedUnderIsomorphisms] in
/-- **A functor into a full triangulated subcategory is triangulated as soon as the ambient
functor it covers is**, over `CategoryTheory.ObjectProperty.commShiftOfCompι`.  The inclusion of
a full triangulated subcategory is triangulated and fully faithful, so this is
`CategoryTheory.Functor.isTriangulated_iff_comp_right`. -/
theorem isTriangulated_of_compι (F : C ⥤ Q.FullSubcategory) (G : C ⥤ D) (hG : G.CommShift ℤ)
    (hGt : letI := hG; G.IsTriangulated) (e : F ⋙ Q.ι = G) :
    letI := commShiftOfCompι Q F G hG e
    F.IsTriangulated :=
  let := hG
  have := hGt
  let := commShiftOfCompι Q F G hG e
  have : NatTrans.CommShift (eqToIso e).hom ℤ := Functor.CommShift.ofComp_compatibility _ ℤ
  (Functor.isTriangulated_iff_comp_right (eqToIso e)).2 inferInstance

end Lift

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Category (4) -/

/-- **Category (4) of Stacks 0H06 is a full triangulated subcategory** of
`D(F_{affine}, 𝒪_F)`.  This is Stacks 0GYW for the base-change datum of the restricted structure
sheaf on the affine étale charts. -/
instance isTriangulated_isQC_affineEtaleBaseChangeData : ObjectProperty.IsTriangulated
    (IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF)) :=
  inferInstance

/-! ### Category (3) -/

/-- The functor of the equivalence of restriction to the affine étale charts is additive. -/
private instance additive_affineEtaleRestrictionEquivalence_functor :
    (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor.Additive :=
  ⟨rfl⟩

/-- The object properties cutting categories (3) and (4) of Stacks 0H06 out of
`D(F_{affine}, 𝒪_F)` are equal.  This is
`AlgebraicGeometry.Space.isQC_iff_hasQuasicoherentCohomology_affineEtaleChartChaotic`, Stacks
0GZR, read as an equality of object properties. -/
theorem isQC_eq_hasQuasicoherentCohomology_affineEtaleChartChaotic :
    IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF) =
      hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF :=
  funext fun K => propext
    (isQC_iff_hasQuasicoherentCohomology_affineEtaleChartChaotic.{u, w} B S hS F hF _ K)

/-- **Category (3) of Stacks 0H06 is a full triangulated subcategory** of
`D(F_{affine}, 𝒪_F)`: it is the same subcategory as (4), by Stacks 0GZR, and (4) is one by
Stacks 0GYW. -/
instance isTriangulated_hasQuasicoherentCohomology_affineEtaleChartChaotic :
    ObjectProperty.IsTriangulated
      (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF) :=
  isQC_eq_hasQuasicoherentCohomology_affineEtaleChartChaotic.{u, w} B S hS F hF ▸
    isTriangulated_isQC_affineEtaleBaseChangeData.{u, w} B S hS F hF

/-- Category (3) of Stacks 0H06 is closed under isomorphisms in `D(F_{affine}, 𝒪_F)`: it is the
same subcategory as (4), which is strictly full by Stacks 0GYW. -/
instance isClosedUnderIsomorphisms_hasQuasicoherentCohomology_affineEtaleChartChaotic :
    ObjectProperty.IsClosedUnderIsomorphisms
      (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF) :=
  isQC_eq_hasQuasicoherentCohomology_affineEtaleChartChaotic.{u, w} B S hS F hF ▸
    (inferInstance : ObjectProperty.IsClosedUnderIsomorphisms
      (IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF)))

/-! ### Category (2) -/

/-- **The subcategory of Stacks 0GZS on the affine étale site is a full triangulated
subcategory**: it is the preimage of `QC(F_{affine}, 𝒪_F)` under `Rε_*`, which is a triangulated
functor, being a right derived functor. -/
instance isTriangulated_isCartesianPushforward_affineEtale : ObjectProperty.IsTriangulated
    (IsCartesianPushforward.{w} (affineEtaleRingRestriction B S hS F hF)
      (affineEtaleBaseChangeData.{u, w} B S hS F hF)) :=
  ObjectProperty.isTriangulated_inverseImage_of_commShift
    (derivedEpsilonPushforward.{w} (affineEtaleRingRestriction B S hS F hF))
    (derivedEpsilonPushforwardCommShift.{w} (affineEtaleRingRestriction B S hS F hF))
    (derivedEpsilonPushforward_isTriangulated.{w} (affineEtaleRingRestriction B S hS F hF))
    (IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF))

/-- The object properties cutting out category (2) of Stacks 0H06 and the subcategory of
Stacks 0GZS out of `D(F_{affine,étale}, 𝒪_F)` are equal
(`AlgebraicGeometry.Space.isCartesianPushforward_affineEtale_iff`). -/
theorem isCartesianPushforward_eq_derivedCategoryB_affineEtale :
    IsCartesianPushforward.{w} (affineEtaleRingRestriction B S hS F hF)
        (affineEtaleBaseChangeData.{u, w} B S hS F hF) =
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
        max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)) :=
  funext fun K => propext (isCartesianPushforward_affineEtale_iff.{u, w} B S hS F hF K)

/-- **Category (2) of Stacks 0H06 is a full triangulated subcategory** of
`D(F_{affine,étale}, 𝒪_F)`: it is the subcategory of Stacks 0GZS, the preimage of (4) under
`Rε_*`.  No weak Serre class of quasi-coherent modules on the affine étale site is needed. -/
instance isTriangulated_affineEtaleChartQuasicoherentDerived : ObjectProperty.IsTriangulated
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
      max (u + 1) w} (affineEtaleRingRestriction B S hS F hF))) :=
  isCartesianPushforward_eq_derivedCategoryB_affineEtale.{u, w} B S hS F hF ▸
    isTriangulated_isCartesianPushforward_affineEtale.{u, w} B S hS F hF

/-! ### Category (1) -/

/-- **Categories (1) and (2) of Stacks 0H06 are cut out by corresponding object properties**:
the object property of (1) is the preimage of that of (2) under the derived functor of
restriction to the affine étale charts.  Restriction is exact, so a complex has quasi-coherent
cohomology exactly when its restriction does
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModulePushforward_iff`). -/
theorem derivedCategoryB_inverseImage_affineEtaleRestrictionEquivalence :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI : (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor.Additive :=
      ⟨rfl⟩
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
          max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (affineEtaleRingedSite B S hS F hF).O))).inverseImage
        (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
          B S hS F hF).functor.mapDerivedCategory =
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) := by
  let : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (affineEtaleRingedSite B S hS F hF).O)).IsClosedUnderIsomorphisms := inferInstance
  ext K
  exact Stacks.UniverseLift.derivedCategoryB_mapDerivedCategory_obj_iff
    (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleRingedSite B S hS F hF).O))
    (isQuasicoherentOnSite_affineEtaleModulePushforward_iff.{u, max (u + 1) w} B S hS F hF) K

/-- **Category (2) of Stacks 0H06 is a full triangulated subcategory**, with its structure sheaf
written as the ring sheaf of the affine étale ringed site.  This is
`AlgebraicGeometry.Space.isTriangulated_affineEtaleChartQuasicoherentDerived`: the two are the
same object property on the same derived category, and both spellings occur, the first in the
chain's categories and the second in the target of derived restriction. -/
theorem isTriangulated_affineEtaleRingedSiteQuasicoherentDerived :
    ObjectProperty.IsTriangulated
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleRingedSite B S hS F hF).O))) :=
  isTriangulated_affineEtaleChartQuasicoherentDerived.{u, w} B S hS F hF

/-- Category (2) of Stacks 0H06 is closed under isomorphisms, with its structure sheaf written as
the ring sheaf of the affine étale ringed site. -/
theorem isClosedUnderIsomorphisms_affineEtaleRingedSiteQuasicoherentDerived :
    ObjectProperty.IsClosedUnderIsomorphisms
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleRingedSite B S hS F hF).O))) :=
  isClosedUnderIsomorphisms_affineEtaleChartQuasicoherentDerived.{u, w} B S hS F hF

/-- **Category (1) of Stacks 0H06 is a full triangulated subcategory** of `D(𝒪_F)`, at the
module universe of the chain: it is the preimage of (2) under the derived functor of restriction
to the affine étale charts, which is exact. -/
theorem isTriangulated_quasicoherentDerivedChart :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    ObjectProperty.IsTriangulated
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) := by
  let : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  have := isTriangulated_affineEtaleRingedSiteQuasicoherentDerived.{u, w} B S hS F hF
  have := isClosedUnderIsomorphisms_affineEtaleRingedSiteQuasicoherentDerived.{u, w} B S hS F hF
  exact derivedCategoryB_inverseImage_affineEtaleRestrictionEquivalence.{u, w} B S hS F hF ▸
    ObjectProperty.isTriangulated_inverseImage_of_commShift
      (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory
      inferInstance
      (Functor.isTriangulated_of_precomp_iso
        (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
          B S hS F hF).functor.mapDerivedCategoryFactorsh)
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
        max (u + 1) w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleRingedSite B S hS F hF).O)))

/-! ### The four categories are triangulated -/

/-- **The four categories of Stacks 0H06 are full triangulated subcategories** of the derived
categories they sit in: in order, `D_QCoh(𝒪_F) ⊆ D(𝒪_F)`,
`D_QCoh(F_{affine,étale}, 𝒪_F) ⊆ D(F_{affine,étale}, 𝒪_F)`, and
`D_QCoh(F_{affine}, 𝒪_F), QC(F_{affine}, 𝒪_F) ⊆ D(F_{affine}, 𝒪_F)`.

A full triangulated subcategory is exactly what
`CategoryTheory.ObjectProperty.IsTriangulated` says: the subcategory contains a zero object, is
stable under the translation in both directions, and is closed under extensions in distinguished
triangles.  From it Mathlib derives the shift and the pretriangulated structure of the
subcategory itself, whose distinguished triangles are the triangles distinguished in the ambient
derived category, and the triangulatedness of the inclusion.  This is the triangulated structure
the tag's phrase *the following triangulated categories* refers to. -/
@[stacks 0H06 "the four categories (1) D_QCoh(O_X), (2) D_QCoh(X_affine_etale, O_X), \
(3) D_QCoh(X_affine, O_X) and (4) QC(X_affine, O_X) are full triangulated subcategories of the \
derived categories they sit in, which is the triangulated structure the tag speaks of"]
theorem isTriangulated_quasicoherentDerivedAffineEtaleChain :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    ObjectProperty.IsTriangulated
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ∧
      ObjectProperty.IsTriangulated
        (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
          max (u + 1) w} (affineEtaleRingRestriction B S hS F hF))) ∧
      ObjectProperty.IsTriangulated
        (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF) ∧
      ObjectProperty.IsTriangulated
        (IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF)) :=
  ⟨isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF,
    isTriangulated_affineEtaleChartQuasicoherentDerived.{u, w} B S hS F hF,
    isTriangulated_hasQuasicoherentCohomology_affineEtaleChartChaotic.{u, w} B S hS F hF,
    isTriangulated_isQC_affineEtaleBaseChangeData.{u, w} B S hS F hF⟩

/-! ### The three equivalences are exact -/

/-- **The equivalence of categories (3) and (4) of Stacks 0H06 commutes with the translation.**
Its functor, followed by the inclusion of `QC(F_{affine}, 𝒪_F)`, is the inclusion of
`D_QCoh(F_{affine}, 𝒪_F)`
(`AlgebraicGeometry.Space.affineEtaleChartChaoticQuasicoherentQCEquivalence_functor_comp_ι`),
and the inclusion of a full triangulated subcategory commutes with the translation.

This is the canonical shift-compatibility of the equivalence `(3) ≌ (4)`, and it is an instance:
the compatibility of the equivalence with the translation `[1]` is half of the tag's assertion
that the equivalence is *exact*, so it is a registered fact about the equivalence and not a
structure chosen inside the statement of the other half. -/
@[instance_reducible, stacks 0H06 "the equivalence (3) D_QCoh(X_affine, O_X) ≃ (4) \
QC(X_affine, O_X) commutes with the translation [1]: half of the tag's assertion that it is \
exact"]
noncomputable instance commShiftAffineEtaleChartChaoticQuasicoherentQCEquivalence :
    (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).functor.CommShift ℤ :=
  ObjectProperty.commShiftOfCompι (IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF))
    (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).functor
    (ObjectProperty.ι (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF))
    inferInstance
    (affineEtaleChartChaoticQuasicoherentQCEquivalence_functor_comp_ι.{u, w} B S hS F hF)

/-- **The equivalence of categories (3) and (4) of Stacks 0H06 is exact**: its functor carries
distinguished triangles to distinguished triangles, over
`AlgebraicGeometry.Space.commShiftAffineEtaleChartChaoticQuasicoherentQCEquivalence`, which is
the instance found here rather than a structure introduced in this statement.  It covers
the inclusion of `D_QCoh(F_{affine}, 𝒪_F)` into `D(F_{affine}, 𝒪_F)`, which is triangulated. -/
theorem isTriangulated_affineEtaleChartChaoticQuasicoherentQCEquivalence :
    (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).functor.IsTriangulated :=
  ObjectProperty.isTriangulated_of_compι
    (IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF))
    (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).functor
    (ObjectProperty.ι (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF))
    inferInstance inferInstance
    (affineEtaleChartChaoticQuasicoherentQCEquivalence_functor_comp_ι.{u, w} B S hS F hF)

/-- **The equivalence of categories (2) and (3) of Stacks 0H06 commutes with the translation.**
Its functor, followed by the inclusion of `D_QCoh(F_{affine}, 𝒪_F)`, is the inclusion of
`D_QCoh(F_{affine,étale}, 𝒪_F)` followed by `Rε_*`
(`AlgebraicGeometry.Space.affineEtaleChartQuasicoherentDerivedChaoticEquivalence_functor_comp_ι`),
and `Rε_*` commutes with the translation
(`Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforwardCommShift`).

This is the canonical shift-compatibility of the equivalence `(2) ≌ (3)`, and it is an instance,
for the reason given at
`AlgebraicGeometry.Space.commShiftAffineEtaleChartChaoticQuasicoherentQCEquivalence`. -/
@[instance_reducible, stacks 0H06 "the equivalence (2) D_QCoh(X_affine_etale, O_X) ≃ \
(3) D_QCoh(X_affine, O_X) commutes with the translation [1]: half of the tag's assertion that it \
is exact"]
noncomputable instance commShiftAffineEtaleChartQuasicoherentDerivedChaoticEquivalence :
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F
      hF).functor.CommShift ℤ :=
  letI := derivedEpsilonPushforwardCommShift.{w} (affineEtaleRingRestriction B S hS F hF)
  ObjectProperty.commShiftOfCompι
    (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF)
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF).functor
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (affineEtaleRingRestriction B S hS F hF))) ⋙
      derivedEpsilonPushforward.{w} (affineEtaleRingRestriction B S hS F hF))
    (Functor.CommShift.comp _ _)
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence_functor_comp_ι.{u, w} B S hS F hF)

/-- **The equivalence of categories (2) and (3) of Stacks 0H06 is exact**, over
`AlgebraicGeometry.Space.commShiftAffineEtaleChartQuasicoherentDerivedChaoticEquivalence`: it
covers the inclusion of `D_QCoh(F_{affine,étale}, 𝒪_F)` followed by `Rε_*`, both of which are
triangulated, the second by
`Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward_isTriangulated`. -/
theorem isTriangulated_affineEtaleChartQuasicoherentDerivedChaoticEquivalence :
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F
      hF).functor.IsTriangulated :=
  let := derivedEpsilonPushforwardCommShift.{w} (affineEtaleRingRestriction B S hS F hF)
  have := derivedEpsilonPushforward_isTriangulated.{w} (affineEtaleRingRestriction B S hS F hF)
  ObjectProperty.isTriangulated_of_compι
    (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF)
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF).functor
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (affineEtaleRingRestriction B S hS F hF))) ⋙
      derivedEpsilonPushforward.{w} (affineEtaleRingRestriction B S hS F hF))
    (Functor.CommShift.comp _ _) inferInstance
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence_functor_comp_ι.{u, w} B S hS F hF)

/-- **The equivalence of categories (1) and (2) of Stacks 0H06 commutes with the translation.**
Its functor, followed by the inclusion of `D_QCoh(F_{affine,étale}, 𝒪_F)`, is the inclusion of
`D_QCoh(𝒪_F)` followed by the derived functor of restriction to the affine charts
(`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChartEquivalence_functor_comp_ι`), and
the derived functor of an exact functor commutes with the translation.

This is the canonical shift-compatibility of the equivalence `(1) ≌ (2)`, and it is an instance,
for the reason given at
`AlgebraicGeometry.Space.commShiftAffineEtaleChartChaoticQuasicoherentQCEquivalence`.  The
derived category of `𝒪_F`-modules it is read over is the standard model, introduced by the `letI`
of the first line as everywhere in the chain; that `letI` names the *category*, not the
shift-compatibility, and the goal it is found at carries the same one. -/
@[instance_reducible, stacks 0H06 "the equivalence (1) D_QCoh(O_X) ≃ \
(2) D_QCoh(X_affine_etale, O_X) commutes with the translation [1]: half of the tag's assertion \
that it is exact"]
noncomputable instance commShiftQuasicoherentDerivedAffineEtaleChartEquivalence :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).functor.CommShift ℤ :=
  letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  haveI : (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor.Additive :=
    ⟨rfl⟩
  haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
  letI hG : (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ⋙
      (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory).CommShift ℤ :=
    Functor.CommShift.comp _ _
  ObjectProperty.commShiftOfCompι
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
      max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)))
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).functor
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ⋙
      (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory)
    hG
    (quasicoherentDerivedAffineEtaleChartEquivalence_functor_comp_ι.{u, w} B S hS F hF)

/-- **The equivalence of categories (1) and (2) of Stacks 0H06 is exact**, over
`AlgebraicGeometry.Space.commShiftQuasicoherentDerivedAffineEtaleChartEquivalence`: it covers the
inclusion of `D_QCoh(𝒪_F)` followed by the derived functor of restriction to the affine charts,
which is triangulated because restriction is exact
(`CategoryTheory.Functor.isTriangulated_of_precomp_iso` applied to
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`).

The triangulated structure of the two ambient derived categories is supplied through the
triangulatedness of that composite rather than left to instance search: `D(F_{affine,étale},
𝒪_F)` has two names here, the modules over the restricted structure sheaf and the modules over
the ring sheaf of the affine étale ringed site, and a search started from the first of them does
not come back. -/
theorem isTriangulated_quasicoherentDerivedAffineEtaleChartEquivalence :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).functor.IsTriangulated :=
  let : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  have := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
  let hG : (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ⋙
      (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory).CommShift ℤ :=
    Functor.CommShift.comp _ _
  have hGt : (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ⋙
      (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory).IsTriangulated :=
    have : (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory.IsTriangulated :=
      Functor.isTriangulated_of_precomp_iso
        (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
          B S hS F hF).functor.mapDerivedCategoryFactorsh
    inferInstance
  have addC : ∀ n : ℤ, (shiftFunctor
      (QuasicoherentDerivedCategory.{u, max (u + 1) w} B S hS F hF) n).Additive :=
    fun _ => inferInstance
  have addD : ∀ n : ℤ, (shiftFunctor (DerivedCategory
      (SheafOfModules.{max (u + 1) w} (affineEtaleRingRestriction B S hS F hF))) n).Additive :=
    fun _ => inferInstance
  @ObjectProperty.isTriangulated_of_compι _ _ _ _ _ _ _ addC _ _ _ _ addD _
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
      max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)))
    (isTriangulated_affineEtaleChartQuasicoherentDerived.{u, w} B S hS F hF)
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).functor
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ⋙
      (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory)
    hG hGt
    (quasicoherentDerivedAffineEtaleChartEquivalence_functor_comp_ι.{u, w} B S hS F hF)

/-- **The three equivalences of Stacks 0H06 are exact.**  For an algebraic space `F` over `S`, the
canonical equivalences

1. `D_QCoh(𝒪_F) ≌ D_QCoh(F_{affine,étale}, 𝒪_F)`, induced by restriction to the affine charts,
2. `D_QCoh(F_{affine,étale}, 𝒪_F) ≌ D_QCoh(F_{affine}, 𝒪_F)`, given by `Rε_*` for the change
   from the étale to the chaotic topology, and
3. `D_QCoh(F_{affine}, 𝒪_F) ≌ QC(F_{affine}, 𝒪_F)`, the identity of the common full subcategory
   of `D(F_{affine}, 𝒪_F)`,

are exact functors of triangulated categories: each carries distinguished triangles to
distinguished triangles, over the shift-compatibility of the equivalence it belongs to.  That
shift-compatibility is not chosen here: `CategoryTheory.Functor.IsTriangulated` takes the
`CategoryTheory.Functor.CommShift` structure it is read over as an instance, and the instance
found at each of the three functors is the one registered for it under this tag, namely
`AlgebraicGeometry.Space.commShiftQuasicoherentDerivedAffineEtaleChartEquivalence`,
`AlgebraicGeometry.Space.commShiftAffineEtaleChartQuasicoherentDerivedChaoticEquivalence` and
`AlgebraicGeometry.Space.commShiftAffineEtaleChartChaoticQuasicoherentQCEquivalence`.  So both
halves of *exact* — compatibility with the translation `[1]` and preservation of distinguished
triangles — are registered facts about the three equivalences.

Together with
`AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedAffineEtaleChain`, which says that
the four categories are full triangulated subcategories of the derived categories they sit in,
and `AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChain`, which is the chain of
equivalences itself, this is the assertion of the tag;
`AlgebraicGeometry.Space.isTriangulatedEquivalence_quasicoherentDerivedAffineEtaleChain` states
the same exactness in Mathlib's bundled form. -/
@[stacks 0H06 "the three equivalences of the chain are exact: (1) D_QCoh(O_X) ≃ \
(2) D_QCoh(X_affine_etale, O_X), (2) ≃ (3) D_QCoh(X_affine, O_X) and (3) ≃ \
(4) QC(X_affine, O_X) each carry distinguished triangles to distinguished triangles, over the \
compatibilities with the translation [1] registered for them under this tag"]
theorem isTriangulated_quasicoherentDerivedAffineEtaleChainEquivalences :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).functor.IsTriangulated ∧
      (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F
        hF).functor.IsTriangulated ∧
      (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F
        hF).functor.IsTriangulated :=
  ⟨isTriangulated_quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF,
    isTriangulated_affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF,
    isTriangulated_affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF⟩

/-! ### The three equivalences are triangulated equivalences

Mathlib bundles the two halves of exactness for an equivalence of triangulated categories as
`CategoryTheory.Equivalence.IsTriangulated`: it is
`CategoryTheory.Adjunction.IsTriangulated` for the adjunction of the equivalence, whose fields
are that the unit and counit commute with the translation and that both the functor and the
inverse are triangulated.  Stating the tag's exactness in that form asks, over the
shift-compatibility of each functor registered above, for the induced one on the inverse
(`CategoryTheory.Equivalence.commShiftInverse`) and for their compatibility
(`CategoryTheory.Equivalence.commShift_of_functor`), which is where the three pairs of instances
below come from. -/

/-- The inverse of the equivalence `(3) ≌ (4)` of Stacks 0H06 commutes with the translation, by
the shift-compatibility of its functor. -/
noncomputable instance commShiftInverseAffineEtaleChartChaoticQuasicoherentQCEquivalence :
    (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).inverse.CommShift ℤ :=
  (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).commShiftInverse ℤ

/-- The shift-compatibilities of the functor and the inverse of the equivalence `(3) ≌ (4)` of
Stacks 0H06 agree: its unit and counit commute with the translation. -/
instance commShiftCompatAffineEtaleChartChaoticQuasicoherentQCEquivalence :
    (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).CommShift ℤ :=
  (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).commShift_of_functor ℤ

/-- The inverse of the equivalence `(2) ≌ (3)` of Stacks 0H06 commutes with the translation, by
the shift-compatibility of its functor. -/
noncomputable instance commShiftInverseAffineEtaleChartQuasicoherentDerivedChaoticEquivalence :
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w}
      B S hS F hF).inverse.CommShift ℤ :=
  (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF).commShiftInverse ℤ

/-- The shift-compatibilities of the functor and the inverse of the equivalence `(2) ≌ (3)` of
Stacks 0H06 agree: its unit and counit commute with the translation. -/
instance commShiftCompatAffineEtaleChartQuasicoherentDerivedChaoticEquivalence :
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF).CommShift ℤ :=
  (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w}
    B S hS F hF).commShift_of_functor ℤ

/-- The inverse of the equivalence `(1) ≌ (2)` of Stacks 0H06 commutes with the translation, by
the shift-compatibility of its functor. -/
noncomputable instance commShiftInverseQuasicoherentDerivedAffineEtaleChartEquivalence :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).inverse.CommShift ℤ :=
  letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
  (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).commShiftInverse ℤ

/-- The shift-compatibilities of the functor and the inverse of the equivalence `(1) ≌ (2)` of
Stacks 0H06 agree: its unit and counit commute with the translation. -/
instance commShiftCompatQuasicoherentDerivedAffineEtaleChartEquivalence :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).CommShift ℤ :=
  letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
  (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).commShift_of_functor ℤ

/-- **The three equivalences of Stacks 0H06 are exact equivalences of triangulated categories**,
in Mathlib's bundled form: for an algebraic space `F` over `S`, each of

1. `D_QCoh(𝒪_F) ≌ D_QCoh(F_{affine,étale}, 𝒪_F)`,
2. `D_QCoh(F_{affine,étale}, 𝒪_F) ≌ D_QCoh(F_{affine}, 𝒪_F)`, and
3. `D_QCoh(F_{affine}, 𝒪_F) ≌ QC(F_{affine}, 𝒪_F)`

is a `CategoryTheory.Equivalence.IsTriangulated`: its functor and its inverse both commute with
the translation `[1]`, those two compatibilities agree on the unit and the counit, and both
carry distinguished triangles to distinguished triangles.  This is the tag's phrase *canonical
exact equivalences between the following triangulated categories* with nothing left implicit:
the triangulated structure of the four categories is
`AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedAffineEtaleChain`, the equivalences
are `AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChain`, and exactness is this. -/
@[stacks 0H06 "each of the three equivalences (1) D_QCoh(O_X) ≃ (2) D_QCoh(X_affine_etale, O_X), \
(2) ≃ (3) D_QCoh(X_affine, O_X) and (3) ≃ (4) QC(X_affine, O_X) is an exact equivalence of \
triangulated categories: functor and inverse both commute with the translation [1], compatibly \
on unit and counit, and both preserve distinguished triangles"]
theorem isTriangulatedEquivalence_quasicoherentDerivedAffineEtaleChain :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).IsTriangulated ∧
      (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF).IsTriangulated ∧
      (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).IsTriangulated :=
  let : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  have := isTriangulated_quasicoherentDerivedChart.{u, w} B S hS F hF
  ⟨Equivalence.IsTriangulated.mk' _
      (isTriangulated_quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF),
    Equivalence.IsTriangulated.mk' _
      (isTriangulated_affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF),
    Equivalence.IsTriangulated.mk' _
      (isTriangulated_affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF)⟩

end AlgebraicGeometry.Space

end

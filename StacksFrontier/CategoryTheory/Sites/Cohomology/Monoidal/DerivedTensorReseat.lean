module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# `D(Mod(O))` monoidal with Tag 06YU's derived tensor product as its tensor product

Stacks Tag 0FPT asks for a symmetric monoidal structure on `D(Mod(O))` whose tensor product
*is* the derived tensor product and whose unit *is* the structure sheaf in degree zero — not
merely isomorphic to them.  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` has the right
  isomorphism class
but the wrong terms: its tensor product is Mathlib's localized tensor bifunctor and its unit
is the image of the unit of `Comp(Mod(O))`.

This file re-seats it.  `CategoryTheory.MonoidalCategory.reseat`, fed
`Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso` and
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso`, produces a
monoidal structure on `D(Mod(O))` whose curried tensor product is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` and whose unit is
`(DerivedCategory.singleFunctor (Mod R) 0).obj (SheafOfModules.unit O)`, both by `rfl`.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso`: the unit of
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` is the
  structure sheaf in degree zero.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`,
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`: the
  re-seated symmetric monoidal structure.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison`: on K-flat complexes its tensor
  product is the total
  tensor product.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal`,
  `Stacks.SheafOfModules.DerivedMonoidal.tensorUnit_canonicalDerivedMonoidal`: the two on-the-nose
    equalities the
  source statement asks for.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_hom`: the comparison is Tag 06YU's own
  `comparison`, so
  it is the canonical one rather than an unspecified isomorphism.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_naturality`: it is natural in both
  complexes.

## Implementation notes

`D(Mod(O))` carries two monoidal structures here,
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` and the
re-seated one, and neither is an instance; every declaration below therefore names the one it
means, either by `@`-application or by a `letI` in its statement.

Nothing is re-proved.  `canonicalUnitIso` is `CochainComplex.KFlatMonoidal.derivedUnitIso`
re-ascribed: `DerivedCategory.singleFunctorIsoCompQ` is `Iso.refl`, so
`(DerivedCategory.singleFunctor (Mod R) 0).obj M` and
`DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Mod R) 0).obj M)` are the same term,
and Tag 0FPQ's `unit_eq_structureSheaf` is `rfl`.  Likewise `canonicalComparison` is Tag
06YU's `comparison` re-ascribed, the re-seated `tensorObj` being
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` applied, by construction.  The
  naturality is the
merged naturality field of Tag 06YU after `MonoidalCategory.tensorHom_def`, which for the
re-seated structure is the composite of the two bifunctor actions by definition.

## What this file does not contain

Two of the clauses Stacks Tag 0FPT records are not stated here, and no declaration in this
file carries the project tag for 0FPT:

* the compatibility of `canonicalComparison` with the **braiding** — that the Koszul symmetry
  of `Comp(Mod(O))` induces the symmetry of the re-seated structure as an equation;
* the compatibility of `canonicalComparison` with the **associator**.

Both hold by construction, each constraint being a localization of the corresponding
constraint of `Comp(Mod(O))`, and both are now proved as checkable equations —
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding` and
`canonicalComparison_associator` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseatConstraints.lean`.
They are not stated here because their proof needs two things from further down the import
graph: the component formula for `monoidalTensorCanonicalIso` at a pair of K-flat complexes,
`CochainComplex.KFlatMonoidal.derivedTensorCompare_comp_comparison`, which identifies the
comparison this file hands its consumers with
`CochainComplex.KFlatMonoidal.derivedTensorIso`; and the coherence of the latter,
`CochainComplex.KFlatMonoidal.associator_derivedTensorIso` and `braiding_derivedTensorIso`.
The transport across the re-seating is
`CategoryTheory.MonoidalCategory.reseat_associator_comp` and
`reseatSymmetric_braiding_comp`, which rest on a lemma computing the braiding of
`CategoryTheory.MonoidalCategory.reseatBraided` as the conjugate of the given braiding by
`CategoryTheory.MonoidalCategory.reseatIso`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **The unit of the monoidal derived category of Tag 0FPT is the structure sheaf in degree
zero.**  This is `CochainComplex.KFlatMonoidal.derivedUnitIso`, read with the single-object
functor of `DerivedCategory` in place of `DerivedCategory.Q` of the single-object functor of
`CochainComplex`: `DerivedCategory.singleFunctorIsoCompQ` is `Iso.refl`, and Tag 0FPQ's
`unit_eq_structureSheaf` is `rfl`. -/
def canonicalUnitIso :
    letI := derivedMonoidal R
    𝟙_ (DerivedModules R) ≅
      (DerivedCategory.singleFunctor (Mod R) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :=
  CochainComplex.KFlatMonoidal.derivedUnitIso (Mod R) (exists_kFlat_resolution R)

/-- **The derived category of modules on a ringed site is monoidal with the derived tensor
product of Tag 06YU as its tensor product and the structure sheaf in degree zero as its
unit**, both on the nose.  The coherence is that of
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`,
transported along `Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso` and
`Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso` by
  `CategoryTheory.MonoidalCategory.reseat`. -/
@[instance_reducible]
def canonicalDerivedMonoidal : MonoidalCategory (DerivedModules R) :=
  @reseat (DerivedModules R) _ (derivedMonoidal R) _ _
    (monoidalTensorCanonicalIso R) (canonicalUnitIso R)

/-- **The tensor product of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` is the
  derived tensor
bifunctor of Tag 06YU**, as an equality of bifunctors, so the identification holds on
morphisms as well as objects. -/
theorem curriedTensor_canonicalDerivedMonoidal :
    @curriedTensor (DerivedModules R) _ (canonicalDerivedMonoidal R) =
      Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R :=
  @curriedTensor_reseat (DerivedModules R) _ (derivedMonoidal R) _ _
    (monoidalTensorCanonicalIso R) (canonicalUnitIso R)

/-- **The unit of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` is the structure
  sheaf in degree
zero**, as an equality of objects. -/
theorem tensorUnit_canonicalDerivedMonoidal :
    @tensorUnit (DerivedModules R) _ (canonicalDerivedMonoidal R).toMonoidalCategoryStruct =
      (DerivedCategory.singleFunctor (Mod R) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :=
  @tensorUnit_reseat (DerivedModules R) _ (derivedMonoidal R) _ _
    (monoidalTensorCanonicalIso R) (canonicalUnitIso R)

/-- **`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` is symmetric**, with the
  commutativity
constraint induced by the Koszul symmetry of complexes. -/
@[instance_reducible]
def canonicalDerivedSymmetric :
    @SymmetricCategory (DerivedModules R) _ (canonicalDerivedMonoidal R) :=
  @reseatSymmetric (DerivedModules R) _ (derivedMonoidal R) _ _ (derivedSymmetric R)
    (monoidalTensorCanonicalIso R) (canonicalUnitIso R)

/-- **On K-flat complexes the tensor product of
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` is
the total tensor product of complexes.**  This is Tag 06YU's K-flat comparison verbatim: the
re-seated tensor product is Tag 06YU's bifunctor by construction, so no transport is
needed. -/
def canonicalComparison (K L : Complexes R) (hK : Stacks.SheafOfModules.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat R L) :
    letI := canonicalDerivedMonoidal R
    DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj (K ⊗ L) :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison K L hK hL

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison` *is* the comparison of the
  canonical derived tensor
product of Tag 06YU, not merely an isomorphism with the same source and target. -/
theorem canonicalComparison_hom (K L : Complexes R) (hK : Stacks.SheafOfModules.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat R L) :
    (canonicalComparison R K L hK hL).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison K L hK hL).hom
        :=
  rfl

/-- **The K-flat comparison is natural in both complexes.**  The re-seated tensor product of
two morphisms is the composite of the two one-variable actions of Tag 06YU's bifunctor, by
`MonoidalCategory.tensorHom_def` and the definition of the re-seated structure, so this is
Tag 06YU's merged naturality field. -/
theorem canonicalComparison_naturality {K K' L L' : Complexes R} (f : K ⟶ K') (g : L ⟶ L')
    (hK : Stacks.SheafOfModules.KFlat R K) (hK' : Stacks.SheafOfModules.KFlat R K')
    (hL : Stacks.SheafOfModules.KFlat R L) (hL' : Stacks.SheafOfModules.KFlat R L') :
    letI := canonicalDerivedMonoidal R
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
        (canonicalComparison R K' L' hK' hL').hom =
      (canonicalComparison R K L hK hL).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  (congrArg (fun t ↦ t ≫ (canonicalComparison R K' L' hK' hL').hom)
      (@tensorHom_def (DerivedModules R) _ (canonicalDerivedMonoidal R) _ _ _ _
        (DerivedCategory.Q.map f) (DerivedCategory.Q.map g))).trans
    ((Category.assoc _ _ _).trans
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison_naturality f g
        hK hK' hL hL'))

end Stacks.SheafOfModules.DerivedMonoidal

end

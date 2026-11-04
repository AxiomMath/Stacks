module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleUniverseComparison
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.MixedInternalHomPullbackMap

/-!
# The canonical map of Stacks 08JP, conditionally on the mixed-universe data

Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites of
Stacks 08H7. Stacks 08JP asserts, for `E` pseudo-coherent with `F ∈ D^+(𝒪_S)` or for `E` perfect
and `F` arbitrary, that the canonical map

`ε^* RSheafHom_{𝒪_S}(E, F) ⟶ RSheafHom_𝒪(ε^* E, ε^* F)`

is an isomorphism. Both sides are defined, as
`AlgebraicGeometry.SmallEtale.raisedDerivedAssociatedModuleDerivedSheafHom` and
`AlgebraicGeometry.SmallEtale.derivedSheafHomOfAssociatedModule`, and are objects of one derived
category. This file builds **the map between them**, out of
`Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison` and the three
mixed-universe data that construction abstracts over, which are carried here as hypotheses. It
does not prove the map is an isomorphism, and the hypotheses of 08JP on `E` and `F` are therefore
not used: the map itself is defined for arbitrary `E` and `F`, exactly as the canonical map of
Stacks 08I3/08JF is.

## The model of the derived category, and why a comparison is needed

The two sides are built with *two different* chosen models of the derived category of
`𝒪_S`-modules on the Zariski site. `Stacks.SheafOfModules.derivedSheafHom`, the derived internal
Hom the left-hand side is built from, is stated in a file pinning `HasDerivedCategory.standard`,
so its morphisms are in `Type (u + 1)`. The pullback `ε^*`,
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleFunctor`, is stated with the ambient
instances, where the global instance `SheafOfModules.hasDerivedCategory` of Tag 079Q supplies a
model with morphisms in `Type u`. The objects of the two models agree definitionally — Tag 079Q's
model shrinks the morphisms of the standard one and leaves its objects alone — which is why the
left-hand side typechecks while mixing them, but the two carry different `Category`
structures, and `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison` needs
*one* category carrying the pullback and the internal Hom at once.

The standard model is the one that carries the whole source-side package: the derived internal Hom
`Stacks.SheafOfModules.derivedSheafHom`, the derived tensor product
`Stacks.Cohomology.DerivedInternalHomPullback.internalHomTensorUncurried` and the
tensor–internal-Hom bijection of Stacks 08DI,
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquiv`, are all stated there. So the
comparison is instantiated at the standard model, with `ε^*` restated there as
`derivedAssociatedModuleFunctorStandardModel`, and
`Stacks.Injectives.mapDerivedCategoryObjIso` identifies that restatement with the ambient `ε^*` at
every object — an identification at the *same* object, which is what lets the map below start at
the left-hand side itself rather than at a transported copy of it.

## Main definitions

* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleFunctorStandardModel`: `ε^*` on the derived
  category, at the standard model of its source.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleObjModelIso`: it agrees with the ambient
  `ε^*` at every object.
* `AlgebraicGeometry.SmallEtale.derivedSheafHomPullbackComparisonAtStandardModel`: the mixed
  comparison map at the standard model.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleDerivedSheafHomComparison`: **the canonical
  map of Stacks 08JP**, from the left-hand side to the right-hand side,
  conditionally on the three mixed-universe data.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedSheafHomPullbackComparisonAtStandardModel_adjoint`: the
  transpose of the comparison is the transpose datum, which pins it down; this is the recipe
  Stacks 08I3 gives for its canonical map, read in the mixed form.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleDerivedSheafHomComparison_eq`: the map is
  the comparison at the standard model, conjugated by the two model identifications.

## What is carried as a hypothesis, and what is not proved

The three data named in the notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.MixedInternalHomPullbackMap` are
hypotheses: a derived tensor product `T₂` of an object with raised sections against one without,
the tensor–internal-Hom bijection `e₂` of Stacks 08J8/08DI in the mixed form, and the monoidality
`m` of `ε^*` against that tensor product, the mixed form of Stacks 07A4/079U. Nothing in this
development inhabits them, and nothing here claims to.

What is *not* proved is that the map is an isomorphism, which is the assertion of 08JP and the
only place its hypotheses on `E` and `F` would enter. No notion of pseudo-coherence and no notion
of strict perfection is used below, so the question of which of the parallel definitions in this
tree is meant does not arise here; it arises only for the isomorphism.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
  Stacks.Cohomology.DerivedInternalHomPullback

universe u

namespace AlgebraicGeometry.SmallEtale

attribute [local instance 2000] HasDerivedCategory.standard

-- The source-side derived tensor product `internalHomTensorUncurried` is stated on
-- `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S.toRingedSpace`, i.e. at the
-- `Stacks.SheafOfModules.Tensor.ringSheaf S.toRingedSpace.sheaf` spelling of the structure sheaf,
-- while the instances carrying `Category (DerivedCategory _)` on it are keyed at the
-- `structureSheafRing` spelling. The two are the same sheaf of rings by `rfl`, but
-- `structureSheafRing` is semireducible and so is not unfolded when the goal is keyed into the
-- instance discrimination tree; reaching the common normal form from the `Tensor.ringSheaf`
-- side instead needs these two Mathlib defs unfolded, which is what this does. This is the
-- same opt-in that
-- `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap`, where
-- these functors are built, carries for the same reason.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [PreservesFiniteLimits (associatedModuleOfSheaf B S hS)]

/-! ### `ε^*` at the standard model of its source -/

/-- **`ε^* : D(𝒪_S) ⥤ D(S_étale, 𝒪)` at the standard model of its source.**

This is `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleFunctor`, the derived functor of the
exact inverse image of sheaves of modules along `ε`, with the chosen model of the derived category
of `𝒪_S`-modules on the Zariski site taken to be `HasDerivedCategory.standard` rather than the
locally small one of Tag 079Q. The model enters only through `Functor.mapDerivedCategory`, which
takes it as a parameter; this is the same construction and not another one, and
`derivedAssociatedModuleObjModelIso` says so. -/
def derivedAssociatedModuleFunctorStandardModel :
    DerivedCategory (SheafOfModules.{u} S.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)) :=
  (associatedModuleOfSheaf B S hS).mapDerivedCategory

/-- **`ε^*` at the standard model agrees with the ambient `ε^*` at every object.** The comparison
of the two models is the identity on objects, so this is an isomorphism between the values of the
two functors at one and the same object of the derived category. -/
def derivedAssociatedModuleObjModelIso
    (Y : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    (derivedAssociatedModuleFunctorStandardModel B S hS).obj Y ≅
      (derivedAssociatedModuleFunctor B S hS).obj Y :=
  Stacks.Injectives.mapDerivedCategoryObjIso _ (associatedModuleOfSheaf B S hS) Y

/-! ### The canonical map of Stacks 08JP -/

section Comparison

variable
  (T₂ : DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ×
        DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)))
  (e₂ : ∀ (A : DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)))
      (K L : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))),
      (A ⟶ ((derivedSheafHomBifunctor B S hS).obj (op K)).obj L) ≃
        (T₂.obj (A, K) ⟶ (derivedModuleULift B S hS).obj L))
  (m : internalHomTensorUncurried S.toRingedSpace ⋙
        derivedAssociatedModuleFunctorStandardModel B S hS ⋙ derivedModuleULift B S hS ≅
      ((derivedAssociatedModuleFunctorStandardModel B S hS ⋙
          derivedModuleULift B S hS).prod
        (derivedAssociatedModuleFunctorStandardModel B S hS)) ⋙ T₂)

/-- The mixed comparison map of Stacks 08I3/08JF at `ε`, written at the standard model of the
source derived category: the transpose, under the mixed tensor–internal-Hom bijection `e₂` of the
target, of the mixed monoidality comparison followed by the evaluation of the source internal
Hom.

The source-side data are the library's: the derived internal Hom
`Stacks.SheafOfModules.derivedSheafHom` of the Zariski ringed site, the derived tensor product
`Stacks.Cohomology.DerivedInternalHomPullback.internalHomTensorUncurried` and the bijection of
Stacks 08DI, `Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquiv`, all of which are
stated at the standard model. -/
def derivedSheafHomPullbackComparisonAtStandardModel
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    (derivedModuleULift B S hS).obj
        ((derivedAssociatedModuleFunctorStandardModel B S hS).obj
          (((Stacks.SheafOfModules.derivedSheafHom S.sheaf).obj (op E)).obj F)) ⟶
      ((derivedSheafHomBifunctor B S hS).obj
          (op ((derivedAssociatedModuleFunctorStandardModel B S hS).obj E))).obj
        ((derivedAssociatedModuleFunctorStandardModel B S hS).obj F) :=
  MixedTranspose.homComparison (derivedAssociatedModuleFunctorStandardModel B S hS)
    (derivedModuleULift B S hS) (Stacks.SheafOfModules.derivedSheafHom S.sheaf)
    (derivedSheafHomBifunctor B S hS) (internalHomTensorUncurried S.toRingedSpace) T₂
    (tensorHomEquiv S.toRingedSpace) e₂ m E F

/-- **The transpose of the comparison is the transpose datum.** The mixed tensor–internal-Hom
bijection being a bijection, this pins the comparison down; it is the recipe Stacks 08I3 gives for
its canonical map, read in the mixed form at `ε`. -/
theorem derivedSheafHomPullbackComparisonAtStandardModel_adjoint
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    e₂ ((derivedModuleULift B S hS).obj
          ((derivedAssociatedModuleFunctorStandardModel B S hS).obj
            (((Stacks.SheafOfModules.derivedSheafHom S.sheaf).obj (op E)).obj F)))
        ((derivedAssociatedModuleFunctorStandardModel B S hS).obj E)
        ((derivedAssociatedModuleFunctorStandardModel B S hS).obj F)
        (derivedSheafHomPullbackComparisonAtStandardModel B S hS T₂ e₂ m E F) =
      MixedTranspose.homComparisonDatum
        (derivedAssociatedModuleFunctorStandardModel B S hS) (derivedModuleULift B S hS)
        (Stacks.SheafOfModules.derivedSheafHom S.sheaf)
        (internalHomTensorUncurried S.toRingedSpace) T₂
        (tensorHomEquiv S.toRingedSpace) m E F :=
  MixedTranspose.homComparison_adjoint _ _ _ _ _ _ _ _ _ E F

/-- The right-hand side of Stacks 08JP written with `ε^*` at the standard model is the
right-hand side `derivedSheafHomOfAssociatedModule`: the internal Hom of the small étale ringed site is functorial, and the two models
compute `ε^*` at `E` and at `F` isomorphically. -/
def derivedSheafHomOfAssociatedModuleModelIso
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    ((derivedSheafHomBifunctor B S hS).obj
          (op ((derivedAssociatedModuleFunctorStandardModel B S hS).obj E))).obj
        ((derivedAssociatedModuleFunctorStandardModel B S hS).obj F) ≅
      derivedSheafHomOfAssociatedModule B S hS E F :=
  ((derivedSheafHomBifunctor B S hS).mapIso
        (derivedAssociatedModuleObjModelIso B S hS E).op).symm.app
      ((derivedAssociatedModuleFunctorStandardModel B S hS).obj F) ≪≫
    ((derivedSheafHomBifunctor B S hS).obj
      (op ((derivedAssociatedModuleFunctor B S hS).obj E))).mapIso
        (derivedAssociatedModuleObjModelIso B S hS F)

/-- **The canonical map of Stacks 08JP**

`ε^* RSheafHom_{𝒪_S}(E, F) ⟶ RSheafHom_𝒪(ε^* E, ε^* F)`,

from the left-hand side to the right-hand side, conditionally on the three
mixed-universe data `T₂`, `e₂` and `m`.

It is the mixed comparison of Stacks 08I3/08JF at `ε`, taken at the standard model of the source
derived category and conjugated by the identifications of that model with the one the two sides
are stated at. That it is an isomorphism under the hypotheses of 08JP — `E` pseudo-coherent with
`F` bounded below, or `E` perfect — is not proved, and those hypotheses do not appear: as in
08I3, the map exists for arbitrary `E` and `F`. -/
def derivedAssociatedModuleDerivedSheafHomComparison
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    raisedDerivedAssociatedModuleDerivedSheafHom B S hS E F ⟶
      derivedSheafHomOfAssociatedModule B S hS E F :=
  (derivedModuleULift B S hS).map
      (derivedAssociatedModuleObjModelIso B S hS
        (((Stacks.SheafOfModules.derivedSheafHom S.sheaf).obj (op E)).obj F)).inv ≫
    derivedSheafHomPullbackComparisonAtStandardModel B S hS T₂ e₂ m E F ≫
    (derivedSheafHomOfAssociatedModuleModelIso B S hS E F).hom

/-- The canonical map of Stacks 08JP is the mixed comparison at the standard model, conjugated by
the two model identifications, by definition. -/
theorem derivedAssociatedModuleDerivedSheafHomComparison_eq
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    derivedAssociatedModuleDerivedSheafHomComparison B S hS T₂ e₂ m E F =
      (derivedModuleULift B S hS).map
          (derivedAssociatedModuleObjModelIso B S hS
            (((Stacks.SheafOfModules.derivedSheafHom S.sheaf).obj (op E)).obj F)).inv ≫
        derivedSheafHomPullbackComparisonAtStandardModel B S hS T₂ e₂ m E F ≫
        (derivedSheafHomOfAssociatedModuleModelIso B S hS E F).hom := rfl

end Comparison

end AlgebraicGeometry.SmallEtale

end

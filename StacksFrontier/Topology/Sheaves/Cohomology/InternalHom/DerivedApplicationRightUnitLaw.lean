module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingRightUnitLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafModulesMonoidal

/-!
# The right unit law of the application morphism of Stacks 08J8, and (E1) from (C) alone

Let `(X, O_X)` be a ringed space and let `M` be an object of `D(O_X)`.  The identification
`M ≅ RSheafHom(O_X, M)` of Stacks 0A91, read backwards, is a morphism
`M ⟶ RSheafHom(O_X, M)`; tensoring it with the unit and applying the evaluation
`RSheafHom(O_X, M) ⊗^L_{O_X} O_X ⟶ M` of **Stacks 08J8** gives a morphism
`M ⊗^L_{O_X} O_X ⟶ M`.  This file proves that it is the right unit constraint:

`(M ≅ RSheafHom(O_X, M))⁻¹ ▷ 𝟙_ ≫ app = (ρ_ M).hom`.

This is the equation the derived-duality cluster calls **(UR)**, recorded until now only as the
`hunit` hypothesis of
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`
and of `Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionUnitLaws` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionLaw`, whose
module docstring states it as absent.  **It is no longer absent**, and that note is superseded
for (UR); it still stands for (C).

## Main results

* `Stacks.SheafOfModules.derivedRightUnitorHom_eq_comparison`: the right unit constraint of the
  monoidal structure of Stacks 0FPT on `D(O_X)`, read on the class of a K-flat complex, is the
  K-flat comparison of Stacks 06YU at the unit in the right factor followed by the image of the
  right unit collapse of complexes.  The mirror of
  `Stacks.SheafOfModules.derivedLeftUnitorHom_eq_comparison`.
* `Stacks.SheafOfModules.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`: **the
  right unit coherence of the derived currying isomorphism of Stacks 08J9**, for *arbitrary*
  objects `A`, `M` of `D(O_X)`:

  `RSheafHom(A, -)` applied to the collapse `RSheafHom(O_X, M) ≅ M` run backwards, followed by
  the currying isomorphism, is the map induced on internal Hom by the right unit constraint
  `ρ_ A`.  The mirror of
  `Stacks.SheafOfModules.derivedStructureSheafHomIso_inv_comp_derivedCurryIso`.
* `Stacks.SheafOfModules.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit`
  and its monoidal spelling
  `derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal`:
  **(UR)**.
* `derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_compositionLaw`:
  **(E1) from the composition law (C) alone**, and
  `Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionLaw`: **the left-dual clause of
  Example 0FPC from (C) alone**.  Both are
  `…InternalHom.DerivedApplicationCompositionLaw`'s two-hypothesis forms with `hunit`
  discharged; applying them is also the check that (UR) is proved in the shape its consumers
  ask for.

## Nothing here is tagged

None of these is a clause of a published statement.  The right unit coherence is a
compatibility of Stacks 08J9 with Stacks 0FNG that neither tag asserts, and (UR) is a
compatibility of Stacks 0A91 with Stacks 08J8 that neither tag asserts either; both are steps
in the proof of the left-dual clause of Example 0FPC, which is
`Stacks.SheafOfModules.derivedDual_isLeftDual`, and of Stacks 0FVB.

## The proof, in three steps

It is `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw` run on
the right, and the three steps are the same.

1. The chain-level right unit law of Stacks 0A90 at a structure-sheaf *middle* variable,
   `AlgebraicGeometry.RingedSite.homMap_structureSheafHomIso_inv_comp_sheafHomTensorCurryIso'`,
   and its derived form at an arbitrary `A` and a K-injective `I`,
   `AlgebraicGeometry.RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`
   of `…InternalHom.DerivedCurryingRightUnitLaw`, are proved.  The first half of this file
   strips the two model comparisons of Stacks 0A97 off that derived form — the source
   identification by the naturality of `derivedSheafHomComparison` in its source variable, the
   target one by the comparison of the tensor source — and then releases the representatives:
   both sides are natural in `A` contravariantly and in `M` covariantly, and every object of
   `D(O_X)` is the class of a K-flat complex and of a K-injective one, by
   `AlgebraicGeometry.RingedSite.kFlatModelIso` and
   `AlgebraicGeometry.RingedSite.kInjectiveModelIso`.
2. The right unit constraint of `D(O_X)` is reconciled with the right unitor of complexes by
   `CategoryTheory.MonoidalCategory.reseat_rightUnitor_comp_of_unitality` applied to
   `Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison`, together with
   `CochainComplex.KFlatMonoidal.rightUnitor_derivedTensorIso`.  No new mathematics: this is
   `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_rightUnitor` re-seated at
   `Stacks.SheafOfModules.derivedTensorAsSiteDatum`.
3. (UR) follows from the right unit coherence by applying degree-zero global hypercohomology.
   Here the two naturalities of Stacks 08JA are *both* needed, unlike on the left: the
   covariant one
   (`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`) turns
   the identity of `M` into the class whose associated morphism is
   `(M ≅ RSheafHom(O_X, M))⁻¹`, and the contravariant one
   (`RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap`) turns the map
   induced by `ρ_ M` on internal Hom back into precomposition with `ρ_ M`.  On the left the
   covariant one was unnecessary because the datum came from a global section of
   `RSheafHom(K, M)`; on the right the datum is an identity, which is what the covariant
   naturality is for.

## Implementation notes

The monoidal, symmetric, preadditive and closed instances on `Mod(O_X)` are pinned here as
file-local instances for the reason `…InternalHom.DerivedApplicationUnitLaw` gives: they are
stated with the sections universe tied to the site universes as `max u v`, which instance
synthesis cannot solve against this cluster's diagonal `u` while those universes are still
metavariables.

The four diagram lemmas over an abstract category that this file shares with the left-hand
mirror — `Stacks.SheafOfModules.transport_leg`,
`Stacks.SheafOfModules.hom_bifunctor_paste`, `Stacks.SheafOfModules.paste_cancel` and
`Stacks.SheafOfModules.map_op_app_comp` — are imported from
`…InternalHom.DerivedApplicationUnitLaw` rather than restated: the chases are the same on both
sides.  Only `bifunctor_target_naturality` is new, and it is new because the collapse enters
the left-hand argument of the internal Hom on the left and the right-hand one here.

The K-flatness of `O_X[0]` is an argument of the model-level statements, so that the proof term
inside `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` is a
variable; it is discharged from `Stacks.SheafOfModules.isKFlat_single_unit` at the one place
where the statement no longer mentions it.

`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv` is a `def` and not an `abbrev`, so
the two naturalities of Stacks 08JA are restated once here at the ringed-space spelling
(`globalSectionsEquiv_naturality_target'`, `globalSectionsEquiv_naturality_source'`) by a
single `exact` each.  Rewriting across that spelling does not fire, which
`…InternalHom.DerivedApplicationUnitLaw` records; restating pays the crossing once.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FVB](https://stacks.math.columbia.edu/tag/0FVB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
  Opposite AlgebraicGeometry Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalSpace'
  Stacks.SheafOfModules.symmetricSpace' Stacks.SheafOfModules.monoidalPreadditiveSpace'
  Stacks.SheafOfModules.monoidalClosedSpace'

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.monoidalPreadditiveSheafTensor SheafOfModules.symmetricCategorySheafTensor
  SheafOfModules.monoidalClosedSheafTensor

-- `⊗_{O_X}` on `Mod(O_X)` with its universes pinned: the local instances of
-- `…InternalHom.DerivedApplicationUnitLaw`, for the reason `monoidalCategoryModUL` gives there.
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryModUL
  Stacks.SheafOfModules.monoidalClosedModUL Stacks.SheafOfModules.monoidalPreadditiveModUL
  Stacks.SheafOfModules.symmetricCategoryModUL

variable [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

attribute [local instance 10000] CochainComplex.symmetricCategory

/-- The monoidal structure on `Comp(Mod(O_X))`, as a top-priority local instance.  The default
search for it has to sift every monoidal instance this file's imports put on the K-flat
subcategories, which costs more than the statements below can afford; naming it answers the
query in one step.  It is `inferInstance`, so it is the same structure the statements elsewhere
are written over.  This is the device
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseatConstraints.lean` and
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedAssociatorComparison.lean` use, for
the same query and the same reason; here it is asked at the
`Stacks.SheafOfModules.DerivedMonoidal.Complexes Rc` spelling, which is the one the unit `𝟙_`
of the statements below is written at. -/
local instance (priority := 100000) monoidalCategoryStructComplexesRU :
    MonoidalCategoryStruct (DerivedMonoidal.Complexes Rc) := inferInstance

/-! ### Pinned spellings -/

/-- **The right unit constraint of the monoidal structure of Stacks 0FPT on `D(O_X)`**,
ascribed at the bifunctor spelling of its source: the tensor product of
`Stacks.SheafOfModules.derivedMonoidalStructure` is the derived tensor product and its unit is
the structure sheaf in degree zero, both by `rfl`, so `ρ_ K` is a morphism
`K ⊗^L_{O_X} O_X ⟶ K` on the nose.  The mirror of
`Stacks.SheafOfModules.derivedLeftUnitorHom`, pinned for the same reason: a goal carrying both
`K ⊗ 𝟙_` and the bifunctor application is not type-correct at the `implicit` transparency
level. -/
def derivedRightUnitorHom (K : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj K).obj (RingedSite.derivedStructureSheaf (ringedSite Rc)) ⟶ K :=
  letI := derivedMonoidalStructure Rc
  (ρ_ K).hom

/-- `Stacks.SheafOfModules.derivedRightUnitorHom` *is* the right unitor of
`Stacks.SheafOfModules.derivedMonoidalStructure`. -/
theorem derivedRightUnitorHom_eq (K : DerivedCategory (StructureSheafModules Rc)) :
    (letI := derivedMonoidalStructure Rc
    derivedRightUnitorHom Rc K = (ρ_ K).hom) :=
  rfl

/-- **The K-flat comparison of Stacks 06YU at the unit on the right**, ascribed at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of its target.  Only the right factor has
to be K-flat for the one-sided comparison `comparisonRight`, and the right factor here is the
structure sheaf in degree zero, so `A` need not be K-flat. -/
def unitComparisonRightHom (A : CochainComplex (StructureSheafModules Rc) ℤ)
    (hO : IsKFlat Rc (RingedSite.structureSheafComplex (ringedSite Rc))) :
    ((derivedTensor Rc).obj (DerivedCategory.Q.obj A)).obj
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) ⟶
      DerivedCategory.Q.obj
        (((Tensor.tensorComplex (ringedSite Rc).O).obj A).obj
          (RingedSite.structureSheafComplex (ringedSite Rc))) :=
  ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight A
    (RingedSite.structureSheafComplex (ringedSite Rc)) hO).hom

/-- `Stacks.SheafOfModules.unitComparisonRightHom` is the two-sided K-flat comparison of
`Stacks.SheafOfModules.derivedTensorAsSiteDatum` at the unit of `Comp(Mod(O_X))` in the right
factor.

This is the one declaration in the file that mentions both spellings of the unit --
`𝟙_ (Comp(Mod(O_X)))` and `AlgebraicGeometry.RingedSite.structureSheafComplex` -- and both
spellings of the total tensor product.  The two are `rfl`, but a goal carrying both is not
type-correct at the `implicit` transparency level, so the crossing is paid here once, by
`congrArg` on the datum's own `comparisonRight_eq_comparison` field, and nowhere else.  This is
the mirror of `Stacks.SheafOfModules.unitComparisonHom_eq`. -/
theorem unitComparisonRightHom_eq (A : CochainComplex (StructureSheafModules Rc) ℤ)
    (hA : IsKFlat Rc A)
    (hO : IsKFlat Rc (RingedSite.structureSheafComplex (ringedSite Rc))) :
    unitComparisonRightHom Rc A hO =
      ((derivedTensorAsSiteDatum Rc).comparison A (𝟙_ (DerivedMonoidal.Complexes Rc)) hA
        (DerivedMonoidal.kFlat_tensorUnit_complexes Rc)).hom :=
  congrArg Iso.hom ((derivedTensorAsSiteDatum Rc).comparisonRight_eq_comparison
    A (𝟙_ (DerivedMonoidal.Complexes Rc)) hA (DerivedMonoidal.kFlat_tensorUnit_complexes Rc))

/-- **The right unit constraint of `D(O_X)` is the right unit collapse of complexes**, carried
across by the K-flat comparison of Stacks 06YU: on the class of a K-flat complex `A`,

`ρ_ (Q A) = (comparison at the unit on the right) ≫ Q (Tot(A ⊗_{O_X} O_X[0]) ≅ A)`.

This is step 2 of the module docstring, and it is a single application:
`Stacks.SheafOfModules.derivedMonoidalStructure` is `CategoryTheory.MonoidalCategory.reseat` at
`Stacks.SheafOfModules.derivedTensorMonoidalIso`, whose comparison
`Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison` computes for an arbitrary
prescribed derived tensor product, and
`CategoryTheory.MonoidalCategory.reseat_rightUnitor_comp_of_unitality` transports the right
unitality axiom `CochainComplex.KFlatMonoidal.rightUnitor_derivedTensorIso` along it.  No
coherence diagram is checked and no braiding is used: the two unitality axioms are independent
fields of a lax monoidal functor.

The mirror of `Stacks.SheafOfModules.derivedLeftUnitorHom_eq_comparison`, and of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_rightUnitor` at
`derivedTensorAsSiteDatum` rather than at Stacks 06YU's canonical datum. -/
theorem derivedRightUnitorHom_eq_comparison (A : CochainComplex (StructureSheafModules Rc) ℤ)
    (hA : IsKFlat Rc A)
    (hO : IsKFlat Rc (RingedSite.structureSheafComplex (ringedSite Rc))) :
    derivedRightUnitorHom Rc (DerivedCategory.Q.obj A) =
      unitComparisonRightHom Rc A hO ≫
        DerivedCategory.Q.map
          (RingedSite.structureSheafComplexTensorRightIso (ringedSite Rc) A).hom :=
  letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
    DerivedMonoidal.derivedMonoidal Rc
  reseat_rightUnitor_comp_of_unitality (derivedTensorMonoidalIso Rc)
    (DerivedMonoidal.canonicalUnitIso Rc)
    (DerivedCategory.Q.map
      (RingedSite.structureSheafComplexTensorRightIso (ringedSite Rc) A).hom)
    ((congrArg (fun v ↦ (reseatIso (derivedTensorMonoidalIso Rc)
            (DerivedCategory.Q.obj A)
            (DerivedCategory.Q.obj (𝟙_ (DerivedMonoidal.Complexes Rc)))).hom ≫ v)
          (unitComparisonRightHom_eq Rc A hA hO)).trans
      (DerivedMonoidal.reseatIso_comp_comparison Rc (derivedTensorAsSiteDatum Rc)
        A (𝟙_ (DerivedMonoidal.Complexes Rc)) hA
        (DerivedMonoidal.kFlat_tensorUnit_complexes Rc)))
    (CochainComplex.KFlatMonoidal.rightUnitor_derivedTensorIso (DerivedMonoidal.Mod Rc)
      (DerivedMonoidal.exists_kFlat_resolution Rc) hA)

/-! ### Diagram lemmas over an abstract category -/

/-- A leg is cancelled off the front of a composite that an isomorphism factors. This is an alias
of `Stacks.Cohomology.DualityDescent.leg_of_inv_comp`. -/
private alias leg_of_inv_comp := Stacks.Cohomology.DualityDescent.leg_of_inv_comp

/-- A square of a bifunctor contravariant in its first variable and covariant in its second,
pasted out of a naturality square in the *second* variable.  The second-variable counterpart of
`Stacks.SheafOfModules.hom_bifunctor_paste`, and the one diagram lemma of this file that the
left-hand mirror does not already have: there the collapse enters the first variable of the
internal Hom, here the second. -/
private alias bifunctor_target_naturality :=
  Stacks.Cohomology.DualityDescent.bifunctor_target_naturality

/-! ### The right unit coherence at representatives -/

/-- `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` at the structure sheaf in the
*second* factor, unfolded into the K-injective model comparison of Stacks 0A97 and the map
induced by the K-flat comparison of Stacks 06YU.  This is `rfl`; it is named so that the step
can be taken by `rw` rather than by unfolding a definition inside a larger goal.  The mirror of
`Stacks.SheafOfModules.tensorHomRepresentativeIso_unit_inv`. -/
theorem tensorHomRepresentativeIso_unit_inv_right
    (A I : CochainComplex (StructureSheafModules Rc) ℤ)
    (hO : IsKFlat Rc (RingedSite.structureSheafComplex (ringedSite Rc))) [I.IsKInjective] :
    (RingedSite.tensorHomRepresentativeIso (ringedSite Rc) A
        (RingedSite.structureSheafComplex (ringedSite Rc)) I hO).inv =
      (RingedSite.derivedSheafHomComparison (ringedSite Rc)
          (((Tensor.tensorComplex (ringedSite Rc).O).obj A).obj
            (RingedSite.structureSheafComplex (ringedSite Rc))) I).inv ≫
        ((derivedSheafHom Rc).map (unitComparisonRightHom Rc A hO).op).app
          (DerivedCategory.Q.obj I) :=
  rfl

/-- **The right-hand side of the derived right unit law, with the model comparisons stripped
off.** The K-injective model comparison of Stacks 0A97, followed by the image of the map of
internal Hom complexes induced by the right unit collapse of complexes, followed by the inverse
of the representative isomorphism of the tensor-source internal Hom, is the map induced on
derived internal Hom by the right unit constraint of `D(O_X)`.

The two inputs are the naturality of the comparison of Stacks 0A97 in its source variable,
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` at the identity of the
target, and step 2, `derivedRightUnitorHom_eq_comparison`.  The mirror of
`Stacks.SheafOfModules.derivedSheafHomComparison_comp_homMap_unitCollapse`. -/
theorem derivedSheafHomComparison_comp_homMap_unitCollapse_right
    (A I : CochainComplex (StructureSheafModules Rc) ℤ) (hA : IsKFlat Rc A)
    (hO : IsKFlat Rc (RingedSite.structureSheafComplex (ringedSite Rc))) [I.IsKInjective] :
    (RingedSite.derivedSheafHomComparison (ringedSite Rc) A I).hom ≫
        DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc)
            (RingedSite.structureSheafComplexTensorRightIso (ringedSite Rc) A).hom (𝟙 I)) ≫
          (RingedSite.tensorHomRepresentativeIso (ringedSite Rc) A
            (RingedSite.structureSheafComplex (ringedSite Rc)) I hO).inv =
      ((derivedSheafHom Rc).map (derivedRightUnitorHom Rc (DerivedCategory.Q.obj A)).op).app
        (DerivedCategory.Q.obj I) := by
  have hnat := RingedSite.derivedSheafHomComparison_naturality (ringedSite Rc)
    (RingedSite.structureSheafComplexTensorRightIso (ringedSite Rc) A).hom (𝟙 I)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  rw [← Category.assoc, ← hnat, tensorHomRepresentativeIso_unit_inv_right]
  refine (paste_cancel _ _ _).trans ?_
  refine (map_op_app_comp _ _ _ _).trans ?_
  exact congrArg (fun v ↦ ((derivedSheafHom Rc).map (Opposite.op v)).app
    (DerivedCategory.Q.obj I)) (derivedRightUnitorHom_eq_comparison Rc A hA hO).symm

/-- **The right unit coherence of Stacks 08J9 at representatives, with no model comparison left
in it.** For an arbitrary complex `A` and a K-injective `I`, the collapse
`RSheafHom(O_X, QI) ≅ QI` of `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, run
backwards inside `RSheafHom(QA, -)` and followed by the derived currying isomorphism of
Stacks 08J9, is the map induced on derived internal Hom by the right unit constraint `ρ_ (QA)`
of `D(O_X)`.

This is
`AlgebraicGeometry.RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`
with both representative isomorphisms cancelled: the source one against the naturality of the
comparison, the target one against
`derivedSheafHomComparison_comp_homMap_unitCollapse_right`. -/
theorem homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model
    (A I : CochainComplex (StructureSheafModules Rc) ℤ) (hA : IsKFlat Rc A)
    (hO : IsKFlat Rc (RingedSite.structureSheafComplex (ringedSite Rc))) [I.IsKInjective] :
    ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map
          (RingedSite.derivedStructureSheafHomIso (ringedSite Rc)
            (DerivedCategory.Q.obj I)).inv ≫
        (derivedCurryIso Rc (DerivedCategory.Q.obj A)
          (RingedSite.derivedStructureSheaf (ringedSite Rc))
            (DerivedCategory.Q.obj I)).hom =
      ((derivedSheafHom Rc).map (derivedRightUnitorHom Rc (DerivedCategory.Q.obj A)).op).app
        (DerivedCategory.Q.obj I) :=
  leg_of_inv_comp (RingedSite.derivedSheafHomComparison (ringedSite Rc) A I) _ _
    (RingedSite.tensorHomRepresentativeIso (ringedSite Rc) A
      (RingedSite.structureSheafComplex (ringedSite Rc)) I hO)
    (RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso' (ringedSite Rc)
      A I hO)
    (derivedSheafHomComparison_comp_homMap_unitCollapse_right Rc A I hA hO)

/-! ### Releasing the representatives -/

/-- At the identity in the right tensor factor, the two-variable map on derived tensor products
is the map induced by the left factor alone; the right-hand counterpart of
`Stacks.SheafOfModules.derivedTensorMap_unit_left`, pinned for the same reason. -/
theorem derivedTensorMap_unit_right
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K ⟶ K') :
    derivedTensorMap Rc k (𝟙 (RingedSite.derivedStructureSheaf (ringedSite Rc))) =
      ((derivedTensor Rc).map k).app (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  RingedSite.derivedTensorMap_id_right (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) k _

/-- **The right unit constraint of `D(O_X)` is natural**, in the pinned spelling: for
`a : A' ⟶ A` the square formed by `ρ_ A` and `ρ_ A'` commutes.  This is
`CategoryTheory.MonoidalCategory.rightUnitor_naturality`, read with right whiskering by the unit
spelled as the action of the derived tensor bifunctor -- which is what it is, by `rfl`, for a
re-seated monoidal structure. -/
theorem derivedRightUnitorHom_naturality
    {A A' : DerivedCategory (StructureSheafModules Rc)} (a : A' ⟶ A) :
    ((derivedTensor Rc).map a).app (RingedSite.derivedStructureSheaf (ringedSite Rc)) ≫
        derivedRightUnitorHom Rc A =
      derivedRightUnitorHom Rc A' ≫ a :=
  letI := derivedMonoidalStructure Rc
  MonoidalCategory.rightUnitor_naturality a

/-- **The right-hand side of the right unit coherence is natural** in the source
contravariantly and in the target covariantly: this is
`Stacks.SheafOfModules.hom_bifunctor_paste` at the naturality square of the right unit
constraint. -/
private lemma rhs_naturality_right
    {A A' M M' : DerivedCategory (StructureSheafModules Rc)} (a : A' ⟶ A) (m : M ⟶ M') :
    ((derivedSheafHom Rc).map (derivedRightUnitorHom Rc A).op).app M ≫
        derivedSheafHomMap Rc
          (((derivedTensor Rc).map a).app
            (RingedSite.derivedStructureSheaf (ringedSite Rc))) m =
      derivedSheafHomMap Rc a m ≫
        ((derivedSheafHom Rc).map (derivedRightUnitorHom Rc A').op).app M' :=
  hom_bifunctor_paste (derivedSheafHom Rc) (derivedRightUnitorHom Rc A)
    (((derivedTensor Rc).map a).app (RingedSite.derivedStructureSheaf (ringedSite Rc))) a
    (derivedRightUnitorHom Rc A') m (derivedRightUnitorHom_naturality Rc a)

/-- **The collapse `RSheafHom(O_X, M) ≅ M`, read inside `RSheafHom(A, -)`, is natural** in `A`
contravariantly and in `M` covariantly: this is `bifunctor_target_naturality` at the naturality
of `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`. -/
private lemma source_naturality_right
    {A A' M M' : DerivedCategory (StructureSheafModules Rc)} (a : A' ⟶ A) (m : M ⟶ M') :
    derivedSheafHomMap Rc a
          (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map m) ≫
        (((derivedSheafHom Rc).obj (op A')).mapIso
          (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M')).hom =
      (((derivedSheafHom Rc).obj (op A)).mapIso
          (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M)).hom ≫
        derivedSheafHomMap Rc a m :=
  bifunctor_target_naturality (derivedSheafHom Rc) a m _ _ _
    (RingedSite.derivedStructureSheafHomIso_naturality (ringedSite Rc) m)

/-- **The left-hand side of the right unit coherence is natural**, as far as the currying
isomorphism is concerned: `Stacks.SheafOfModules.derivedCurryIso_natural` at the identity of the
structure-sheaf *middle* object, with both induced maps rewritten into the one-variable
spellings `derivedSheafHomMap_unit_left` and `derivedTensorMap_unit_right`. -/
private lemma curry_naturality_right
    {A A' M M' : DerivedCategory (StructureSheafModules Rc)} (a : A' ⟶ A) (m : M ⟶ M') :
    derivedSheafHomMap Rc a
          (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map m) ≫
        (derivedCurryIso Rc A' (RingedSite.derivedStructureSheaf (ringedSite Rc)) M').hom =
      (derivedCurryIso Rc A (RingedSite.derivedStructureSheaf (ringedSite Rc)) M).hom ≫
        derivedSheafHomMap Rc
          (((derivedTensor Rc).map a).app
            (RingedSite.derivedStructureSheaf (ringedSite Rc))) m :=
  (congrArg
        (fun v ↦ derivedSheafHomMap Rc a v ≫
          (derivedCurryIso Rc A' (RingedSite.derivedStructureSheaf (ringedSite Rc)) M').hom)
        (derivedSheafHomMap_unit_left Rc m).symm).trans
    ((derivedCurryIso_natural Rc a
          (𝟙 (RingedSite.derivedStructureSheaf (ringedSite Rc))) m).trans
      (congrArg
        (fun v ↦
          (derivedCurryIso Rc A (RingedSite.derivedStructureSheaf (ringedSite Rc)) M).hom ≫
            derivedSheafHomMap Rc v m)
        (derivedTensorMap_unit_right Rc a)))

/-- **The right unit coherence of Stacks 08J9 at an arbitrary pair of objects, given models for
them.** Both sides of the equation are natural -- contravariantly in `A` by
`curry_naturality_right`, `source_naturality_right` and `rhs_naturality_right`, covariantly in
`M` by the same three -- and the map induced by the two model isomorphisms is invertible, so the
equation at `(QL, QI)` gives the equation at `(A, M)`.

The models are arbitrary: no property of the chosen ones is used beyond K-flatness of `L`,
K-injectivity of `I` and the two isomorphisms. -/
private lemma right_unit_law_of_models
    (A M : DerivedCategory (StructureSheafModules Rc))
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) (hL : IsKFlat Rc L)
    (hO : IsKFlat Rc (RingedSite.structureSheafComplex (ringedSite Rc)))
    [I.IsKInjective] (e : DerivedCategory.Q.obj L ≅ A)
    (f : DerivedCategory.Q.obj I ≅ M) :
    ((derivedSheafHom Rc).obj (op A)).map
          (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv ≫
        (derivedCurryIso Rc A (RingedSite.derivedStructureSheaf (ringedSite Rc)) M).hom =
      ((derivedSheafHom Rc).map (derivedRightUnitorHom Rc A).op).app M := by
  have hmap : ∀ {A A' B B' : DerivedCategory (StructureSheafModules Rc)} (a : A' ⟶ A) (b : B ⟶ B'),
      IsIso a → IsIso b → IsIso (derivedSheafHomMap Rc a b) := fun a b _ _ => by
    show IsIso (((derivedSheafHom Rc).map a.op).app _ ≫ ((derivedSheafHom Rc).obj (op _)).map b)
    infer_instance
  haveI := hmap (((derivedTensor Rc).map e.hom).app
    (RingedSite.derivedStructureSheaf (ringedSite Rc))) f.inv inferInstance inferInstance
  refine (cancel_mono (derivedSheafHomMap Rc
    (((derivedTensor Rc).map e.hom).app
      (RingedSite.derivedStructureSheaf (ringedSite Rc))) f.inv)).1 ?_
  refine Eq.trans (transport_leg _ _ (derivedSheafHomMap Rc e.hom f.inv)
    (derivedSheafHomMap Rc e.hom
      (((derivedSheafHom Rc).obj
        (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map f.inv)) _ _ _
    (source_naturality_right Rc e.hom f.inv)
    (curry_naturality_right Rc e.hom f.inv)) ?_
  refine Eq.trans (congrArg (fun v ↦ derivedSheafHomMap Rc e.hom f.inv ≫ v)
    (homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model Rc L I hL hO)) ?_
  exact (rhs_naturality_right Rc e.hom f.inv).symm

/-- **The right unit coherence of the derived currying isomorphism of Stacks 08J9, for
arbitrary objects of `D(O_X)`.** For all `A` and `M`,

`RSheafHom(A, (RSheafHom(O_X, M) ≅ M)⁻¹) ≫ (currying of Stacks 08J9) = RSheafHom(ρ_ A, M)`,

the collapse being `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and `ρ_ A` the
right unit constraint of the monoidal structure of Stacks 0FPT.

No hypothesis is carried: `right_unit_law_of_models` is instantiated at the chosen K-flat and
K-injective models of `A` and `M`, which exist for every object by Stacks 06YS and Stacks 0A89,
and the K-flatness of the structure sheaf in degree zero is
`Stacks.SheafOfModules.isKFlat_single_unit`.  The mirror of
`Stacks.SheafOfModules.derivedStructureSheafHomIso_inv_comp_derivedCurryIso`, and the input to
(UR) below. -/
theorem homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (A M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedSheafHom Rc).obj (op A)).map
          (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv ≫
        (derivedCurryIso Rc A (RingedSite.derivedStructureSheaf (ringedSite Rc)) M).hom =
      ((derivedSheafHom Rc).map (derivedRightUnitorHom Rc A).op).app M :=
  haveI : (RingedSite.kInjectiveModel (ringedSite Rc) M).IsKInjective :=
    RingedSite.isKInjective_kInjectiveModel (ringedSite Rc) M
  right_unit_law_of_models Rc A M (RingedSite.kFlatModel (ringedSite Rc) A)
    (RingedSite.kInjectiveModel (ringedSite Rc) M)
    (RingedSite.isKFlat_kFlatModel (ringedSite Rc) A)
    (isKFlat_single_unit (ringedSite Rc).O)
    (RingedSite.kFlatModelIso (ringedSite Rc) A)
    (RingedSite.kInjectiveModelIso (ringedSite Rc) M)

/-! ### From the right unit coherence to (UR) -/

/-- **Stacks 08JA, naturality in the target variable**, at the ringed-space spelling of the
identification.  `Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv` is a `def` and not
an `abbrev`, so a rewrite does not cross between it and
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`; restating pays the crossing
once, by `exact`. -/
private lemma globalSectionsEquiv_naturality_target'
    (L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (φ : M ⟶ M')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv Rc L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedSheafHom Rc).obj (op L)).map φ)) x) =
      derivedSheafHomGlobalSectionsEquiv Rc L M x ≫ φ :=
  RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target (ringedSite Rc) L φ x

/-- **Stacks 08JA, naturality in the source variable**, at the ringed-space spelling of the
identification, for the reason given on `globalSectionsEquiv_naturality_target'`. -/
private lemma globalSectionsEquiv_naturality_source'
    {L L' : DerivedCategory (StructureSheafModules Rc)}
    (M : DerivedCategory (StructureSheafModules Rc)) (u : L' ⟶ L)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv Rc L' M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedSheafHom Rc).map u.op).app M)) x) =
      u ≫ derivedSheafHomGlobalSectionsEquiv Rc L M x :=
  RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap (ringedSite Rc) M u x

/-- The right unit coherence `homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`, read
on degree-zero global hypercohomology and applied to a class. -/
theorem homologyMap_homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (A M : DerivedCategory (StructureSheafModules Rc))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op A)).obj M)) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map
          (((derivedSheafHom Rc).map (derivedRightUnitorHom Rc A).op).app M)) x =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map
          (derivedCurryIso Rc A (RingedSite.derivedStructureSheaf (ringedSite Rc)) M).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (((derivedSheafHom Rc).obj (op A)).map
              (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv)) x) := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp,
    homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso]

/-- **(UR) at a degree-zero global hypercohomology class of `RSheafHom(M, M)`.**  For a class
`w ∈ H⁰(X, RSheafHom(M, M))`, the morphism `M ⟶ RSheafHom(O_X, M)` that `w` names after
`RSheafHom(M, -)` is applied to the collapse run backwards, tensored with the unit and followed
by the application morphism of Stacks 08J8, is `ρ_ M` followed by the morphism `M ⟶ M` that `w`
names under Stacks 08JA.

The three inputs are `Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit`
at source `M`, `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_globalSections` (Stacks 08J8
read on global hypercohomology, i.e. the last assertion of Stacks 08J9) and the contravariant
naturality of Stacks 08JA; the right unit coherence enters through
`homologyMap_homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`. -/
theorem derivedSheafHomCounit_right_unit_law_apply
    (M : DerivedCategory (StructureSheafModules Rc))
    (w : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op M)).obj M)) : Type u)) :
    ((derivedTensor Rc).map
            (derivedSheafHomGlobalSectionsEquiv Rc M
              (((derivedSheafHom Rc).obj
                (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
              ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
                ((derivedModuleGlobalSections (ringedSite Rc)).map
                  (((derivedSheafHom Rc).obj (op M)).map
                    (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv))
                w))).app (RingedSite.derivedStructureSheaf (ringedSite Rc)) ≫
        derivedSheafHomCounit Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) M =
      derivedRightUnitorHom Rc M ≫ derivedSheafHomGlobalSectionsEquiv Rc M M w := by
  rw [derivedTensor_map_app_comp_derivedSheafHomCounit, derivedSheafHomTensorEquiv_globalSections,
    ← homologyMap_homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso]
  exact globalSectionsEquiv_naturality_source' Rc M (derivedRightUnitorHom Rc M) w

/-- **(UR), the right unit law tying Stacks 0A91 to Stacks 08J8.**  The identification
`M ≅ RSheafHom(O_X, M)` of Stacks 0A91, run backwards, tensored with the unit and followed by
the application morphism of Stacks 08J8, is the right unit constraint of `D(O_X)`:

`(M ≅ RSheafHom(O_X, M))⁻¹ ▷ 𝟙_ ≫ app = (ρ_ M).hom`.

This is `derivedSheafHomCounit_right_unit_law_apply` at the class that Stacks 08JA attaches to
the identity of `M`, whose associated morphism is the collapse run backwards by the covariant
naturality of Stacks 08JA.  It carries no hypothesis and no tag: it is a compatibility of two
published identifications, not a clause of either. -/
theorem derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit
    (M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).map
          (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv).app
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) ≫
      derivedSheafHomCounit Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) M =
    derivedRightUnitorHom Rc M := by
  have hw : derivedSheafHomGlobalSectionsEquiv Rc M M
      ((derivedSheafHomGlobalSectionsEquiv Rc M M).symm (𝟙 M)) = 𝟙 M :=
    (derivedSheafHomGlobalSectionsEquiv Rc M M).apply_symm_apply (𝟙 M)
  have htgt := globalSectionsEquiv_naturality_target' Rc M
    (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv
    ((derivedSheafHomGlobalSectionsEquiv Rc M M).symm (𝟙 M))
  rw [hw, Category.id_comp] at htgt
  refine Eq.trans (congrArg (fun v ↦ ((derivedTensor Rc).map v).app
      (RingedSite.derivedStructureSheaf (ringedSite Rc)) ≫
    derivedSheafHomCounit Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) M)
      htgt.symm) ?_
  refine Eq.trans (derivedSheafHomCounit_right_unit_law_apply Rc M
    ((derivedSheafHomGlobalSectionsEquiv Rc M M).symm (𝟙 M))) ?_
  rw [hw, Category.comp_id]

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- **(UR) in the monoidal spelling**, with right whiskering written `▷` and the right unit
constraint written `ρ_` -- the exact shape of the `hunit` hypothesis of
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`
and of `Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionUnitLaws` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionLaw`, so that
each of those can be applied to it directly.  This is
`derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit` with the two pinned
spellings undone, which is `rfl`: the `whiskerRight` field of
`CategoryTheory.MonoidalCategory.reseatStruct` is literally `(T.map f).app Y`, and the unit of
the re-seated structure is the structure sheaf in degree zero.

The whiskering is written out as
`CategoryTheory.MonoidalCategory.MonoidalCategoryStruct.whiskerRight` with its category argument
given, rather than with the `▷` notation: the collapse
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` is a ringed-site declaration, so with
the category left implicit the whiskering is elaborated over
`SheafOfModules (Tensor.ringSheaf (ringedSite Rc).O)` and the monoidal structure pinned above,
which is stated over `StructureSheafModules Rc`, is not found for it.  The term is the one `▷`
produces. -/
theorem derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal
    (M : DerivedCategory (StructureSheafModules Rc)) :
    MonoidalCategoryStruct.whiskerRight (C := DerivedCategory (StructureSheafModules Rc))
          (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv
          (𝟙_ (DerivedCategory (StructureSheafModules Rc))) ≫
        derivedSheafHomCounit Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) M =
      (ρ_ M).hom :=
  derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit Rc M

end Monoidal

/-! ### (E1) and Example 0FPC's left-dual clause, from (C) alone -/

/-- **(E1), for arbitrary `L` and `M`, from the composition law (C) alone.**  The canonical map
of Stacks 08I1 followed by the application morphism of Stacks 08J8 is the contraction against
`ev`:

`Φ_{L,M} ▷ L ≫ app = (α_ M L^∨ L).hom ≫ (M ◁ ev) ≫ (ρ_ M).hom`.

This is
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`
with its `hunit` hypothesis -- the right unit law (UR) -- discharged by
`derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit`.  The remaining
hypothesis `hcomp` is (C), the compatibility of the composition morphism of Stacks 0A8V with the
application morphism of Stacks 08J8 at intermediate object the structure sheaf; it holds for all
objects, by `Stacks.SheafOfModules.compositionApplicationLaw`.

The inner application stays the variable `ev`, for the reason
`…InternalHom.DerivedApplicationCompositionLaw` gives: its two spellings
`derivedSheafHomCounit Rc L O_X` and `Stacks.SheafOfModules.derivedDualEvaluation Rc L` are the
same term and the elaborator cannot cross between them. -/
theorem derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_compositionLaw
    (L M : DerivedCategory (StructureSheafModules Rc))
    (ev : letI := derivedMonoidalStructure Rc
      MonoidalCategoryStruct.tensorObj (C := DerivedCategory (StructureSheafModules Rc))
            (derivedDual Rc L) L ⟶
        𝟙_ (DerivedCategory (StructureSheafModules Rc)))
    (hcomp : letI := derivedMonoidalStructure Rc
      derivedSheafHomComposition Rc L
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) M ▷ L ≫
          derivedSheafHomCounit Rc L M =
        (α_ (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
            (derivedDual Rc L) L).hom ≫
          (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M ◁ ev) ≫
            derivedSheafHomCounit Rc
              (RingedSite.derivedStructureSheaf (ringedSite Rc)) M) :
    letI := derivedMonoidalStructure Rc
    derivedTensorDualToSheafHom Rc L M ▷ L ≫ derivedSheafHomCounit Rc L M =
      (α_ M (derivedDual Rc L) L).hom ≫ (M ◁ ev) ≫ (ρ_ M).hom :=
  derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws Rc L M ev hcomp
    (derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit Rc M)

/-- **The left dual of a perfect object, from the composition law (C).** For a perfect object `K`
of `D(O_X)` the pair `(η, ε)` is an exact pairing — `K^∨ = RSheafHom(K, O_X)` is a left dual of
`K` in the sense of Categories, Definition 0FFP — as soon as (C) at intermediate object the
structure sheaf holds.  This is
`Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionUnitLaws` with its `hunit` hypothesis
discharged by (UR).  (C) holds for every `K` (`Stacks.SheafOfModules.compositionApplicationLaw`),
which gives `Stacks.SheafOfModules.exactPairingDerivedDual`. -/
@[instance_reducible]
def exactPairingDerivedDualOfCompositionLaw
    (K : DerivedCategory (StructureSheafModules Rc)) (hK : (ringedSite Rc).IsPerfect K)
    (hcomp : letI := derivedMonoidalStructure Rc
      derivedSheafHomComposition Rc K
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) K ▷ K ≫
          derivedSheafHomCounit Rc K K =
        (α_ (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K)
            (derivedDual Rc K) K).hom ≫
          (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K ◁
            derivedDualEvaluation Rc K) ≫
            derivedSheafHomCounit Rc
              (RingedSite.derivedStructureSheaf (ringedSite Rc)) K) :
    letI := derivedMonoidalStructure Rc
    ExactPairing K (derivedDual Rc K) :=
  exactPairingDerivedDualOfCompositionUnitLaws Rc K hK hcomp
    (derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit Rc K)

end Stacks.SheafOfModules

end

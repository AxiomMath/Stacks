module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingUnitLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafModulesMonoidal

/-!
# The unit law of the application morphism of Stacks 08J8

Let `(X, O_X)` be a ringed space and let `K` and `M` be objects of `D(O_X)`.  A morphism
`y : O_X ⟶ RSheafHom(K, M)` names a morphism `K ⟶ M` in two ways: by the two identifications
of **Stacks 08JA**, `Hom(O_X, RSheafHom(K, M)) = H⁰(X, RSheafHom(K, M)) = Hom(K, M)`; and by
tensoring with `K` and applying the evaluation `RSheafHom(K, M) ⊗^L_{O_X} K ⟶ M` of
**Stacks 08J8**.  This file proves that the two agree:

`y ▷ K ≫ app = (λ_ K).hom ≫ (the morphism K ⟶ M that y names under Stacks 08JA)`.

This is the equation the derived-duality cluster calls **(UL)**, recorded until now only as the
`hunit` hypothesis of `Stacks.SheafOfModules.derivedDualCoevaluation_triangle`,
`Stacks.SheafOfModules.exactPairingDerivedDualOfApplicationLaws` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` and
`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CupProductAndDualityPairing`, whose module
docstrings state it as absent.  It is no longer absent, and those three hypotheses are
discharged by `derivedSheafHomCounit_unit_law_monoidal` below.

## Main results

* `Stacks.SheafOfModules.derivedLeftUnitorHom_eq_comparison`: the left unit constraint of the
  monoidal structure of Stacks 0FPT on `D(O_X)`, read on the class of a K-flat complex, is the
  K-flat comparison of Stacks 06YU at the unit followed by the image of the left unit collapse
  of complexes.
* `Stacks.SheafOfModules.derivedStructureSheafHomIso_inv_comp_derivedCurryIso`: **the unit
  coherence of the derived currying isomorphism of Stacks 08J9**, for *arbitrary* objects `K`,
  `M` of `D(O_X)`:

  `RSheafHom(O_X, -)` applied to `RSheafHom(K, M)`, collapsed by
  `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and then curried, is the map
  induced on internal Hom by the left unit constraint `λ_ K`.
* `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law` and its two monoidal spellings
  `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal` and
  `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal'`: **(UL)**.

## Nothing here is tagged

None of these is a clause of a published statement.  The unit coherence is a compatibility of
Stacks 08J9 with Stacks 0FNG that neither tag asserts, and (UL) is a compatibility of
Stacks 08JA with Stacks 08J8 that neither tag asserts either; both are steps in the proof of the
left-dual clause of Example 0FPC and of the left vertical arrow of Stacks 0FVB.  Accordingly no
declaration below carries a tag attribute.

Together with
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit`, the
canonical map of Stacks 08I1 followed by application is the contraction against `ε`, (UL) gives
the left vertical arrow of Stacks 0FVB in `Stacks.SheafOfModules.derivedDualPairingSquare`.

## The proof, in three steps

1. The chain-level unit law of Stacks 0A90 at a structure-sheaf source,
   `AlgebraicGeometry.RingedSite.structureSheafHomIso_inv_comp_sheafHomTensorCurryIso`, and its
   derived form at a K-flat `L` and a K-injective `I`,
   `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso'` of
   `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingUnitLaw`, are proved.
   The first half of this file strips the two model comparisons of Stacks 0A97 off that derived
   form — the source identification by the naturality of
   `derivedStructureSheafHomIso`, the target one by the naturality of the comparison in its
   source variable — and then releases the representatives: both sides of the resulting equation
   are natural in `K` contravariantly and in `M` covariantly, and every object of `D(O_X)` is
   isomorphic to the class of a K-flat complex and to the class of a K-injective one, by
   `AlgebraicGeometry.RingedSite.kFlatModelIso` and
   `AlgebraicGeometry.RingedSite.kInjectiveModelIso`.  The release is therefore a transport
   along two isomorphisms, not a dévissage.
2. The left unit constraint of `D(O_X)` is reconciled with the left unitor of complexes by
   `CategoryTheory.MonoidalCategory.reseat_leftUnitor_comp_of_unitality` applied to
   `Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison` — which is stated for an
   arbitrary prescribed derived tensor product, hence for
   `Stacks.SheafOfModules.derivedTensorAsSiteDatum`, the datum
   `Stacks.SheafOfModules.derivedMonoidalStructure` is seated on — together with
   `CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso`.  No new mathematics: this is
   `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_leftUnitor` re-seated, and the
   whole cost is instance pinning and the choice of spellings described below.
3. (UL) follows from the unit coherence by applying degree-zero global hypercohomology: the
   contravariant naturality of Stacks 08JA
   (`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap`)
   turns
   `(λ_ K).hom ≫ -` into the map induced by `λ_ K` on internal Hom, Stacks 08DI read on global
   hypercohomology (`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_globalSections`) turns the
   currying isomorphism into the bijection of morphism groups, and
   `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation` identifies `y ▷ K`
   followed by application with that bijection at `y`.  The covariant naturality of Stacks 08JA
   is *not* needed, contrary to the reduction recorded in `PerfectCoevaluation`: the
   identification of `H⁰(X, Z)` with `Hom(O_X, Z)` unfolds to the contravariant one at source
   the structure sheaf by `rfl`.

## Implementation notes

The monoidal, symmetric, preadditive, closed, colimit-preservation and total-tensor-complex
instances on `Mod(O_X)` are pinned here as file-local instances from the library's own
`Stacks.SheafOfModules.monoidalCategorySheafTensor` and siblings, for the reason
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace` gives: they are
stated with the sections universe tied to the site universes as `max u v`, which instance
synthesis cannot solve against this cluster's diagonal `u` while those universes are still
metavariables.  Without the monoidal one the unit of `Comp(Mod(O_X))` does not even elaborate.

Two spellings of the left unit collapse occur, `𝟙_ ⊗ L` and
`Tot(O_X[0] ⊗_{O_X} L)`, and a goal mentioning both is not type-correct at the `implicit`
transparency level, so no rewriting tactic acts on it.  The crossing is therefore paid once, in
`unitComparisonHom_eq`, and every other statement is at the `tensorComplex` spelling; this is
the discipline of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingUnitLaw`.

For the same reason the two-variable maps `Stacks.SheafOfModules.derivedSheafHomMap` and
`Stacks.SheafOfModules.derivedTensorMap` are never rewritten: their object arguments are
ascribed at `Stacks.SheafOfModules.StructureSheafModules` while the site-level declarations
expect `SheafOfModules (ringedSite Rc).ringSheaf`, so a goal mentioning them is again not
type-correct at `implicit` transparency.  Each such step is an `exact` or a `congrArg`, and the
diagram chases are lifted into private lemmas over an abstract category with every object and
morphism a variable (`inv_comp_eq_of_transport`, `transport_leg`, `hom_bifunctor_paste`,
`map_op_app_comp`, `paste_cancel`).  The last four are not `private`: the right-hand mirror
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw` runs the
same diagram chases on the other side and uses them verbatim, so they are stated here once
rather than duplicated there.

The three declarations of step 3 are split rather than inlined: the composite statement exceeds
the recursion limit of a single elaboration, and raising that limit is not available here.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
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

/-- `⊗_{O_X}` as a monoidal structure on `Mod(O_X)`, with its universes pinned.
`SheafOfModules.monoidalCategorySheafTensor`, registered above, is this very term; but it is
stated with the sections universe tied to the site universes as `max u v`, and instance search
will not solve `max ?u ?v =?= u` against this cluster's diagonal `u`, so the registration is
unreachable from a goal over `SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)`, which is what
`Stacks.SheafOfModules.DerivedMonoidal.Mod Rc` is.  Supplying the site makes it reachable.
Nothing is bridged: the type is the one `SheafOfModules.monoidalCategorySheafTensor` is already
stated at, and `Stacks.SheafOfModules.monoidalSpace'` is the same structure at the
`StructureSheafModules Rc` spelling, which remains registered beside it.  This is the device
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedCohomologyProductNaturality.lean`
uses, for the same query and the same reason; the right-hand mirror
`…InternalHom.DerivedApplicationRightUnitLaw` activates these four instances from here. -/
@[instance_reducible]
local instance monoidalCategoryModUL :
    MonoidalCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) :=
  SheafOfModules.monoidalCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `Mod(O_X)` is monoidal closed at the `DerivedMonoidal.Mod` spelling.  Pinned for the reason
`Stacks.SheafOfModules.monoidalCategoryModUL` gives: `monoidalClosedSheafTensor` is declared
`@MonoidalClosed _ _ (monoidalCategorySheafTensor R)`, hence over the `max u v` structure, so the
registration above does not answer a diagonal-`u` goal on its own. -/
@[instance_reducible]
local instance monoidalClosedModUL : MonoidalClosed (DerivedMonoidal.Mod Rc) :=
  SheafOfModules.monoidalClosedSheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `⊗_{O_X}` is bilinear on morphisms of `Mod(O_X)`, with its universes pinned, for the reason
`Stacks.SheafOfModules.monoidalCategoryModUL` gives. -/
local instance monoidalPreadditiveModUL :
    MonoidalPreadditive (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) :=
  SheafOfModules.monoidalPreadditiveSheafTensor (J := Opens.grothendieckTopology X) Rc

/-- The symmetry of `⊗_{O_X}` on `Mod(O_X)`, with its universes pinned, for the reason
`Stacks.SheafOfModules.monoidalCategoryModUL` gives. -/
local instance symmetricCategoryModUL :
    SymmetricCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) :=
  SheafOfModules.symmetricCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

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
local instance (priority := 100000) monoidalCategoryStructComplexesUL :
    MonoidalCategoryStruct (DerivedMonoidal.Complexes Rc) := inferInstance

/-! ### Pinned spellings -/

/-- **The left unit constraint of the monoidal structure of Stacks 0FPT on `D(O_X)`**,
ascribed at the bifunctor spelling of its source: the tensor product of
`Stacks.SheafOfModules.derivedMonoidalStructure` is the derived tensor product and its unit is
the structure sheaf in degree zero, both by `rfl`, so `λ_ K` is a morphism
`O_X ⊗^L_{O_X} K ⟶ K` on the nose.  Pinning it is what lets the statements below mention the
left unit constraint and the derived currying isomorphism at once: `derivedCurryIso` is built
from the derived tensor bifunctor directly, and a goal carrying both `𝟙_ ⊗ K` and the
bifunctor application is not type-correct at the `implicit` transparency level. -/
def derivedLeftUnitorHom (K : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj (RingedSite.derivedStructureSheaf (ringedSite Rc))).obj K ⟶ K :=
  letI := derivedMonoidalStructure Rc
  (λ_ K).hom

/-- `Stacks.SheafOfModules.derivedLeftUnitorHom` *is* the left unitor of
`Stacks.SheafOfModules.derivedMonoidalStructure`. -/
theorem derivedLeftUnitorHom_eq (K : DerivedCategory (StructureSheafModules Rc)) :
    (letI := derivedMonoidalStructure Rc
    derivedLeftUnitorHom Rc K = (λ_ K).hom) :=
  rfl

/-- **The K-flat comparison of Stacks 06YU at the unit on the left**, ascribed at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of its target.  Only the right factor is
assumed K-flat, so this is the one-sided comparison `comparisonRight`; on the left sits the
structure sheaf in degree zero, which is K-flat anyway. -/
def unitComparisonHom (L : CochainComplex (StructureSheafModules Rc) ℤ) (hL : IsKFlat Rc L) :
    ((derivedTensor Rc).obj (RingedSite.derivedStructureSheaf (ringedSite Rc))).obj
        (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj
        (((Tensor.tensorComplex (ringedSite Rc).O).obj
          (RingedSite.structureSheafComplex (ringedSite Rc))).obj L) :=
  ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight
    (RingedSite.structureSheafComplex (ringedSite Rc)) L hL).hom

/-- `Stacks.SheafOfModules.unitComparisonHom` is the two-sided K-flat comparison of
`Stacks.SheafOfModules.derivedTensorAsSiteDatum` at the unit of `Comp(Mod(O_X))`.

This is the one declaration in the file that mentions both spellings of the unit --
`𝟙_ (Comp(Mod(O_X)))` and `AlgebraicGeometry.RingedSite.structureSheafComplex` -- and both
spellings of the total tensor product.  The two are `rfl`, but a goal carrying both is not
type-correct at the `implicit` transparency level, so the crossing is paid here once, by
`congrArg` on the datum's own `comparisonRight_eq_comparison` field, and nowhere else. -/
theorem unitComparisonHom_eq (L : CochainComplex (StructureSheafModules Rc) ℤ)
    (hL : IsKFlat Rc L) :
    unitComparisonHom Rc L hL =
      ((derivedTensorAsSiteDatum Rc).comparison
          (𝟙_ (CochainComplex (StructureSheafModules Rc) ℤ)) L
        (DerivedMonoidal.kFlat_tensorUnit_complexes Rc) hL).hom :=
  congrArg Iso.hom ((derivedTensorAsSiteDatum Rc).comparisonRight_eq_comparison
    (𝟙_ (CochainComplex (StructureSheafModules Rc) ℤ)) L
    (DerivedMonoidal.kFlat_tensorUnit_complexes Rc) hL)

/-- **The left unit constraint of `D(O_X)` is the left unit collapse of complexes**, carried
across by the K-flat comparison of Stacks 06YU: on the class of a K-flat complex `L`,

`λ_ (Q L) = (comparison at the unit) ≫ Q (Tot(O_X[0] ⊗_{O_X} L) ≅ L)`.

This is step 2 of the module docstring, and it is a single application:
`Stacks.SheafOfModules.derivedMonoidalStructure` is `CategoryTheory.MonoidalCategory.reseat` at
`Stacks.SheafOfModules.derivedTensorMonoidalIso`, whose comparison
`Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison` computes for an arbitrary
prescribed derived tensor product, and
`CategoryTheory.MonoidalCategory.reseat_leftUnitor_comp_of_unitality` transports the left
unitality axiom `CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso` along it.  No
coherence diagram is checked and no braiding is used: the two unitality axioms are independent
fields of a lax monoidal functor.

The mirror of `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_leftUnitor`, which is
the same identification for the re-seating at Stacks 06YU's canonical datum rather than at
`derivedTensorAsSiteDatum`. -/
theorem derivedLeftUnitorHom_eq_comparison
    (L : CochainComplex (StructureSheafModules Rc) ℤ) (hL : IsKFlat Rc L) :
    derivedLeftUnitorHom Rc (DerivedCategory.Q.obj L) =
      unitComparisonHom Rc L hL ≫
        DerivedCategory.Q.map
          (RingedSite.structureSheafComplexTensorLeftIso (ringedSite Rc) L).hom :=
  letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
    DerivedMonoidal.derivedMonoidal Rc
  reseat_leftUnitor_comp_of_unitality (derivedTensorMonoidalIso Rc)
    (DerivedMonoidal.canonicalUnitIso Rc)
    (DerivedCategory.Q.map
      (RingedSite.structureSheafComplexTensorLeftIso (ringedSite Rc) L).hom)
    ((congrArg (fun v ↦ (reseatIso (derivedTensorMonoidalIso Rc)
            (DerivedCategory.Q.obj (𝟙_ (CochainComplex (StructureSheafModules Rc) ℤ)))
            (DerivedCategory.Q.obj L)).hom ≫ v)
          (unitComparisonHom_eq Rc L hL)).trans
      (DerivedMonoidal.reseatIso_comp_comparison Rc (derivedTensorAsSiteDatum Rc)
        (𝟙_ (CochainComplex (StructureSheafModules Rc) ℤ)) L
        (DerivedMonoidal.kFlat_tensorUnit_complexes Rc) hL))
    (CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso (StructureSheafModules Rc)
      (DerivedMonoidal.exists_kFlat_resolution Rc) hL)

/-! ### Diagram lemmas over an abstract category -/

/-- A retraction and a cancelling isomorphism are stripped off a commuting square. This is an
alias of `Stacks.Cohomology.DualityDescent.inv_comp_eq_of_transport`. -/
private alias inv_comp_eq_of_transport := Stacks.Cohomology.DualityDescent.inv_comp_eq_of_transport

/-- Two legs induced contravariantly by a bifunctor compose into the leg induced by their
composite.  Stated over an arbitrary category and an arbitrary bifunctor, for the reason given on
`inv_comp_eq_of_transport`. -/
lemma map_op_app_comp {D E : Type*} [Category D] [Category E]
    (F : Dᵒᵖ ⥤ E ⥤ E) {a b c : D} (x : b ⟶ a) (y : c ⟶ b) (M : E) :
    (F.map x.op).app M ≫ (F.map y.op).app M = (F.map (y ≫ x).op).app M := by
  rw [← NatTrans.comp_app, ← F.map_comp, ← op_comp]

/-- An isomorphism cancels between two legs.  Stated over an arbitrary category for the reason
given on `inv_comp_eq_of_transport`. -/
lemma paste_cancel {D : Type*} [Category D] {a b c e : D}
    (p : a ⟶ b) (i : b ≅ c) (r : b ⟶ e) :
    (p ≫ i.hom) ≫ i.inv ≫ r = p ≫ r := by
  rw [Category.assoc, Iso.hom_inv_id_assoc]

/-! ### The unit coherence at representatives -/

/-- `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` at the structure sheaf in the
first factor, unfolded into the K-injective model comparison of Stacks 0A97 and the map induced
by the K-flat comparison of Stacks 06YU.  This is `rfl`; it is named so that the step can be
taken by `rw` rather than by unfolding a definition inside a larger goal. -/
theorem tensorHomRepresentativeIso_unit_inv
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) (hL : IsKFlat Rc L)
    [I.IsKInjective] :
    (RingedSite.tensorHomRepresentativeIso (ringedSite Rc)
        (RingedSite.structureSheafComplex (ringedSite Rc)) L I hL).inv =
      (RingedSite.derivedSheafHomComparison (ringedSite Rc)
          (((Tensor.tensorComplex (ringedSite Rc).O).obj
            (RingedSite.structureSheafComplex (ringedSite Rc))).obj L) I).inv ≫
        ((derivedSheafHom Rc).map (unitComparisonHom Rc L hL).op).app
          (DerivedCategory.Q.obj I) :=
  rfl

/-- **The right-hand side of the derived unit law, with the model comparisons stripped off.**
The K-injective model comparison of Stacks 0A97, followed by the image of the map of internal Hom
complexes induced by the left unit collapse of complexes, followed by the inverse of the
representative isomorphism of the tensor-source internal Hom, is the map induced on derived
internal Hom by the left unit constraint of `D(O_X)`.

The two inputs are the naturality of the comparison of Stacks 0A97 in its source variable,
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` at the identity of the
target, and step 2, `derivedLeftUnitorHom_eq_comparison`. -/
theorem derivedSheafHomComparison_comp_homMap_unitCollapse
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) (hL : IsKFlat Rc L)
    [I.IsKInjective] :
    (RingedSite.derivedSheafHomComparison (ringedSite Rc) L I).hom ≫
        DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc)
            (RingedSite.structureSheafComplexTensorLeftIso (ringedSite Rc) L).hom (𝟙 I)) ≫
          (RingedSite.tensorHomRepresentativeIso (ringedSite Rc)
            (RingedSite.structureSheafComplex (ringedSite Rc)) L I hL).inv =
      ((derivedSheafHom Rc).map (derivedLeftUnitorHom Rc (DerivedCategory.Q.obj L)).op).app
        (DerivedCategory.Q.obj I) := by
  have hnat := RingedSite.derivedSheafHomComparison_naturality (ringedSite Rc)
    (RingedSite.structureSheafComplexTensorLeftIso (ringedSite Rc) L).hom (𝟙 I)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  rw [← Category.assoc, ← hnat, tensorHomRepresentativeIso_unit_inv]
  refine (paste_cancel _ _ _).trans ?_
  refine (map_op_app_comp _ _ _ _).trans ?_
  exact congrArg (fun v ↦ ((derivedSheafHom Rc).map (Opposite.op v)).app
    (DerivedCategory.Q.obj I)) (derivedLeftUnitorHom_eq_comparison Rc L hL).symm

/-- **The unit coherence of Stacks 08J9 at representatives, with no model comparison left in
it.** For a K-flat `L` and a K-injective `I`, the collapse
`RSheafHom(O_X, RSheafHom(QL, QI)) ≅ RSheafHom(QL, QI)` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, run backwards and followed by the
derived currying isomorphism of Stacks 08J9, is the map induced on derived internal Hom by the
left unit constraint `λ_ (QL)` of `D(O_X)`.

This is `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`
with both representative isomorphisms cancelled: the source one against the naturality of
`derivedStructureSheafHomIso`, the target one against
`derivedSheafHomComparison_comp_homMap_unitCollapse`. -/
theorem derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) (hL : IsKFlat Rc L)
    [I.IsKInjective] :
    (RingedSite.derivedStructureSheafHomIso (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj L))).obj
            (DerivedCategory.Q.obj I))).inv ≫
        (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).hom =
      ((derivedSheafHom Rc).map (derivedLeftUnitorHom Rc (DerivedCategory.Q.obj L)).op).app
        (DerivedCategory.Q.obj I) :=
  inv_comp_eq_of_transport _ _ (RingedSite.derivedSheafHomComparison (ringedSite Rc) L I) _ _
    (RingedSite.tensorHomRepresentativeIso (ringedSite Rc)
      (RingedSite.structureSheafComplex (ringedSite Rc)) L I hL)
    (RingedSite.derivedStructureSheafHomIso_naturality (ringedSite Rc)
      (RingedSite.derivedSheafHomComparison (ringedSite Rc) L I).inv)
    (RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso' (ringedSite Rc) L I hL)
    (derivedSheafHomComparison_comp_homMap_unitCollapse Rc L I hL)

/-! ### Releasing the representatives -/

instance isIsoDerivedSheafHomMapUL
    {A A' B B' : DerivedCategory (StructureSheafModules Rc)}
    (a : A' ⟶ A) (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedSheafHomMap Rc a b) := by
  change IsIso (((derivedSheafHom Rc).map a.op).app B ≫
    ((derivedSheafHom Rc).obj (op A')).map b)
  infer_instance

omit [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)] in
/-- At the identity of the structure sheaf in the source, the two-variable map on derived
internal Hom is the map induced by the target alone.  This is
`AlgebraicGeometry.RingedSite.derivedSheafHomMap_id_left` with the bifunctor spelled
`Stacks.SheafOfModules.derivedSheafHom` rather than as a projection of
`Stacks.SheafOfModules.derivedInternalHom`, so that the identification is settled once by
elaboration rather than at every rewrite. -/
theorem derivedSheafHomMap_unit_left
    {A B : DerivedCategory (StructureSheafModules Rc)} (ψ : A ⟶ B) :
    derivedSheafHomMap Rc (𝟙 (RingedSite.derivedStructureSheaf (ringedSite Rc))) ψ =
      ((derivedSheafHom Rc).obj
        (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map ψ :=
  RingedSite.derivedSheafHomMap_id_left (ringedSite Rc) (derivedInternalHom Rc) _ ψ

/-- At the identity of the structure sheaf in the left factor, the two-variable map on derived
tensor products is the map induced by the right factor alone; the tensor counterpart of
`derivedSheafHomMap_unit_left`, pinned for the same reason. -/
theorem derivedTensorMap_unit_left
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K) :
    derivedTensorMap Rc (𝟙 (RingedSite.derivedStructureSheaf (ringedSite Rc))) k =
      ((derivedTensor Rc).obj (RingedSite.derivedStructureSheaf (ringedSite Rc))).map k :=
  RingedSite.derivedTensorMap_id_left (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) _ k

/-- **The left unit constraint of `D(O_X)` is natural**, in the pinned spelling: for
`k : K' ⟶ K` the square formed by `λ_ K` and `λ_ K'` commutes.  This is
`CategoryTheory.MonoidalCategory.leftUnitor_naturality`, read with left whiskering by the unit
spelled as the action of the derived tensor bifunctor -- which is what it is, by `rfl`, for a
re-seated monoidal structure. -/
theorem derivedLeftUnitorHom_naturality
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K) :
    ((derivedTensor Rc).obj (RingedSite.derivedStructureSheaf (ringedSite Rc))).map k ≫
        derivedLeftUnitorHom Rc K =
      derivedLeftUnitorHom Rc K' ≫ k :=
  letI := derivedMonoidalStructure Rc
  MonoidalCategory.leftUnitor_naturality k

/-- A square of a bifunctor contravariant in its first variable and covariant in its second
pastes out of a commuting square of first-variable morphisms.  Stated over an arbitrary category
and an arbitrary bifunctor, for the reason given on `inv_comp_eq_of_transport`. -/
lemma hom_bifunctor_paste {D : Type*} [Category D] (F : Dᵒᵖ ⥤ D ⥤ D)
    {A P Q R M M' : D} (p : P ⟶ A) (q : Q ⟶ P) (s : R ⟶ A) (r : Q ⟶ R) (m : M ⟶ M')
    (h : q ≫ p = r ≫ s) :
    (F.map p.op).app M ≫ (F.map q.op).app M ≫ (F.obj (op Q)).map m =
      ((F.map s.op).app M ≫ (F.obj (op R)).map m) ≫ (F.map r.op).app M' := by
  rw [← Category.assoc, map_op_app_comp, h, ← map_op_app_comp, Category.assoc, Category.assoc,
    (F.map r.op).naturality m]

/-- **The right-hand side of the unit coherence is natural** in the source contravariantly and
in the target covariantly: this is `hom_bifunctor_paste` at the naturality square of the left
unit constraint. -/
private lemma rhs_naturality
    {K K' M M' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K) (m : M ⟶ M') :
    ((derivedSheafHom Rc).map (derivedLeftUnitorHom Rc K).op).app M ≫
        derivedSheafHomMap Rc
          (((derivedTensor Rc).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc))).map k) m =
      derivedSheafHomMap Rc k m ≫
        ((derivedSheafHom Rc).map (derivedLeftUnitorHom Rc K').op).app M' :=
  hom_bifunctor_paste (derivedSheafHom Rc) (derivedLeftUnitorHom Rc K)
    (((derivedTensor Rc).obj (RingedSite.derivedStructureSheaf (ringedSite Rc))).map k) k
    (derivedLeftUnitorHom Rc K') m (derivedLeftUnitorHom_naturality Rc k)

/-- **The left-hand side of the unit coherence is natural**, as far as the currying isomorphism
is concerned: `Stacks.SheafOfModules.derivedCurryIso_natural` at the identity of the
structure-sheaf source, with both induced maps rewritten into the one-variable spellings
`derivedSheafHomMap_unit_left` and `derivedTensorMap_unit_left`. -/
private lemma curry_naturality
    {K K' M M' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K) (m : M ⟶ M') :
    ((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map
          (derivedSheafHomMap Rc k m) ≫
        (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) K' M').hom =
      (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) K M).hom ≫
        derivedSheafHomMap Rc
          (((derivedTensor Rc).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc))).map k) m :=
  (congrArg
        (fun v ↦ v ≫
          (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) K' M').hom)
        (derivedSheafHomMap_unit_left Rc (derivedSheafHomMap Rc k m)).symm).trans
    ((derivedCurryIso_natural Rc (𝟙 (RingedSite.derivedStructureSheaf (ringedSite Rc))) k
          m).trans
      (congrArg
        (fun v ↦
          (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) K M).hom ≫
            derivedSheafHomMap Rc v m)
        (derivedTensorMap_unit_left Rc k)))

/-- A leg built from the inverse of an isomorphism and a morphism transports along a naturality
square.  Stated over an arbitrary category with every object and morphism a variable, for the
reason given on `inv_comp_eq_of_transport`. -/
lemma transport_leg {D : Type*} [Category D] {FH FH' H H' T T' : D}
    (A : FH ≅ H) (A' : FH' ≅ H') (ψ : H ⟶ H') (w : FH ⟶ FH')
    (q : FH ⟶ T) (q' : FH' ⟶ T') (χ : T ⟶ T')
    (hnat : w ≫ A'.hom = A.hom ≫ ψ)
    (hq : w ≫ q' = q ≫ χ) :
    (A.inv ≫ q) ≫ χ = ψ ≫ A'.inv ≫ q' := by
  have hAw : A.inv ≫ w = ψ ≫ A'.inv := by
    rw [← Iso.eq_comp_inv] at hnat
    rw [hnat, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Category.assoc, ← hq, ← Category.assoc, hAw, Category.assoc]

/-- **The unit coherence of Stacks 08J9 at an arbitrary pair of objects, given models for
them.** Both sides of the equation are natural -- contravariantly in `K` by `curry_naturality`
and `rhs_naturality`, covariantly in `M` by the same two -- and the map induced by the two model
isomorphisms is invertible, so the equation at `(QL, QI)` gives the equation at `(K, M)`.

The models are arbitrary: no property of the chosen ones is used beyond K-flatness of `L`,
K-injectivity of `I` and the two isomorphisms. -/
private lemma unit_law_of_models
    (K M : DerivedCategory (StructureSheafModules Rc))
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) (hL : IsKFlat Rc L)
    [I.IsKInjective] (e : DerivedCategory.Q.obj L ≅ K)
    (f : DerivedCategory.Q.obj I ≅ M) :
    (RingedSite.derivedStructureSheafHomIso (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op K)).obj M)).inv ≫
        (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) K M).hom =
      ((derivedSheafHom Rc).map (derivedLeftUnitorHom Rc K).op).app M := by
  refine (cancel_mono (derivedSheafHomMap Rc
    (((derivedTensor Rc).obj
      (RingedSite.derivedStructureSheaf (ringedSite Rc))).map e.hom) f.inv)).1 ?_
  refine Eq.trans (transport_leg _ _ (derivedSheafHomMap Rc e.hom f.inv)
    (((derivedSheafHom Rc).obj
      (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).map
        (derivedSheafHomMap Rc e.hom f.inv)) _ _ _
    (RingedSite.derivedStructureSheafHomIso_naturality (ringedSite Rc)
      (derivedSheafHomMap Rc e.hom f.inv))
    (curry_naturality Rc e.hom f.inv)) ?_
  refine Eq.trans (congrArg (fun v ↦ derivedSheafHomMap Rc e.hom f.inv ≫ v)
    (derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model Rc L I hL)) ?_
  exact (rhs_naturality Rc e.hom f.inv).symm

/-- **The unit coherence of the derived currying isomorphism of Stacks 08J9, for arbitrary
objects of `D(O_X)`.** For all `K` and `M`,

`(RSheafHom(O_X, RSheafHom(K, M)) ≅ RSheafHom(K, M))⁻¹ ≫ (currying of Stacks 08J9) =
  RSheafHom(λ_ K, M)`,

the collapse being `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and `λ_ K` the
left unit constraint of the monoidal structure of Stacks 0FPT.

No hypothesis is carried: `unit_law_of_models` is instantiated at the chosen K-flat and
K-injective models of `K` and `M`, which exist for every object by Stacks 06YS and Stacks 0A89.
This is the equation that
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` displays as what the
unit law (UL) needs, and it is the input to `derivedSheafHomCounit_unit_law` below. -/
theorem derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (K M : DerivedCategory (StructureSheafModules Rc)) :
    (RingedSite.derivedStructureSheafHomIso (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op K)).obj M)).inv ≫
        (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) K M).hom =
      ((derivedSheafHom Rc).map (derivedLeftUnitorHom Rc K).op).app M :=
  haveI : (RingedSite.kInjectiveModel (ringedSite Rc) M).IsKInjective :=
    RingedSite.isKInjective_kInjectiveModel (ringedSite Rc) M
  unit_law_of_models Rc K M (RingedSite.kFlatModel (ringedSite Rc) K)
    (RingedSite.kInjectiveModel (ringedSite Rc) M)
    (RingedSite.isKFlat_kFlatModel (ringedSite Rc) K)
    (RingedSite.kFlatModelIso (ringedSite Rc) K)
    (RingedSite.kInjectiveModelIso (ringedSite Rc) M)

/-! ### From the unit coherence to (UL) -/

/-- **The identification of Stacks 08JA at source the structure sheaf is the general one.**
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`, which identifies
`H⁰(X, Z)` with `Hom_{D(O_X)}(O_X, Z)`, is by construction the collapse
`RSheafHom(O_X, Z) ≅ Z` run backwards on global hypercohomology followed by Stacks 08JA for
`RSheafHom(O_X, Z)`.  It is `rfl`; naming it is what makes the covariant naturality of
Stacks 08JA unnecessary in the proof of (UL). -/
theorem derivedStructureSheafGlobalSectionsEquiv_apply
    (Z : DerivedCategory (StructureSheafModules Rc))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj Z) : Type u)) :
    RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) Z x =
      derivedSheafHomGlobalSectionsEquiv Rc
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) Z
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) Z).inv) x) :=
  rfl

/-- **The application morphism of Stacks 08J8 is the transpose of the identity.**  This is the
definition of `Stacks.SheafOfModules.derivedSheafHomCounit`, named so that the step can be taken
by `rw`: unfolding it inside the larger goal of
`derivedTensor_map_app_comp_derivedSheafHomCounit` exceeds the recursion limit of a single
elaboration. -/
theorem derivedSheafHomCounit_eq (K M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomCounit Rc K M =
      derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op K)).obj M) K M
        (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M)) :=
  rfl

/-- **Tensoring a datum with `K` and applying is its transpose under Stacks 08J8.**  For
`y : A ⟶ RSheafHom(K, M)`,

`y ▷ K ≫ app = (the bijection of Stacks 08J8 at y)`.

This is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation`, with the
application morphism recognised as the transpose of the identity by
`derivedSheafHomCounit_eq`.

The source `A` is arbitrary.  (UL) uses it only at `A = O_X`, but the right unit law (UR) of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw` needs it
at `A = M`, and the underlying
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation` is stated for an
arbitrary source; restricting it here would only force it to be re-derived. -/
theorem derivedTensor_map_app_comp_derivedSheafHomCounit
    (A K M : DerivedCategory (StructureSheafModules Rc))
    (y : A ⟶ ((derivedSheafHom Rc).obj (op K)).obj M) :
    ((derivedTensor Rc).map y).app K ≫ derivedSheafHomCounit Rc K M =
      derivedSheafHomTensorEquiv Rc A K M y := by
  rw [derivedSheafHomCounit_eq, derivedSheafHomTensorEquiv_eq, derivedSheafHomTensorEquiv_eq,
    RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation (ringedSite Rc) A K M y]

/-- The unit coherence `derivedStructureSheafHomIso_inv_comp_derivedCurryIso`, read on
degree-zero global hypercohomology and applied to a class. -/
theorem homologyMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (K M : DerivedCategory (StructureSheafModules Rc))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op K)).obj M)) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map
          (((derivedSheafHom Rc).map (derivedLeftUnitorHom Rc K).op).app M)) x =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map
          (derivedCurryIso Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) K M).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (RingedSite.derivedStructureSheafHomIso (ringedSite Rc)
              (((derivedSheafHom Rc).obj (op K)).obj M)).inv) x) := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp,
    derivedStructureSheafHomIso_inv_comp_derivedCurryIso]

/-- **(UL) at a degree-zero global hypercohomology class.**  For a class
`x ∈ H⁰(X, RSheafHom(K, M))`, the morphism `O_X ⟶ RSheafHom(K, M)` that `x` names under
Stacks 08JA, tensored with `K` and followed by the application morphism of Stacks 08J8, is
`λ_ K` followed by the morphism `K ⟶ M` that `x` names under Stacks 08JA.

The three inputs are `derivedTensor_map_app_comp_derivedSheafHomCounit`,
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_globalSections` (Stacks 08J8 read on global
hypercohomology, i.e. the last assertion of Stacks 08J9) and the contravariant naturality of
Stacks 08JA; the unit coherence enters through
`homologyMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`. -/
theorem derivedSheafHomCounit_unit_law_apply
    (K M : DerivedCategory (StructureSheafModules Rc))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op K)).obj M)) : Type u)) :
    ((derivedTensor Rc).map (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
            (((derivedSheafHom Rc).obj (op K)).obj M) x)).app K ≫
        derivedSheafHomCounit Rc K M =
      derivedLeftUnitorHom Rc K ≫ derivedSheafHomGlobalSectionsEquiv Rc K M x := by
  rw [derivedTensor_map_app_comp_derivedSheafHomCounit,
    derivedStructureSheafGlobalSectionsEquiv_apply,
    derivedSheafHomTensorEquiv_globalSections,
    ← homologyMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso]
  exact RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap
    (ringedSite Rc) M (derivedLeftUnitorHom Rc K) x

/-- **(UL), the unit law tying Stacks 08JA at source the structure sheaf to Stacks 08J8.**  For
every `y : O_X ⟶ RSheafHom(K, M)`, the morphism `K ⟶ M` that `y` names under the two
identifications of Stacks 08JA is `λ_K` followed by `y ▷ K` and the application morphism:

`y ▷ K ≫ app = (λ_ K).hom ≫ (Stacks 08JA)(Stacks 08JA⁻¹ y)`.

This is `derivedSheafHomCounit_unit_law_apply` with the class written as the one Stacks 08JA
attaches to `y`, which is the form the consumers of (UL) ask for.  It carries no hypothesis and
no tag: it is a compatibility of two published identifications, not a clause of either. -/
theorem derivedSheafHomCounit_unit_law
    (K M : DerivedCategory (StructureSheafModules Rc))
    (y : RingedSite.derivedStructureSheaf (ringedSite Rc) ⟶
      ((derivedSheafHom Rc).obj (op K)).obj M) :
    ((derivedTensor Rc).map y).app K ≫ derivedSheafHomCounit Rc K M =
      derivedLeftUnitorHom Rc K ≫
        derivedSheafHomGlobalSectionsEquiv Rc K M
          ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
            (((derivedSheafHom Rc).obj (op K)).obj M)).symm y) := by
  obtain ⟨x, rfl⟩ : ∃ x, RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
      (((derivedSheafHom Rc).obj (op K)).obj M) x = y :=
    ⟨_, (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
      (((derivedSheafHom Rc).obj (op K)).obj M)).apply_symm_apply y⟩
  rw [AddEquiv.symm_apply_apply]
  exact derivedSheafHomCounit_unit_law_apply Rc K M x

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- **(UL) in the monoidal spelling**, with right whiskering written `▷` and the left unit
constraint written `λ_`, quantified over `y` -- the exact shape of the `hunit` hypothesis of
`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CupProductAndDualityPairing`, so that it
can be applied to it directly.  This is `derivedSheafHomCounit_unit_law` with the two pinned
spellings undone, which is `rfl`.

The monoidal structure is in force as a section-local instance rather than as a `letI` in the
statement: a `let`-bound instance in the type is not the shape the consumers' hypotheses have,
and unifying the two exceeds the recursion limit of a single elaboration. -/
theorem derivedSheafHomCounit_unit_law_monoidal
    (K M : DerivedCategory (StructureSheafModules Rc)) :
    ∀ y : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
        ((derivedSheafHom Rc).obj (op K)).obj M,
      y ▷ K ≫ derivedSheafHomCounit Rc K M =
        (λ_ K).hom ≫ derivedSheafHomGlobalSectionsEquiv Rc K M
          ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
            (((derivedSheafHom Rc).obj (op K)).obj M)).symm y) :=
  fun y ↦ derivedSheafHomCounit_unit_law Rc K M y

/-- **(UL) in the monoidal spelling, with Stacks 08JA at the site-level spelling.** The outer
identification is the ringed-site one, the same morphism as
`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv` by
`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv_eq`.

The `hunit` hypotheses of `Stacks.SheafOfModules.derivedDualCoevaluation_triangle` and
`Stacks.SheafOfModules.exactPairingDerivedDualOfApplicationLaws` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` differ from this
statement only in the inner identification, which there receives `RSheafHom(K, K)` through
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`. Match the two inner identifications by
`rfl` before applying them, as
`Stacks.SheafOfModules.derivedDualCoevaluation_triangle_of_applicationLaw` does: matching them
applied exceeds the default recursion depth. -/
theorem derivedSheafHomCounit_unit_law_monoidal'
    (K M : DerivedCategory (StructureSheafModules Rc)) :
    ∀ y : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
        ((derivedSheafHom Rc).obj (op K)).obj M,
      y ▷ K ≫ derivedSheafHomCounit Rc K M =
        (λ_ K).hom ≫ RingedSite.derivedSheafHomGlobalSectionsEquiv (ringedSite Rc) K M
          ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
            (((derivedSheafHom Rc).obj (op K)).obj M)).symm y) :=
  fun y ↦ derivedSheafHomCounit_unit_law Rc K M y

end Monoidal

end Stacks.SheafOfModules

end

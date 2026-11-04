module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationPinningsOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingCounitFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingRightUnitLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw

/-!
# The right unit law of the application morphism of Stacks 08J8, on a ringed site

Let `(C, O)` be a ringed site and let `M` be an object of `D(O)`.  The identification
`M ≅ R𝓗om_O(O, M)` of Stacks 0A91, read backwards, is a morphism `M ⟶ R𝓗om_O(O, M)`; tensoring
it with the unit and applying the evaluation `R𝓗om_O(O, M) ⊗^𝐋_O O ⟶ M` of **Stacks 08J8** gives
a morphism `M ⊗^𝐋_O O ⟶ M`.  This file proves that it is the right unit constraint:

`(M ≅ R𝓗om_O(O, M))⁻¹ ▷ 𝟙_ ≫ app = (ρ_ M).hom`.

This is the equation the derived-duality cluster calls **(UR)**.  It is the ringed-site form of
`Stacks.SheafOfModules.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit`
of `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw`, and it
is needed separately because the slice site `C/U` of a ringed site is not a ringed space, so the
left-dual clause of **Stacks 0FPU** over an arbitrary ringed site cannot be read off the
ringed-space statement.

## Main results

* `RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects`:
  **the right unit coherence of the derived currying isomorphism of Stacks 08J9**, for
  *arbitrary* objects `A`, `M` of `D(O)`:

  `R𝓗om_O(A, -)` applied to the collapse `R𝓗om_O(O, M) ≅ M` run backwards, followed by the
  currying isomorphism, is the map induced on internal Hom by the right unit constraint `ρ_ A`.
* `RingedSite.derivedSheafHomCounit_right_unit_law_apply`: (UR) at a degree-zero global
  hypercohomology class of `R𝓗om_O(M, M)`.
* `RingedSite.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit` and
  its monoidal spelling
  `RingedSite.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal`:
  **(UR)**.

## Nothing here is tagged

None of these is a clause of a published statement.  The right unit coherence is a compatibility
of Stacks 08J9 with Stacks 0FNG that neither tag asserts, and (UR) is a compatibility of
Stacks 0A91 with Stacks 08J8 that neither tag asserts either; both are steps in the proof of the
left-dual clause of Example 0FPC and of its ringed-site form Stacks 0FPU.

## The proof, in three steps

1. The chain-level right unit law of Stacks 0A90 at a structure-sheaf *middle* variable, in its
   derived form at an arbitrary complex `A` and a K-injective `I`,
   `AlgebraicGeometry.RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`
   of `…InternalHom.DerivedCurryingRightUnitLaw`, is available.  The first half of this file strips
   the two model comparisons of Stacks 0A97 off it — the source identification by the naturality
   of `AlgebraicGeometry.RingedSite.derivedSheafHomComparison` in its source variable, the target
   one by the comparison of the tensor source — and then releases the representatives: both sides
   are natural in `A` contravariantly and in `M` covariantly, and every object of `D(O)` is the
   class of a K-flat complex and of a K-injective one, by
   `AlgebraicGeometry.RingedSite.kFlatModelIso` and
   `AlgebraicGeometry.RingedSite.kInjectiveModelIso`.
2. The right unit constraint of `D(O)` is reconciled with the right unitor of complexes by
   `AlgebraicGeometry.RingedSite.derivedRightUnitorHom_eq_comparison` of
   `…InternalHom.DerivedApplicationPinningsOnASite`.  No new mathematics enters here.
3. (UR) follows from the right unit coherence by applying degree-zero global hypercohomology.
   Here the two naturalities of Stacks 08JA are *both* needed, unlike on the left: the covariant
   one (`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`)
   turns the identity of `M` into the class whose associated morphism is
   `(M ≅ R𝓗om_O(O, M))⁻¹`, and the contravariant one
   (`RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap`)
   turns the map induced by `ρ_ M` on internal Hom back into precomposition with `ρ_ M`.  On the
   left the covariant one was unnecessary because the datum came from a global section of
   `R𝓗om_O(K, M)`; on the right the datum is an identity, which is what the covariant naturality
   is for.

## Implementation notes

The monoidal, symmetric, preadditive and closed instances on `Mod(O)` are pinned here as
file-local instances, as in `…InternalHom.DerivedApplicationPinningsOnASite`: they are stated
with the sections universe tied to the site universes as `max u v`, which instance synthesis
cannot solve against this cluster's diagonal `u` while those universes are still metavariables.

The diagram lemmas over an abstract category that this file uses —
`Stacks.SheafOfModules.transport_leg`,
`Stacks.SheafOfModules.hom_bifunctor_paste`,
`Stacks.SheafOfModules.paste_cancel`,
`Stacks.SheafOfModules.map_op_app_comp`,
`Stacks.Cohomology.DualityDescent.leg_of_inv_comp` and
`Stacks.Cohomology.DualityDescent.bifunctor_target_naturality` — are taken from
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams` rather than
restated: each is applied by `exact`, because the goals they act on carry the source of a
derived internal Hom at two definitionally equal spellings and are therefore not type-correct at
the `implicit` transparency level, so no rewriting tactic fires on them.

The K-flatness of `O[0]` is carried as a hypothesis through the model-level statements, so that
the proof term inside `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` is a variable; it
is discharged from `Stacks.SheafOfModules.isKFlat_single_unit` at the one place where the
statement becomes unconditional.

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
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.DualityDescent
open Stacks.SheafOfModules (transport_leg hom_bifunctor_paste paste_cancel map_op_app_comp)

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
attribute [local instance 10000] CochainComplex.symmetricCategory
  SheafOfModules.monoidalCategorySheafTensor

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-! ### The right unit coherence at representatives -/

/-- `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` at the structure sheaf in the
*second* factor, unfolded into the K-injective model comparison of Stacks 0A97 and the map
induced by the K-flat comparison of Stacks 06YU.  This is `rfl`; it is named so that the step
can be taken by `rw` rather than by unfolding a definition inside a larger goal. -/
theorem tensorHomRepresentativeIso_unit_inv_right
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) [I.IsKInjective] :
    (tensorHomRepresentativeIso X A (structureSheafComplex X) I hO).inv =
      (derivedSheafHomComparison X
          (((tensorComplex X.O).obj A).obj (structureSheafComplex X)) I).inv ≫
        ((derivedSheafHomBifunctor X).map (unitComparisonRightHom X A hO).op).app
          (DerivedCategory.Q.obj I) :=
  rfl

/-- **The right-hand side of the derived right unit law, with the model comparisons stripped
off.** The K-injective model comparison of Stacks 0A97, followed by the image of the map of
internal Hom complexes induced by the right unit collapse of complexes, followed by the inverse
of the representative isomorphism of the tensor-source internal Hom, is the map induced on
derived internal Hom by the right unit constraint of `D(O)`.

The two inputs are the naturality of the comparison of Stacks 0A97 in its source variable,
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` at the identity of the
target, and step 2, `AlgebraicGeometry.RingedSite.derivedRightUnitorHom_eq_comparison`. -/
theorem derivedSheafHomComparison_comp_homMap_unitCollapse_right
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) [I.IsKInjective] :
    (derivedSheafHomComparison X A I).hom ≫
        DerivedCategory.Q.map
            (homMap X (structureSheafComplexTensorRightIso X A).hom (𝟙 I)) ≫
          (tensorHomRepresentativeIso X A (structureSheafComplex X) I hO).inv =
      ((derivedSheafHomBifunctor X).map
          (derivedRightUnitorHom X (DerivedCategory.Q.obj A)).op).app
        (DerivedCategory.Q.obj I) := by
  have hnat := derivedSheafHomComparison_naturality X
    (structureSheafComplexTensorRightIso X A).hom (𝟙 I)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  rw [← Category.assoc, ← hnat, tensorHomRepresentativeIso_unit_inv_right]
  refine (paste_cancel _ _ _).trans ?_
  refine (map_op_app_comp _ _ _ _).trans ?_
  exact congrArg (fun v ↦ ((derivedSheafHomBifunctor X).map (Opposite.op v)).app
    (DerivedCategory.Q.obj I)) (derivedRightUnitorHom_eq_comparison X A hA hO).symm

/-- **The right unit coherence of Stacks 08J9 at representatives, with no model comparison left
in it.** For an arbitrary complex `A` and a K-injective `I`, the collapse
`R𝓗om_O(O, QI) ≅ QI` of `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, run
backwards inside `R𝓗om_O(QA, -)` and followed by the derived currying isomorphism of
Stacks 08J9, is the map induced on derived internal Hom by the right unit constraint `ρ_ (QA)`
of `D(O)`.

This is
`AlgebraicGeometry.RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`
with both representative isomorphisms cancelled: the source one against the naturality of the
comparison, the target one against
`derivedSheafHomComparison_comp_homMap_unitCollapse_right`. -/
theorem homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) [I.IsKInjective] :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
          (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).inv ≫
        (derivedCurryIso X (DerivedCategory.Q.obj A) (derivedStructureSheaf X)
          (DerivedCategory.Q.obj I)).hom =
      ((derivedSheafHomBifunctor X).map
          (derivedRightUnitorHom X (DerivedCategory.Q.obj A)).op).app
        (DerivedCategory.Q.obj I) :=
  leg_of_inv_comp (derivedSheafHomComparison X A I) _ _
    (tensorHomRepresentativeIso X A (structureSheafComplex X) I hO)
    (homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso' X A I hO)
    (derivedSheafHomComparison_comp_homMap_unitCollapse_right X A I hA hO)

/-! ### Releasing the representatives -/

/-- **The right-hand side of the right unit coherence is natural** in the source
contravariantly and in the target covariantly: this is
`Stacks.SheafOfModules.hom_bifunctor_paste` at the naturality square of the right
unit constraint. -/
private lemma rhs_naturality_right
    {A A' M M' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) (m : M ⟶ M') :
    ((derivedSheafHomBifunctor X).map (derivedRightUnitorHom X A).op).app M ≫
        derivedSheafHomMap X (derivedInternalHomOfBifunctor X)
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app
            (derivedStructureSheaf X)) m =
      derivedSheafHomMap X (derivedInternalHomOfBifunctor X) a m ≫
        ((derivedSheafHomBifunctor X).map (derivedRightUnitorHom X A').op).app M' :=
  hom_bifunctor_paste (derivedSheafHomBifunctor X) (derivedRightUnitorHom X A)
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app
      (derivedStructureSheaf X)) a
    (derivedRightUnitorHom X A') m (derivedRightUnitorHom_naturality X a)

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- **The collapse `R𝓗om_O(O, M) ≅ M`, read inside `R𝓗om_O(A, -)`, is natural** in `A`
contravariantly and in `M` covariantly: this is
`Stacks.Cohomology.DualityDescent.bifunctor_target_naturality` at the naturality of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`. -/
private lemma source_naturality_right
    {A A' M M' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) (m : M ⟶ M') :
    derivedSheafHomMap X (derivedInternalHomOfBifunctor X) a
          (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map m) ≫
        (((derivedSheafHomBifunctor X).obj (op A')).mapIso
          (derivedStructureSheafHomIso X M')).hom =
      (((derivedSheafHomBifunctor X).obj (op A)).mapIso
          (derivedStructureSheafHomIso X M)).hom ≫
        derivedSheafHomMap X (derivedInternalHomOfBifunctor X) a m :=
  bifunctor_target_naturality (derivedSheafHomBifunctor X) a m _ _ _
    (derivedStructureSheafHomIso_naturality X m)

/-- **The left-hand side of the right unit coherence is natural**, as far as the currying
isomorphism is concerned: `AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity
of the structure-sheaf *middle* object, with both induced maps rewritten into the one-variable
spellings `AlgebraicGeometry.RingedSite.derivedSheafHomMap_unit_left` and
`AlgebraicGeometry.RingedSite.derivedTensorMap_unit_right`. -/
private lemma curry_naturality_right
    {A A' M M' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) (m : M ⟶ M') :
    derivedSheafHomMap X (derivedInternalHomOfBifunctor X) a
          (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map m) ≫
        (derivedCurryIso X A' (derivedStructureSheaf X) M').hom =
      (derivedCurryIso X A (derivedStructureSheaf X) M).hom ≫
        derivedSheafHomMap X (derivedInternalHomOfBifunctor X)
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app
            (derivedStructureSheaf X)) m := by
  have h := derivedCurryIso_natural X a (𝟙 (derivedStructureSheaf X)) m
  simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id] at h
  exact (Category.assoc _ _ _).trans h

/-- **The right unit coherence of Stacks 08J9 at an arbitrary pair of objects, given models for
them.** Both sides of the equation are natural -- contravariantly in `A` by
`curry_naturality_right`, `source_naturality_right` and `rhs_naturality_right`, covariantly in
`M` by the same three -- and the map induced by the two model isomorphisms is invertible, so the
equation at `(QL, QI)` gives the equation at `(A, M)`.

The models are arbitrary: no property of the chosen ones is used beyond K-flatness of `L`,
K-injectivity of `I` and the two isomorphisms. -/
private lemma right_unit_law_of_models
    (A M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L)
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X))
    [I.IsKInjective] (e : DerivedCategory.Q.obj L ≅ A) (f : DerivedCategory.Q.obj I ≅ M) :
    ((derivedSheafHomBifunctor X).obj (op A)).map (derivedStructureSheafHomIso X M).inv ≫
        (derivedCurryIso X A (derivedStructureSheaf X) M).hom =
      ((derivedSheafHomBifunctor X).map (derivedRightUnitorHom X A).op).app M := by
  refine (cancel_mono (derivedSheafHomMap X (derivedInternalHomOfBifunctor X)
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map e.hom).app
      (derivedStructureSheaf X)) f.inv)).1 ?_
  refine Eq.trans (transport_leg _ _
    (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) e.hom f.inv)
    (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) e.hom
      (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map f.inv)) _ _ _
    (source_naturality_right X e.hom f.inv)
    (curry_naturality_right X e.hom f.inv)) ?_
  refine Eq.trans (congrArg
    (fun v ↦ derivedSheafHomMap X (derivedInternalHomOfBifunctor X) e.hom f.inv ≫ v)
    (homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model X L I hL hO)) ?_
  exact (rhs_naturality_right X e.hom f.inv).symm

/-- **The right unit coherence of the derived currying isomorphism of Stacks 08J9, for
arbitrary objects of `D(O)`.** For all `A` and `M`,

`R𝓗om_O(A, (R𝓗om_O(O, M) ≅ M)⁻¹) ≫ (currying of Stacks 08J9) = R𝓗om_O(ρ_ A, M)`,

the collapse being `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and `ρ_ A` the
right unit constraint of the monoidal structure of Stacks 0FPT.

No hypothesis is carried: `right_unit_law_of_models` is instantiated at the chosen K-flat and
K-injective models of `A` and `M`, which exist for every object by Stacks 06YS and Stacks 0A89,
and the K-flatness of the structure sheaf in degree zero is
`Stacks.SheafOfModules.isKFlat_single_unit`.  This is the input to (UR) below.

The name carries the suffix `_objects` because
`AlgebraicGeometry.RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso` of
`…InternalHom.DerivedCurryingRightUnitLaw` is the same coherence at *representatives*, which is
this statement's input through `right_unit_law_of_models`. -/
theorem homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects
    (A M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op A)).map (derivedStructureSheafHomIso X M).inv ≫
        (derivedCurryIso X A (derivedStructureSheaf X) M).hom =
      ((derivedSheafHomBifunctor X).map (derivedRightUnitorHom X A).op).app M :=
  have : (kInjectiveModel X M).IsKInjective := isKInjective_kInjectiveModel X M
  right_unit_law_of_models X A M (kFlatModel X A) (kInjectiveModel X M)
    (isKFlat_kFlatModel X A) (Stacks.SheafOfModules.isKFlat_single_unit X.O)
    (kFlatModelIso X A) (kInjectiveModelIso X M)

/-! ### From the right unit coherence to (UR) -/

/-- The right unit coherence `homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`, read
on degree-zero global hypercohomology and applied to a class. -/
theorem homologyMap_homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (A M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op A)).obj M)) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (derivedRightUnitorHom X A).op).app M)) x =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedCurryIso X A (derivedStructureSheaf X) M).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op A)).map
              (derivedStructureSheafHomIso X M).inv)) x) := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp,
    homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects]

/-- **(UR) at a degree-zero global hypercohomology class of `R𝓗om_O(M, M)`.**  For a class
`w ∈ H⁰(C, R𝓗om_O(M, M))`, the morphism `M ⟶ R𝓗om_O(O, M)` that `w` names after
`R𝓗om_O(M, -)` is applied to the collapse run backwards, tensored with the unit and followed
by the application morphism of Stacks 08J8, is `ρ_ M` followed by the morphism `M ⟶ M` that `w`
names under Stacks 08JA.

The three inputs are `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply` at source `M`,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections_homologyMap` (Stacks 08J8 read
on global hypercohomology, i.e. the last assertion of Stacks 08J9) and the contravariant
naturality of Stacks 08JA; the right unit coherence enters through
`homologyMap_homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`. -/
theorem derivedSheafHomCounit_right_unit_law_apply
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (w : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj M)) : Type u)) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (derivedSheafHomGlobalSectionsEquiv X M
              (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj M)
              ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
                ((derivedModuleGlobalSections X).map
                  (((derivedSheafHomBifunctor X).obj (op M)).map
                    (derivedStructureSheafHomIso X M).inv))
                w))).app (derivedStructureSheaf X) ≫
        derivedSheafHomCounit X (derivedStructureSheaf X) M =
      derivedRightUnitorHom X M ≫ derivedSheafHomGlobalSectionsEquiv X M M w := by
  rw [← derivedCurryHomEquiv_apply, derivedCurryHomEquiv_globalSections_homologyMap,
    ← homologyMap_homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso]
  exact derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap X M
    (derivedRightUnitorHom X M) w

/-- **(UR), the right unit law tying Stacks 0A91 to Stacks 08J8.**  The identification
`M ≅ R𝓗om_O(O, M)` of Stacks 0A91, run backwards, tensored with the unit and followed by the
application morphism of Stacks 08J8, is the right unit constraint of `D(O)`:

`(M ≅ R𝓗om_O(O, M))⁻¹ ▷ 𝟙_ ≫ app = (ρ_ M).hom`.

This is `derivedSheafHomCounit_right_unit_law_apply` at the class that Stacks 08JA attaches to
the identity of `M`, whose associated morphism is the collapse run backwards by the covariant
naturality of Stacks 08JA.  It carries no hypothesis and no tag: it is a compatibility of two
published identifications, not a clause of either. -/
theorem derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (derivedStructureSheafHomIso X M).inv).app (derivedStructureSheaf X) ≫
        derivedSheafHomCounit X (derivedStructureSheaf X) M =
      derivedRightUnitorHom X M := by
  have hw : derivedSheafHomGlobalSectionsEquiv X M M
      ((derivedSheafHomGlobalSectionsEquiv X M M).symm (𝟙 M)) = 𝟙 M :=
    (derivedSheafHomGlobalSectionsEquiv X M M).apply_symm_apply (𝟙 M)
  have htgt := derivedSheafHomGlobalSectionsEquiv_naturality_target X M
    (derivedStructureSheafHomIso X M).inv
    ((derivedSheafHomGlobalSectionsEquiv X M M).symm (𝟙 M))
  rw [hw, Category.id_comp] at htgt
  refine Eq.trans (congrArg
    (fun v ↦ ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map v).app
        (derivedStructureSheaf X) ≫ derivedSheafHomCounit X (derivedStructureSheaf X) M)
    htgt.symm) ?_
  refine Eq.trans (derivedSheafHomCounit_right_unit_law_apply X M
    ((derivedSheafHomGlobalSectionsEquiv X M M).symm (𝟙 M))) ?_
  rw [hw, Category.comp_id]

section Monoidal

attribute [local instance] derivedTensorMonoidal

/-- **(UR) in the monoidal spelling**, with right whiskering written `▷` and the right unit
constraint written `ρ_` -- the shape in which the derived-duality cluster's consumers ask for
it, so that each of them can be applied to it directly.  This is
`derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit` with the two pinned
spellings undone, which is `rfl`: the `whiskerRight` field of
`CategoryTheory.MonoidalCategory.reseatStruct` is literally `(T.map f).app Y`, and the unit of
the re-seated structure is the structure sheaf in degree zero. -/
theorem derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedStructureSheafHomIso X M).inv ▷
          𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≫
        derivedSheafHomCounit X (derivedStructureSheaf X) M = (ρ_ M).hom :=
  derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit X M

end Monoidal

end AlgebraicGeometry.RingedSite

end

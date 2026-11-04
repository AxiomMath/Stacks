module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationPinningsOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingUnitLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingCounitFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw

/-!
# The unit law of the application morphism of Stacks 08J8, on a ringed site

Let `(C, O)` be a ringed site and let `K` and `M` be objects of `D(O)`.  A morphism
`y : O ⟶ R𝓗om_O(K, M)` names a morphism `K ⟶ M` in two ways: by the two identifications of
**Stacks 08JA**, `Hom(O, R𝓗om_O(K, M)) = H⁰(C, R𝓗om_O(K, M)) = Hom(K, M)`; and by tensoring
with `K` and applying the evaluation `R𝓗om_O(K, M) ⊗^𝐋_O K ⟶ M` of **Stacks 08J8**.  This file
proves that the two agree:

`y ▷ K ≫ app = (λ_ K).hom ≫ (the morphism K ⟶ M that y names under Stacks 08JA)`.

This is the equation the derived-duality cluster calls **(UL)**, over an arbitrary ringed site.
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw` proves it for a
ringed *space*; the slice site `C/U` of a ringed site is not a ringed space, so the left-dual
clause of **Stacks 0FPU** over an arbitrary ringed site needs it here.

## Main results

* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects`:
  **the unit coherence of the derived currying isomorphism of Stacks 08J9**, for *arbitrary*
  objects `K`, `M` of `D(O)`:

  `R𝓗om_O(O, -)` applied to `R𝓗om_O(K, M)`, collapsed by
  `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and then curried, is the map
  induced on internal Hom by the left unit constraint `λ_ K`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomCounit_unit_law` and its monoidal spelling
  `AlgebraicGeometry.RingedSite.derivedSheafHomCounit_unit_law_monoidal`: **(UL)**.

## Nothing here is tagged

None of these is a clause of a published statement.  The unit coherence is a compatibility of
Stacks 08J9 with Stacks 0FNG that neither tag asserts, and (UL) is a compatibility of
Stacks 08JA with Stacks 08J8 that neither tag asserts either; both are steps in the proof of the
left-dual clause of Example 0FPC and of Stacks 0FPU.  Accordingly no declaration below carries a
tag attribute.

## The proof, in three steps

1. The chain-level unit law of Stacks 0A90 at a structure-sheaf source, in its derived form at a
   K-flat `L` and a K-injective `I`,
   `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso'` of
   `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingUnitLaw`, is proved.
   The first half of this file strips the two model comparisons of Stacks 0A97 off that derived
   form -- the source identification by the naturality of `derivedStructureSheafHomIso`, the
   target one by the naturality of the comparison in its source variable -- and then releases
   the representatives: both sides of the resulting equation are natural in `K` contravariantly
   and in `M` covariantly, and every object of `D(O)` is isomorphic to the class of a K-flat
   complex and to the class of a K-injective one, by
   `AlgebraicGeometry.RingedSite.kFlatModelIso` and
   `AlgebraicGeometry.RingedSite.kInjectiveModelIso`.  The release is therefore a transport
   along two isomorphisms, not a dévissage.
2. The left unit constraint of `D(O)` is reconciled with the left unitor of complexes by
   `AlgebraicGeometry.RingedSite.derivedLeftUnitorHom_eq_comparison` of
   `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationPinningsOnASite`,
   which is where the pinned spellings of this cluster live.  No new mathematics enters here.
3. (UL) follows from the unit coherence by applying degree-zero global hypercohomology: the
   contravariant naturality of Stacks 08JA, namely
   `derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap`,
   turns `(λ_ K).hom ≫ -` into the map induced by `λ_ K` on internal Hom, the last assertion of
   Stacks 08J9 (`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections_homologyMap`)
   turns the currying isomorphism into the bijection of morphism groups, and
   `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply` identifies `y ▷ K` followed by
   application with that bijection at `y`.  The covariant naturality of Stacks 08JA is *not*
   needed: the identification of `H⁰(C, Z)` with `Hom(O, Z)` unfolds to the contravariant one at
   source the structure sheaf by `rfl`, which is
   `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv_apply`.

## Implementation notes

The `open` block, the file-local instances and the instance arguments on `X` are those of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationPinningsOnASite`,
where the spellings this proof is stated at are pinned and the reason for pinning them is given:
two spellings of the left unit collapse occur, `𝟙_ ⊗ L` and `Tot(O[0] ⊗_O L)`, and a goal
mentioning both is not type-correct at the `implicit` transparency level, so no rewriting tactic
acts on it.  Every statement below is at the `tensorComplex` spelling.

For the same reason the two-variable maps `AlgebraicGeometry.RingedSite.derivedSheafHomMap` and
`AlgebraicGeometry.RingedSite.derivedTensorMap` are never rewritten: a goal mentioning them
carries the source of a derived internal Hom at two definitionally equal spellings.  Each such
step is an `exact` or a `congrArg`, and the diagram chases are lifted into lemmas over an
abstract category with every object and morphism a variable --
`Stacks.Cohomology.DualityDescent.inv_comp_eq_of_transport`,
`Stacks.SheafOfModules.transport_leg`,
`Stacks.SheafOfModules.hom_bifunctor_paste`,
`Stacks.SheafOfModules.map_op_app_comp` and
`Stacks.SheafOfModules.paste_cancel` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams`, where the
whole cluster's chases are collected.

The three declarations of step 3 are split rather than inlined: the composite statement exceeds
the recursion limit of a single elaboration, and raising that limit is not available here.

The unit coherence for arbitrary objects is named
`derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects` rather than
`derivedStructureSheafHomIso_inv_comp_derivedCurryIso`, which in this namespace is already the
representative-level statement of `DerivedCurryingUnitLaw`.

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

/-! ### The unit coherence at representatives -/

/-- `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` at the structure sheaf in the
first factor, unfolded into the K-injective model comparison of Stacks 0A97 and the map induced
by the K-flat comparison of Stacks 06YU.  This is `rfl`; it is named so that the step can be
taken by `rw` rather than by unfolding a definition inside a larger goal. -/
theorem tensorHomRepresentativeIso_unit_inv
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (tensorHomRepresentativeIso X (structureSheafComplex X) L I hL).inv =
      (derivedSheafHomComparison X
          (((tensorComplex X.O).obj (structureSheafComplex X)).obj L) I).inv ≫
        ((derivedSheafHomBifunctor X).map (unitComparisonHom X L hL).op).app
          (DerivedCategory.Q.obj I) :=
  rfl

/-- **The right-hand side of the derived unit law, with the model comparisons stripped off.**
The K-injective model comparison of Stacks 0A97, followed by the image of the map of internal Hom
complexes induced by the left unit collapse of complexes, followed by the inverse of the
representative isomorphism of the tensor-source internal Hom, is the map induced on derived
internal Hom by the left unit constraint of `D(O)`.

The two inputs are the naturality of the comparison of Stacks 0A97 in its source variable,
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` at the identity of the
target, and step 2, `AlgebraicGeometry.RingedSite.derivedLeftUnitorHom_eq_comparison`. -/
theorem derivedSheafHomComparison_comp_homMap_unitCollapse
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (derivedSheafHomComparison X L I).hom ≫
        DerivedCategory.Q.map
            (homMap X (structureSheafComplexTensorLeftIso X L).hom (𝟙 I)) ≫
          (tensorHomRepresentativeIso X (structureSheafComplex X) L I hL).inv =
      ((derivedSheafHomBifunctor X).map
          (derivedLeftUnitorHom X (DerivedCategory.Q.obj L)).op).app
        (DerivedCategory.Q.obj I) := by
  have hnat := derivedSheafHomComparison_naturality X
    (structureSheafComplexTensorLeftIso X L).hom (𝟙 I)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  rw [← Category.assoc, ← hnat, tensorHomRepresentativeIso_unit_inv]
  refine (paste_cancel _ _ _).trans ?_
  refine (map_op_app_comp _ _ _ _).trans ?_
  exact congrArg (fun v ↦ ((derivedSheafHomBifunctor X).map (Opposite.op v)).app
    (DerivedCategory.Q.obj I)) (derivedLeftUnitorHom_eq_comparison X L hL).symm

/-- **The unit coherence of Stacks 08J9 at representatives, with no model comparison left in
it.** For a K-flat `L` and a K-injective `I`, the collapse
`R𝓗om_O(O, R𝓗om_O(QL, QI)) ≅ R𝓗om_O(QL, QI)` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, run backwards and followed by the
derived currying isomorphism of Stacks 08J9, is the map induced on derived internal Hom by the
left unit constraint `λ_ (QL)` of `D(O)`.

This is `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`
with both representative isomorphisms cancelled: the source one against the naturality of
`derivedStructureSheafHomIso`, the target one against
`derivedSheafHomComparison_comp_homMap_unitCollapse`. -/
theorem derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (derivedStructureSheafHomIso X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj L))).obj
            (DerivedCategory.Q.obj I))).inv ≫
        (derivedCurryIso X (derivedStructureSheaf X) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj I)).hom =
      ((derivedSheafHomBifunctor X).map
          (derivedLeftUnitorHom X (DerivedCategory.Q.obj L)).op).app
        (DerivedCategory.Q.obj I) :=
  inv_comp_eq_of_transport _ _ (derivedSheafHomComparison X L I) _ _
    (tensorHomRepresentativeIso X (structureSheafComplex X) L I hL)
    (derivedStructureSheafHomIso_naturality X (derivedSheafHomComparison X L I).inv)
    (derivedStructureSheafHomIso_inv_comp_derivedCurryIso' X L I hL)
    (derivedSheafHomComparison_comp_homMap_unitCollapse X L I hL)

/-! ### Releasing the representatives -/

/-- **The right-hand side of the unit coherence is natural** in the source contravariantly and
in the target covariantly: this is `Stacks.SheafOfModules.hom_bifunctor_paste` at the
naturality square of the left unit constraint. -/
private lemma rhs_naturality
    {K K' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K) (m : M ⟶ M') :
    ((derivedSheafHomBifunctor X).map (derivedLeftUnitorHom X K).op).app M ≫
        derivedSheafHomMap X (derivedInternalHomOfBifunctor X)
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (derivedStructureSheaf X)).map k) m =
      derivedSheafHomMap X (derivedInternalHomOfBifunctor X) k m ≫
        ((derivedSheafHomBifunctor X).map (derivedLeftUnitorHom X K').op).app M' :=
  hom_bifunctor_paste (derivedSheafHomBifunctor X) (derivedLeftUnitorHom X K)
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (derivedStructureSheaf X)).map k) k
    (derivedLeftUnitorHom X K') m (derivedLeftUnitorHom_naturality X k)

/-- **The left-hand side of the unit coherence is natural**, as far as the currying isomorphism
is concerned: `AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity of the
structure-sheaf source, with both induced maps rewritten into the one-variable spellings
`AlgebraicGeometry.RingedSite.derivedSheafHomMap_unit_left` and
`AlgebraicGeometry.RingedSite.derivedTensorMap_unit_left`. -/
private lemma curry_naturality
    {K K' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K) (m : M ⟶ M') :
    ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
          (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) k m) ≫
        (derivedCurryIso X (derivedStructureSheaf X) K' M').hom =
      (derivedCurryIso X (derivedStructureSheaf X) K M).hom ≫
        derivedSheafHomMap X (derivedInternalHomOfBifunctor X)
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (derivedStructureSheaf X)).map k) m :=
  (congrArg
        (fun v ↦ v ≫ (derivedCurryIso X (derivedStructureSheaf X) K' M').hom)
        (derivedSheafHomMap_unit_left X
          (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) k m)).symm).trans
    ((Category.assoc
          (((derivedSheafHomBifunctor X).map (𝟙 (derivedStructureSheaf X)).op).app
            (((derivedSheafHomBifunctor X).obj (op K)).obj M))
          (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
            (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) k m))
          (derivedCurryIso X (derivedStructureSheaf X) K' M').hom).trans
      ((derivedCurryIso_natural X (𝟙 (derivedStructureSheaf X)) k m).trans
        (congrArg
          (fun v ↦ (derivedCurryIso X (derivedStructureSheaf X) K M).hom ≫
            derivedSheafHomMap X (derivedInternalHomOfBifunctor X) v m)
          (derivedTensorMap_unit_left X k))))

/-- **The unit coherence of Stacks 08J9 at an arbitrary pair of objects, given models for
them.** Both sides of the equation are natural -- contravariantly in `K` by `curry_naturality`
and `rhs_naturality`, covariantly in `M` by the same two -- and the map induced by the two model
isomorphisms is invertible, so the equation at `(QL, QI)` gives the equation at `(K, M)`.

The models are arbitrary: no property of the chosen ones is used beyond K-flatness of `L`,
K-injectivity of `I` and the two isomorphisms. -/
private lemma unit_law_of_models
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ K) (f : DerivedCategory.Q.obj I ≅ M) :
    (derivedStructureSheafHomIso X
          (((derivedSheafHomBifunctor X).obj (op K)).obj M)).inv ≫
        (derivedCurryIso X (derivedStructureSheaf X) K M).hom =
      ((derivedSheafHomBifunctor X).map (derivedLeftUnitorHom X K).op).app M := by
  refine (cancel_mono (derivedSheafHomMap X (derivedInternalHomOfBifunctor X)
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (derivedStructureSheaf X)).map e.hom) f.inv)).1 ?_
  refine Eq.trans (transport_leg _ _
    (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) e.hom f.inv)
    (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
      (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) e.hom f.inv)) _ _ _
    (derivedStructureSheafHomIso_naturality X
      (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) e.hom f.inv))
    (curry_naturality X e.hom f.inv)) ?_
  refine Eq.trans (congrArg
    (fun v ↦ derivedSheafHomMap X (derivedInternalHomOfBifunctor X) e.hom f.inv ≫ v)
    (derivedStructureSheafHomIso_inv_comp_derivedCurryIso_model X L I hL)) ?_
  exact (rhs_naturality X e.hom f.inv).symm

/-- **The unit coherence of the derived currying isomorphism of Stacks 08J9, for arbitrary
objects of `D(O)`.** For all `K` and `M`,

`(R𝓗om_O(O, R𝓗om_O(K, M)) ≅ R𝓗om_O(K, M))⁻¹ ≫ (currying of Stacks 08J9) = R𝓗om_O(λ_ K, M)`,

the collapse being `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and `λ_ K` the
left unit constraint of the monoidal structure of Stacks 0FPT.

No hypothesis is carried: `unit_law_of_models` is instantiated at the chosen K-flat and
K-injective models of `K` and `M`, which exist for every object by Stacks 06YS and Stacks 0A89.
It is the input to `derivedSheafHomCounit_unit_law` below. -/
theorem derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedStructureSheafHomIso X
          (((derivedSheafHomBifunctor X).obj (op K)).obj M)).inv ≫
        (derivedCurryIso X (derivedStructureSheaf X) K M).hom =
      ((derivedSheafHomBifunctor X).map (derivedLeftUnitorHom X K).op).app M :=
  unit_law_of_models X K M (kFlatModel X K) (kInjectiveModel X M) (isKFlat_kFlatModel X K)
    (kFlatModelIso X K) (kInjectiveModelIso X M)

/-! ### From the unit coherence to (UL) -/

/-- The unit coherence `derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects`, read on
degree-zero global hypercohomology and applied to a class. -/
theorem homologyMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj M)) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (derivedLeftUnitorHom X K).op).app M)) x =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedCurryIso X (derivedStructureSheaf X) K M).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedStructureSheafHomIso X
              (((derivedSheafHomBifunctor X).obj (op K)).obj M)).inv) x) := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp,
    derivedStructureSheafHomIso_inv_comp_derivedCurryIso_objects]

/-- **(UL) at a degree-zero global hypercohomology class.**  For a class
`x ∈ H⁰(C, R𝓗om_O(K, M))`, the morphism `O ⟶ R𝓗om_O(K, M)` that `x` names under Stacks 08JA,
tensored with `K` and followed by the application morphism of Stacks 08J8, is `λ_ K` followed by
the morphism `K ⟶ M` that `x` names under Stacks 08JA.

The three inputs are `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections_homologyMap` (Stacks 08J8 read
on global hypercohomology, i.e. the last assertion of Stacks 08J9) and the contravariant
naturality of Stacks 08JA; the unit coherence enters through
`homologyMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`. -/
theorem derivedSheafHomCounit_unit_law_apply
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj M)) : Type u)) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (derivedStructureSheafGlobalSectionsEquiv X
              (((derivedSheafHomBifunctor X).obj (op K)).obj M) x)).app K ≫
        derivedSheafHomCounit X K M =
      derivedLeftUnitorHom X K ≫ derivedSheafHomGlobalSectionsEquiv X K M x := by
  rw [← derivedCurryHomEquiv_apply, derivedStructureSheafGlobalSectionsEquiv_apply,
    derivedCurryHomEquiv_globalSections_homologyMap,
    ← homologyMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso]
  exact derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap X M
    (derivedLeftUnitorHom X K) x

/-- **(UL), the unit law tying Stacks 08JA at source the structure sheaf to Stacks 08J8.**  For
every `y : O ⟶ R𝓗om_O(K, M)`, the morphism `K ⟶ M` that `y` names under the two identifications
of Stacks 08JA is `λ_ K` followed by `y ▷ K` and the application morphism:

`y ▷ K ≫ app = (λ_ K).hom ≫ (Stacks 08JA)(Stacks 08JA⁻¹ y)`.

This is `derivedSheafHomCounit_unit_law_apply` with the class written as the one Stacks 08JA
attaches to `y`, which is the form the consumers of (UL) ask for.  It carries no hypothesis and
no tag: it is a compatibility of two published identifications, not a clause of either. -/
theorem derivedSheafHomCounit_unit_law
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (y : derivedStructureSheaf X ⟶ ((derivedSheafHomBifunctor X).obj (op K)).obj M) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map y).app K ≫
        derivedSheafHomCounit X K M =
      derivedLeftUnitorHom X K ≫
        derivedSheafHomGlobalSectionsEquiv X K M
          ((derivedStructureSheafGlobalSectionsEquiv X
            (((derivedSheafHomBifunctor X).obj (op K)).obj M)).symm y) := by
  obtain ⟨x, rfl⟩ : ∃ x, derivedStructureSheafGlobalSectionsEquiv X
      (((derivedSheafHomBifunctor X).obj (op K)).obj M) x = y :=
    ⟨_, (derivedStructureSheafGlobalSectionsEquiv X
      (((derivedSheafHomBifunctor X).obj (op K)).obj M)).apply_symm_apply y⟩
  rw [AddEquiv.symm_apply_apply]
  exact derivedSheafHomCounit_unit_law_apply X K M x

section Monoidal

attribute [local instance] derivedTensorMonoidal

/-- **(UL) in the monoidal spelling**, with right whiskering written `▷` and the left unit
constraint written `λ_`, quantified over `y` -- the shape the consumers' `hunit` hypotheses
have, so that it can be applied to them directly.  This is `derivedSheafHomCounit_unit_law`
with the two pinned spellings undone, which is `rfl`.

The monoidal structure is in force as a section-local instance rather than as a `letI` in the
statement: a `let`-bound instance in the type is not the shape the consumers' hypotheses have,
and unifying the two exceeds the recursion limit of a single elaboration. -/
theorem derivedSheafHomCounit_unit_law_monoidal
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∀ y : 𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
        ((derivedSheafHomBifunctor X).obj (op K)).obj M,
      y ▷ K ≫ derivedSheafHomCounit X K M =
        (λ_ K).hom ≫ derivedSheafHomGlobalSectionsEquiv X K M
          ((derivedStructureSheafGlobalSectionsEquiv X
            (((derivedSheafHomBifunctor X).obj (op K)).obj M)).symm y) :=
  fun y ↦ derivedSheafHomCounit_unit_law X K M y

end Monoidal

end AlgebraicGeometry.RingedSite

end

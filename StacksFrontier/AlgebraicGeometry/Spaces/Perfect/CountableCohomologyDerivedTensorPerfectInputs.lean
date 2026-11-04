module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensorOfEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictionOfEssentiallySmall

/-!
# Slice restriction of derived tensor products and local strictly perfect models

This file proves three statements on sheaves of modules that carry the cohomology clause of
Stacks 0CRU from strictly perfect complexes to perfect complexes, which are only étale locally
strictly perfect.

* The derived tensor product commutes with restriction to a slice of the site, on arbitrary
  objects of `D(𝒪)`, over a ringed site whose objects form a type in a universe `c` above the
  universe `u` of its morphisms and sections — the shape of the small étale site of an algebraic
  space, which is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`. The derived tensor product is
  the datum `Stacks.SheafOfModules.DerivedTensorProduct`.
* A sheaf of modules whose sections over the members of a finite covering family of an object
  are countable has countable sections over that object. This is the separatedness half of the
  sheaf condition: the restriction maps to the members of a covering family are jointly
  injective.
* A perfect complex of `𝒪_F`-modules on an algebraic space has a strictly perfect model over
  each member of a *finite* family of *affine* étale charts covering a given affine étale chart.
  Perfectness gives a covering with strictly perfect models but with no control on the members;
  Stacks 0218 on the small étale site refines it to a finite affine family, and the models
  restrict along the refining arrows.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.SliceRestriction.derivedTensorRestrictIso`:
  `(K ⊗^𝐋_𝒪 L)|_U ≅ K|_U ⊗^𝐋_{𝒪|_U} L|_U`, for arbitrary objects `K`, `L` of `D(𝒪)`.

## Main results

* `Stacks.SheafOfModules.sections_injective_of_ofArrows`: the restrictions of a section along a
  covering family determine it.
* `Stacks.SheafOfModules.countable_sections_of_ofArrows`: countability of the sections over the
  members of a finite covering family gives countability of the sections.
* `Stacks.SheafOfModules.exists_isStrictlyPerfect_quasiIso_restrict`: a strictly perfect model
  of `E|_Z` restricts to one of `E|_W` along an arrow `W ⟶ Z`.
* `AlgebraicGeometry.Space.exists_finite_affine_isStrictlyPerfect_refinement`: the finite affine
  family with strictly perfect models.

## Implementation notes

The left factor is represented by a K-flat complex (Stacks 06YS) and the right one by any
complex. At a K-flat left factor both derived tensor products are total tensor complexes, by the
field `comparisonLeft` of the datum; restriction of a K-flat complex is K-flat (Stacks 0E8K at
this universe shape) and restriction commutes with the total tensor complex
(`AlgebraicGeometry.RingedSite.tensorComplexOverIso`), so the two total complexes agree. No
naturality is asserted.

Restriction between slices is exact, so it preserves quasi-isomorphisms; with
`Stacks.SheafOfModules.overFunctorMapComplexIso`, the identification of `(E|_Z)|_W` with `E|_W`
on complexes, it carries a strictly perfect model along an arrow of the site.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe t w v u c d

namespace Stacks.SheafOfModules.DerivedTensorProduct.SliceRestriction

open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex ringSheaf)
open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceHasMapBifunctor

variable (X : RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ,
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]

/-- Every object of `D(𝒪)` is represented by a K-flat complex, Stacks 06YS. -/
theorem exists_kFlatRep (K : RingedSite.DerivedModules.{c, u, u, d} X) :
    ∃ A : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ,
      Stacks.SheafOfModules.IsKFlat X.O A ∧ Nonempty (DerivedCategory.Q.obj A ≅ K) := by
  obtain ⟨A, p, hA, hqis⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    X.O (DerivedCategory.Q.objPreimage K)
  have _ := hqis
  exact ⟨A, hA, ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- A chosen K-flat complex representing an object of `D(𝒪)`. -/
def kFlatRep (K : RingedSite.DerivedModules.{c, u, u, d} X) :
    CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ :=
  (exists_kFlatRep X K).choose

/-- The chosen representative is K-flat. -/
theorem isKFlat_kFlatRep (K : RingedSite.DerivedModules.{c, u, u, d} X) :
    Stacks.SheafOfModules.IsKFlat X.O (kFlatRep X K) :=
  (exists_kFlatRep X K).choose_spec.1

/-- The chosen K-flat complex does represent the object. -/
def kFlatRepIso (K : RingedSite.DerivedModules.{c, u, u, d} X) :
    DerivedCategory.Q.obj (kFlatRep X K) ≅ K :=
  (exists_kFlatRep X K).choose_spec.2.some

variable [EssentiallySmall.{u} X.C]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, (sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{max c u, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [∀ U : X.C, HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]

/-- **The derived tensor product commutes with restriction to a slice, at a K-flat left
factor.** Both sides are the ordinary total tensor complex of the restrictions. -/
def restrictIsoOfKFlat (U : X.C)
    (T : DerivedTensorProduct.{c, u, u, d} X)
    (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (A B : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) :
    (RingedSite.derivedRestriction.{c, u, u, d} X U).obj
        ((T.tensor.obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) ≅
      (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A))).obj
        (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) :=
  (RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso (T.comparisonLeft A B hA) ≪≫
    (SheafOfModules.overFunctor.{u} (ringSheaf.{c, u, u} X.O) U).mapDerivedCategoryFactors.app
      (((tensorComplex.{c, u, u} X.O).obj A).obj B) ≪≫
    DerivedCategory.Q.mapIso (RingedSite.tensorComplexOverIso X U A B) ≪≫
    (TU.comparisonLeft ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B)
      (Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.kFlat_restrictionComplex
        X U A hA)).symm

/-- **The derived tensor product commutes with restriction to a slice**, read at complexes
representing the two factors, the left one K-flat. -/
def restrictIsoOfModels (U : X.C)
    (T : DerivedTensorProduct.{c, u, u, d} X)
    (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (A B : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    {K : RingedSite.DerivedModules.{c, u, u, d} X} (eK : DerivedCategory.Q.obj A ≅ K)
    {L : RingedSite.DerivedModules.{c, u, u, d} X} (eL : DerivedCategory.Q.obj B ≅ L) :
    (RingedSite.derivedRestriction.{c, u, u, d} X U).obj ((T.tensor.obj K).obj L) ≅
      (TU.tensor.obj ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj K)).obj
        ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj L) :=
  (RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso
      (((T.tensor.mapIso eK).app L).symm ≪≫
        ((T.tensor.obj (DerivedCategory.Q.obj A)).mapIso eL).symm) ≪≫
    restrictIsoOfKFlat X U T TU A B hA ≪≫
    (TU.tensor.mapIso
      (((SheafOfModules.overFunctor.{u} (ringSheaf.{c, u, u} X.O) U).mapDerivedCategoryFactors.app
          A).symm ≪≫
        (RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso eK)).app
      (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≪≫
    (TU.tensor.obj ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj K)).mapIso
      (((SheafOfModules.overFunctor.{u} (ringSheaf.{c, u, u} X.O) U).mapDerivedCategoryFactors.app
          B).symm ≪≫
        (RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso eL)

/-- **The derived tensor product commutes with restriction to a slice of the site**:
`(K ⊗^𝐋_𝒪 L)|_U ≅ K|_U ⊗^𝐋_{𝒪|_U} L|_U` for arbitrary objects `K`, `L` of `D(𝒪)`. -/
def derivedTensorRestrictIso (U : X.C)
    (T : DerivedTensorProduct.{c, u, u, d} X)
    (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (K L : RingedSite.DerivedModules.{c, u, u, d} X) :
    (RingedSite.derivedRestriction.{c, u, u, d} X U).obj ((T.tensor.obj K).obj L) ≅
      (TU.tensor.obj ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj K)).obj
        ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj L) :=
  restrictIsoOfModels X U T TU (kFlatRep X K) (DerivedCategory.Q.objPreimage L)
    (isKFlat_kFlatRep X K) (kFlatRepIso X K) (DerivedCategory.Q.objObjPreimageIso L)

end Stacks.SheafOfModules.DerivedTensorProduct.SliceRestriction

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **The restrictions of a section along a covering family determine it.** -/
theorem sections_injective_of_ofArrows (M : SheafOfModules.{w} R) {U : C} {ι : Type t}
    (V : ι → C) (g : ∀ i, V i ⟶ U) (hcov : Sieve.ofArrows V g ∈ J U) :
    Function.Injective fun s : M.val.presheaf.obj (op U) =>
      fun i => M.val.presheaf.map (g i).op s := by
  have hM : Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{w}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ M.isSheaf)
  have hsep : Presieve.IsSeparatedFor (M.val.presheaf ⋙ forget AddCommGrpCat.{w})
      (Presieve.ofArrows V g) := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact (hM _ hcov).isSeparatedFor
  exact fun s s' hss' => hsep.ext fun _ _ ⟨i⟩ => congrFun hss' i

/-- **A sheaf of modules with countable sections over a finite covering family has countable
sections.** The restriction maps to the members of a covering family are jointly injective. -/
theorem countable_sections_of_ofArrows (M : SheafOfModules.{w} R) {U : C} {ι : Type t} [Finite ι]
    (V : ι → C) (g : ∀ i, V i ⟶ U) (hcov : Sieve.ofArrows V g ∈ J U)
    (hc : ∀ i, Countable (M.val.obj (op (V i)))) : Countable (M.val.obj (op U)) := by
  have _ : ∀ i, Countable (M.val.presheaf.obj (op (V i))) := hc
  exact (sections_injective_of_ofArrows M V g hcov).countable

section StrictlyPerfect

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits

variable (R)
variable [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A strictly perfect model of `E|_Z` restricts to one of `E|_W` along an arrow
`a : W ⟶ Z`.** Restriction between slices is exact and carries the unit to the unit. -/
theorem exists_isStrictlyPerfect_quasiIso_restrict
    (E : CochainComplex (SheafOfModules.{w} R) ℤ) {Z W : C} (a : W ⟶ Z)
    {P : CochainComplex (SheafOfModules.{w} (R.over Z)) ℤ}
    (hP : IsStrictlyPerfect (R.over Z) P)
    {q : P ⟶ ((SheafOfModules.overFunctor.{w} R Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E} (hq : QuasiIso q) :
    ∃ (P' : CochainComplex (SheafOfModules.{w} (R.over W)) ℤ)
      (_ : IsStrictlyPerfect (R.over W) P')
      (q' : P' ⟶ ((SheafOfModules.overFunctor.{w} R W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E), QuasiIso q' := by
  have _ := hq
  exact ⟨restrictComplexAlongGeneral R a P,
    isStrictlyPerfect_restrictComplexAlong_general R a hP,
    ((SheafOfModules.overMap.{w} R a).mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫
      ((Stacks.SheafOfModules.overFunctorMapComplexIso R a).app E).hom, inferInstance⟩

end StrictlyPerfect

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Sheafification of abelian presheaves with sections in the universe of the schemes exists on
every slice of the small étale site, at the spelling of the ringed site. -/
local instance hasSheafifySmallEtaleSlice (Y : (smallEtaleRingedSite B S hS F hF).C) :
    HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over Y) AddCommGrpCat.{u} :=
  SmallEtale.instHasSheafifyOver B S hS F _ Y

/-- **A perfect complex of `𝒪_F`-modules has a strictly perfect model on each member of a finite
covering family of affine étale charts of an affine étale chart.** -/
theorem exists_finite_affine_isStrictlyPerfect_refinement
    (v : (smallEtaleRingedSite B S hS F hF).C) (hv : IsAffineChart B S hS F v)
    (E : CochainComplex (Modules.{u, u} B S hS F hF) ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPerfectComplex.{u + 1, u, u, u} E) :
    ∃ (ι : Type) (_ : Finite ι) (V : ι → (smallEtaleRingedSite B S hS F hF).C)
      (f : ∀ i, V i ⟶ v),
      (∀ i, IsAffineChart B S hS F (V i)) ∧
        Sieve.ofArrows V f ∈ (smallEtaleRingedSite B S hS F hF).J v ∧
          ∀ i, ∃ (P : CochainComplex (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS F hF).O).over (V i))) ℤ)
            (_ : IsStrictlyPerfect
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS F hF).O).over (V i)) P)
            (q : P ⟶ (smallEtaleRingedSite B S hS F hF).restrictComplex E (V i)), QuasiIso q := by
  classical
  obtain ⟨Sp, hSp, hmodel⟩ := hE v
  obtain ⟨ι, hfin, V, f, haff, hle, hcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F v hv (Sieve.generate Sp) hSp
  refine ⟨ι, hfin, V, f, haff, hcov, fun i => ?_⟩
  obtain ⟨Z, a, g, hg, -⟩ := hle _ (Sieve.ofArrows_mk V f i)
  obtain ⟨P, hP, q, hq⟩ := hmodel g hg
  exact Stacks.SheafOfModules.exists_isStrictlyPerfect_quasiIso_restrict
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) E a hP hq

end AlgebraicGeometry.Space

end

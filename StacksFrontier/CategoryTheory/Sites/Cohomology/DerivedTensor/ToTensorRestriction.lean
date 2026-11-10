module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction

/-!
# The derived-to-total comparison of Stacks 06YU commutes with restriction to a slice

Let `(C, O)` be a ringed site and let `U` be an object of `C`. The derived tensor product datum
of Stacks 06YU carries, besides the comparison at a pair of K-flat complexes, a canonical map

`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.toTensor`, `A ⊗^L_O B ⟶ Q(Tot(A ⊗_O B))`,

defined for an **arbitrary** pair of complexes and natural in both. This file proves that this
map commutes with restriction to the localized ringed site of Stacks 04IX: its restriction,
read through Mathlib's identification of the restriction of a class with the class of a
restriction and through the chain-level comparison of total tensor complexes, is the comparison
`(A ⊗^L_O B)|_U ≅ A|_U ⊗^L_{O|_U} B|_U` followed by the canonical map formed over `U`.

## Why this is the brick that was owed

The derived restriction compatibility of the canonical map of Stacks 08JD, which is what the
third assertion of Stacks 08JJ needs, goes through the derived form of
`AlgebraicGeometry.RingedSite.compositionMap_restrict_square`, and that in turn through the
restriction compatibility of `AlgebraicGeometry.RingedSite.derivedEvaluationSourceComparison`.
That comparison is built from `toTensor` and **not** from the two-sided comparison of
Stacks 06YU: its left tensor factor is an internal Hom complex `SheafHom(J, I)`, which is
K-injective and not K-flat, so only the right factor is K-flat and only the one-sided
normalization applies. The natural isomorphism
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` is therefore not directly
usable there; what is usable is the statement below, which transports it across `toTensor`.

## Main definitions

* `Stacks.DerivedTensor.SliceRestriction.tensorRestrictFactorsHom`: the identification of the
  value of `tensorRestrictTargetFunctor` at a pair of classes of complexes with the derived
  tensor product over `U` of the classes of the two restrictions — the two trailing factors of
  `derivedTensorRestrictModelIso`, read in the other direction.

## Main results

* `Stacks.DerivedTensor.SliceRestriction.toTensor_restrict_square_kFlat`: the square at a pair
  of K-flat complexes.
* `Stacks.DerivedTensor.SliceRestriction.tensorRestrictFactorsHom_naturality`: that
  identification is natural for a pair of morphisms of complexes.
* `Stacks.DerivedTensor.SliceRestriction.toTensor_restrict_square`: **the square, for an
  arbitrary pair of complexes.**

## Implementation notes

At a pair of K-flat complexes `toTensor` *is* the comparison of Stacks 06YU
(`toTensor_eq_comparison`, on both sites), so the square there is
`derivedTensorRestrictNatIso_hom_app_models` together with the two `rfl` decompositions
`derivedTensorRestrictModelIso_hom` and `derivedTensorRestrictIsoOfKFlat_hom`, after the two
trailing identifications of `derivedTensorRestrictModelIso` have been cancelled against
`tensorRestrictFactorsHom`. That cancellation is `tensorRestrictFactors_inv_hom`.

The general case is a pair of K-flat resolutions (Stacks 06YS,
`Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso`): the induced map of the two sources is
invertible, so it may be cancelled, and both sides become natural along it — the left by
`toTensor_naturality` together with `tensorComplexOverIsoSquare`, the right by the naturality
of `derivedTensorRestrictNatIso` together with `tensorRestrictFactorsHom_naturality`. Neither
side needs the calculus of fractions: the morphism being cancelled is the class of a pair of
morphisms of complexes to begin with.

Both `rw` with `CategoryTheory.Functor.bifunctorPairMap_comp` below supply **every** object
argument by name. Without them the pattern is built with the source of
`mapDerivedCategoryFactors.app` spelled through the composite functor
`DerivedCategory.Q ⋙ F.mapDerivedCategory` and the rewrite reports *did not find an occurrence
of the pattern*; this is the measurement already recorded in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceNaturality`, and
it repeats here in both variables.

The derived tensor products are taken in the packaging indexed by the structure sheaf,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, which is the packaging
`derivedTensorRestrictNatIso` is stated for. A datum in the packaging indexed by a ringed site
is carried across by
`Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct`.

## What this file does not contain

**Nothing is tagged.** The statement below is the restriction compatibility of a *structural*
field of the derived tensor product datum of Stacks 06YU; Stacks 06YU asserts the existence of
that field and says nothing about restriction, and the derived tensor product analogue of
Stacks 08JB — the comparison this file transports — is itself untagged, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction`, for
the same reason. No assertion of Stacks 08JJ follows from what is here.

What is still absent, and what this file was written for, is the restriction compatibility of
`AlgebraicGeometry.RingedSite.derivedEvaluationSourceComparison`. Two further inputs are owed
for that: the restriction compatibility of the chain-level identification
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` of the two spellings of the total
tensor complex, and the compatibility of the K-injective model comparison
`AlgebraicGeometry.RingedSite.DerivedInternalHom.homComparison` with
`(AlgebraicGeometry.RingedSite.derivedHomRestriction X U).iso`, which is
`AlgebraicGeometry.RingedSite.derivedHomRestriction_model` read in the tensor factor.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction restrictionComplex
  kFlat_restrictionComplex)

universe d u

attribute [local instance] AlgebraicGeometry.RingedSite.ringSheafSectionsCommRing
  AlgebraicGeometry.RingedSite.presheafOfModulesMonoidalCategory
  AlgebraicGeometry.RingedSite.ringSheafOverSectionsCommRing
  Stacks.hasSheafCompose_forget₂_commRingCat

namespace Stacks.DerivedTensor.SliceRestriction

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.tensorComplex
  tensorRestrictSourceFunctor tensorRestrictTargetFunctor

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]
  [(sheafTensor X.O).Additive] [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive] [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]
  (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
  (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))

/-- The identification of the value of `tensorRestrictTargetFunctor` at a pair of classes of
complexes with the derived tensor product over `U` of the classes of their restrictions. -/
def tensorRestrictFactorsHom (A B : CochainComplex (Modules X.O) ℤ) :
    (tensorRestrictTargetFunctor X U TU).obj
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ⟶
      (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A))).obj
        (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) :=
  (TU.tensor.map ((restriction X U).mapDerivedCategoryFactors.app A).hom).app
      ((restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
    (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A))).map
      ((restriction X U).mapDerivedCategoryFactors.app B).hom

omit
  [(sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).Additive]
  [∀ M, ((sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- The two identifications folded into `derivedTensorRestrictModelIso` are inverse to
`tensorRestrictFactorsHom`. -/
lemma tensorRestrictFactors_inv_hom (A B : CochainComplex (Modules X.O) ℤ) :
    (TU.tensor.map ((restriction X U).mapDerivedCategoryFactors.app A).inv).app
          (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≫
        (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj A))).map
          ((restriction X U).mapDerivedCategoryFactors.app B).inv ≫
        tensorRestrictFactorsHom X U TU A B =
      𝟙 ((TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A))).obj
        (DerivedCategory.Q.obj ((restrictionComplex X U).obj B))) := by
  dsimp only [tensorRestrictFactorsHom]
  rw [← Category.assoc]
  erw [CategoryTheory.Functor.bifunctorPairMap_comp TU.tensor]
  simp

/-- **The derived-to-total comparison of Stacks 06YU commutes with restriction to a slice, at a
pair of K-flat complexes.** -/
lemma toTensor_restrict_square_models (m : tensorRestrictModels X) :
    (restriction X U).mapDerivedCategory.map (T.toTensor m.1.1 m.2.1) ≫
        ((restriction X U).mapDerivedCategoryFactors.app
          (((tensorComplex X.O).obj m.1.1).obj m.2.1)).hom ≫
        DerivedCategory.Q.map (restrictTensorComplexOver X U m.1.1 m.2.1) =
      (derivedTensorRestrictNatIso X U T TU).hom.app
          (DerivedCategory.Q.obj m.1.1, DerivedCategory.Q.obj m.2.1) ≫
        tensorRestrictFactorsHom X U TU m.1.1 m.2.1 ≫
        TU.toTensor ((restrictionComplex X U).obj m.1.1)
          ((restrictionComplex X U).obj m.2.1) := by
  rw [derivedTensorRestrictNatIso_hom_app_models X U T TU m,
    derivedTensorRestrictModelIso_hom X U T TU m,
    derivedTensorRestrictIsoOfKFlat_hom X U T TU m.1.1 m.2.1 m.1.2 m.2.2,
    TU.toTensor_eq_comparison ((restrictionComplex X U).obj m.1.1)
      ((restrictionComplex X U).obj m.2.1) (kFlat_restrictionComplex X U m.1.1 m.1.2)
      (kFlat_restrictionComplex X U m.2.1 m.2.2),
    T.toTensor_eq_comparison m.1.1 m.2.1 m.1.2 m.2.2]
  simp only [Category.assoc]
  rw [reassoc_of% tensorRestrictFactors_inv_hom X U TU m.1.1 m.2.1]
  simp

/-- **The derived-to-total comparison of Stacks 06YU commutes with restriction to a slice, at a
pair of K-flat complexes**, with the K-flatness carried as hypotheses rather than in a model. -/
lemma toTensor_restrict_square_kFlat (A B : CochainComplex (Modules X.O) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B) :
    (restriction X U).mapDerivedCategory.map (T.toTensor A B) ≫
        ((restriction X U).mapDerivedCategoryFactors.app
          (((tensorComplex X.O).obj A).obj B)).hom ≫
        DerivedCategory.Q.map (restrictTensorComplexOver X U A B) =
      (derivedTensorRestrictNatIso X U T TU).hom.app
          (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        tensorRestrictFactorsHom X U TU A B ≫
        TU.toTensor ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B) :=
  toTensor_restrict_square_models X U T TU (⟨A, hA⟩, ⟨B, hB⟩)

variable {A A' B B' : CochainComplex (Modules X.O) ℤ}

/-- The naturality of the derived-to-total comparison, with the induced map of total complexes
named by `tensorComplexPairMap` so that both sides are in one spelling. -/
lemma toTensorPairSquare (a : A ⟶ A') (b : B ⟶ B') :
    ((T.tensor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj B) ≫
          (T.tensor.obj (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map b)) ≫
        T.toTensor A' B' =
      T.toTensor A B ≫ DerivedCategory.Q.map (tensorComplexPairMap X a b) :=
  (Category.assoc _ _ _).trans (T.toTensor_naturality a b)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules X.O)]
  [(sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).Additive]
  [∀ M, ((sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- The same on the site over `U`, between the restrictions. -/
lemma toTensorOverPairSquare (a : A ⟶ A') (b : B ⟶ B') :
    (TU.tensor.map (DerivedCategory.Q.map ((restrictionComplex X U).map a))).app
          (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≫
        (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A'))).map
          (DerivedCategory.Q.map ((restrictionComplex X U).map b)) ≫
        TU.toTensor ((restrictionComplex X U).obj A') ((restrictionComplex X U).obj B') =
      TU.toTensor ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B) ≫
        DerivedCategory.Q.map (tensorComplexOverPairMap X U a b) :=
  TU.toTensor_naturality _ _

omit
  [(sheafTensor (X.O.over U) :
      Modules (X.O.over U) ⥤ Modules (X.O.over U) ⥤ Modules (X.O.over U)).Additive]
  [∀ M, ((sheafTensor (X.O.over U) :
      Modules (X.O.over U) ⥤ Modules (X.O.over U) ⥤ Modules (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)] in
/-- The source functor on a pair of classes of morphisms of complexes, with neither endpoint
required to be a model; `rfl`. -/
lemma tensorRestrictSourceFunctor_map_Q' (a : A ⟶ A') (b : B ⟶ B') :
    (tensorRestrictSourceFunctor X U T).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ⟶
            (DerivedCategory.Q.obj A', DerivedCategory.Q.obj B')) =
      (restriction X U).mapDerivedCategory.map
        ((T.tensor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj B) ≫
          (T.tensor.obj (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map b)) :=
  rfl

omit
  [(sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).Additive]
  [∀ M, ((sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- The target functor on a pair of classes of morphisms of complexes; `rfl`. -/
lemma tensorRestrictTargetFunctor_map_Q' (a : A ⟶ A') (b : B ⟶ B') :
    (tensorRestrictTargetFunctor X U TU).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ⟶
            (DerivedCategory.Q.obj A', DerivedCategory.Q.obj B')) =
      (TU.tensor.map ((restriction X U).mapDerivedCategory.map
            (DerivedCategory.Q.map a))).app
          ((restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
        (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj A'))).map
          ((restriction X U).mapDerivedCategory.map (DerivedCategory.Q.map b)) :=
  rfl

omit
  [(sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).Additive]
  [∀ M, ((sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- **`tensorRestrictFactorsHom` is natural for a pair of morphisms of complexes.** -/
lemma tensorRestrictFactorsHom_naturality (a : A ⟶ A') (b : B ⟶ B') :
    ((TU.tensor.map ((restriction X U).mapDerivedCategory.map
              (DerivedCategory.Q.map a))).app
            ((restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
          (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj A'))).map
            ((restriction X U).mapDerivedCategory.map (DerivedCategory.Q.map b))) ≫
        tensorRestrictFactorsHom X U TU A' B' =
      tensorRestrictFactorsHom X U TU A B ≫
        ((TU.tensor.map (DerivedCategory.Q.map ((restrictionComplex X U).map a))).app
            (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≫
          (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A'))).map
            (DerivedCategory.Q.map ((restrictionComplex X U).map b))) := by
  dsimp only [tensorRestrictFactorsHom]
  erw [CategoryTheory.Functor.bifunctorPairMap_comp TU.tensor,
    CategoryTheory.Functor.bifunctorPairMap_comp TU.tensor]
  erw [(restriction X U).mapDerivedCategoryFactors_hom_naturality a,
    (restriction X U).mapDerivedCategoryFactors_hom_naturality b]
  rfl

/-- **The derived-to-total comparison of Stacks 06YU commutes with restriction to a slice.**
For arbitrary complexes `A` and `B` of `O`-modules, the restriction to the site over `U` of the
canonical map `A ⊗^L_O B ⟶ Q(Tot(A ⊗_O B))`, read through the identification of the restriction
of a class with the class of a restriction and the chain-level comparison of total tensor
complexes, is the comparison `(A ⊗^L_O B)|_U ≅ A|_U ⊗^L_{O|_U} B|_U` followed by the canonical
map formed over `U`.

Both sides are natural for a pair of morphisms of complexes, and on a pair of K-flat complexes
the statement is `toTensor_restrict_square_kFlat`; a pair of K-flat resolutions (Stacks 06YS)
therefore reduces the general case to that one, the two induced maps being invertible. -/
lemma toTensor_restrict_square (A B : CochainComplex (Modules X.O) ℤ) :
    (restriction X U).mapDerivedCategory.map (T.toTensor A B) ≫
        ((restriction X U).mapDerivedCategoryFactors.app
          (((tensorComplex X.O).obj A).obj B)).hom ≫
        DerivedCategory.Q.map (restrictTensorComplexOver X U A B) =
      (derivedTensorRestrictNatIso X U T TU).hom.app
          (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        tensorRestrictFactorsHom X U TU A B ≫
        TU.toTensor ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B) := by
  obtain ⟨A₀, p, hA₀, hp⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.O A
  obtain ⟨B₀, q, hB₀, hq⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.O B
  have hfi :
      @IsIso (DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O)) _
        (DerivedCategory.Q.obj A₀, DerivedCategory.Q.obj B₀)
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B)
        (DerivedCategory.Q.map p, DerivedCategory.Q.map q) :=
    (isIso_prod_iff _ _).2
      ⟨(DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp,
        (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq⟩
  apply (cancel_epi ((tensorRestrictSourceFunctor X U T).map
    ((DerivedCategory.Q.map p, DerivedCategory.Q.map q) :
      (DerivedCategory.Q.obj A₀, DerivedCategory.Q.obj B₀) ⟶
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B)))).1
  have hL : (tensorRestrictSourceFunctor X U T).map
          ((DerivedCategory.Q.map p, DerivedCategory.Q.map q) :
            (DerivedCategory.Q.obj A₀, DerivedCategory.Q.obj B₀) ⟶
              (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B)) ≫
        ((restriction X U).mapDerivedCategory.map (T.toTensor A B) ≫
          ((restriction X U).mapDerivedCategoryFactors.app
            (((tensorComplex X.O).obj A).obj B)).hom ≫
          DerivedCategory.Q.map (restrictTensorComplexOver X U A B)) =
      (restriction X U).mapDerivedCategory.map (T.toTensor A₀ B₀) ≫
        ((restriction X U).mapDerivedCategoryFactors.app
            (((tensorComplex X.O).obj A₀).obj B₀)).hom ≫
        DerivedCategory.Q.map (restrictTensorComplexOver X U A₀ B₀) ≫
        DerivedCategory.Q.map (tensorComplexOverPairMap X U p q) := by
    rw [tensorRestrictSourceFunctor_map_Q', ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, toTensorPairSquare X T p q,
      CategoryTheory.Functor.map_comp, Category.assoc]
    erw [reassoc_of% (restriction X U).mapDerivedCategoryFactors_hom_naturality
      (tensorComplexPairMap X p q)]
    rw [← CategoryTheory.Functor.map_comp, tensorComplexOverIsoSquare X U p q,
      CategoryTheory.Functor.map_comp]
    rfl
  have hR : (tensorRestrictSourceFunctor X U T).map
          ((DerivedCategory.Q.map p, DerivedCategory.Q.map q) :
            (DerivedCategory.Q.obj A₀, DerivedCategory.Q.obj B₀) ⟶
              (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B)) ≫
        ((derivedTensorRestrictNatIso X U T TU).hom.app
            (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
          tensorRestrictFactorsHom X U TU A B ≫
          TU.toTensor ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B)) =
      (derivedTensorRestrictNatIso X U T TU).hom.app
          (DerivedCategory.Q.obj A₀, DerivedCategory.Q.obj B₀) ≫
        tensorRestrictFactorsHom X U TU A₀ B₀ ≫
        TU.toTensor ((restrictionComplex X U).obj A₀)
            ((restrictionComplex X U).obj B₀) ≫
        DerivedCategory.Q.map (tensorComplexOverPairMap X U p q) := by
    rw [← Category.assoc, (derivedTensorRestrictNatIso X U T TU).hom.naturality
      ((DerivedCategory.Q.map p, DerivedCategory.Q.map q) :
        (DerivedCategory.Q.obj A₀, DerivedCategory.Q.obj B₀) ⟶
          (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B)),
      Category.assoc, tensorRestrictTargetFunctor_map_Q']
    simp only [Category.assoc]
    rw [reassoc_of% tensorRestrictFactorsHom_naturality X U TU p q,
      toTensorOverPairSquare X U TU p q]
  rw [hL, hR, reassoc_of% toTensor_restrict_square_kFlat X U T TU A₀ B₀ hA₀ hB₀]

end Stacks.DerivedTensor.SliceRestriction

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceNaturality

/-!
# The derived tensor product commutes with restriction to a slice, naturally

Let `(C, O)` be a ringed site and let `U` be an object of `C`.
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceNaturality`
assembles the inputs of the naturality of
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIsoOfKFlat` and records that one of
the five squares it splits into was missing: the junction between the comparison field of
Stacks 06YU and Mathlib's `CategoryTheory.Functor.mapDerivedCategoryFactors`. This file supplies
that square, chains all five, extends the naturality to an arbitrary morphism of `D(O) × D(O)`
by the calculus of fractions, and assembles the comparison into a natural isomorphism of
functors `D(O) × D(O) ⥤ D(O|_U)`.

## The junction, and what unblocks it

`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison` has target `Q(Tot(K ⊗_O L))`
with the total complex spelled `Stacks.SheafOfModules.Tensor.tensorComplex`, while its
naturality field ends in `Q.map (HomologicalComplex.mapBifunctorMap f g ...)`, whose own source
and target are spelled `HomologicalComplex.mapBifunctor`. The two spellings are definitionally
equal — that is `Stacks.DerivedTensor.SliceRestriction.tensorComplex_obj_obj_eq`, which is
`rfl` — but the composite recorded in the field carries *both* at once, so a rewrite written in
either one alone does not match it.

The measurement that unblocks this is that **the identification is cheap exactly when both
types are concrete**, and ruinous when it has to be discovered through a metavariable under
`DerivedCategory.Q.obj`. So the induced map of total complexes is given a name,
`tensorComplexPairMap`, whose *ascribed type* is in the `tensorComplex` spelling; the
identification is then paid once, inside that definition, and every statement below is uniformly
in one spelling. The orientation of each equation matters for the same reason: the comparison is
written first, so that the composite elaborates left to right and the spelling of the
`DerivedCategory.Q.map` in it is fixed by the comparison rather than discovered from the
induced map.

## Main results

* `Stacks.DerivedTensor.SliceRestriction.comparisonRestrictFactorsSquare`: the junction — the
  first two squares, the comparison of Stacks 06YU restricted and Mathlib's identification of
  the derived restriction of a class with the class of a restriction, joined.
* `Stacks.DerivedTensor.SliceRestriction.tensorComplexOverIsoSquare`: the third square, the
  chain-level naturality of `AlgebraicGeometry.RingedSite.tensorComplexOverIso` respelled.
* `Stacks.DerivedTensor.SliceRestriction.comparisonOverInvSquare`: the fourth square, the
  comparison of Stacks 06YU on the site over `U`, read through its inverse.
* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIsoOfKFlat_hom_naturality`: the
  four chained.
* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictModelIso_hom_naturality`: all
  five — the comparison at a pair of K-flat complexes is natural for a pair of morphisms of
  complexes.
* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictModelIso_natural`: the same for
  an arbitrary morphism of `D(O) × D(O)` between classes of K-flat complexes, by the calculus
  of fractions.
* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso`: **the derived tensor
  product commutes with restriction to a slice, naturally in both variables** —
  `(K ⊗^L_O L)|_U ≅ K|_U ⊗^L_{O|_U} L|_U` as an isomorphism of functors
  `D(O) × D(O) ⥤ D(O|_U)`, the derived tensor product analogue of Stacks 08JB.

## Why a separate module

The statements below do not elaborate inside
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceNaturality`:
placed there, verbatim and with the same variable block, the two that mention a comparison
exhaust the heartbeat budget while elaborating `T.comparison A' B' hA' hB'`, and they elaborate
at once here. The local instance and the `implicit_reducible`
declarations of that module are not the cause, since varying them one at a time changes
nothing; what is left is the import boundary itself. This module therefore carries the
`implicit_reducible` declaration of `tensorComplex` and nothing else from there, together with one
of `tensorRestrictSourceFunctor` and `tensorRestrictTargetFunctor` in the last section: without it
`Category.assoc` cannot be applied across the junction between a value of either functor and
the composite `derivedTensorRestrictModelIso` is built from, the two being equal only after
those `def`s are unfolded.

## What this file does not contain

**No assertion of Stacks 08JJ, and nothing is tagged.** What the natural isomorphism above
supplies is one of the two inputs the restriction compatibility of the canonical map

`Φ : M ⊗^L_O K^∨ ⟶ RSheafHom_O(K, M)`

of Stacks 08JD needs, the one three modules —
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionRestriction`,
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals` — record as absent. The other is
the compatibility of `Φ` itself with the composition morphism of Stacks 0A98, which the library
has only at the chain level, as
`AlgebraicGeometry.RingedSite.compositionMap_restrict_square`. Without that, the locality step
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` still cannot be applied to `Φ`,
and the third assertion of Stacks 08JJ needs in addition the identification of the chain-level
composition morphism of Stacks 0A91, with its Koszul signs, with the module-level map
`Stacks.SheafOfModules.tensorDualToSheafHom`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
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

/-- **The restriction comparison of the total tensor complex**, with its source and target
written at the `restrictionComplex` spelling of the restriction functor.

`AlgebraicGeometry.RingedSite.tensorComplexOverIso` is stated with
`AlgebraicGeometry.RingedSite.restrictComplex`, which is the same functor indexed by `X.ringSheaf`
rather than by `Stacks.SheafOfModules.Tensor.ringSheaf X.O`. The two are definitionally equal, but
the difference is invisible at the transparency `simp` and `rw` use, and with it in place even
`Category.assoc` cannot be applied across this factor. -/
def restrictTensorComplexOver (A B : CochainComplex (Modules X.O) ℤ) :
    (restrictionComplex X U).obj (((tensorComplex X.O).obj A).obj B) ⟶
      ((tensorComplex (X.O.over U)).obj ((restrictionComplex X U).obj A)).obj
        ((restrictionComplex X U).obj B) :=
  (RingedSite.tensorComplexOverIso X U A B).hom

/-- **The four factors of `derivedTensorRestrictIsoOfKFlat`, written out.** The isomorphism is
a `≪≫` of four, so this is `rfl`; it is hoisted into a lemma because `simp` cannot unfold the
last `≪≫` in place — the rewrite changes the type of a subterm and the motive is not type
correct at the transparency `simp` works at. -/
lemma derivedTensorRestrictIsoOfKFlat_hom (A B : CochainComplex (Modules X.O) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B) :
    (derivedTensorRestrictIsoOfKFlat X U T TU A B hA hB).hom =
      (restriction X U).mapDerivedCategory.map (T.comparison A B hA hB).hom ≫
        ((restriction X U).mapDerivedCategoryFactors.app
          (((tensorComplex X.O).obj A).obj B)).hom ≫
        DerivedCategory.Q.map (restrictTensorComplexOver X U A B) ≫
        (TU.comparison ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B)
          (kFlat_restrictionComplex X U A hA) (kFlat_restrictionComplex X U B hB)).inv :=
  rfl

variable {A A' B B' : CochainComplex (Modules X.O) ℤ} (a : A ⟶ A') (b : B ⟶ B')
  (hA : Stacks.SheafOfModules.KFlat X.O A)
  (hA' : Stacks.SheafOfModules.KFlat X.O A')
  (hB : Stacks.SheafOfModules.KFlat X.O B)
  (hB' : Stacks.SheafOfModules.KFlat X.O B')

/-- **The map induced on total tensor complexes by a pair of morphisms of complexes**, with its
type written at the spelling `Stacks.SheafOfModules.Tensor.tensorComplex`.

Mathlib's `HomologicalComplex.mapBifunctorMap` spells its source and target through
`HomologicalComplex.mapBifunctor`, while the comparison field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` spells them through `tensorComplex`. The
two are definitionally equal, by `tensorComplex_obj_obj_eq`, but a composite of a morphism
spelled one way with a morphism spelled the other carries both spellings in its implicit
arguments, and then neither alone matches it. Ascribing the type here pays the identification
once, on concrete arguments, which is where it is cheap. -/
def tensorComplexPairMap :
    ((tensorComplex X.O).obj A).obj B ⟶ ((tensorComplex X.O).obj A').obj B' :=
  HomologicalComplex.mapBifunctorMap a b (sheafTensor X.O) (ComplexShape.up ℤ)

/-- The induced map on the site over `U`, between the total tensor complexes of the
restrictions, with its type ascribed at the `tensorComplex` spelling for the same reason. -/
def tensorComplexOverPairMap :
    ((tensorComplex (X.O.over U)).obj ((restrictionComplex X U).obj A)).obj
        ((restrictionComplex X U).obj B) ⟶
      ((tensorComplex (X.O.over U)).obj ((restrictionComplex X U).obj A')).obj
        ((restrictionComplex X U).obj B') :=
  HomologicalComplex.mapBifunctorMap ((restrictionComplex X U).map a)
    ((restrictionComplex X U).map b) (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)

/-- **The comparison field of Stacks 06YU, respelled.** It is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison_naturality` and nothing more;
what it adds is that the induced map of total complexes is `tensorComplexPairMap`, so that both
sides of the equation are in the `tensorComplex` spelling and the equation can be composed with
a square stated in that spelling. -/
lemma comparisonPairSquare :
    (T.comparison A B hA hB).hom ≫ DerivedCategory.Q.map (tensorComplexPairMap X a b) =
      (T.tensor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj B) ≫
        (T.tensor.obj (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map b) ≫
        (T.comparison A' B' hA' hB').hom :=
  (T.comparison_naturality a b hA hA' hB hB').symm

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)] in
/-- **The first two squares, joined — the junction.** The restriction of the comparison of
Stacks 06YU followed by Mathlib's identification of the derived restriction of a class with the
class of a restriction is natural for a pair of morphisms of K-flat complexes.

The proof is `comparisonPairSquare` and
`CategoryTheory.Functor.mapDerivedCategoryFactors_hom_naturality` composed. What makes the
composition possible is that the induced map is named: that fixes the implicit source and
target of the `DerivedCategory.Q.map` in the `tensorComplex` spelling, which is the spelling
both the comparison's target and the `.app` argument of `mapDerivedCategoryFactors` are already
in, so that `CategoryTheory.Functor.map_comp` finds the composite. -/
lemma comparisonRestrictFactorsSquare :
    (restriction X U).mapDerivedCategory.map (T.comparison A B hA hB).hom ≫
        ((restriction X U).mapDerivedCategoryFactors.app
          (((tensorComplex X.O).obj A).obj B)).hom ≫
        DerivedCategory.Q.map ((restrictionComplex X U).map (tensorComplexPairMap X a b)) =
      (restriction X U).mapDerivedCategory.map
          ((T.tensor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj B) ≫
            (T.tensor.obj (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map b)) ≫
        (restriction X U).mapDerivedCategory.map (T.comparison A' B' hA' hB').hom ≫
        ((restriction X U).mapDerivedCategoryFactors.app
          (((tensorComplex X.O).obj A').obj B')).hom := by
  have h2 := (restriction X U).mapDerivedCategoryFactors_hom_naturality
    (tensorComplexPairMap X a b)
  rw [← Iso.app_hom, ← Iso.app_hom] at h2
  rw [← h2, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    comparisonPairSquare X T a b hA hA' hB hB']
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

omit [HasDerivedCategory.{d} (Modules X.O)] [HasDerivedCategory.{d} (Modules (X.O.over U))] in
/-- **The third square**: the chain-level naturality of the restriction comparison of the total
tensor complex, `AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality_mapBifunctorMap`,
respelled through `tensorComplexPairMap` and `tensorComplexOverPairMap` so that it composes with
the squares on either side of it. -/
lemma tensorComplexOverIsoSquare :
    (restrictionComplex X U).map (tensorComplexPairMap X a b) ≫
        restrictTensorComplexOver X U A' B' =
      restrictTensorComplexOver X U A B ≫ tensorComplexOverPairMap X U a b :=
  RingedSite.tensorComplexOverIso_hom_naturality_mapBifunctorMap X U a b

omit [HasDerivedCategory.{d} (Modules X.O)] in
/-- **The fourth square**: the comparison of Stacks 06YU on the site over `U`, read through its
inverse, which is how it occurs in `derivedTensorRestrictIsoOfKFlat`. The restrictions are
K-flat by Stacks 0E8K. -/
lemma comparisonOverInvSquare :
    DerivedCategory.Q.map (tensorComplexOverPairMap X U a b) ≫
        (TU.comparison ((restrictionComplex X U).obj A') ((restrictionComplex X U).obj B')
          (kFlat_restrictionComplex X U A' hA') (kFlat_restrictionComplex X U B' hB')).inv =
      (TU.comparison ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B)
          (kFlat_restrictionComplex X U A hA) (kFlat_restrictionComplex X U B hB)).inv ≫
        ((TU.tensor.map (DerivedCategory.Q.map ((restrictionComplex X U).map a))).app
            (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≫
          (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A'))).map
            (DerivedCategory.Q.map ((restrictionComplex X U).map b))) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, Category.assoc]
  exact (TU.comparison_naturality ((restrictionComplex X U).map a)
    ((restrictionComplex X U).map b) (kFlat_restrictionComplex X U A hA)
    (kFlat_restrictionComplex X U A' hA') (kFlat_restrictionComplex X U B hB)
    (kFlat_restrictionComplex X U B' hB')).symm

/-- **The derived tensor product comparison with a slice is natural at a pair of K-flat
complexes, for a pair of morphisms of complexes.**

This is the four squares above chained along the four factors of
`derivedTensorRestrictIsoOfKFlat`: the restricted comparison of Stacks 06YU and Mathlib's
identification of the derived restriction of a class with the class of a restriction
(`comparisonRestrictFactorsSquare`), the chain-level comparison of the total tensor complexes
(`tensorComplexOverIsoSquare`), and the comparison of Stacks 06YU on the slice site, inverted
(`comparisonOverInvSquare`). -/
lemma derivedTensorRestrictIsoOfKFlat_hom_naturality :
    (derivedTensorRestrictIsoOfKFlat X U T TU A B hA hB).hom ≫
        ((TU.tensor.map (DerivedCategory.Q.map ((restrictionComplex X U).map a))).app
            (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≫
          (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A'))).map
            (DerivedCategory.Q.map ((restrictionComplex X U).map b))) =
      (restriction X U).mapDerivedCategory.map
          ((T.tensor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj B) ≫
            (T.tensor.obj (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map b)) ≫
        (derivedTensorRestrictIsoOfKFlat X U T TU A' B' hA' hB').hom := by
  rw [derivedTensorRestrictIsoOfKFlat_hom X U T TU A B hA hB,
    derivedTensorRestrictIsoOfKFlat_hom X U T TU A' B' hA' hB']
  simp only [Category.assoc]
  rw [← comparisonOverInvSquare X U TU a b hA hA' hB hB',
    ← CategoryTheory.Functor.map_comp_assoc, ← tensorComplexOverIsoSquare X U a b,
    CategoryTheory.Functor.map_comp_assoc,
    reassoc_of% comparisonRestrictFactorsSquare X U T a b hA hA' hB hB']

/-! ### The square at the level of the models -/

section Models

attribute [local implicit_reducible] tensorRestrictSourceFunctor tensorRestrictTargetFunctor

variable (m m' : tensorRestrictModels X)

/-- The three factors of `derivedTensorRestrictModelIso`, written out; `rfl`, hoisted for the
same reason as `derivedTensorRestrictIsoOfKFlat_hom`. -/
lemma derivedTensorRestrictModelIso_hom :
    (derivedTensorRestrictModelIso X U T TU m).hom =
      (derivedTensorRestrictIsoOfKFlat X U T TU m.1.1 m.2.1 m.1.2 m.2.2).hom ≫
        (TU.tensor.map ((restriction X U).mapDerivedCategoryFactors.app m.1.1).inv).app
            (DerivedCategory.Q.obj ((restrictionComplex X U).obj m.2.1)) ≫
          (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj m.1.1))).map
            ((restriction X U).mapDerivedCategoryFactors.app m.2.1).inv :=
  rfl

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)] in
/-- The source functor on a pair of classes of morphisms of complexes; `rfl`. -/
lemma tensorRestrictSourceFunctor_map_Q (a : m.1.1 ⟶ m'.1.1) (b : m.2.1 ⟶ m'.2.1) :
    (tensorRestrictSourceFunctor X U T).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          tensorRestrictModelObject X m ⟶ tensorRestrictModelObject X m') =
      (restriction X U).mapDerivedCategory.map
        ((T.tensor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj m.2.1) ≫
          (T.tensor.obj (DerivedCategory.Q.obj m'.1.1)).map (DerivedCategory.Q.map b)) :=
  rfl

/-- The target functor on a pair of classes of morphisms of complexes; `rfl`. -/
lemma tensorRestrictTargetFunctor_map_Q (a : m.1.1 ⟶ m'.1.1) (b : m.2.1 ⟶ m'.2.1) :
    (tensorRestrictTargetFunctor X U TU).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          tensorRestrictModelObject X m ⟶ tensorRestrictModelObject X m') =
      (TU.tensor.map ((restriction X U).mapDerivedCategory.map
            (DerivedCategory.Q.map a))).app
          ((restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj m.2.1)) ≫
        (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj m'.1.1))).map
          ((restriction X U).mapDerivedCategory.map (DerivedCategory.Q.map b)) :=
  rfl

/-- **The comparison at a pair of K-flat complexes is natural for a pair of morphisms of
complexes**, as a square between the two functors
`Stacks.DerivedTensor.SliceRestriction.tensorRestrictSourceFunctor` and
`Stacks.DerivedTensor.SliceRestriction.tensorRestrictTargetFunctor`.

This is `derivedTensorRestrictIsoOfKFlat_hom_naturality` with the fifth square,
`tensorOver_mapDerivedCategoryFactors_inv_naturality`, folded in — all five of the squares the
naturality of `derivedTensorRestrictModelIso` splits into. -/
lemma derivedTensorRestrictModelIso_hom_naturality
    (a : m.1.1 ⟶ m'.1.1) (b : m.2.1 ⟶ m'.2.1) :
    (tensorRestrictSourceFunctor X U T).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          tensorRestrictModelObject X m ⟶ tensorRestrictModelObject X m') ≫
      (derivedTensorRestrictModelIso X U T TU m').hom =
    (derivedTensorRestrictModelIso X U T TU m).hom ≫
      (tensorRestrictTargetFunctor X U TU).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          tensorRestrictModelObject X m ⟶ tensorRestrictModelObject X m') := by
  have h5 := tensorOver_mapDerivedCategoryFactors_inv_naturality X U TU
    m.1.1 m'.1.1 m.2.1 m'.2.1 a b
  have h4 := derivedTensorRestrictIsoOfKFlat_hom_naturality X U T TU a b
    m.1.2 m'.1.2 m.2.2 m'.2.2
  simp only [Category.assoc] at h4 h5
  rw [tensorRestrictSourceFunctor_map_Q, tensorRestrictTargetFunctor_map_Q,
    derivedTensorRestrictModelIso_hom, derivedTensorRestrictModelIso_hom]
  simp only [Category.assoc]
  rw [← h5, ← reassoc_of% h4]

/-- **Naturality of the comparison between models, for an arbitrary morphism of
`D(O) × D(O)`.** Both slots are factored simultaneously through a single third pair of K-flat
complexes: each by a right fraction, whose apex is then replaced by a K-flat resolution of it
(Stacks 06YS). The given morphism is thus the inverse of an invertible morphism of model pairs
followed by another one, both of which come from morphisms of complexes, and naturality for
those is `derivedTensorRestrictModelIso_hom_naturality`. -/
lemma derivedTensorRestrictModelIso_natural
    (f : tensorRestrictModelObject X m ⟶ tensorRestrictModelObject X m') :
    (tensorRestrictSourceFunctor X U T).map f ≫
        (derivedTensorRestrictModelIso X U T TU m').hom =
      (derivedTensorRestrictModelIso X U T TU m).hom ≫
        (tensorRestrictTargetFunctor X U TU).map f := by
  obtain ⟨A₀, sa, hsa, ga, ha⟩ := DerivedCategory.right_fac f.1
  obtain ⟨B₀, sb, hsb, gb, hb⟩ := DerivedCategory.right_fac f.2
  obtain ⟨AF, qa, hAF, hqa⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.O A₀
  obtain ⟨BF, qb, hBF, hqb⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.O B₀
  have hqa' : IsIso (DerivedCategory.Q.map qa) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqa
  have hqb' : IsIso (DerivedCategory.Q.map qb) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqb
  have hs := derivedTensorRestrictModelIso_hom_naturality X U T TU
    (⟨⟨AF, hAF⟩, ⟨BF, hBF⟩⟩ : tensorRestrictModels X) m (qa ≫ sa) (qb ≫ sb)
  have ht := derivedTensorRestrictModelIso_hom_naturality X U T TU
    (⟨⟨AF, hAF⟩, ⟨BF, hBF⟩⟩ : tensorRestrictModels X) m' (qa ≫ ga) (qb ≫ gb)
  have := hsa
  have := hsb
  have := hqa'
  have := hqb'
  have ha' : IsIso (DerivedCategory.Q.map (qa ≫ sa)) := by
    rw [CategoryTheory.Functor.map_comp]; infer_instance
  have hb' : IsIso (DerivedCategory.Q.map (qb ≫ sb)) := by
    rw [CategoryTheory.Functor.map_comp]; infer_instance
  have hsIso :
      @IsIso (DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O)) _
        (tensorRestrictModelObject X (⟨⟨AF, hAF⟩, ⟨BF, hBF⟩⟩ : tensorRestrictModels X))
        (tensorRestrictModelObject X m)
        (DerivedCategory.Q.map (qa ≫ sa), DerivedCategory.Q.map (qb ≫ sb)) :=
    (isIso_prod_iff _ _).2 ⟨ha', hb'⟩
  have hsf : ((DerivedCategory.Q.map (qa ≫ sa), DerivedCategory.Q.map (qb ≫ sb)) :
        tensorRestrictModelObject X (⟨⟨AF, hAF⟩, ⟨BF, hBF⟩⟩ : tensorRestrictModels X) ⟶
          tensorRestrictModelObject X m) ≫ f =
      ((DerivedCategory.Q.map (qa ≫ ga), DerivedCategory.Q.map (qb ≫ gb)) :
        tensorRestrictModelObject X (⟨⟨AF, hAF⟩, ⟨BF, hBF⟩⟩ : tensorRestrictModels X) ⟶
          tensorRestrictModelObject X m') := by
    ext
    · change DerivedCategory.Q.map (qa ≫ sa) ≫ f.1 = DerivedCategory.Q.map (qa ≫ ga)
      simp only [ha, CategoryTheory.Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    · change DerivedCategory.Q.map (qb ≫ sb) ≫ f.2 = DerivedCategory.Q.map (qb ≫ gb)
      simp only [hb, CategoryTheory.Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  apply (cancel_epi ((tensorRestrictSourceFunctor X U T).map
    ((DerivedCategory.Q.map (qa ≫ sa), DerivedCategory.Q.map (qb ≫ sb)) :
      tensorRestrictModelObject X (⟨⟨AF, hAF⟩, ⟨BF, hBF⟩⟩ : tensorRestrictModels X) ⟶
        tensorRestrictModelObject X m))).1
  rw [← CategoryTheory.Functor.map_comp_assoc, hsf, ht, ← Category.assoc, hs, Category.assoc,
    ← CategoryTheory.Functor.map_comp, hsf]

/-- The model chosen for a pair of objects of `D(O)`: the chosen K-flat representative of each
slot, `Stacks.DerivedTensor.RingedSite.kFlatModel`. -/
def tensorRestrictChosenModel (d : DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O)) :
    tensorRestrictModels X :=
  (⟨Stacks.DerivedTensor.RingedSite.kFlatModel X.O d.1,
      Stacks.DerivedTensor.RingedSite.kFlatModel_kFlat X.O d.1⟩,
    ⟨Stacks.DerivedTensor.RingedSite.kFlatModel X.O d.2,
      Stacks.DerivedTensor.RingedSite.kFlatModel_kFlat X.O d.2⟩)

/-- The chosen model does present the given pair of objects of `D(O)`. -/
def tensorRestrictChosenModelIso
    (d : DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O)) :
    tensorRestrictModelObject X (tensorRestrictChosenModel X d) ≅ d :=
  (Stacks.DerivedTensor.RingedSite.kFlatModelIso X.O d.1).prod
    (Stacks.DerivedTensor.RingedSite.kFlatModelIso X.O d.2)

/-- **The derived tensor product commutes with restriction to a slice, naturally in both
variables.** The comparison

`(K ⊗^L_O L)|_U ≅ K|_U ⊗^L_{O|_U} L|_U`

as an isomorphism of functors `D(O) × D(O) ⥤ D(O|_U)`. This is the derived tensor product
analogue of Stacks 08JB, which is the same statement for the derived internal Hom.

It is `derivedTensorRestrictModelIso` on the pairs of K-flat complexes, extended by
`CategoryTheory.NatIso.ofModels`: every object of `D(O)` is the class of a K-flat complex by
Stacks 06YS, and the comparison on those pairs is natural by
`derivedTensorRestrictModelIso_natural`. -/
def derivedTensorRestrictNatIso :
    tensorRestrictSourceFunctor X U T ≅ tensorRestrictTargetFunctor X U TU :=
  NatIso.ofModels (tensorRestrictSourceFunctor X U T) (tensorRestrictTargetFunctor X U TU)
    (tensorRestrictModelObject X) (derivedTensorRestrictModelIso X U T TU)
    (derivedTensorRestrictModelIso_natural X U T TU)
    (tensorRestrictChosenModel X) (tensorRestrictChosenModelIso X)

/-- At a pair of K-flat complexes the natural isomorphism is the comparison it was built
from. -/
lemma derivedTensorRestrictNatIso_hom_app_models (n : tensorRestrictModels X) :
    (derivedTensorRestrictNatIso X U T TU).hom.app (tensorRestrictModelObject X n) =
      (derivedTensorRestrictModelIso X U T TU n).hom :=
  NatIso.ofModels_hom_app_models _ _ _ _ _ _ _ n

end Models

end Stacks.DerivedTensor.SliceRestriction

end

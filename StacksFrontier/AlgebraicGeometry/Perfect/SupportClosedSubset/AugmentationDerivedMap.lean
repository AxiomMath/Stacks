module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData

/-!
# The augmentation of the extended alternating Čech complex (Stacks 0G7L)

The extended alternating Čech complex of Stacks 0G7I is a complex of `𝒪_X`-modules indexed by
`ℕ` whose degree-`0` term is canonically the coefficient module `F`.  Projecting onto that term
gives a map of `ℕ`-indexed complexes onto `F` placed in degree `0`; extending both sides by zero
to `ℤ`-indexed complexes and passing to the derived category gives the canonical map

`𝓕^• ⟶ F[0]`

which Stacks 0G7L uses to compare the complex with `i_* R𝓗_Z(F)`.

## Main definitions

* `Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentationComplex`: the projection of the
  `ℕ`-indexed complex onto its
  degree-`0` term, as a map of complexes.
* `Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation`: the induced map in the
  unbounded derived category.

## Main results

* `Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation_natural`: the augmentation is
  natural in the coefficient module.
* `Stacks.Perfect.ExtendedAlternatingCech.Augmentation.isIso_augmentationComplex_f_zero`: the
  augmentation is an isomorphism in
  degree `0`.
* `Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentationComplex_f_succ_eq_zero`: it is
  zero in every positive degree,
  the target being zero there.

## Implementation notes

`augmentationComplex` is defined through `CochainComplex.toSingle₀Equiv`, which identifies maps
into `(CochainComplex.single₀ _).obj F` with maps `complex.X 0 ⟶ F` annihilating the first
differential; the chosen element is `zeroIso.hom`, so the composite is an isomorphism in
degree `0` by construction and zero in positive degrees because `single₀` is.

The `ℤ`-indexed form is obtained with `HomologicalComplex.extendMap` along
`ComplexShape.embeddingUpNat`, followed by `HomologicalComplex.extendSingleIso`, which
identifies the extension of `single₀ F` with the `ℤ`-indexed `single 0 F` that
`DerivedCategory.singleFunctor _ 0` lands in.  Naturality is proved at the level of complexes
and then transported by `DerivedCategory.Q.map`, which is the only step that leaves the
`1`-categorical setting; stating it this way avoids reasoning with derived-category morphisms.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.ExtendedAlternatingCech.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-- Projection of the extended alternating Čech complex onto its degree-zero term. -/
public def augmentationComplex (F : X.Modules) :
    (extendedAlternatingCech f F).complex ⟶ (CochainComplex.single₀ X.Modules).obj F :=
  (((extendedAlternatingCech f F).complex.toSingle₀Equiv F).symm
    (extendedAlternatingCech f F).zeroIso.hom)

/-- In degree `0` the projection is the canonical identification of the degree-`0` term with the
coefficient module, hence an isomorphism. -/
public instance isIso_augmentationComplex_f_zero (F : X.Modules) :
    IsIso ((augmentationComplex f F).f 0) := by
  have h : (augmentationComplex f F).f 0 =
      (extendedAlternatingCech f F).zeroIso.hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv := by
    simp [augmentationComplex, CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
  rw [h]
  infer_instance

/-- In positive degrees the projection vanishes, its target being zero there. -/
public theorem augmentationComplex_f_succ_eq_zero (F : X.Modules) (p : ℕ) :
    (augmentationComplex f F).f (p + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 F (p + 1)
    (by omega)).eq_of_tgt _ _

/-- **Stacks Project, Tag 0G7L.** The canonical map from the extended alternating Čech complex
to its coefficient module placed in degree `0`, in the unbounded derived category. -/
@[stacks 0G7L "augmentation"]
public def augmentation (F : X.Modules) :
    DerivedCategory.Q.obj
        ((extendedAlternatingCech f F).complex.extend ComplexShape.embeddingUpNat) ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj F :=
  DerivedCategory.Q.map
    ((HomologicalComplex.extendMap (augmentationComplex f F) ComplexShape.embeddingUpNat) ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom)

/-- **Stacks Project, Tag 0G7L.** The canonical augmentation is natural in the coefficient
module. -/
@[stacks 0G7L "augmentation"]
public theorem augmentation_natural {F G : X.Modules} (φ : F ⟶ G) :
    DerivedCategory.Q.map
        (HomologicalComplex.extendMap ((extendedAlternatingCechFunctor f).map φ)
          ComplexShape.embeddingUpNat) ≫
      augmentation f G =
    augmentation f F ≫ (DerivedCategory.singleFunctor X.Modules 0).map φ := by
  have h₀ :
      ((extendedAlternatingCechFunctor f).map φ) ≫ augmentationComplex f G =
        augmentationComplex f F ≫ (CochainComplex.single₀ X.Modules).map φ := by
    apply (CochainComplex.toSingle₀Equiv
      (extendedAlternatingCech f F).complex G).injective
    simpa [augmentationComplex] using (extendedAlternatingCechFunctor f).map_zero φ
  have hsingle :
      HomologicalComplex.extendMap ((CochainComplex.single₀ X.Modules).map φ)
          ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 (by simp)).hom =
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 (by simp)).hom ≫
          (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ := by
    let e := ComplexShape.embeddingUpNat
    have hzero : e.f 0 = 0 := rfl
    change HomologicalComplex.extendMap ((CochainComplex.single₀ X.Modules).map φ) e ≫
          (HomologicalComplex.extendSingleIso e G 0 0 hzero).hom =
        (HomologicalComplex.extendSingleIso e F 0 0 hzero).hom ≫
          (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    by_cases hn : n = 0
    · subst n
      rw [HomologicalComplex.comp_f,
        HomologicalComplex.extendMap_f (φ := (CochainComplex.single₀ X.Modules).map φ)
          (e := e) (h := hzero),
        HomologicalComplex.extendSingleIso_hom_f e G 0 0 hzero, HomologicalComplex.comp_f,
        HomologicalComplex.extendSingleIso_hom_f e F 0 0 hzero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp [CochainComplex.single₀, HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single_map_f_self]
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn).eq_of_tgt _ _
  have hcomplex :
      HomologicalComplex.extendMap ((extendedAlternatingCechFunctor f).map φ)
          ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.extendMap (augmentationComplex f G)
              ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0
              (by simp)).hom) =
        (HomologicalComplex.extendMap (augmentationComplex f F) ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0
              (by simp)).hom) ≫
          (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ := by
    calc
      _ = (HomologicalComplex.extendMap ((extendedAlternatingCechFunctor f).map φ)
              ComplexShape.embeddingUpNat ≫
            HomologicalComplex.extendMap (augmentationComplex f G)
              ComplexShape.embeddingUpNat) ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0
              (by simp)).hom := by rw [Category.assoc]
      _ = HomologicalComplex.extendMap
            (((extendedAlternatingCechFunctor f).map φ) ≫ augmentationComplex f G)
              ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0
              (by simp)).hom := by rw [← HomologicalComplex.extendMap_comp]
      _ = HomologicalComplex.extendMap
            (augmentationComplex f F ≫ (CochainComplex.single₀ X.Modules).map φ)
              ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0
              (by simp)).hom := by rw [h₀]
      _ = HomologicalComplex.extendMap (augmentationComplex f F) ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendMap ((CochainComplex.single₀ X.Modules).map φ)
                ComplexShape.embeddingUpNat ≫
              (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0
                (by simp)).hom) := by rw [HomologicalComplex.extendMap_comp, Category.assoc]
      _ = HomologicalComplex.extendMap (augmentationComplex f F) ComplexShape.embeddingUpNat ≫
            ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0
                (by simp)).hom ≫
              (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ) := by
          rw [hsingle]
      _ = _ := by rw [← Category.assoc]
  change DerivedCategory.Q.map
      (HomologicalComplex.extendMap ((extendedAlternatingCechFunctor f).map φ)
        ComplexShape.embeddingUpNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap (augmentationComplex f G) ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0
              (by simp)).hom) =
    DerivedCategory.Q.map
      (HomologicalComplex.extendMap (augmentationComplex f F) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 (by simp)).hom) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ)
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  exact congrArg DerivedCategory.Q.map hcomplex

end Stacks.Perfect.ExtendedAlternatingCech.Augmentation

end

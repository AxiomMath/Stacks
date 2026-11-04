module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ExtendedAlternatingCech

/-!
# Augmentation of the extended alternating Čech complex

The degree-zero term of the extended alternating Čech complex of a module is canonically
isomorphic to the module. Projection onto this term gives the augmentation of the complex, both
at the level of cochain complexes and, after extending the grading from `ℕ` to `ℤ`, in the
unbounded derived category of sheaves of modules.

## Main definitions

* `AlgebraicGeometry.ExtendedAlternatingCech.augmentationComplex`: the projection onto the
  degree-zero term, as a map of cochain complexes indexed by `ℕ`.
* `AlgebraicGeometry.ExtendedAlternatingCech.augmentation`: the canonical derived-category map.

## Main results

* `AlgebraicGeometry.ExtendedAlternatingCech.augmentation_natural`: naturality of the
  augmentation in the coefficient module.

## Implementation notes

The complex indexed by natural numbers is extended by zero to integer degrees. The projection is
the morphism corresponding to the degree-zero isomorphism under `CochainComplex.toSingle₀Equiv`;
thus it is the identity in degree zero after that identification and zero in all positive
degrees.

## References

* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ExtendedAlternatingCech

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-- Projection of the extended alternating Čech complex onto its degree-zero term. -/
public def augmentationComplex (F : X.Modules) :
    (data f F).complex ⟶ (CochainComplex.single₀ X.Modules).obj F :=
  (((data f F).complex.toSingle₀Equiv F).symm (data f F).zeroIso.hom)

/-- The canonical map from the extended alternating Čech complex to its
degree-zero module, in the unbounded derived category. -/
@[stacks 0G7L "augmentation"]
public def augmentation (F : X.Modules) :
    DerivedCategory.Q.obj
        ((data f F).complex.extend ComplexShape.embeddingUpNat) ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj F :=
  DerivedCategory.Q.map
    ((HomologicalComplex.extendMap (augmentationComplex f F)
        ComplexShape.embeddingUpNat) ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom)

/-- The canonical augmentation is natural in the coefficient module. -/
@[stacks 0G7L "augmentation"]
public theorem augmentation_natural {F G : X.Modules} (φ : F ⟶ G) :
    DerivedCategory.Q.map
        (HomologicalComplex.extendMap ((functor f).map φ)
          ComplexShape.embeddingUpNat) ≫
      augmentation f G =
      augmentation f F ≫ (DerivedCategory.singleFunctor X.Modules 0).map φ := by
  have h₀ :
      ((functor f).map φ) ≫ augmentationComplex f G =
        augmentationComplex f F ≫ (CochainComplex.single₀ X.Modules).map φ := by
    apply (CochainComplex.toSingle₀Equiv (data f F).complex G).injective
    simpa [augmentationComplex] using (functor f).map_zero φ
  have hsingle :
      HomologicalComplex.extendMap ((CochainComplex.single₀ X.Modules).map φ)
          ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 (by simp)).hom =
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 (by simp)).hom ≫
          (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ := by
    let e := ComplexShape.embeddingUpNat
    have hzero : e.f 0 = 0 := by
      show ComplexShape.embeddingUpNat.f 0 = 0
      rfl
    show HomologicalComplex.extendMap ((CochainComplex.single₀ X.Modules).map φ) e ≫
          (HomologicalComplex.extendSingleIso e G 0 0 hzero).hom =
        (HomologicalComplex.extendSingleIso e F 0 0 hzero).hom ≫
          (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0
    · subst n
      rw [HomologicalComplex.comp_f]
      rw [HomologicalComplex.extendMap_f
        (φ := (CochainComplex.single₀ X.Modules).map φ)
        (e := e) (h := hzero)]
      rw [HomologicalComplex.extendSingleIso_hom_f e G 0 0 hzero]
      rw [HomologicalComplex.comp_f]
      rw [HomologicalComplex.extendSingleIso_hom_f e F 0 0 hzero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp [CochainComplex.single₀, HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single_map_f_self]
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn).eq_of_tgt _ _
  unfold augmentation
  change _ ≫ _ = _ ≫ DerivedCategory.Q.map
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ)
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp, h₀, HomologicalComplex.extendMap_comp,
    Category.assoc, hsingle, Category.assoc]

end AlgebraicGeometry.ExtendedAlternatingCech

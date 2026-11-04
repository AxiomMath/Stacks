module

public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.ConeHomology

/-!
# Naturality of the degree-zero comparison, in a free module universe

`StacksFrontier/RingTheory/LocalCohomology/FreeUniverse/ConeHomology.lean` identifies the
degree-zero cohomology of derived sections on `U = Spec R \ V(I)` with the degree-one Čech
cocycles, at a module universe `v` independent of the ring universe `u`. This file proves that
identification natural in the module. It is
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/CechHomology.lean` with the constraint
`ModuleCat.{max u v}` removed, plus the one extra step the small model introduces: the passage
from the cocycles of `Cech.cechComplexShrink` to those of `Cech.cechComplex` along
`Cech.cechTermShrinkEquiv` is compatible with the maps induced by a module map.

## Main results

* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerShrink_naturality` — the comparison
  with the cocycles of the small model is natural in the module.
* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerFree_naturality` — **the comparison
  `H⁰(RΓ(U, M̃|U)) ≃ ker d¹` is natural in the module, at a module universe independent of the
  ring universe.** This is the first of the two remaining hypotheses of Stacks 0DWR at that
  universe.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {M N : ModuleCat.{v} R}

/-! ### The action of a module map on the cocycles of the small model -/

/-- The action of a module map on the degree-one cocycles of the small Čech complex: the induced
map on the terms of the small model commutes with its differential, so it preserves the
kernel. -/
def kerCechDShrinkOneMap (g : M ⟶ N) :
    LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1) →ₗ[R]
      LinearMap.ker (Cech.cechDShrink.{v} f (N : Type v) 1) :=
  (Cech.cechTermShrinkMap.{v} f g.hom 1).restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, Cech.cechTermShrinkMap_comp_cechDShrink, LinearMap.comp_apply,
      hx, map_zero]

/-- The underlying element of the image of a cocycle under `kerCechDShrinkOneMap` is the image of
the underlying element under `Cech.cechTermShrinkMap`. -/
@[simp]
theorem kerCechDShrinkOneMap_coe (g : M ⟶ N)
    (x : LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1)) :
    (kerCechDShrinkOneMap.{v} f g x).1 = Cech.cechTermShrinkMap.{v} f g.hom 1 x.1 :=
  LinearMap.coe_restrict_apply _ _

/-- **The passage from the cocycles of the small model to those of `Cech.cechComplex` is
natural.** Both sides are `Cech.cechTermShrinkEquiv` followed by the induced map on the
degree-one Čech term. -/
theorem kerCechDShrinkOneEquivKer_naturality (g : M ⟶ N)
    (x : LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1)) :
    kerCechDShrinkOneEquivKer.{v} f N (kerCechDShrinkOneMap.{v} f g x) =
      kerCechDOneMap f g (kerCechDShrinkOneEquivKer.{v} f M x) := by
  refine Subtype.ext ?_
  rw [kerCechDOneMap_coe, kerCechDShrinkOneEquivKer_coe, kerCechDShrinkOneEquivKer_coe,
    kerCechDShrinkOneMap_coe]
  exact Cech.cechTermShrinkEquiv_cechTermShrinkMap.{v} f g.hom 1 x.1

/-! ### Naturality of the comparison of the cycles with the kernel -/

/-- The comparison of the degree-one cycles of the small model with the kernel of its first
differential is natural in the module. -/
theorem cechCyclesOneIsoKerShrink_hom_naturality (g : M ⟶ N)
    (z : (Cech.cechComplexShrink.{v} f (M : Type v)).cycles 1) :
    (cechCyclesOneIsoKerShrink.{v} f N).hom
        (HomologicalComplex.cyclesMap (Cech.cechComplexShrinkMap.{v} f g) 1 z) =
      kerCechDShrinkOneMap.{v} f g ((cechCyclesOneIsoKerShrink.{v} f M).hom z) := by
  refine Subtype.ext ?_
  rw [kerCechDShrinkOneMap_coe, cechCyclesOneIsoKerShrink_hom_coe,
    cechCyclesOneIsoKerShrink_hom_coe]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (Cech.cechComplexShrinkMap.{v} f g) 1) z

/-- Passing between the natural-number and the integer indexing of the small model is natural in
the module. -/
theorem extendedCechCyclesOneIsoShrink_hom_naturality (g : M ⟶ N)
    (z : (Cech.extendedCechComplexShrink.{v} f (M : Type v)).cycles 1) :
    (extendedCechCyclesOneIsoShrink.{v} f N).hom
        (HomologicalComplex.cyclesMap (Cech.extendedCechComplexShrinkMap.{v} f g) 1 z) =
      HomologicalComplex.cyclesMap (Cech.cechComplexShrinkMap.{v} f g) 1
        ((extendedCechCyclesOneIsoShrink.{v} f M).hom z) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.extendCyclesIso_hom_naturality (Cech.cechComplexShrinkMap.{v} f g)
      ComplexShape.embeddingUpNat (j := 1) (j' := 1) (by simp)) z

/-! ### Naturality of the computation of the cohomology of the cone -/

/-- The computation of the degree-zero cohomology of the small Čech cone is natural in the
module. -/
theorem cechComplementHomologyZeroIsoCyclesShrink_hom_naturality (g : M ⟶ N)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
      ((cechComplementFunctorShrink.{v} f).obj M)) :
    (cechComplementHomologyZeroIsoCyclesShrink.{v} f N).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechComplementFunctorShrink.{v} f).map g) z) =
      HomologicalComplex.cyclesMap (Cech.extendedCechComplexShrinkMap.{v} f g) 1
        ((cechComplementHomologyZeroIsoCyclesShrink.{v} f M).hom z) := by
  have := isIso_extendedCechAugmentationShrink_f_zero.{v} f M
  have := isIso_extendedCechAugmentationShrink_f_zero.{v} f N
  have hfac : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
        ((cechComplementFunctorShrink.{v} f).map g) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f N)) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M)) ≫
        HomologicalComplex.homologyMap (CochainComplex.mappingCone.map
          (extendedCechAugmentationShrink.{v} f M) (extendedCechAugmentationShrink.{v} f N)
          (Cech.extendedCechComplexShrinkMap.{v} f g)
          ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g)
          (extendedCechAugmentationShrink_naturality.{v} f g).symm) 0 :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.naturality _
  have hZ := fun (X : ModuleCat.{v} R) (i : ℤ) (hi : i ≠ 0) =>
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X i hi
  have hcyc := Stacks.MappingCone.homologyIsoCycles_hom_naturality
    (extendedCechAugmentationShrink_naturality.{v} f g).symm 0
    (hZ M _ (by omega))
    (hZ M _ (by omega))
    (hZ N _ (by omega))
    (hZ N _ (by omega))
  show (Stacks.MappingCone.homologyIsoCycles
      (extendedCechAugmentationShrink.{v} f N) 0 _ _).hom
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app
        (CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f N))
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechComplementFunctorShrink.{v} f).map g) z)) = _
  exact (congrArg _ (ConcreteCategory.congr_hom hfac z)).trans (ConcreteCategory.congr_hom hcyc _)

/-! ### Naturality of the comparison -/

/-- **The comparison `H⁰(RΓ(U, M̃|U)) ≃ ker d¹` of the small model is natural in the module.** -/
theorem cechComplementHomologyZeroEquivKerShrink_naturality (g : M ⟶ N)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
      ((cechComplementFunctorShrink.{v} f).obj M)) :
    cechComplementHomologyZeroEquivKerShrink.{v} f N
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechComplementFunctorShrink.{v} f).map g) z) =
      kerCechDShrinkOneMap.{v} f g (cechComplementHomologyZeroEquivKerShrink.{v} f M z) := by
  show (cechCyclesOneIsoKerShrink.{v} f N).hom ((extendedCechCyclesOneIsoShrink.{v} f N).hom
      ((cechComplementHomologyZeroIsoCyclesShrink.{v} f N).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechComplementFunctorShrink.{v} f).map g) z))) = _
  rw [cechComplementHomologyZeroIsoCyclesShrink_hom_naturality,
    extendedCechCyclesOneIsoShrink_hom_naturality, cechCyclesOneIsoKerShrink_hom_naturality]
  rfl

/-- **The comparison `H⁰(RΓ(U, M̃|U)) ≃ ker d¹` is natural in the module, at a module universe
independent of the ring universe.** This is the first of the two hypotheses that remain for
Stacks 0DWR at an independent module universe. -/
theorem cechComplementHomologyZeroEquivKerFree_naturality (g : M ⟶ N)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
      ((cechComplementFunctorShrink.{v} f).obj M)) :
    cechComplementHomologyZeroEquivKerFree.{v} f N
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechComplementFunctorShrink.{v} f).map g) z) =
      kerCechDOneMap f g (cechComplementHomologyZeroEquivKerFree.{v} f M z) := by
  show kerCechDShrinkOneEquivKer.{v} f N (cechComplementHomologyZeroEquivKerShrink.{v} f N
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
        ((cechComplementFunctorShrink.{v} f).map g) z)) = _
  rw [cechComplementHomologyZeroEquivKerShrink_naturality,
    kerCechDShrinkOneEquivKer_naturality]
  rfl

end Stacks.LocalCohomology

end

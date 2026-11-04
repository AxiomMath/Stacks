module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Data.MappingConeNaturality
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Naturality

/-!
# Naturality of the degree-zero cohomology of the Čech cone

Let `R` be a commutative ring, `f : Fin r → R` a finite family and `M` an `R`-module.
`StacksFrontier/RingTheory/LocalCohomology/MappingConeH0/Cech.lean` identifies the degree-zero
cohomology of the cone of the Čech augmentation with the degree-one Čech cocycles,

`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer :
  H⁰(RΓ(U, M̃|U)) ≃ₗ[R] ker (Cech.cechD f M 1)`,

as a composite of three isomorphisms: the comparison of derived-category cohomology with the
cohomology of a cochain complex, the computation of the cohomology of the cone, and the passage
from the integer to the natural-number indexing with the cycles spelled out as a kernel. This file
proves that composite natural in the module. That is the first of the two hypotheses of
`Stacks.LocalCohomology.localizationTriangleDataOfCechHomologyComparison`, hence one of the two
remaining ingredients of the affine localization triangle of Stacks 0DWR.

Each of the three factors is natural for its own reason: the comparison with cochain-complex
cohomology is a natural isomorphism of functors, the computation of the cohomology of the cone is
natural in a commutative square by
`Stacks.MappingCone.homologyIsoCycles_hom_naturality`, and the last two are natural because the
inclusion of the cycles is a monomorphism, so a morphism out of them is determined by its
composite with it.

## Main results

* `Stacks.LocalCohomology.cechCyclesOneIsoKer_hom_coe` — the comparison of the degree-one cycles
  with the kernel of the first Čech differential is the inclusion of the cycles.
* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer_naturality` — **the comparison
  `H⁰(RΓ(U, M̃|U)) ≃ ker d¹` is natural in the module.**

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex

attribute [local instance] HasDerivedCategory.standard

universe w v u

namespace Stacks.LocalCohomology

/-- Transport along an equality of submodules does not change the underlying element. -/
theorem eqToHom_submodule_coe {R : Type u} [Ring R] {X : ModuleCat.{w} R}
    {P Q : Submodule R X} (hPQ : P = Q) (x : ↥P) :
    ((eqToHom (congrArg (fun S : Submodule R X => ModuleCat.of R ↥S) hPQ) x : ↥Q) : X) =
      (x : X) := by
  subst hPQ
  simp

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M N : ModuleCat.{max u v} R)

/-! ### The comparison of the cycles with the kernel -/

/-- **The comparison of the degree-one cycles with the kernel of the first Čech differential is
the inclusion of the cycles.** The two intermediate identifications are both characterized by
that property, and the final transport along the equality of the two descriptions of the kernel
does not move an element. -/
theorem cechCyclesOneIsoKer_hom_coe (z : (Cech.cechComplex f (M : Type _)).cycles 1) :
    (((cechCyclesOneIsoKer f M).hom z : LinearMap.ker (Cech.cechD f (M : Type _) 1)) :
        Cech.cechTerm f (M : Type _) 1) =
      (Cech.cechComplex f (M : Type _)).iCycles 1 z := by
  have hker : (LinearMap.ker
        ((HomologicalComplex.sc' (Cech.cechComplex f (M : Type _)) 0 1 2).g).hom :
      Submodule R (Cech.cechTerm f (M : Type _) 1)) =
      LinearMap.ker (Cech.cechD f (M : Type _) 1) :=
    congrArg (fun φ => LinearMap.ker (ModuleCat.Hom.hom φ)) (cechComplex_d_one_two f M)
  show ((eqToHom (congrArg (fun S : Submodule R (Cech.cechTerm f (M : Type _) 1) =>
        ModuleCat.of R ↥S) hker)
      ((HomologicalComplex.sc' (Cech.cechComplex f (M : Type _)) 0 1 2).moduleCatCyclesIso.hom
        (((Cech.cechComplex f (M : Type _)).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom z)) :
        ↥(LinearMap.ker (Cech.cechD f (M : Type _) 1))) :
      Cech.cechTerm f (M : Type _) 1) = _
  have h2 := ConcreteCategory.congr_hom
    (ShortComplex.moduleCatCyclesIso_hom_i
      (HomologicalComplex.sc' (Cech.cechComplex f (M : Type _)) 0 1 2))
    (((Cech.cechComplex f (M : Type _)).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom z)
  have h1 := ConcreteCategory.congr_hom
    ((Cech.cechComplex f (M : Type _)).cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)) z
  exact (eqToHom_submodule_coe hker _).trans (h2.trans h1)

variable {M N}

/-- The comparison of the degree-one cycles with the kernel of the first Čech differential is
natural in the module: both sides are the inclusion of the cycles followed by the induced map of
degree-one Čech terms. -/
theorem cechCyclesOneIsoKer_hom_naturality (g : M ⟶ N)
    (z : (Cech.cechComplex f (M : Type _)).cycles 1) :
    (cechCyclesOneIsoKer f N).hom
        (HomologicalComplex.cyclesMap (cechComplexMap f g) 1 z) =
      kerCechDOneMap f g ((cechCyclesOneIsoKer f M).hom z) := by
  refine Subtype.ext ?_
  rw [kerCechDOneMap_coe, cechCyclesOneIsoKer_hom_coe, cechCyclesOneIsoKer_hom_coe]
  exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (cechComplexMap f g) 1) z

/-- Passing between the natural-number and the integer indexing of the Čech complex is natural in
the module. -/
theorem extendedCechCyclesOneIso_hom_naturality (g : M ⟶ N)
    (z : (extendedCechComplex f M).cycles 1) :
    (extendedCechCyclesOneIso.{v} f N).hom
        (HomologicalComplex.cyclesMap (extendedCechComplexMap f g) 1 z) =
      HomologicalComplex.cyclesMap (cechComplexMap f g) 1
        ((extendedCechCyclesOneIso.{v} f M).hom z) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.extendCyclesIso_hom_naturality (cechComplexMap f g)
      ComplexShape.embeddingUpNat (j := 1) (j' := 1) (by simp)) z

/-! ### Naturality of the computation of the cohomology of the cone -/

/-- The computation of the degree-zero cohomology of the Čech cone is natural in the module: the
comparison with cochain-complex cohomology is a natural isomorphism, and the computation of the
cohomology of a mapping cone is natural in the commutative square expressing naturality of the
Čech augmentation.

This is the statement on elements; the naturality square itself is
`Stacks.LocalCohomology.cechComplementHomologyZeroIsoCycles_hom_naturality`. -/
theorem cechComplementHomologyZeroIsoCycles_hom_naturality_apply (g : M ⟶ N)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
      ((cechComplementFunctor.{v} f).obj M)) :
    (cechComplementHomologyZeroIsoCycles.{v} f N).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechComplementFunctor.{v} f).map g) z) =
      HomologicalComplex.cyclesMap (extendedCechComplexMap f g) 1
        ((cechComplementHomologyZeroIsoCycles.{v} f M).hom z) := by
  have := isIso_extendedCechAugmentation_f_zero f M
  have := isIso_extendedCechAugmentation_f_zero f N
  have hfac : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
        ((cechComplementFunctor.{v} f).map g) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentation f N)) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentation f M)) ≫
        HomologicalComplex.homologyMap (CochainComplex.mappingCone.map
          (extendedCechAugmentation f M) (extendedCechAugmentation f N)
          (extendedCechComplexMap f g)
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g)
          (extendedCechAugmentation_naturality f g).symm) 0 :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.naturality _
  have hcyc := Stacks.MappingCone.homologyIsoCycles_hom_naturality
    (extendedCechAugmentation_naturality f g).symm 0
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N _ (by omega))
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N _ (by omega))
  show (Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentation f N) 0 _ _).hom
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
        (CochainComplex.mappingCone (extendedCechAugmentation f N))
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechComplementFunctor.{v} f).map g) z)) = _
  exact ((congrArg
      (Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentation f N) 0
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N _ (by omega))
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N _ (by omega))).hom
      (ConcreteCategory.congr_hom hfac z)).trans
    (ConcreteCategory.congr_hom hcyc
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
        (CochainComplex.mappingCone (extendedCechAugmentation f M)) z)))

/-! ### Naturality of the comparison -/

/-- **The comparison `H⁰(RΓ(U, M̃|U)) ≃ ker d¹` is natural in the module.** This is the first of
the two hypotheses of
`Stacks.LocalCohomology.localizationTriangleDataOfCechHomologyComparison`. -/
theorem cechComplementHomologyZeroEquivKer_naturality (g : M ⟶ N)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
      ((cechComplementFunctor.{v} f).obj M)) :
    cechComplementHomologyZeroEquivKer.{v} f N
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechComplementFunctor.{v} f).map g) z) =
      kerCechDOneMap f g (cechComplementHomologyZeroEquivKer.{v} f M z) := by
  show (cechCyclesOneIsoKer f N).hom ((extendedCechCyclesOneIso.{v} f N).hom
      ((cechComplementHomologyZeroIsoCycles.{v} f N).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechComplementFunctor.{v} f).map g) z))) = _
  rw [cechComplementHomologyZeroIsoCycles_hom_naturality_apply,
    extendedCechCyclesOneIso_hom_naturality, cechCyclesOneIsoKer_hom_naturality]
  rfl

end Stacks.LocalCohomology

end

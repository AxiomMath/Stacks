module

public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.Triangle
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Cech
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.CechHomology
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Data.MappingConeNaturality

/-!
# The degree-zero cohomology of the small Čech cone

Let `R` be a commutative ring in `Type u`, let `f : Fin r → R` and let `M` be an `R`-module in
`Type v`, with `v` independent of `u`. `StacksFrontier/RingTheory/LocalCohomology/FreeUniverse/`
builds derived sections on `U = Spec R \ V(I)` at that free module universe as the cone of the
small Čech augmentation. This file identifies the degree-zero cohomology of that cone with the
degree-one cocycles of the small Čech complex, and then with the degree-one cocycles of
`Cech.cechComplex` itself.

The first identification is
`StacksFrontier/RingTheory/LocalCohomology/MappingConeH0/Cech.lean` with the constraint
`ModuleCat.{max u v}` removed: every input is stated for an arbitrary abelian category, so only
the names of the complex and its augmentation change. The second is
`Cech.cechTermShrinkEquiv` carrying one kernel onto the other, which is what connects the small
model to the sheaf-theoretic chain of
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/`, whose statements are about
`LinearMap.ker (Cech.cechD f M 1)`.

## Main definitions

* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerShrink` — **`H⁰` of derived sections
  on `U` at a free module universe is the kernel of the first differential of the small Čech
  complex.**
* `Stacks.LocalCohomology.kerCechDShrinkOneEquivKer` — the two descriptions of the degree-one
  cocycles, in the small model and in `Cech.cechComplex`.
* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerFree` — their composite.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : ModuleCat.{v} R)

/-! ### The cohomology of the cone as the degree-one cocycles -/

/-- **The degree-zero cohomology of derived sections on `U = Spec R \ V(I)` at a free module
universe** is the module of degree-one cycles of the integer-indexed small Čech complex. -/
def cechComplementHomologyZeroIsoCyclesShrink :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((cechComplementFunctorShrink.{v} f).obj M) ≅
      (Cech.extendedCechComplexShrink.{v} f (M : Type v)).cycles 1 :=
  haveI := isIso_extendedCechAugmentationShrink_f_zero.{v} f M
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).app
      (CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M)) ≪≫
    Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentationShrink.{v} f M) 0
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))

/-- Passing between the natural-number and the integer indexing of the small Čech complex does
not change its degree-one cycles. -/
def extendedCechCyclesOneIsoShrink :
    (Cech.extendedCechComplexShrink.{v} f (M : Type v)).cycles 1 ≅
      (Cech.cechComplexShrink.{v} f (M : Type v)).cycles 1 :=
  HomologicalComplex.extendCyclesIso (Cech.cechComplexShrink.{v} f (M : Type v))
    ComplexShape.embeddingUpNat (j := 1) (j' := 1) (by simp)

/-- The degree-one differential of the small Čech complex is `Cech.cechDShrink`. -/
theorem cechComplexShrink_d_one_two :
    (Cech.cechComplexShrink.{v} f (M : Type v)).d 1 2 =
      ModuleCat.ofHom (Cech.cechDShrink.{v} f (M : Type v) 1) :=
  Cech.cechComplexShrink_d.{v} f (M : Type v) 1

/-- The degree-one cycles of the small Čech complex, spelled out as the kernel of
`Cech.cechDShrink`. -/
def cechCyclesOneIsoKerShrink :
    (Cech.cechComplexShrink.{v} f (M : Type v)).cycles 1 ≅
      ModuleCat.of R (LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1)) :=
  (Cech.cechComplexShrink.{v} f (M : Type v)).cyclesIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ((Cech.cechComplexShrink.{v} f (M : Type v)).sc' 0 1 2).moduleCatCyclesIso ≪≫
    eqToIso (by
      rw [ShortComplex.moduleCatLeftHomologyData_K,
        show ((Cech.cechComplexShrink.{v} f (M : Type v)).sc' 0 1 2).g =
          ModuleCat.ofHom (Cech.cechDShrink.{v} f (M : Type v) 1) from
            cechComplexShrink_d_one_two.{v} f M]
      rfl)

/-- **`H⁰(RΓ(U, M̃|U)) ≅ ker (⨁_{i} M_{f_i} ⟶ ⨁_{i < j} M_{f_i f_j})` at a free module
universe**, with both sides in `Type v`. -/
def cechComplementHomologyZeroIsoKerShrink :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((cechComplementFunctorShrink.{v} f).obj M) ≅
      ModuleCat.of R (LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1)) :=
  cechComplementHomologyZeroIsoCyclesShrink.{v} f M ≪≫
    extendedCechCyclesOneIsoShrink.{v} f M ≪≫ cechCyclesOneIsoKerShrink.{v} f M

/-- `Stacks.LocalCohomology.cechComplementHomologyZeroIsoKerShrink` as an `R`-linear
equivalence. -/
def cechComplementHomologyZeroEquivKerShrink :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((cechComplementFunctorShrink.{v} f).obj M) ≃ₗ[R]
      LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1) :=
  (cechComplementHomologyZeroIsoKerShrink.{v} f M).toLinearEquiv

/-- **The comparison of the degree-one cycles with the kernel of the first small Čech
differential is the inclusion of the cycles.** -/
theorem cechCyclesOneIsoKerShrink_hom_coe
    (z : (Cech.cechComplexShrink.{v} f (M : Type v)).cycles 1) :
    (((cechCyclesOneIsoKerShrink.{v} f M).hom z :
          LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1)) :
        Cech.cechTermShrink.{v} f (M : Type v) 1) =
      (Cech.cechComplexShrink.{v} f (M : Type v)).iCycles 1 z := by
  have hker : (LinearMap.ker
        ((HomologicalComplex.sc' (Cech.cechComplexShrink.{v} f (M : Type v)) 0 1 2).g).hom :
      Submodule R (Cech.cechTermShrink.{v} f (M : Type v) 1)) =
      LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1) :=
    congrArg (fun φ => LinearMap.ker (ModuleCat.Hom.hom φ)) (cechComplexShrink_d_one_two.{v} f M)
  change ((eqToHom (congrArg (fun S : Submodule R (Cech.cechTermShrink.{v} f (M : Type v) 1) =>
        ModuleCat.of R ↥S) hker)
      ((HomologicalComplex.sc'
            (Cech.cechComplexShrink.{v} f (M : Type v)) 0 1 2).moduleCatCyclesIso.hom
        (((Cech.cechComplexShrink.{v} f (M : Type v)).cyclesIsoSc' 0 1 2
          (by simp) (by simp)).hom z)) :
        ↥(LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1))) :
      Cech.cechTermShrink.{v} f (M : Type v) 1) = _
  have h2 := ConcreteCategory.congr_hom
    (ShortComplex.moduleCatCyclesIso_hom_i
      (HomologicalComplex.sc' (Cech.cechComplexShrink.{v} f (M : Type v)) 0 1 2))
    (((Cech.cechComplexShrink.{v} f (M : Type v)).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom z)
  have h1 := ConcreteCategory.congr_hom
    ((Cech.cechComplexShrink.{v} f (M : Type v)).cyclesIsoSc'_hom_iCycles 0 1 2
      (by simp) (by simp)) z
  exact (eqToHom_submodule_coe hker _).trans (h2.trans h1)

/-! ### The two descriptions of the degree-one cocycles -/

/-- The comparison of the small model with `Cech.cechComplex` carries the degree-one cocycles of
the one onto those of the other. -/
theorem map_ker_cechDShrink_one :
    Submodule.map (Cech.cechTermShrinkEquiv.{v} f (M : Type v) 1).toLinearMap
        (LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1)) =
      LinearMap.ker (Cech.cechD f (M : Type v) 1) := by
  ext z
  obtain ⟨x, rfl⟩ := (Cech.cechTermShrinkEquiv.{v} f (M : Type v) 1).surjective z
  rw [LinearMap.mem_ker, ← Cech.cechTermShrinkEquiv_cechDShrink.{v} f (M : Type v) 1 x,
    map_eq_zero_iff _ (Cech.cechTermShrinkEquiv.{v} f (M : Type v) 2).injective]
  simp

/-- The degree-one cocycles of the small model and of `Cech.cechComplex` agree: the two modules
live in different universes, and `Cech.cechTermShrinkEquiv` identifies them. -/
def kerCechDShrinkOneEquivKer :
    LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1) ≃ₗ[R]
      LinearMap.ker (Cech.cechD f (M : Type v) 1) :=
  (Submodule.equivMapOfInjective _
      (Cech.cechTermShrinkEquiv.{v} f (M : Type v) 1).injective _).trans
    (LinearEquiv.ofEq _ _ (map_ker_cechDShrink_one.{v} f M))

/-- The identification of the two descriptions of the degree-one cocycles does not move an
element: it is `Cech.cechTermShrinkEquiv` on the underlying terms. -/
@[simp] theorem kerCechDShrinkOneEquivKer_coe
    (x : LinearMap.ker (Cech.cechDShrink.{v} f (M : Type v) 1)) :
    ((kerCechDShrinkOneEquivKer.{v} f M x : LinearMap.ker (Cech.cechD f (M : Type v) 1)) :
        Cech.cechTerm f (M : Type v) 1) =
      Cech.cechTermShrinkEquiv.{v} f (M : Type v) 1
        (x : Cech.cechTermShrink.{v} f (M : Type v) 1) :=
  rfl

/-- **`H⁰` of derived sections on `U` at a free module universe, as the degree-one cocycles of
`Cech.cechComplex`.** This is the shape in which the sheaf-theoretic chain of
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/` consumes the cohomology of the cone. -/
def cechComplementHomologyZeroEquivKerFree :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((cechComplementFunctorShrink.{v} f).obj M) ≃ₗ[R]
      LinearMap.ker (Cech.cechD f (M : Type v) 1) :=
  (cechComplementHomologyZeroEquivKerShrink.{v} f M).trans
    (kerCechDShrinkOneEquivKer.{v} f M)

end Stacks.LocalCohomology

end

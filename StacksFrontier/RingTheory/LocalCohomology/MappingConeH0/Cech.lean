module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Basic

/-!
# The degree-zero cohomology of derived sections on the complement of a zero locus

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `R`, let
`U = Spec R \ V(I)` and let `M` be an `R`-module. The third term of the localization triangle of
Stacks 0DWR, built in `StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle.lean`, is
`Stacks.LocalCohomology.cechComplementFunctor`, the cone of the Čech augmentation
`C^•(f₁, …, f_r; M) ⟶ M⟦0⟧` viewed in the derived category. This file computes its degree-zero
cohomology.

The augmentation is an isomorphism in degree zero
(`Stacks.LocalCohomology.isIso_extendedCechAugmentation_f_zero`) and its target is concentrated in
degree zero, so `Stacks.MappingCone.homologyIsoCycles` applies and identifies the degree-zero
cohomology of the cone with the degree-one cycles of the Čech complex. Transporting along the
embedding `ℕ ↪ ℤ` and spelling the cycles out as a kernel of linear maps, this reads

`H⁰(RΓ(U, M̃|U)) ≅ ker (⨁_{i} M_{f_i} ⟶ ⨁_{i < j} M_{f_i f_j})`,

the degree-one differential of the extended alternating Čech complex. The sign bookkeeping is
already in the differential: on the summand indexed by `{i}` the component landing in the summand
indexed by `{i, j}` with `i < j` has sign `-1`, and the one coming from `{j}` has sign `+1`, so the
kernel consists exactly of the families `(m_i)` whose images in `M_{f_i f_j}` agree.

This is one of the two halves of the field `sectionsIso` of
`Stacks.LocalCohomology.LocalizationTriangleData`. The other half, which this file does **not**
prove, is the sheaf-theoretic statement that `Γ(U, M̃)` is that same kernel; see the implementation
notes.

## Main definitions

* `Stacks.LocalCohomology.cechComplementHomologyZeroIsoCycles` — `H⁰(RΓ(U, M̃|U))` is the
  degree-one cycles of the integer-indexed Čech complex.
* `Stacks.LocalCohomology.cechComplementHomologyZeroIsoKer` — the same, with the cycles spelled
  out as `ker (Cech.cechD f M 1)`.
* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer` — the previous isomorphism as an
  `R`-linear equivalence, the shape in which `sectionsIso` consumes it.

## Main results

* `Stacks.LocalCohomology.cechComplex_d_one_two` — the degree-one differential of the Čech complex
  is `Cech.cechD f M 1`.

## Implementation notes

What `sectionsIso` still needs is an `R`-linear equivalence

`ker (Cech.cechD f M 1) ≃ₗ[R] complementGlobalSections R I (complementTilde R I M)`

together with its naturality in `M` and the formula `m ↦ m / 1`. All three are sheaf-theoretic and
involve local cohomology no further: the right-hand side is the sections of the associated sheaf on
`ι ''ᵁ ⊤ = U`, `U` is covered by the standard opens `D(f_i)`, the sections on each of them are
`M_{f_i}` by `Stacks.LocalCohomology.isLocalizedModule_moduleSectionsMk_basicOpen`, and a
compatible family is exactly an element of the kernel above by
`Stacks.LocalCohomology.moduleSectionsCoverEquiv`. The remaining mismatch is bookkeeping, not
mathematics: the Čech complex is indexed by `Finset (Fin r)` and localizes at the powers of
`∏ i ∈ s, f i`, the cover is indexed by `Fin r`, and `complementGlobalSections` carries the
`R`-action obtained by restricting scalars along `R ⟶ Γ(U, 𝒪_U)` rather than the evident one — for
which `Stacks.LocalCohomology.sectionsOnAffineComplementIso` is the comparison.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : ModuleCat.{max u v} R)

/-- **The degree-zero cohomology of derived sections on `U = Spec R \ V(I)`** is the module of
degree-one cycles of the integer-indexed extended alternating Čech complex. The Čech augmentation
is invertible in degree zero and its target is a module placed in degree zero, so
`Stacks.MappingCone.homologyIsoCycles` applies to it; the index shift is the one of the mapping
cone, whose degree-zero term has the degree-one Čech term as its first summand. -/
def cechComplementHomologyZeroIsoCycles :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
        ((cechComplementFunctor.{v} f).obj M) ≅ (extendedCechComplex f M).cycles 1 :=
  haveI := isIso_extendedCechAugmentation_f_zero f M
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).app
      (CochainComplex.mappingCone (extendedCechAugmentation f M)) ≪≫
    Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentation f M) 0
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))

/-- Passing between the natural-number and the integer indexing of the Čech complex does not
change its degree-one cycles. -/
def extendedCechCyclesOneIso :
    (extendedCechComplex f M).cycles 1 ≅ (Cech.cechComplex f (M : Type _)).cycles 1 :=
  HomologicalComplex.extendCyclesIso (Cech.cechComplex f (M : Type _))
    ComplexShape.embeddingUpNat (j := 1) (j' := 1) (by simp)

/-- The degree-one differential of the Čech complex is the alternating sum of the transition maps
`Cech.cechD f M 1`. -/
theorem cechComplex_d_one_two :
    (Cech.cechComplex f (M : Type _)).d 1 2 = ModuleCat.ofHom (Cech.cechD f (M : Type _) 1) :=
  CochainComplex.of_d (fun p => ModuleCat.of R (Cech.cechTerm f (M : Type _) p))
    (fun p => ModuleCat.ofHom (Cech.cechD f (M : Type _) p)) 1

/-- The degree-one cycles of the Čech complex, spelled out as the kernel of the linear map
`⨁_{i} M_{f_i} ⟶ ⨁_{i < j} M_{f_i f_j}`. -/
def cechCyclesOneIsoKer :
    (Cech.cechComplex f (M : Type _)).cycles 1 ≅
      ModuleCat.of R (LinearMap.ker (Cech.cechD f (M : Type _) 1)) :=
  (Cech.cechComplex f (M : Type _)).cyclesIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ((Cech.cechComplex f (M : Type _)).sc' 0 1 2).moduleCatCyclesIso ≪≫
    eqToIso (by
      rw [ShortComplex.moduleCatLeftHomologyData_K,
        show ((Cech.cechComplex f (M : Type _)).sc' 0 1 2).g =
          ModuleCat.ofHom (Cech.cechD f (M : Type _) 1) from cechComplex_d_one_two f M]
      rfl)

/-- **`H⁰(RΓ(U, M̃|U)) ≅ ker (⨁_{i} M_{f_i} ⟶ ⨁_{i < j} M_{f_i f_j})`.** The degree-zero
cohomology of derived sections on `U = Spec R \ V(I)` is the module of compatible families of
fractions: an element of `⨁_{i} M_{f_i}` whose images in each `M_{f_i f_j}` agree. -/
def cechComplementHomologyZeroIsoKer :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
        ((cechComplementFunctor.{v} f).obj M) ≅
      ModuleCat.of R (LinearMap.ker (Cech.cechD f (M : Type _) 1)) :=
  cechComplementHomologyZeroIsoCycles.{v} f M ≪≫ extendedCechCyclesOneIso.{v} f M ≪≫
    cechCyclesOneIsoKer f M

/-- `Stacks.LocalCohomology.cechComplementHomologyZeroIsoKer` as an `R`-linear equivalence: the
shape in which the field `sectionsIso` of `Stacks.LocalCohomology.LocalizationTriangleData`
consumes a degree-zero comparison. -/
def cechComplementHomologyZeroEquivKer :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
        ((cechComplementFunctor.{v} f).obj M) ≃ₗ[R]
      LinearMap.ker (Cech.cechD f (M : Type _) 1) :=
  (cechComplementHomologyZeroIsoKer.{v} f M).toLinearEquiv

end Stacks.LocalCohomology

end

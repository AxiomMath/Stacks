module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.QuotSMulTop
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs
public import StacksFrontier.RingTheory.Lattice.Distance

/-!
# Multiplying a differential in a two-periodic complex

Multiplying either differential of a finite two-periodic complex by an element of a
Noetherian local ring changes its periodic length by the periodic length of the image of that
differential, equipped with the zero map and scalar multiplication.

## Main results

* `AlgebraicGeometry.periodicLength_smul_fst` computes the effect of multiplying the first
  differential.
* `AlgebraicGeometry.periodicLength_smul_snd` computes the effect of multiplying the second
  differential.

## Implementation notes

The two maps are placed in degrees `0` and `1` of a `ZMod 2`-indexed cochain complex. The two
equalities in the source are stated separately. The quotient `M / xM` is represented by
`QuotSMulTop x M`, and the image modules are the ranges of the corresponding linear maps.
Both the original and the modified complexes, and the complexes on the image modules with
differentials zero and scalar multiplication, are instances of
`AlgebraicGeometry.twoPeriodicComplex`.

The second statement is deduced from the first by interchanging the two differentials, which
negates the periodic length.

## References

* [Stacks Project, Tag 0EAC](https://stacks.math.columbia.edu/tag/0EAC)
-/

@[expose] public section

open CategoryTheory
open scoped Pointwise

universe u v

namespace AlgebraicGeometry

/-- The support of `N / xN` for a submodule `N` lies in the support of `M / xM`. -/
private lemma support_quotient_range_lsmul_subset {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (x : R) :
    Module.support R (N ⧸ LinearMap.range (LinearMap.lsmul R N x)) ⊆
      Module.support R (QuotSMulTop x M) := by
  let e : (N ⧸ LinearMap.range (LinearMap.lsmul R N x)) ≃ₗ[R] QuotSMulTop x N :=
    Submodule.quotEquivOfEq _ _ (range_lsmul_eq_smul_top x)
  have hsup : Module.support R (QuotSMulTop x N) ⊆ Module.support R (QuotSMulTop x M) := by
    rw [Module.support_quotSMulTop, Module.support_quotSMulTop]
    exact Set.inter_subset_inter (Module.support_subset_of_injective N.subtype
      (Submodule.subtype_injective _)) (Set.Subset.refl _)
  exact (Module.support_subset_of_injective e e.injective).trans hsup

/-- The support of the `x`-torsion of a submodule `N` lies in the support of `M / xM`. -/
private lemma support_ker_lsmul_subset {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (x : R) :
    Module.support R (LinearMap.ker (LinearMap.lsmul R N x)) ⊆
      Module.support R (QuotSMulTop x M) := by
  rw [Module.support_quotSMulTop]
  intro p hp
  refine ⟨Module.support_subset_of_injective (N.subtype.comp (LinearMap.ker _).subtype)
    (fun _ _ h => Subtype.ext (Subtype.ext h)) hp, ?_⟩
  have hx : x ∈ Module.annihilator R (LinearMap.ker (LinearMap.lsmul R N x)) :=
    Module.mem_annihilator.mpr fun a => Subtype.ext (LinearMap.mem_ker.mp a.2)
  simpa [PrimeSpectrum.mem_zeroLocus] using Module.annihilator_le_of_mem_support hp hx

/-- The kernel of `x • φ` modulo the kernel of `φ` has the length of the `x`-torsion of the
image of `φ`. -/
private lemma length_ker_smul_quotient_ker {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] M) (x : R) :
    Module.length R
        (LinearMap.ker (x • φ) ⧸ (LinearMap.ker φ).submoduleOf (LinearMap.ker (x • φ))) =
      Module.length R (LinearMap.ker (LinearMap.lsmul R (LinearMap.range φ) x)) := by
  let f : LinearMap.ker (x • φ) →ₗ[R] LinearMap.ker (LinearMap.lsmul R (LinearMap.range φ) x) :=
    (φ.rangeRestrict.comp (LinearMap.ker (x • φ)).subtype).codRestrict _ (by
      intro m
      change LinearMap.lsmul R (LinearMap.range φ) x (φ.rangeRestrict m.1) = 0
      apply Subtype.ext
      change (x • φ) m.1 = 0
      exact m.2)
  have hker : LinearMap.ker f = (LinearMap.ker φ).submoduleOf (LinearMap.ker (x • φ)) := by
    ext m
    simp [f, LinearMap.mem_ker, Submodule.submoduleOf]
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨m, hm⟩ := a.1.2
    have hmx : m ∈ LinearMap.ker (x • φ) := by
      have ht : x • (a.1 : LinearMap.range φ) = 0 := by
        simpa only [LinearMap.lsmul_apply] using (LinearMap.mem_ker.mp a.2)
      change x • φ m = 0
      rw [hm]
      exact congrArg Subtype.val ht
    exact ⟨⟨m, hmx⟩, Subtype.ext (Subtype.ext hm)⟩
  rw [← hker]
  exact (f.quotKerEquivOfSurjective hsurj).length_eq

/-- The degree-zero cohomology of a two-periodic complex has the length of `ker f / range g`. -/
private lemma length_homology_zero_eq_ker_quotient {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (f g : Module.End R M) (hfg : f * g = 0) (hgf : g * f = 0) :
    Module.length R ((twoPeriodicComplex f g hfg hgf).homology 0) =
      Module.length R (↥(LinearMap.ker f) ⧸ (LinearMap.range g).submoduleOf (LinearMap.ker f)) := by
  convert homology_length_eq_ker_quotient f g hfg hgf 0 (Or.inl rfl) using 1
  rfl

/-- The degree-one cohomology of a two-periodic complex has the length of `ker g / range f`. -/
private lemma length_homology_one_eq_ker_quotient {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (f g : Module.End R M) (hfg : f * g = 0) (hgf : g * f = 0) :
    Module.length R ((twoPeriodicComplex f g hfg hgf).homology 1) =
      Module.length R (↥(LinearMap.ker g) ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) := by
  convert homology_length_eq_ker_quotient f g hfg hgf 1 (Or.inr rfl) using 1
  rfl

/-- The degree-zero cohomology of the complex with differentials zero and multiplication by `x`
has the length of `N / xN`. -/
private lemma length_homology_zero_twoPeriodicComplex_zero_lsmul {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N] (x : R) :
    Module.length R ((twoPeriodicComplex (0 : Module.End R N) (LinearMap.lsmul R N x)
      (zero_mul _) (mul_zero _)).homology 0) =
      Module.length R (N ⧸ LinearMap.range (LinearMap.lsmul R N x)) := by
  have hker0 : LinearMap.ker (0 : Module.End R N) = ⊤ := by
    ext a
    simp
  have hh := homology_length_eq_ker_quotient (0 : Module.End R N) (LinearMap.lsmul R N x)
      (zero_mul _) (mul_zero _) 0 (Or.inl rfl)
  rw [hker0] at hh
  have hlen := quotient_length_of_bijective_map
    (Submodule.topEquiv : (↥(⊤ : Submodule R N)) ≃ₗ[R] N).toLinearMap
    (Submodule.topEquiv : (↥(⊤ : Submodule R N)) ≃ₗ[R] N).surjective
    (LinearMap.range (LinearMap.lsmul R N x))
  simpa [Submodule.topEquiv] using hh.trans hlen

/-- The degree-one cohomology of the complex with differentials zero and multiplication by `x`
has the length of the `x`-torsion of `N`. -/
private lemma length_homology_one_twoPeriodicComplex_zero_lsmul {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N] (x : R) :
    Module.length R ((twoPeriodicComplex (0 : Module.End R N) (LinearMap.lsmul R N x)
      (zero_mul _) (mul_zero _)).homology 1) =
      Module.length R (LinearMap.ker (LinearMap.lsmul R N x)) := by
  have hh := homology_length_eq_ker_quotient (0 : Module.End R N)
    (LinearMap.lsmul R N x) (zero_mul _) (mul_zero _) 1 (Or.inr rfl)
  have hbot : (LinearMap.range (0 : Module.End R N)).comap
      (LinearMap.ker (LinearMap.lsmul R N x)).subtype = ⊥ := by
    simp [LinearMap.range_zero]
  rw [hbot] at hh
  have e : (↥(LinearMap.ker (LinearMap.lsmul R N x)) ⧸
      (⊥ : Submodule R (↥(LinearMap.ker (LinearMap.lsmul R N x))))) ≃ₗ[R]
      ↥(LinearMap.ker (LinearMap.lsmul R N x)) :=
    Submodule.quotEquivOfEqBot _ rfl
  rw [e.length_eq] at hh
  simpa using hh

/-- Multiplying the first differential by `x` adds the length of the `x`-torsion of its image
to the degree-zero cohomology. -/
private lemma length_homology_zero_twoPeriodicComplex_smul_fst {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : φ.comp ψ = 0) (hψφ : ψ.comp φ = 0) (x : R)
    (h₁ : (x • φ).comp ψ = 0) (h₂ : ψ.comp (x • φ) = 0) :
    Module.length R ((twoPeriodicComplex (x • φ) ψ h₁ h₂).homology 0) =
      Module.length R ((twoPeriodicComplex φ ψ hφψ hψφ).homology 0) +
        Module.length R (LinearMap.ker (LinearMap.lsmul R (LinearMap.range φ) x)) := by
  have hBK : LinearMap.range ψ ≤ LinearMap.ker φ := by
    rintro z ⟨m, rfl⟩
    change φ (ψ m) = 0
    simpa using LinearMap.congr_fun hφψ m
  have hKKx : LinearMap.ker φ ≤ LinearMap.ker (x • φ) := by
    intro m hm
    change (x • φ) m = 0
    simp [LinearMap.smul_apply, LinearMap.mem_ker.mp hm]
  rw [length_homology_zero_eq_ker_quotient (x • φ) ψ h₁ h₂,
    Module.length_quotient_submoduleOf_eq_add hBK hKKx,
    length_homology_zero_eq_ker_quotient φ ψ hφψ hψφ, length_ker_smul_quotient_ker φ x]

/-- Multiplying the first differential by `x` adds the length of `A / xA`, for `A` its image,
to the degree-one cohomology. -/
private lemma length_homology_one_twoPeriodicComplex_smul_fst {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : φ.comp ψ = 0) (hψφ : ψ.comp φ = 0) (x : R)
    (h₁ : (x • φ).comp ψ = 0) (h₂ : ψ.comp (x • φ) = 0) :
    Module.length R ((twoPeriodicComplex (x • φ) ψ h₁ h₂).homology 1) =
      Module.length R
          (↥(LinearMap.range φ) ⧸ LinearMap.range (LinearMap.lsmul R (LinearMap.range φ) x)) +
        Module.length R ((twoPeriodicComplex φ ψ hφψ hψφ).homology 1) := by
  let X : Submodule R M := LinearMap.range
    ((LinearMap.range φ).subtype.comp (LinearMap.lsmul R (LinearMap.range φ) x))
  have hAL : LinearMap.range φ ≤ LinearMap.ker ψ := by
    rintro z ⟨m, rfl⟩
    change ψ (φ m) = 0
    simpa using LinearMap.congr_fun hψφ m
  have hXA : X ≤ LinearMap.range φ := by
    rintro z ⟨a, rfl⟩
    exact (LinearMap.range φ).smul_mem x a.2
  have hXeq : X = LinearMap.range (x • φ) := by
    apply le_antisymm
    · rintro z ⟨a, rfl⟩
      obtain ⟨m, hm⟩ := a.2
      refine ⟨m, ?_⟩
      change x • φ m = x • (a : M)
      rw [hm]
    · rintro z ⟨m, rfl⟩
      exact ⟨⟨φ m, m, rfl⟩, rfl⟩
  have hZmap : X = (LinearMap.range (LinearMap.lsmul R (LinearMap.range φ) x)).map
      (LinearMap.range φ).subtype := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨LinearMap.lsmul R (LinearMap.range φ) x a, ⟨a, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨a, ha⟩, hb⟩
      refine ⟨a, ?_⟩
      change (LinearMap.range φ).subtype (LinearMap.lsmul R (LinearMap.range φ) x a) = _
      rw [ha, hb]
  have hXsub : X.submoduleOf (LinearMap.range φ) =
      LinearMap.range (LinearMap.lsmul R (LinearMap.range φ) x) := by
    rw [hZmap]
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, hba⟩ := (Submodule.mem_map).mp ha
      obtain rfl : b = a := Subtype.ext hba
      exact hb
    · rintro ⟨b, rfl⟩
      exact Submodule.mem_map.mpr ⟨LinearMap.lsmul R (LinearMap.range φ) x b, ⟨b, rfl⟩, rfl⟩
  rw [length_homology_one_eq_ker_quotient (x • φ) ψ h₁ h₂, ← hXeq,
    Module.length_quotient_submoduleOf_eq_add hXA hAL, hXsub,
    length_homology_one_eq_ker_quotient φ ψ hφψ hψφ]

/-- Multiplying the first differential of a two-periodic complex by `x` subtracts the periodic
length of its image with differentials zero and multiplication by `x`. -/
@[stacks 0EAC "multiplying the first differential"]
public lemma periodicLength_smul_fst {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (φ ψ : M →ₗ[R] M) (hφψ : φ.comp ψ = 0) (hψφ : ψ.comp φ = 0) (x : R)
    (hH₀ : IsFiniteLength R
      ((twoPeriodicComplex φ ψ hφψ hψφ).homology (0 : ZMod 2)))
    (hH₁ : IsFiniteLength R
      ((twoPeriodicComplex φ ψ hφψ hψφ).homology (1 : ZMod 2)))
    (hsupp : Module.supportDim R (QuotSMulTop x M) ≤ 0) :
    periodicLength
        (twoPeriodicComplex (x • φ) ψ
          (by change (x • φ).comp ψ = 0; rw [LinearMap.smul_comp, hφψ, smul_zero])
          (by change ψ.comp (x • φ) = 0; rw [LinearMap.comp_smul, hψφ, smul_zero])) =
      periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) -
        periodicLength
          (twoPeriodicComplex (0 : Module.End R (LinearMap.range φ))
            (LinearMap.lsmul R (LinearMap.range φ) x) (zero_mul _) (mul_zero _)) := by
  have hfinT : IsFiniteLength R (LinearMap.ker (LinearMap.lsmul R (LinearMap.range φ) x)) :=
    finite_length_of_supportDim_le_zero ((supportDim_le_of_support_subset
      (support_ker_lsmul_subset (LinearMap.range φ) x)).trans hsupp)
  have hfinAZ : IsFiniteLength R
      (↥(LinearMap.range φ) ⧸ LinearMap.range (LinearMap.lsmul R (LinearMap.range φ) x)) :=
    finite_length_of_supportDim_le_zero ((supportDim_le_of_support_subset
      (support_quotient_range_lsmul_subset (LinearMap.range φ) x)).trans hsupp)
  rw [periodicLength, periodicLength, periodicLength,
    length_homology_zero_twoPeriodicComplex_smul_fst φ ψ hφψ hψφ x,
    length_homology_one_twoPeriodicComplex_smul_fst φ ψ hφψ hψφ x,
    length_homology_zero_twoPeriodicComplex_zero_lsmul (N := ↥(LinearMap.range φ)) x,
    length_homology_one_twoPeriodicComplex_zero_lsmul (N := ↥(LinearMap.range φ)) x,
    ENat.toNat_add (Module.length_ne_top_iff.mpr hH₀) (Module.length_ne_top_iff.mpr hfinT),
    ENat.toNat_add (Module.length_ne_top_iff.mpr hfinAZ) (Module.length_ne_top_iff.mpr hH₁)]
  push_cast
  ring

/-- Interchanging the two differentials of a two-periodic complex negates its periodic
length. -/
private lemma periodicLength_swap {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M]
    (f g : Module.End R M) (hfg : f.comp g = 0) (hgf : g.comp f = 0) :
    periodicLength (twoPeriodicComplex f g hfg hgf) =
      - periodicLength (twoPeriodicComplex g f hgf hfg) := by
  simp only [periodicLength,
    homology_length_eq_ker_quotient f g hfg hgf 0 (Or.inl rfl),
    homology_length_eq_ker_quotient f g hfg hgf 1 (Or.inr rfl),
    homology_length_eq_ker_quotient g f hgf hfg 0 (Or.inl rfl),
    homology_length_eq_ker_quotient g f hgf hfg 1 (Or.inr rfl)]
  simp

/-- Multiplying the second differential of a two-periodic complex by `x` adds the periodic
length of its image with differentials zero and multiplication by `x`. -/
@[stacks 0EAC "multiplying the second differential"]
public lemma periodicLength_smul_snd {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (φ ψ : M →ₗ[R] M) (hφψ : φ.comp ψ = 0) (hψφ : ψ.comp φ = 0) (x : R)
    (hH₀ : IsFiniteLength R
      ((twoPeriodicComplex φ ψ hφψ hψφ).homology (0 : ZMod 2)))
    (hH₁ : IsFiniteLength R
      ((twoPeriodicComplex φ ψ hφψ hψφ).homology (1 : ZMod 2)))
    (hsupp : Module.supportDim R (QuotSMulTop x M) ≤ 0) :
    periodicLength
        (twoPeriodicComplex φ (x • ψ)
          (by
            change φ.comp (x • ψ) = 0
            rw [LinearMap.comp_smul, hφψ, smul_zero])
          (by
            change (x • ψ).comp φ = 0
            rw [LinearMap.smul_comp, hψφ, smul_zero])) =
      periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) +
        periodicLength
          (twoPeriodicComplex (0 : Module.End R (LinearMap.range ψ))
            (LinearMap.lsmul R (LinearMap.range ψ) x) (zero_mul _) (mul_zero _)) := by
  let Cswap := twoPeriodicComplex ψ φ hψφ hφψ
  let C := twoPeriodicComplex φ ψ hφψ hψφ
  let Cx := twoPeriodicComplex φ (x • ψ)
    (by change φ.comp (x • ψ) = 0; rw [LinearMap.comp_smul, hφψ, smul_zero])
    (by change (x • ψ).comp φ = 0; rw [LinearMap.smul_comp, hψφ, smul_zero])
  have hswap0 : Module.length R (Cswap.homology 0) =
      Module.length R ((twoPeriodicComplex φ ψ hφψ hψφ).homology 1) := by
    rw [length_homology_zero_eq_ker_quotient ψ φ hψφ hφψ,
      length_homology_one_eq_ker_quotient φ ψ hφψ hψφ]
  have hswap1 : Module.length R (Cswap.homology 1) =
      Module.length R ((twoPeriodicComplex φ ψ hφψ hψφ).homology 0) := by
    rw [length_homology_one_eq_ker_quotient ψ φ hψφ hφψ,
      length_homology_zero_eq_ker_quotient φ ψ hφψ hψφ]
  have hfiniteSwap0 : IsFiniteLength R (Cswap.homology 0) := by
    apply Module.length_ne_top_iff.mp
    rw [hswap0]
    exact Module.length_ne_top_iff.mpr hH₁
  have hfiniteSwap1 : IsFiniteLength R (Cswap.homology 1) := by
    apply Module.length_ne_top_iff.mp
    rw [hswap1]
    exact Module.length_ne_top_iff.mpr hH₀
  have hswapNew := periodicLength_swap φ (x • ψ)
    (by change φ.comp (x • ψ) = 0; rw [LinearMap.comp_smul, hφψ, smul_zero])
    (by change (x • ψ).comp φ = 0; rw [LinearMap.smul_comp, hψφ, smul_zero])
  change periodicLength Cx = periodicLength C + _
  rw [hswapNew, periodicLength_swap φ ψ hφψ hψφ,
    periodicLength_smul_fst M ψ φ hψφ hφψ x hfiniteSwap0 hfiniteSwap1 hsupp]
  ring

end AlgebraicGeometry

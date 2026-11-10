module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.NormTrace
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantSheaf
public import StacksFrontier.RingTheory.FormsTrace.Nice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The discriminant as a nice element

Let `B` be a finite free algebra over a commutative ring `R`, with a basis `e`, and let
`Δ = disc_{B/R}(e)` be the discriminant of `e`. This file shows that `Δ` has the three properties
which make it a *nice element* for the uniqueness argument of Stacks, Lemma 0FLB and
Proposition 0FLC, as soon as `Ω_{R/ℤ}` is projective and `Δ` is a nonzerodivisor of `R`:

1. `Δ` is a nonzerodivisor on every module of forms `Ω^p_R = ⋀^p_R Ω_{R/ℤ}`;
2. a power of `Δ` kills `Ω_{B/R}`;
3. the kernel of `B ⊗_R Ω_{R/ℤ} → Ω_{B/ℤ}` is `Δ`-power torsion.

The last two hold because `B[1/Δ]` is étale over `R[1/Δ]`: a finite free algebra with invertible
discriminant is étale, its fibres having nondegenerate trace forms.

## Main results

* `Stacks.FormsTrace.trace_map_of_basis`, `Stacks.FormsTrace.discr_map_of_basis`: traces and
  discriminants are compatible with a ring map carrying one basis to another.
* `Stacks.FormsTrace.etale_of_isUnit_discr`: a finite free algebra with invertible discriminant
  is étale.
* `Stacks.FormsTrace.isSMulRegular_forms_discr`: property (1).
* `Stacks.FormsTrace.exists_pow_discr_smul_kaehler_eq_zero`: property (2).
* `Stacks.FormsTrace.exists_pow_discr_smul_eq_zero_of_mapBaseChange`: property (3).
* `Stacks.FormsTrace.discr_nice`: the discriminant is a nice element
  (`Stacks.FormsTrace.IsNiceElement`).

## Implementation notes

The étale criterion is checked fibrewise, through
`AlgebraicGeometry.etale_of_flat_of_fibers_finite_separable`: over a field `K` the base change
`K ⊗_R B` is free on the base changed basis, whose discriminant is the image of `Δ`, so its trace
form is nondegenerate and `Stacks.Discriminant.finiteDimensional_etale_iff_traceForm_nondegenerate`
applies.

For (2) and (3) we pass to the localization `B_Δ` of `B` at the powers of `Δ`, which is formally
étale over `R` (étale over `R_Δ`, which is a localization of `R`). Then `Ω_{B_Δ/R} = 0` is the
localization of `Ω_{B/R}`, a finite `B`-module, and `B_Δ ⊗_R Ω_{R/ℤ} → Ω_{B_Δ/ℤ}` is injective
while `B_Δ ⊗_R Ω_{R/ℤ}` is the localization of `B ⊗_R Ω_{R/ℤ}`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0BVH](https://stacks.math.columbia.edu/tag/0BVH)
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors
open KaehlerDifferential AlgebraicGeometry CategoryTheory

universe u v

namespace Stacks.FormsTrace

section MapOfBasis

variable {R S B C : Type*} [CommRing R] [CommRing S] [CommRing B] [CommRing C] [Algebra R B]
  [Algebra S C] {ι : Type*}

/-- **Coordinates along a ring map matching two bases.** If a ring map `q : B → C`, semilinear
along `f : R → S`, carries a basis `b` of `B` over `R` to a basis `c` of `C` over `S`, then the
coordinates of `q x` in `c` are the images under `f` of the coordinates of `x` in `b`. -/
theorem repr_map_of_basis [Finite ι] (f : R →+* S) (q : B →+* C)
    (hq : ∀ r, q (algebraMap R B r) = algebraMap S C (f r))
    (b : Module.Basis ι R B) (c : Module.Basis ι S C) (hbc : ∀ i, q (b i) = c i)
    (x : B) (i : ι) : c.repr (q x) i = f (b.repr x i) := by
  have := Fintype.ofFinite ι
  have hx : q x = ∑ j, f (b.repr x j) • c j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, hq, hbc, ← Algebra.smul_def]
  rw [hx, c.repr_sum_self]

/-- **Traces along a ring map matching two bases.** If `q : B → C`, semilinear along
`f : R → S`, carries a basis of `B` over `R` to a basis of `C` over `S`, then
`Tr_{C/S}(q x) = f (Tr_{B/R}(x))`. -/
theorem trace_map_of_basis [Finite ι] (f : R →+* S) (q : B →+* C)
    (hq : ∀ r, q (algebraMap R B r) = algebraMap S C (f r))
    (b : Module.Basis ι R B) (c : Module.Basis ι S C) (hbc : ∀ i, q (b i) = c i) (x : B) :
    Algebra.trace S C (q x) = f (Algebra.trace R B x) := by
  classical
  have := Fintype.ofFinite ι
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace c, Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [← hbc i, ← map_mul, repr_map_of_basis f q hq b c hbc]

/-- **Trace matrices along a ring map matching two bases.** -/
theorem traceMatrix_map_of_basis [Finite ι] (f : R →+* S) (q : B →+* C)
    (hq : ∀ r, q (algebraMap R B r) = algebraMap S C (f r))
    (b : Module.Basis ι R B) (c : Module.Basis ι S C) (hbc : ∀ i, q (b i) = c i) :
    Algebra.traceMatrix S c = (Algebra.traceMatrix R b).map f := by
  ext i j
  rw [Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Algebra.traceForm_apply, ← hbc i, ← hbc j, ← map_mul,
    trace_map_of_basis f q hq b c hbc]

/-- **Discriminants along a ring map matching two bases.** If `q : B → C`, semilinear along
`f : R → S`, carries a basis `b` of `B` over `R` to a basis `c` of `C` over `S`, then
`disc_{C/S}(c) = f (disc_{B/R}(b))`. -/
theorem discr_map_of_basis [Fintype ι] [DecidableEq ι] (f : R →+* S) (q : B →+* C)
    (hq : ∀ r, q (algebraMap R B r) = algebraMap S C (f r))
    (b : Module.Basis ι R B) (c : Module.Basis ι S C) (hbc : ∀ i, q (b i) = c i) :
    Algebra.discr S c = f (Algebra.discr R b) := by
  rw [Algebra.discr_def, Algebra.discr_def, traceMatrix_map_of_basis f q hq b c hbc,
    RingHom.map_det]
  rfl

end MapOfBasis

section Etale

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {ι : Type*} [Fintype ι]
    [DecidableEq ι]

/-- **The fibres of a finite free algebra with invertible discriminant are étale.** For every
field `K` over `R`, the base change `K ⊗_R B` is étale over `K`: its trace form is nondegenerate
because the discriminant of the base changed basis is the image of the discriminant. -/
@[sga "1 I 4.10" "special case"]
theorem etale_tensor_of_isUnit_discr (e : Module.Basis ι R B) (h : IsUnit (Algebra.discr R e))
    (K : Type v) [Field K] [Algebra R K] : Algebra.Etale K (K ⊗[R] B) := by
  classical
  let eK : Module.Basis ι K (K ⊗[R] B) := e.baseChange K
  have hd : Algebra.discr K eK = algebraMap R K (Algebra.discr R e) := by
    refine discr_map_of_basis (algebraMap R K)
      (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom (fun r => ?_) e eK
      (fun i => ?_)
    · change Algebra.TensorProduct.includeRight (algebraMap R B r) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R K (K ⊗[R] B)]
    · simp [eK, Module.Basis.baseChange_apply]
  have : FiniteDimensional K (K ⊗[R] B) := Module.Finite.of_basis eK
  rw [Stacks.Discriminant.finiteDimensional_etale_iff_traceForm_nondegenerate,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero eK, ← Algebra.traceMatrix_of_basis,
    ← Algebra.discr_def, hd]
  exact (h.map (algebraMap R K)).ne_zero

/-- **A finite free algebra with invertible discriminant is étale.** If `B` is free over `R` on a
basis whose discriminant is a unit of `R`, then `R → B` is étale. -/
@[ega "IV 18.10.15" "free case, partial", ega "IV 18.2.1" "partial", sga "1 I 4.10" "special case"]
theorem etale_of_isUnit_discr (e : Module.Basis ι R B) (h : IsUnit (Algebra.discr R e)) :
    Algebra.Etale R B := by
  classical
  have : Module.Free R B := Module.Free.of_basis e
  have : Module.Finite R B := Module.Finite.of_basis e
  let g : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  have : Algebra.FinitePresentation R B := inferInstance
  have : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : LocallyOfFinitePresentation g := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hg : Etale g := by
    apply etale_of_flat_of_fibers_finite_separable
    intro (p : PrimeSpectrum R)
    let K := p.asIdeal.ResidueField
    have hEtaleScheme : Etale (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B)))) :=
      HasRingHomProperty.Spec_iff.mpr
        (RingHom.etale_algebraMap.mpr (etale_tensor_of_isUnit_discr e h K))
    have hEtaleFiber : Etale (g.fiberToSpecResidueField p) := by
      have : MorphismProperty.RespectsIso (@Etale) := by
        rw [HasRingHomProperty.eq_affineLocally (P := @Etale)]
        exact AlgebraicGeometry.affineLocally_respectsIso
          (P := RingHom.Etale) RingHom.Etale.respectsIso
      exact (MorphismProperty.arrow_mk_iso_iff (P := @Etale)
        (Spec.fiberToSpecResidueFieldIso R B p)).mpr hEtaleScheme
    have : IsLocalRing ((Spec (.of R)).presheaf.stalk p) :=
      (Spec.stalkIso (.of R) p).commRingCatIsoToRingEquiv.symm.isLocalRing
    exact (etale_iff_iso_coproduct_spectra_finite_separable
      (IsLocalRing.ResidueField ((Spec (.of R)).presheaf.stalk p))
      (g.fiberToSpecResidueField p)).mp hEtaleFiber
  exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hg)

end Etale

section Localization

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {ι : Type*} [Fintype ι]
    [DecidableEq ι]

/-- An element of a `B`-module killed by a localization map at the powers of `Δ` is killed by a
power of `Δ`. -/
private theorem exists_pow_smul_eq_zero_of_isLocalizedModule {N P : Type*} [AddCommGroup N]
    [Module R N] [Module B N] [IsScalarTower R B N] [AddCommGroup P] [Module B P] (Δ : R)
    (f : N →ₗ[B] P) [IsLocalizedModule (Algebra.algebraMapSubmonoid B (Submonoid.powers Δ)) f]
    (x : N) (hx : f x = 0) : ∃ n : ℕ, Δ ^ n • x = 0 := by
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff
    (Algebra.algebraMapSubmonoid B (Submonoid.powers Δ)) f).mp hx
  obtain ⟨r, ⟨n, rfl⟩, rfl⟩ := hs
  exact ⟨n, by rwa [← algebraMap_smul B (Δ ^ n) x]⟩

/-- **A finite free algebra becomes formally étale after inverting its discriminant.** The
localization of `B` at the powers of `Δ = disc(e)` is formally étale over `R`. -/
@[sga "1 I 4.10" "special case"]
theorem formallyEtale_localization_discr (e : Module.Basis ι R B) :
    Algebra.FormallyEtale R (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers
        (Algebra.discr R e)))) := by
  classical
  set Δ := Algebra.discr R e
  let RΔ := Localization (Submonoid.powers Δ)
  let BΔ := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers Δ))
  let eΔ : Module.Basis ι RΔ BΔ := e.localizationLocalization RΔ (Submonoid.powers Δ) BΔ
  have hunit : IsUnit (Algebra.discr RΔ eΔ) := by
    rw [Algebra.discr_localizationLocalization]
    exact IsLocalization.map_units RΔ (⟨Δ, Submonoid.mem_powers Δ⟩ : Submonoid.powers Δ)
  have : Algebra.Etale RΔ BΔ := etale_of_isUnit_discr eΔ hunit
  have : Algebra.FormallyEtale R RΔ := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers Δ)
  exact Algebra.FormallyEtale.comp R RΔ BΔ

/-- **Property (2) of a nice element.** A power of the discriminant of a basis kills the
relative differentials `Ω_{B/R}` of a finite free algebra. -/
theorem exists_pow_discr_smul_kaehler_eq_zero (e : Module.Basis ι R B) :
    ∃ N : ℕ, ∀ x : Ω[B⁄R], Algebra.discr R e ^ N • x = 0 := by
  classical
  set Δ := Algebra.discr R e
  set M := Algebra.algebraMapSubmonoid B (Submonoid.powers Δ)
  have : Algebra.FormallyEtale R (Localization M) := formallyEtale_localization_discr e
  have : Subsingleton Ω[Localization M⁄R] :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have : Module.Finite R B := Module.Finite.of_basis e
  have hkill : ∀ x : Ω[B⁄R], ∃ n : ℕ, Δ ^ n • x = 0 := by
    intro x
    exact exists_pow_smul_eq_zero_of_isLocalizedModule Δ
      (KaehlerDifferential.map R R B (Localization M)) x (Subsingleton.elim _ _)
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B Ω[B⁄R]).FG)
  choose n hn using hkill
  refine ⟨∑ y ∈ t, n y, fun x => ?_⟩
  have hx : x ∈ Submodule.span B (t : Set Ω[B⁄R]) := ht ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ : ∃ k, ∑ z ∈ t, n z = n y + k :=
      ⟨_, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy)).symm⟩
    rw [hk, pow_add, mul_comm, mul_smul, hn y, smul_zero]
  | zero => exact smul_zero _
  | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
  | smul b y _ hy => rw [smul_comm, hy, smul_zero]

/-- **Property (3) of a nice element.** Every element of the kernel of
`B ⊗_R Ω_{R/ℤ} → Ω_{B/ℤ}` is killed by a power of the discriminant of a basis of the finite free
algebra `B`. -/
theorem exists_pow_discr_smul_eq_zero_of_mapBaseChange (e : Module.Basis ι R B)
    (x : B ⊗[R] Ω[R⁄ℤ]) (hx : x ∈ LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ R B)) :
    ∃ n : ℕ, Algebra.discr R e ^ n • x = 0 := by
  classical
  set Δ := Algebra.discr R e
  set BΔ := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers Δ))
  have : Algebra.FormallyEtale R BΔ := formallyEtale_localization_discr e
  set M := Algebra.algebraMapSubmonoid B (Submonoid.powers Δ)
  let g : B →ₗ[B] BΔ := Algebra.linearMap B BΔ
  let qt : B ⊗[R] Ω[R⁄ℤ] →ₗ[B] BΔ ⊗[R] Ω[R⁄ℤ] :=
    TensorProduct.AlgebraTensorModule.rTensor R Ω[R⁄ℤ] g
  have : IsLocalizedModule M qt := inferInstance
  have hmap : ∀ ω : Ω[R⁄ℤ], KaehlerDifferential.map ℤ ℤ B BΔ
      (KaehlerDifferential.map ℤ ℤ R B ω) = KaehlerDifferential.map ℤ ℤ R BΔ ω := by
    intro ω
    have hω : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℤ R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, rfl⟩ := hy
      simp only [KaehlerDifferential.map_D]
      rw [← IsScalarTower.algebraMap_apply]
    | zero => simp only [map_zero]
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul a y _ hy =>
      rw [LinearMap.map_smul, LinearMap.map_smul_of_tower, LinearMap.map_smul, hy]
  have hcomm : ∀ y : B ⊗[R] Ω[R⁄ℤ],
      KaehlerDifferential.mapBaseChange ℤ R BΔ (qt y) =
        KaehlerDifferential.map ℤ ℤ B BΔ (KaehlerDifferential.mapBaseChange ℤ R B y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul b ω =>
      simp only [qt, g, TensorProduct.AlgebraTensorModule.rTensor_tmul, Algebra.linearMap_apply,
        KaehlerDifferential.mapBaseChange_tmul, LinearMap.map_smul]
      rw [algebraMap_smul, hmap]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hzero : qt x = 0 := by
    apply (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ R BΔ).injective
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, hcomm, LinearMap.mem_ker.mp hx,
      map_zero, map_zero]
  exact exists_pow_smul_eq_zero_of_isLocalizedModule Δ qt x hzero

end Localization

section Regular

variable {R : Type u} [CommRing R]

/-- An exterior power of a projective module is projective: it is a direct summand of the
corresponding exterior power of a free module. -/
private theorem projective_exteriorPower (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Projective R M] (p : ℕ) : Module.Projective R (⋀[R]^p M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  refine Module.Projective.of_split (exteriorPower.map p s)
    (exteriorPower.map p (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

/-- **Property (1) of a nice element.** If `Ω_{R/ℤ}` is projective, a nonzerodivisor of `R` is a
nonzerodivisor on every module of forms `Ω^p_R = ⋀^p_R Ω_{R/ℤ}`. -/
theorem isSMulRegular_forms_of_mem_nonZeroDivisors [Module.Projective R Ω[R⁄ℤ]] {h : R}
    (hh : h ∈ R⁰) (p : ℕ) : IsSMulRegular (⋀[R]^p Ω[R⁄ℤ]) h := by
  have := projective_exteriorPower (R := R) Ω[R⁄ℤ] p
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hh

end Regular

/-- **The discriminant is a nice element** (Stacks 0FLB, 0FLC, universal case). Let `B` be free
over `R` on a basis `e`, with `Ω_{R/ℤ}` projective and `Δ = disc(e)` a nonzerodivisor of `R`.
Then `Δ` is a nice element for `B/R`: a nonzerodivisor on every `Ω^p_R`, a power of `Δ` kills
`Ω_{B/R}`, and the kernel of `B ⊗_R Ω_{R/ℤ} → Ω_{B/ℤ}` is `Δ`-power torsion. -/
theorem discr_nice {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Projective R Ω[R⁄ℤ]] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι R B) (he : Algebra.discr R e ∈ R⁰) :
    IsNiceElement R B (Algebra.discr R e) where
  regular := isSMulRegular_forms_of_mem_nonZeroDivisors he
  pow_smul_kaehler := exists_pow_discr_smul_kaehler_eq_zero e
  ker_torsion := exists_pow_discr_smul_eq_zero_of_mapBaseChange e

end Stacks.FormsTrace

end

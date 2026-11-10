module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppVerticalAgreement
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWeakSolutionBridge
public import StacksFrontier.RingTheory.DiscreteValuationRing.SeparableSolution
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# The generic fibres of a totally ramified enlargement

Let `D₁` and `D₂` be `IntegralClosureBaseChange` packages for finite extensions `K₁` and `K₂` of
`K`, with `K₁ → K₂`. At every *minimal* prime `p` of `D₁.B₁` the fibre of `D₂.B₁` satisfies

    `Module.finrank p.ResidueField (p.Fiber D₂.B₁) ≤ Module.finrank K₁ K₂`,

and consequently a weak solution over `K₁` is one over `K₂`
(`Stacks.EppTheorem.isWeakSolution_of_totallyRamified`), with no degree hypothesis.

## Why the minimal primes

At a maximal ideal the fibre is a statement about integral closures, where no compositum
identification is available; at a minimal prime it is a statement about the composita, where one
is. At a minimal prime of a **reduced** ring the localisation is already a field, so `κ(p)` *is*
`R_p`, and `R_p` inverts everything a localisation of `R` can invert. In particular it inverts the
image of a uniformizer of `B`, which makes `D₁.L₁`, the localisation of `D₁.B₁` away from that
image, into a ring over which `κ(p)` is an algebra. So `L₁`-scalars become `κ(p)`-scalars, a
spanning family of `L₂` over `L₁` stays a spanning family after base change, and `[K₂ : K₁]` of
them suffice.

The bound is assembled in five steps:

1. at a minimal prime of a reduced ring `R`, `κ(p)` is the localisation `R_p`;
2. hence `κ(p)` is flat over `R`;
3. a flat base change turns an injection into a rank inequality, applied to `D₂.B₁ ↪ L₂`;
4. `L₂` is a quotient of `L₁ ⊗[K₁] K₂`
   (`Stacks.EppTheorem.exists_surjective_algHom_reduction_tensor`, transported to the carriers of
   the packages);
5. a scalar of `F = R[1/π]` crosses the tensor sign in `T ⊗[R] N` when `π` is a unit in `T`, so an
   `F`-spanning family of `N` gives a `T`-spanning family of `T ⊗[R] N`.

## Main results

* `Stacks.EppTheorem.maximalIdeal_localization_eq_bot_of_mem_minimalPrimes`,
  `Stacks.EppTheorem.residueFieldAlgEquivLocalization`: step 1.
* `Stacks.EppTheorem.flat_residueField_of_mem_minimalPrimes`: step 2.
* `Stacks.EppTheorem.finrank_tensor_le_finrank_tensor_of_flat`: step 3.
* `Stacks.EppTheorem.tmul_smul_eq_of_isLocalizationAway`: in `T ⊗[R] N` with `N` an `F`-module,
  `F = R[1/π]` and `π` a unit in `T`, `(φ a * c) ⊗ x = c ⊗ (a • x)` for `a ∈ F`.
* `Stacks.EppTheorem.span_one_tmul_eq_top_of_isLocalizationAway`,
  `Stacks.EppTheorem.finrank_tensor_le_card_of_isLocalizationAway`: an `F`-spanning family of `N`
  gives a `T`-spanning family of `T ⊗[R] N`, and the rank bound.
* `Stacks.EppTheorem.finrank_fiber_le_of_isLocalizationAway`: steps 1, 2, 3 and 5 composed, for a
  reduced ring.
* `Stacks.EppTheorem.isLocalization_away_of_irreducible`,
  `Stacks.EppTheorem.isLocalization_away_algebraMap_B₁`: the fraction field of a discrete
  valuation ring is the localisation away from a uniformizer, and `L₁` is the localisation of
  `B₁` away from that uniformizer's image.
* `Stacks.EppTheorem.isReduced_L₁`, `Stacks.EppTheorem.isReduced_B₁`: the compositum of a package
  and its `B₁` are reduced.
* `Stacks.EppTheorem.ringHom_ext_L₁`: two ring maps out of `L₁` agreeing on the images of `L` and
  `K₁` are equal.
* `Stacks.EppTheorem.exists_surjective_ringHom_compositum`: step 4, `L₂` is a quotient of
  `L₁ ⊗[K₁] K₂`.
* `Stacks.EppTheorem.exists_span_compositum`: `L₂` is spanned over `L₁` by `[K₂ : K₁]` elements.
* `Stacks.EppTheorem.finrank_fiber_le_minimalPrimes`: the fibre bound at the minimal primes.
* `Stacks.EppTheorem.isWeakSolution_of_totallyRamified`: a weak solution over `K₁` is one over
  `K₂`, in every residue characteristic and without completeness or henselianness.
* `Stacks.EppTheorem.reductionTensorMap`, `Stacks.EppTheorem.compositumMap`: the base change of
  the tower `K → K₁ → K₂` on the reduced composita, and its conjugate by the packages' `eL₁`.
* `Stacks.EppTheorem.compositumMap_algebraMap_left`,
  `Stacks.EppTheorem.compositumMap_algebraMap_right`: `compositumMap` respects the squares
  `L → L₁ → L₂` and `K₁ → K₂ → L₂`.
* `Stacks.EppTheorem.exists_algHom_B₁_compositum`: `D₁.B₁ → L₁ → L₂` factors through `D₂.B₁`.
* `Stacks.EppTheorem.isWeakSolution_of_totallyRamified_compositum`: the weak-solution statement
  with `compositumMap` as the map `L₁ → L₂`.

## References

* [The Stacks Project, Tag 09ER](https://stacks.math.columbia.edu/tag/09ER)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.EppTheorem

/-! ### Step 1 -/

/-- The localization of a reduced ring at a minimal prime has zero maximal ideal. -/
theorem maximalIdeal_localization_eq_bot_of_mem_minimalPrimes
    {R : Type*} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : p ∈ minimalPrimes R) :
    IsLocalRing.maximalIdeal (Localization.AtPrime p) = ⊥ := by
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp _
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mp Ring.KrullDimLE.isField_of_isReduced

/-- **Step 1: at a minimal prime of a reduced ring, `κ(p)` *is* the localisation `R_p`.** -/
def residueFieldAlgEquivLocalization
    {R : Type*} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : p ∈ minimalPrimes R) :
    p.ResidueField ≃ₐ[R] Localization.AtPrime p :=
  (AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom R (Localization.AtPrime p) p.ResidueField)
      ⟨by
        intro x y hxy
        have h0 : IsLocalRing.residue (Localization.AtPrime p) x
            = IsLocalRing.residue (Localization.AtPrime p) y := by
          simpa [IsLocalRing.ResidueField.algebraMap_eq] using hxy
        have h : IsLocalRing.residue (Localization.AtPrime p) (x - y) = 0 := by
          rw [map_sub, h0, sub_self]
        rw [IsLocalRing.residue_eq_zero_iff,
          maximalIdeal_localization_eq_bot_of_mem_minimalPrimes p hp, Ideal.mem_bot,
          sub_eq_zero] at h
        exact h,
      by
        intro x
        obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective x
        exact ⟨y, by simpa [IsLocalRing.ResidueField.algebraMap_eq] using hy⟩⟩).symm

/-! ### Step 2 -/

/-- **Step 2: hence `κ(p)` is flat over `R`.** -/
theorem flat_residueField_of_mem_minimalPrimes
    {R : Type*} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : p ∈ minimalPrimes R) :
    Module.Flat R p.ResidueField :=
  have : Module.Flat R (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) p.primeCompl
  Module.Flat.of_linearEquiv (residueFieldAlgEquivLocalization p hp).toLinearEquiv

/-- A non-zerodivisor avoids every minimal prime. -/
theorem notMem_of_mem_nonZeroDivisors_of_mem_minimalPrimes
    {R : Type*} [CommRing R] {p : Ideal R} (hp : p ∈ minimalPrimes R)
    {π : R} (hπ : π ∈ nonZeroDivisors R) : π ∉ p :=
  fun h => notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h hp hπ

/-- The image of a non-zerodivisor in `κ(p)` is a unit, `p` minimal. -/
theorem isUnit_algebraMap_residueField
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] {π : R} (hπ : π ∉ p) :
    IsUnit (algebraMap R p.ResidueField π) :=
  isUnit_iff_ne_zero.mpr fun h => hπ (Ideal.algebraMap_residueField_eq_zero.mp h)

/-! ### Step 5, the core: clearing denominators across the tensor product -/

/-- **Denominators clear across `T ⊗[R] N` when `T` already inverts `π`.** -/
theorem tmul_smul_eq_of_isLocalizationAway
    {R F T N : Type*} [CommRing R] [CommRing F] [Algebra R F] [CommRing T] [Algebra R T]
    [AddCommGroup N] [Module R N] [Module F N] [IsScalarTower R F N]
    (π : R) [IsLocalization.Away π F] (φ : F →+* T)
    (hφ : ∀ a : R, φ (algebraMap R F a) = algebraMap R T a)
    (hπ : IsUnit (algebraMap R T π)) (a : F) (c : T) (x : N) :
    (φ a * c) ⊗ₜ[R] x = c ⊗ₜ[R] (a • x) := by
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj π a
  have key : (algebraMap R T π ^ n) • ((φ a * c) ⊗ₜ[R] x)
      = (algebraMap R T π ^ n) • (c ⊗ₜ[R] (a • x)) := by
    have hl : (algebraMap R T π ^ n) • ((φ a * c) ⊗ₜ[R] x)
        = (algebraMap R T r * c) ⊗ₜ[R] x := by
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      have h : algebraMap R T π ^ n * (φ a * c) = φ (a * algebraMap R F π ^ n) * c := by
        rw [map_mul, map_pow, hφ]; ring
      rw [h, hr, hφ]
    have hrr : (algebraMap R T π ^ n) • (c ⊗ₜ[R] (a • x))
        = (algebraMap R T r * c) ⊗ₜ[R] x := by
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      have h1 : (algebraMap R T π ^ n * c) ⊗ₜ[R] (a • x)
          = ((π ^ n : R) • c) ⊗ₜ[R] (a • x) := by
        rw [Algebra.smul_def, map_pow]
      have h2 : ((π ^ n : R) • c) ⊗ₜ[R] (a • x) = c ⊗ₜ[R] ((π ^ n : R) • (a • x)) :=
        TensorProduct.smul_tmul _ _ _
      have h3 : ((π ^ n : R) • (a • x)) = (algebraMap R F r) • x := by
        rw [← smul_assoc]
        have h4 : ((π ^ n : R) • a) = a * algebraMap R F π ^ n := by
          rw [Algebra.smul_def, map_pow]; ring
        rw [h4, hr]
      rw [h1, h2, h3, IsScalarTower.algebraMap_smul, ← TensorProduct.smul_tmul,
        Algebra.smul_def]
    rw [hl, hrr]
  exact ((hπ.pow n).smul_left_cancel).mp key

/-- **Step 5: a spanning family over `F` spans the base change over `T`.** -/
theorem span_one_tmul_eq_top_of_isLocalizationAway
    {R F T N : Type*} [CommRing R] [CommRing F] [Algebra R F] [CommRing T] [Algebra R T]
    [AddCommGroup N] [Module R N] [Module F N] [IsScalarTower R F N]
    (π : R) [IsLocalization.Away π F] (φ : F →+* T)
    (hφ : ∀ a : R, φ (algebraMap R F a) = algebraMap R T a)
    (hπ : IsUnit (algebraMap R T π))
    {ι : Type*} (v : ι → N) (hv : Submodule.span F (Set.range v) = ⊤) :
    Submodule.span T (Set.range fun i => (1 : T) ⊗ₜ[R] v i) = ⊤ := by
  classical
  set W := Submodule.span T (Set.range fun i => (1 : T) ⊗ₜ[R] v i) with hWdef
  have htmul : ∀ (c : T) (x : N), c ⊗ₜ[R] x ∈ W := by
    intro c x
    have hx : x ∈ Submodule.span F (Set.range v) := hv ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have hc : c ⊗ₜ[R] v i = c • ((1 : T) ⊗ₜ[R] v i) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hWdef, hc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      rw [← tmul_smul_eq_of_isLocalizationAway π φ hφ hπ a c y,
        show (φ a * c) ⊗ₜ[R] y = (φ a) • (c ⊗ₜ[R] y) from by
          rw [TensorProduct.smul_tmul', smul_eq_mul]]
      exact Submodule.smul_mem _ _ hy
  have hall : ∀ z : T ⊗[R] N, z ∈ W := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c x => exact htmul c x
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  exact eq_top_iff.mpr fun z _ => hall z

/-- The base change of a module spanned by `v` over `F` is finite over `T`. -/
theorem module_finite_tensor_of_isLocalizationAway
    {R F T N : Type*} [CommRing R] [CommRing F] [Algebra R F] [CommRing T] [Algebra R T]
    [AddCommGroup N] [Module R N] [Module F N] [IsScalarTower R F N]
    (π : R) [IsLocalization.Away π F] (φ : F →+* T)
    (hφ : ∀ a : R, φ (algebraMap R F a) = algebraMap R T a)
    (hπ : IsUnit (algebraMap R T π))
    {ι : Type*} [Finite ι] (v : ι → N) (hv : Submodule.span F (Set.range v) = ⊤) :
    Module.Finite T (T ⊗[R] N) := by
  classical
  let _ := Fintype.ofFinite ι
  exact ⟨⟨Finset.image (fun i => (1 : T) ⊗ₜ[R] v i) Finset.univ, by
    simpa using span_one_tmul_eq_top_of_isLocalizationAway π φ hφ hπ v hv⟩⟩

/-- The base change of a module spanned by `v` over `F` has `T`-rank at most `#ι`. -/
theorem finrank_tensor_le_card_of_isLocalizationAway
    {R F T N : Type*} [CommRing R] [CommRing F] [Algebra R F] [CommRing T] [Algebra R T]
    [StrongRankCondition T]
    [AddCommGroup N] [Module R N] [Module F N] [IsScalarTower R F N]
    (π : R) [IsLocalization.Away π F] (φ : F →+* T)
    (hφ : ∀ a : R, φ (algebraMap R F a) = algebraMap R T a)
    (hπ : IsUnit (algebraMap R T π))
    {ι : Type*} [Fintype ι] (v : ι → N) (hv : Submodule.span F (Set.range v) = ⊤) :
    Module.finrank T (T ⊗[R] N) ≤ Fintype.card ι := by
  have h : Module.finrank T
      (Submodule.span T (Set.range fun i => (1 : T) ⊗ₜ[R] v i)) ≤ Fintype.card ι :=
    finrank_range_le_card _
  rwa [span_one_tmul_eq_top_of_isLocalizationAway π φ hφ hπ v hv, finrank_top] at h

/-! ### Step 3 -/

/-- **Step 3: a flat base change turns an injection into a rank inequality.** -/
theorem finrank_tensor_le_finrank_tensor_of_flat
    {R T S N : Type*} [CommRing R] [CommRing T] [Algebra R T] [StrongRankCondition T]
    [AddCommGroup S] [Module R S] [AddCommGroup N] [Module R N]
    [Module.Flat R T] [Module.Finite T (T ⊗[R] N)]
    (f : S →ₗ[R] N) (hf : Function.Injective f) :
    Module.finrank T (T ⊗[R] S) ≤ Module.finrank T (T ⊗[R] N) := by
  have hcoe : ∀ z : T ⊗[R] S, LinearMap.baseChange T f z = f.lTensor T z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x => simp
    | add x y hx hy => simp [hx, hy]
  have hinj : Function.Injective (LinearMap.baseChange T f) := by
    intro x y hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
      (by rw [← hcoe, ← hcoe, hxy])
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-! ### The generic-fibre bound, as a general statement -/

/-- **The generic fibres of a flat enlargement, bounded.** -/
theorem finrank_fiber_le_of_isLocalizationAway
    {R F S N : Type*} [CommRing R] [IsReduced R] [CommRing F] [Algebra R F]
    [AddCommGroup S] [Module R S]
    [AddCommGroup N] [Module R N] [Module F N] [IsScalarTower R F N]
    (π : R) [IsLocalization.Away π F] (hπ : π ∈ nonZeroDivisors R)
    (f : S →ₗ[R] N) (hf : Function.Injective f)
    {ι : Type*} [Fintype ι] (v : ι → N) (hv : Submodule.span F (Set.range v) = ⊤)
    (p : Ideal R) [p.IsPrime] (hp : p ∈ minimalPrimes R) :
    Module.finrank p.ResidueField (p.Fiber S) ≤ Fintype.card ι := by
  have hπp : π ∉ p := notMem_of_mem_nonZeroDivisors_of_mem_minimalPrimes hp hπ
  have hunit : IsUnit (algebraMap R p.ResidueField π) := isUnit_algebraMap_residueField p hπp
  have hflat : Module.Flat R p.ResidueField := flat_residueField_of_mem_minimalPrimes p hp
  have hφ : ∀ a : R,
      IsLocalization.Away.lift (S := F) π hunit (algebraMap R F a)
        = algebraMap R p.ResidueField a := fun a => IsLocalization.Away.lift_eq π hunit a
  have hfin : Module.Finite p.ResidueField (p.ResidueField ⊗[R] N) :=
    module_finite_tensor_of_isLocalizationAway π _ hφ hunit v hv
  exact (finrank_tensor_le_finrank_tensor_of_flat f hf).trans
    (finrank_tensor_le_card_of_isLocalizationAway π _ hφ hunit v hv)

/-! ### The fraction field of a discrete valuation ring inverts a uniformizer -/

/-- **The fraction field of a discrete valuation ring is the localisation away from a
uniformizer.** -/
theorem isLocalization_away_of_irreducible
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    {π : B} (hπ : Irreducible π) :
    IsLocalization.Away π L := by
  have hmem : π ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := L)
    (nonZeroDivisors B) (Submonoid.powers_le.mpr hmem) ?_).mpr inferInstance
  intro n hn
  obtain ⟨k, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hn) hπ
  refine ⟨π ^ k, ⟨k, rfl⟩, (u⁻¹ : Bˣ), ?_⟩
  rw [mul_comm (u : B), mul_assoc, Units.mul_inv, mul_one]

end Stacks.EppTheorem

/-! ### The package layer -/

namespace Stacks.EppTheorem

open IsDiscreteValuationRing

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraKL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraK₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureB₁

variable {A B K L K₁ K₂ : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    [Algebra K₁ K₂]

/-- **A package's compositum is reduced**, being a quotient by a nilradical. -/
theorem isReduced_L₁ (D : IntegralClosureBaseChange A B K L K₁) : IsReduced D.L₁ :=
  have : IsReduced ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  isReduced_of_injective D.eL₁.toRingEquiv D.eL₁.injective

/-- **A package's `B₁` is reduced**, sitting inside the reduced compositum. -/
theorem isReduced_B₁ (D : IntegralClosureBaseChange A B K L K₁) : IsReduced D.B₁ :=
  have := isReduced_L₁ D
  isReduced_of_injective (algebraMap D.B₁ D.L₁)
    (IsIntegralClosure.algebraMap_injective D.B₁ B D.L₁)

/-- **The generic-fibre bound, from a spanning family of the compositum.** If `D₂.L₁` is spanned
over `D₁.L₁` by `[K₂ : K₁]` elements, then at every minimal prime `p` of `D₁.B₁` the fibre of
`D₂.B₁` has dimension at most `[K₂ : K₁]`. -/
theorem finrank_fiber_le_of_span_of_isLocalizationAway
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.B₁ D₂.B₁] [Algebra D₁.B₁ D₂.L₁] [Algebra D₁.L₁ D₂.L₁]
    [IsScalarTower D₁.B₁ D₂.B₁ D₂.L₁] [IsScalarTower D₁.B₁ D₁.L₁ D₂.L₁]
    (π : D₁.B₁) [IsLocalization.Away π D₁.L₁] (hπ : π ∈ nonZeroDivisors D₁.B₁)
    (v : Fin (Module.finrank K₁ K₂) → D₂.L₁)
    (hv : Submodule.span D₁.L₁ (Set.range v) = ⊤)
    (p : Ideal D₁.B₁) [p.IsPrime] (hp : p ∈ minimalPrimes D₁.B₁) :
    Module.finrank p.ResidueField (p.Fiber D₂.B₁) ≤ Module.finrank K₁ K₂ := by
  have : IsReduced D₁.B₁ := isReduced_B₁ D₁
  have hinj : Function.Injective
      ((IsScalarTower.toAlgHom D₁.B₁ D₂.B₁ D₂.L₁).toLinearMap) :=
    IsIntegralClosure.algebraMap_injective D₂.B₁ B D₂.L₁
  simpa using finrank_fiber_le_of_isLocalizationAway (F := D₁.L₁) π hπ _ hinj v hv p hp

/-- `eL₁` sends the image of `x ∈ L` to the class of `x ⊗ 1`. -/
private theorem eL₁_algebraMap_left (D : IntegralClosureBaseChange A B K L K₁) (x : L) :
    D.eL₁ (algebraMap L D.L₁ x)
      = Ideal.Quotient.mk (nilradical (L ⊗[K] K₁)) (x ⊗ₜ[K] (1 : K₁)) := by
  simpa using D.eL₁_left x

/-- `eL₁` sends the image of `y ∈ K₁` to the class of `1 ⊗ y`. -/
private theorem eL₁_algebraMap_right (D : IntegralClosureBaseChange A B K L K₁) (y : K₁) :
    D.eL₁ (algebraMap K₁ D.L₁ y)
      = Ideal.Quotient.mk (nilradical (L ⊗[K] K₁)) ((1 : L) ⊗ₜ[K] y) := by
  simpa using D.eL₁_right y

/-! ### Presenting `L₁` as a localisation of `B₁` -/

/-- **A package's compositum is finite over `L`.**

`L ⊗[K] K₁` is finite over `L` because `K₁` is finite over `K`, the reduction is a quotient of it,
and `eL₁` is `L`-linear by `eL₁_left`. -/
theorem module_finite_L₁ (D : IntegralClosureBaseChange A B K L K₁) :
    Module.Finite L D.L₁ := by
  have hq : Module.Finite L ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ L (nilradical (L ⊗[K] K₁))).toLinearMap
      Ideal.Quotient.mk_surjective
  exact Module.Finite.equiv
    (AlgEquiv.ofRingEquiv (f := D.eL₁.toRingEquiv) D.eL₁_left).symm.toLinearEquiv

/-- **A package's compositum is the localisation of `B₁` away from a uniformizer.**

`IsDiscreteValuationRing.isLocalization_away_of_isIntegralClosure` turns
`IsLocalization.Away π L` into `IsLocalization.Away (algebraMap B B₁ π) L₁`, given that `B₁` is the
integral closure of `B` in `L₁` — which is a package field — and that `L₁` is integral over `L`,
which `module_finite_L₁` supplies. -/
theorem isLocalization_away_algebraMap_B₁ (D : IntegralClosureBaseChange A B K L K₁)
    {π : B} (hπ : Irreducible π) :
    IsLocalization.Away (algebraMap B D.B₁ π) D.L₁ := by
  have : IsLocalization.Away π L := isLocalization_away_of_irreducible B L hπ
  have : Module.Finite L D.L₁ := module_finite_L₁ D
  have : Algebra.IsIntegral L D.L₁ := Algebra.IsIntegral.of_finite L D.L₁
  exact IsDiscreteValuationRing.isLocalization_away_of_isIntegralClosure B L D.L₁ D.B₁ π

/-- **The image of a uniformizer in `B₁` is a non-zerodivisor**, being a unit in `L₁`. -/
theorem algebraMap_mem_nonZeroDivisors_B₁ (D : IntegralClosureBaseChange A B K L K₁)
    {π : B} (hπ : Irreducible π) :
    algebraMap B D.B₁ π ∈ nonZeroDivisors D.B₁ := by
  have := isLocalization_away_algebraMap_B₁ D hπ
  have hu : IsUnit (algebraMap D.B₁ D.L₁ (algebraMap B D.B₁ π)) :=
    IsLocalization.Away.algebraMap_isUnit (S := D.L₁) (algebraMap B D.B₁ π)
  have key : ∀ x : D.B₁, x * algebraMap B D.B₁ π = 0 → x = 0 := by
    intro x hx
    apply IsIntegralClosure.algebraMap_injective D.B₁ B D.L₁
    rw [map_zero]
    have h0 : algebraMap D.B₁ D.L₁ x * algebraMap D.B₁ D.L₁ (algebraMap B D.B₁ π) = 0 := by
      rw [← map_mul, hx, map_zero]
    exact hu.mul_left_eq_zero.mp h0
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

/-! ### Step 4: the compositum surjection, on the carriers of the packages -/

/-- **Two ring maps out of `L₁` agreeing on `L` and on `K₁` are equal.**

`L₁` is a quotient of `L ⊗[K] K₁` through `eL₁`, so it is generated as a ring by the images of `L`
and `K₁`; `eL₁_left` and `eL₁_right` say where those images go. -/
theorem ringHom_ext_L₁ (D : IntegralClosureBaseChange A B K L K₁)
    {T : Type*} [CommRing T] (f g : D.L₁ →+* T)
    (hL : ∀ x : L, f (algebraMap L D.L₁ x) = g (algebraMap L D.L₁ x))
    (hK : ∀ x : K₁, f (algebraMap K₁ D.L₁ x) = g (algebraMap K₁ D.L₁ x)) :
    ∀ z : D.L₁, f z = g z := by
  intro z
  obtain ⟨w, hw⟩ : ∃ w, D.eL₁.symm w = z := ⟨D.eL₁ z, by simp⟩
  subst hw
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have hxy : D.eL₁.symm (Ideal.Quotient.mk (nilradical (L ⊗[K] K₁)) (x ⊗ₜ[K] y))
        = algebraMap L D.L₁ x * algebraMap K₁ D.L₁ y := by
      apply D.eL₁.injective
      rw [AlgEquiv.apply_symm_apply, map_mul, D.eL₁_left, D.eL₁_right, ← map_mul]
      congr 1
      simp [Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hxy, map_mul, map_mul, hL, hK]
  | add s t hs ht =>
    rw [map_add, map_add, map_add, map_add, hs, ht]

/-- **Step 4, transported to the package's carriers: `L₂` is a quotient of `L₁ ⊗[K₁] K₂`.**

`Stacks.EppTheorem.exists_surjective_algHom_reduction_tensor` is the general form: the reduction
of a base change is a quotient of the base change of the reduction. This puts it on the composita
of two packages, through three identifications:

* `eL₁`, read as an equivalence of `K₁`-algebras (its `K₁`-compatibility is `eL₁_right`, and
  `algebraMap K₁ ((L ⊗[K] K₁) ⧸ nilradical) = Ideal.Quotient.mk ∘ includeRight` holds by `rfl`
  under `Algebra.TensorProduct.rightAlgebra`), tensored with `K₂`;
* the cancellation `(L ⊗[K] K₁) ⊗[K₁] K₂ ≅ L ⊗[K] K₂`
  (`Stacks.DiscreteValuationRing.EppLevelInduction.exists_ringEquiv_tensorCancel_includeRight`),
  pushed through the nilradical by
  `Stacks.DiscreteValuationRing.EppLevelInduction.reductionRingEquiv`;
* `eL₂`, inverted.

The two identities returned say that the resulting map sends `x ⊗ 1` to the image of `x ∈ L` and
`1 ⊗ y` to the image of `y ∈ K₂`. -/
theorem exists_surjective_ringHom_compositum
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [IsScalarTower K K₁ K₂] :
    ∃ Ψ : (D₁.L₁ ⊗[K₁] K₂) →+* D₂.L₁, Function.Surjective Ψ ∧
      (∀ x : L, Ψ (algebraMap L D₁.L₁ x ⊗ₜ[K₁] (1 : K₂)) = algebraMap L D₂.L₁ x) ∧
      (∀ y : K₂, Ψ ((1 : D₁.L₁) ⊗ₜ[K₁] y) = algebraMap K₂ D₂.L₁ y) := by
  let _ : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨f, hfsurj, hfmk⟩ :=
    exists_surjective_algHom_reduction_tensor K₁ (L ⊗[K] K₁) K₂
  obtain ⟨c, hcR, hcL⟩ :=
    Stacks.DiscreteValuationRing.EppLevelInduction.exists_ringEquiv_tensorCancel_includeRight K K₁
      K₂ L
  let e₁ : D₁.L₁ ≃ₐ[K₁] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) :=
    AlgEquiv.ofRingEquiv (f := D₁.eL₁.toRingEquiv) D₁.eL₁_right
  let e₂ : (D₁.L₁ ⊗[K₁] K₂) ≃ₐ[K₁] (((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ⊗[K₁] K₂) :=
    Algebra.TensorProduct.congr e₁ AlgEquiv.refl
  let cr := Stacks.DiscreteValuationRing.EppLevelInduction.reductionRingEquiv _ _ c
  refine ⟨(((D₂.eL₁.symm.toRingEquiv).toRingHom).comp
    ((cr.toRingHom).comp ((f : _ →+* _).comp (e₂.toRingEquiv.toRingHom)))), ?_, ?_, ?_⟩
  · intro z
    obtain ⟨y1, hy1⟩ := D₂.eL₁.symm.surjective z
    obtain ⟨y2, hy2⟩ := cr.surjective y1
    obtain ⟨y3, hy3⟩ := hfsurj y2
    obtain ⟨y4, hy4⟩ := e₂.surjective y3
    refine ⟨y4, ?_⟩
    change D₂.eL₁.symm (cr (f (e₂ y4))) = z
    rw [hy4, hy3, hy2, hy1]
  · intro x
    have h1 : e₂ (algebraMap L D₁.L₁ x ⊗ₜ[K₁] (1 : K₂))
        = Ideal.Quotient.mk (nilradical (L ⊗[K] K₁)) (x ⊗ₜ[K] (1 : K₁)) ⊗ₜ[K₁] (1 : K₂) := by
      simp only [e₂, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      change D₁.eL₁ (algebraMap L D₁.L₁ x) ⊗ₜ[K₁] (1 : K₂) = _
      rw [eL₁_algebraMap_left]
    change D₂.eL₁.symm (cr (f (e₂ _))) = _
    rw [h1, hfmk, Stacks.DiscreteValuationRing.EppLevelInduction.reductionRingEquiv_mk, hcL,
      AlgEquiv.symm_apply_eq,
      D₂.eL₁_left]
    simp
  · intro y
    have h1 : e₂ ((1 : D₁.L₁) ⊗ₜ[K₁] y)
        = Ideal.Quotient.mk (nilradical (L ⊗[K] K₁)) (1 : L ⊗[K] K₁) ⊗ₜ[K₁] y := by
      simp only [e₂, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      change D₁.eL₁ (1 : D₁.L₁) ⊗ₜ[K₁] y = _
      simp
    change D₂.eL₁.symm (cr (f (e₂ _))) = _
    rw [h1, hfmk, show ((1 : L ⊗[K] K₁) ⊗ₜ[K₁] y)
      = Algebra.TensorProduct.includeRight y from rfl,
      Stacks.DiscreteValuationRing.EppLevelInduction.reductionRingEquiv_mk, hcR,
        AlgEquiv.symm_apply_eq, D₂.eL₁_right]

/-! ### From the surjection to a spanning family -/

/-- **`L₂` is spanned over `L₁` by `[K₂ : K₁]` elements.**

The surjection `L₁ ⊗[K₁] K₂ ↠ L₂` of `exists_surjective_ringHom_compositum` carries the `L₁`-basis
of `L₁ ⊗[K₁] K₂` induced by a `K₁`-basis of `K₂` (`Algebra.TensorProduct.basis`) onto a spanning
family. Its restriction to the left factor is `algebraMap L₁ L₂` by `ringHom_ext_L₁`, given that
this map respects the two squares `L → L₁ → L₂` and `K₁ → K₂ → L₂` (`hL` and `hK`). -/
theorem exists_span_compositum
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.L₁ D₂.L₁] [IsScalarTower K K₁ K₂] [FiniteDimensional K₁ K₂]
    (hL : ∀ x : L, algebraMap D₁.L₁ D₂.L₁ (algebraMap L D₁.L₁ x) = algebraMap L D₂.L₁ x)
    (hK : ∀ x : K₁, algebraMap D₁.L₁ D₂.L₁ (algebraMap K₁ D₁.L₁ x)
      = algebraMap K₂ D₂.L₁ (algebraMap K₁ K₂ x)) :
    ∃ v : Fin (Module.finrank K₁ K₂) → D₂.L₁,
      Submodule.span D₁.L₁ (Set.range v) = ⊤ := by
  obtain ⟨Ψ, hsurj, hΨL, hΨK⟩ := exists_surjective_ringHom_compositum D₁ D₂
  have hleft : ∀ a : D₁.L₁, Ψ (a ⊗ₜ[K₁] (1 : K₂)) = algebraMap D₁.L₁ D₂.L₁ a := by
    refine ringHom_ext_L₁ D₁ (Ψ.comp Algebra.TensorProduct.includeLeftRingHom)
      (algebraMap D₁.L₁ D₂.L₁) ?_ ?_
    · intro x
      simpa [hΨL x] using (hL x).symm
    · intro x
      have htm : algebraMap K₁ D₁.L₁ x ⊗ₜ[K₁] (1 : K₂)
          = (1 : D₁.L₁) ⊗ₜ[K₁] algebraMap K₁ K₂ x := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      simp only [RingHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [htm, hΨK, hK]
  have hsmul : ∀ (a : D₁.L₁) (z : D₁.L₁ ⊗[K₁] K₂), Ψ (a • z) = a • Ψ z := by
    intro a z
    have ha : a • z = (a ⊗ₜ[K₁] (1 : K₂)) * z := by
      rw [Algebra.smul_def]
      rfl
    rw [ha, map_mul, hleft, Algebra.smul_def]
  let Ψl : (D₁.L₁ ⊗[K₁] K₂) →ₗ[D₁.L₁] D₂.L₁ :=
    { toFun := Ψ, map_add' := Ψ.map_add, map_smul' := hsmul }
  let bt : Module.Basis (Fin (Module.finrank K₁ K₂)) D₁.L₁ (D₁.L₁ ⊗[K₁] K₂) :=
    Algebra.TensorProduct.basis D₁.L₁ (Module.finBasis K₁ K₂)
  refine ⟨fun i => Ψl (bt i), ?_⟩
  rw [show (Set.range fun i => Ψl (bt i)) = Ψl '' Set.range bt from
      (Set.range_comp (Ψl : (D₁.L₁ ⊗[K₁] K₂) → D₂.L₁) bt).symm ▸ rfl,
    Submodule.span_image, bt.span_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr (show Function.Surjective Ψl from hsurj)]

/-- **The generic fibres are bounded by the degree.**

For every minimal prime of `D₁.B₁` the fibre of `D₂.B₁` has dimension at most
`Module.finrank K₁ K₂`. The uniformizer comes from `B` being a discrete valuation ring, the `Away`
presentation of `L₁` over `B₁` from `isLocalization_away_algebraMap_B₁`, and the spanning family
from `exists_span_compositum`. -/
theorem finrank_fiber_le_minimalPrimes
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.B₁ D₂.B₁] [Algebra D₁.B₁ D₂.L₁] [Algebra D₁.L₁ D₂.L₁]
    [IsScalarTower D₁.B₁ D₂.B₁ D₂.L₁] [IsScalarTower D₁.B₁ D₁.L₁ D₂.L₁]
    [IsScalarTower K K₁ K₂] [FiniteDimensional K₁ K₂]
    (hL : ∀ x : L, algebraMap D₁.L₁ D₂.L₁ (algebraMap L D₁.L₁ x) = algebraMap L D₂.L₁ x)
    (hK : ∀ x : K₁, algebraMap D₁.L₁ D₂.L₁ (algebraMap K₁ D₁.L₁ x)
      = algebraMap K₂ D₂.L₁ (algebraMap K₁ K₂ x))
    (p : Ideal D₁.B₁) (hp : p ∈ minimalPrimes D₁.B₁) (hpP : p.IsPrime) :
    Module.finrank p.ResidueField (p.Fiber D₂.B₁) ≤ Module.finrank K₁ K₂ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨v, hv⟩ := exists_span_compositum D₁ D₂ hL hK
  have : IsLocalization.Away (algebraMap B D₁.B₁ π) D₁.L₁ :=
    isLocalization_away_algebraMap_B₁ D₁ hπ
  exact finrank_fiber_le_of_span_of_isLocalizationAway D₁ D₂ (algebraMap B D₁.B₁ π)
    (algebraMap_mem_nonZeroDivisors_B₁ D₁ hπ) v hv p hp


/-- **A weak solution survives the totally ramified enlargement.**

This is `Stacks.EppTheorem.isWeakSolution_of_totallyRamified_of_finrank_fiber_le_minimalPrimes`
with its degree inequality at the minimal primes of `D₁.B₁` supplied by
`finrank_fiber_le_minimalPrimes`. Besides the package data and instances, the hypotheses are:

* `htot`, that `K₂ / K₁` is totally ramified with respect to `D₁.A₁`;
* `hmaxdown`, that a maximal ideal of `D₂.B₁` contracts to a maximal ideal of `D₂.A₁`, which
  [Stacks, Tag 09EM] provides; it does not follow here because `D₂.B₁` is integral over `B`, not
  over `D₂.A₁`;
* `hL` and `hK`, that `algebraMap D₁.L₁ D₂.L₁` respects the squares `L → L₁ → L₂` and
  `K₁ → K₂ → L₂`. Those two pin the map down, `L₁` being generated by the images of `L` and `K₁`.

Unconditional in the residue characteristic, and free of completeness and henselianness. -/
theorem isWeakSolution_of_totallyRamified
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.B₁ D₂.B₁] [Algebra D₁.A₁ D₂.B₁]
    [Algebra D₁.B₁ D₂.L₁] [Algebra D₁.L₁ D₂.L₁]
    [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁]
    [IsScalarTower D₁.B₁ D₂.B₁ D₂.L₁] [IsScalarTower D₁.B₁ D₁.L₁ D₂.L₁]
    [Module.Finite D₁.B₁ D₂.B₁]
    [Module.Flat D₁.B₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    [IsDomain D₁.A₁] [IsDiscreteValuationRing D₁.A₁] [IsFractionRing D₁.A₁ K₁]
    [IsDedekindDomain D₂.A₁]
    [FiniteDimensional K₁ K₂] [Algebra.IsSeparable K₁ K₂] [IsScalarTower K K₁ K₂]
    [Algebra D₁.A₁ K₂] [IsScalarTower D₁.A₁ K₁ K₂] [IsScalarTower D₁.A₁ D₂.A₁ K₂]
    [IsIntegralClosure D₂.A₁ D₁.A₁ K₂]
    (htot : IsTotallyRamifiedWithRespectTo D₁.A₁ K₁ K₂)
    (hmaxdown : ∀ q' : Ideal D₂.B₁, q'.IsMaximal → (q'.under D₂.A₁).IsMaximal)
    (hL : ∀ x : L, algebraMap D₁.L₁ D₂.L₁ (algebraMap L D₁.L₁ x) = algebraMap L D₂.L₁ x)
    (hK : ∀ x : K₁, algebraMap D₁.L₁ D₂.L₁ (algebraMap K₁ D₁.L₁ x)
      = algebraMap K₂ D₂.L₁ (algebraMap K₁ K₂ x))
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution :=
  isWeakSolution_of_totallyRamified_of_finrank_fiber_le_minimalPrimes D₁ D₂ htot hmaxdown
    (fun p hp hpP => finrank_fiber_le_minimalPrimes D₁ D₂ hL hK p hp hpP) hD₁


/-! ### The canonical compositum map -/

/-- The base change of the tower `K → K₁ → K₂` on reduced composita,
`(L ⊗[K] K₁) ⧸ nilradical → (L ⊗[K] K₂) ⧸ nilradical`.

`Algebra.TensorProduct.map (id L) (K₁ → K₂)` carries nilpotents to nilpotents, so it descends to
the reductions. This is the only map there is between the two composita, and `compositumMap` below
is it read through a pair of packages' `eL₁`. -/
def reductionTensorMap (K L K₁ K₂ : Type*) [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) →+*
      ((L ⊗[K] K₂) ⧸ nilradical (L ⊗[K] K₂)) :=
  Ideal.Quotient.lift (nilradical (L ⊗[K] K₁))
    ((Ideal.Quotient.mk (nilradical (L ⊗[K] K₂))).comp
      (Algebra.TensorProduct.map (AlgHom.id K L)
        (IsScalarTower.toAlgHom K K₁ K₂) : (L ⊗[K] K₁) →+* (L ⊗[K] K₂)))
    (by
      intro a ha
      obtain ⟨n, hn⟩ := ha
      have ha0 : a ^ n = 0 := by simpa using hn
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ⟨n, ?_⟩
      simp only [← map_pow, ha0, map_zero]
      exact Submodule.zero_mem _)

/-- `reductionTensorMap` sends the class of `t` to the class of its image under
`Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K K₁ K₂)`. -/
@[simp]
theorem reductionTensorMap_mk (K L K₁ K₂ : Type*) [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂]
    (t : L ⊗[K] K₁) :
    reductionTensorMap K L K₁ K₂ (Ideal.Quotient.mk _ t)
      = Ideal.Quotient.mk (nilradical (L ⊗[K] K₂))
        ((Algebra.TensorProduct.map (AlgHom.id K L)
          (IsScalarTower.toAlgHom K K₁ K₂) : (L ⊗[K] K₁) →ₐ[K] (L ⊗[K] K₂)) t) := rfl

/-- **The canonical map between the composita of two packages over a tower `K → K₁ → K₂`.**

A package records its compositum only up to `eL₁`, and the reduced composita are connected by
`reductionTensorMap`; this is that map conjugated by `D₁.eL₁` and `D₂.eL₁`. It respects the
squares `L → L₁ → L₂` and `K₁ → K₂ → L₂` (`compositumMap_algebraMap_left`,
`compositumMap_algebraMap_right`), by the package fields `eL₁_left` and `eL₁_right`. -/
def compositumMap [IsScalarTower K K₁ K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂) : D₁.L₁ →+* D₂.L₁ :=
  ((D₂.eL₁.symm.toRingEquiv).toRingHom).comp
    ((reductionTensorMap K L K₁ K₂).comp (D₁.eL₁.toRingEquiv.toRingHom))

/-- `compositumMap D₁ D₂` is `D₂.eL₁.symm ∘ reductionTensorMap K L K₁ K₂ ∘ D₁.eL₁`. -/
theorem compositumMap_apply [IsScalarTower K K₁ K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂) (x : D₁.L₁) :
    compositumMap D₁ D₂ x = D₂.eL₁.symm (reductionTensorMap K L K₁ K₂ (D₁.eL₁ x)) := rfl

/-- `compositumMap` is the identity on the image of `L`. -/
theorem compositumMap_algebraMap_left [IsScalarTower K K₁ K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂) (x : L) :
    compositumMap D₁ D₂ (algebraMap L D₁.L₁ x) = algebraMap L D₂.L₁ x := by
  rw [compositumMap_apply, eL₁_algebraMap_left, reductionTensorMap_mk,
    Algebra.TensorProduct.map_tmul, AlgEquiv.symm_apply_eq, D₂.eL₁_left]
  simp

/-- `compositumMap` carries the image of `K₁` to the image of `K₂`. -/
theorem compositumMap_algebraMap_right [IsScalarTower K K₁ K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂) (y : K₁) :
    compositumMap D₁ D₂ (algebraMap K₁ D₁.L₁ y)
      = algebraMap K₂ D₂.L₁ (algebraMap K₁ K₂ y) := by
  rw [compositumMap_apply, eL₁_algebraMap_right, reductionTensorMap_mk,
    Algebra.TensorProduct.map_tmul, AlgEquiv.symm_apply_eq, D₂.eL₁_right]
  simp [IsScalarTower.coe_toAlgHom']

/-- **`compositumMap` is a `B`-algebra map**, hence lifts to the integral closures. -/
theorem compositumMap_algebraMap_base [IsScalarTower K K₁ K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂) (b : B) :
    compositumMap D₁ D₂ (algebraMap B D₁.L₁ b) = algebraMap B D₂.L₁ b := by
  rw [IsScalarTower.algebraMap_apply B L D₁.L₁, compositumMap_algebraMap_left,
    ← IsScalarTower.algebraMap_apply B L D₂.L₁]

/-- **The `B₁`-side square.**

`D₁.B₁` is integral over `B` and `D₂.B₁` is the integral closure of `B` in `L₂`, so the composite
`D₁.B₁ → L₁ → L₂` factors through `D₂.B₁` by `IsIntegralClosure.lift`. -/
theorem exists_algHom_B₁_compositum [IsScalarTower K K₁ K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂) :
    ∃ b : D₁.B₁ →ₐ[B] D₂.B₁, ∀ x : D₁.B₁,
      algebraMap D₂.B₁ D₂.L₁ (b x)
        = compositumMap D₁ D₂ (algebraMap D₁.B₁ D₁.L₁ x) := by
  let _ : Algebra D₁.B₁ D₂.L₁ :=
    ((compositumMap D₁ D₂).comp (algebraMap D₁.B₁ D₁.L₁)).toAlgebra
  have : IsScalarTower B D₁.B₁ D₂.L₁ := by
    refine IsScalarTower.of_algebraMap_eq fun b => ?_
    change algebraMap B D₂.L₁ b
      = compositumMap D₁ D₂ (algebraMap D₁.B₁ D₁.L₁ (algebraMap B D₁.B₁ b))
    rw [← IsScalarTower.algebraMap_apply B D₁.B₁ D₁.L₁, compositumMap_algebraMap_base]
  have : Algebra.IsIntegral B D₁.B₁ := IsIntegralClosure.isIntegral_algebra B D₁.L₁
  exact ⟨IsIntegralClosure.lift B D₂.B₁ D₂.L₁, IsIntegralClosure.algebraMap_lift B D₂.B₁ D₂.L₁⟩

/-- **A weak solution survives the totally ramified enlargement, with the canonical compositum
map.**

This is `isWeakSolution_of_totallyRamified` with `Algebra D₁.L₁ D₂.L₁` given by `compositumMap`,
so that the squares `hL` and `hK` hold by `compositumMap_algebraMap_left` and
`compositumMap_algebraMap_right`. The remaining hypotheses are:

* the `A`-side data `Algebra D₁.A₁ D₂.A₁`, the towers, and `IsIntegralClosure D₂.A₁ D₁.A₁ K₂`;
* `bmap` with `hb`, a `B`-algebra map `B₁ → B₂` compatible with `compositumMap` in `L₂`, which
  `exists_algHom_B₁_compositum` provides;
* `Module.Finite`, `Module.Flat` for `D₁.B₁ → D₂.B₁`, and `htot`, `hmaxdown`. -/
theorem isWeakSolution_of_totallyRamified_compositum
    [IsScalarTower K K₁ K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.A₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    [IsDomain D₁.A₁] [IsDiscreteValuationRing D₁.A₁] [IsFractionRing D₁.A₁ K₁]
    [IsDedekindDomain D₂.A₁]
    [FiniteDimensional K₁ K₂] [Algebra.IsSeparable K₁ K₂]
    [Algebra D₁.A₁ K₂] [IsScalarTower D₁.A₁ K₁ K₂] [IsScalarTower D₁.A₁ D₂.A₁ K₂]
    [IsIntegralClosure D₂.A₁ D₁.A₁ K₂]
    (htot : IsTotallyRamifiedWithRespectTo D₁.A₁ K₁ K₂)
    (hmaxdown : ∀ q' : Ideal D₂.B₁, q'.IsMaximal → (q'.under D₂.A₁).IsMaximal)
    (bmap : D₁.B₁ →ₐ[B] D₂.B₁)
    (hb : ∀ x : D₁.B₁, algebraMap D₂.B₁ D₂.L₁ (bmap x)
      = compositumMap D₁ D₂ (algebraMap D₁.B₁ D₁.L₁ x)) :
    letI : Algebra D₁.L₁ D₂.L₁ := (compositumMap D₁ D₂).toAlgebra
    letI : Algebra D₁.B₁ D₂.B₁ := bmap.toRingHom.toAlgebra
    letI : Algebra D₁.B₁ D₂.L₁ :=
      ((algebraMap D₂.B₁ D₂.L₁).comp bmap.toRingHom).toAlgebra
    ∀ [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁] [Module.Finite D₁.B₁ D₂.B₁]
      [Module.Flat D₁.B₁ D₂.B₁], D₁.IsWeakSolution → D₂.IsWeakSolution := by
  let : Algebra D₁.L₁ D₂.L₁ := (compositumMap D₁ D₂).toAlgebra
  let : Algebra D₁.B₁ D₂.B₁ := bmap.toRingHom.toAlgebra
  let : Algebra D₁.B₁ D₂.L₁ :=
    ((algebraMap D₂.B₁ D₂.L₁).comp bmap.toRingHom).toAlgebra
  intro _ _ _ hD₁
  have : IsScalarTower D₁.B₁ D₂.B₁ D₂.L₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower D₁.B₁ D₁.L₁ D₂.L₁ := IsScalarTower.of_algebraMap_eq hb
  exact isWeakSolution_of_totallyRamified D₁ D₂ htot hmaxdown
    (compositumMap_algebraMap_left D₁ D₂) (compositumMap_algebraMap_right D₁ D₂) hD₁


end Stacks.EppTheorem

end

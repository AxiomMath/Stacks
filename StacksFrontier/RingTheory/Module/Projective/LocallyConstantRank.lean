module

import StacksCore.RingTheory.Nakayama
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
import StacksCore.Tactic.EgaSgaAttribute
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section

universe u v

/-!
# Finite modules with locally constant fibre dimension over a reduced ring

Let `R` be a reduced commutative ring and `M` a finite `R`-module. This file proves that `M` is
projective as soon as the fibre dimension `ρ_M : Spec(R) → ℕ`,
`𝔭 ↦ dim_{κ(𝔭)} κ(𝔭) ⊗_R M`, is locally constant, and conversely; this is item (9) of the list
of characterizations of finite projective modules, added to the eight items of
`Module.finite_projective_tfae` in the presence of reducedness.

The forward implication needs no reducedness: a finite projective module is finitely presented and
flat, its fibre dimension is `Module.rankAtStalk` and that function is locally constant. For the
converse, fix a maximal ideal `𝔪` and put `r = ρ_M(𝔪)`. Lifting a basis of the fibre
`κ(𝔪) ⊗_R M` to `r` elements `x₁, …, x_r` of `M`, Nakayama's lemma produces `f ∉ 𝔪` such that the
`xᵢ` generate `M_f`, and local constancy produces `g ∉ 𝔪` with `ρ_M` constant equal to `r` on
`D(g)`. On `h = fg` the resulting surjection `Ψ : R_h^{⊕ r} → M_h` is injective as well, so `M_h`
is free, and the elements `h` obtained this way from all maximal ideals generate the unit ideal:
`M` is finite locally free, from which finite presentation and flatness — hence projectivity —
follow by localization at that cover.

## Main results

* `Stacks.FiniteProjective.ConstantFibreRank.solution`: over a reduced ring, a finite module is
  projective if and only if its fibre dimension is locally constant on the spectrum.

## Implementation notes

Injectivity of `Ψ` is where reducedness enters, and it is carried by
`Stacks.FiniteProjective.ConstantFibreRank.mul_eq_zero_of_sum_smul_eq_zero`: if the `xᵢ` generate
`M` after inverting `h` and `ρ_M = r` on `D(h)`, then every relation `∑ bᵢ xᵢ = 0` in `M` has `h bᵢ
= 0`. The source instead localizes `R_h` at its minimal primes, at which the local ring is a field
(Lemma 00EU) and the localization map of `R_h` into the product of those fields is injective (Lemma
00EW). Here the same idea is carried out one step earlier, over `R` itself and with the fibres
rather than the localizations: for *every* prime `𝔮` not containing `h` the base change `κ(𝔮)^{⊕ r}
→ κ(𝔮) ⊗_R M` of `Ψ` is a surjection between `κ(𝔮)`-vector spaces of the same dimension `r`, so the
images of the `xᵢ` are a basis and every `bᵢ` lies in `𝔮`
(`Stacks.FiniteProjective.ConstantFibreRank.mem_of_sum_smul_eq_zero`); thus `h bᵢ` lies in every
prime of `R` and so is nilpotent, that is zero. This avoids localizing a localization and needs of
reducedness only that the nilradical is zero; the fibre dimension is used exactly where the source
uses it, and `κ(𝔮) ⊗_R M` is the fibre whose dimension `ρ_M(𝔮)` is, so no comparison with
`Module.rankAtStalk` — which differs from `ρ_M` for non-flat modules — is needed on this side.

That the base changed family spans the fibre is a general fact about base change,
`Stacks.FiniteProjective.ConstantFibreRank.span_image_mk_one_eq_top`: if the `R`-span of a set `s ⊆
M` contains, for every `m ∈ M`, a multiple `t • m` by an element `t` of `R` that becomes a unit in
an `R`-algebra `A`, then `1 ⊗ s` spans `A ⊗_R M` over `A`.

At a maximal ideal the fibre is the reduction of `M`:
`Stacks.FiniteProjective.ConstantFibreRank.fiberEquivQuotSMul` is the `R`-linear isomorphism `κ(𝔪)
⊗_R M ≅ M ⧸ 𝔪M` carrying `1 ⊗ m` to the class of `m`, assembled from `R ⧸ 𝔪 ≅ κ(𝔪)` and
`TensorProduct.quotTensorEquivQuotSMul`. It is what turns a basis of the fibre into the generating
family of `M ⧸ 𝔪M` that Nakayama's lemma consumes.

Nakayama's lemma enters as Lemma 00DV (7), in the concrete form
`Submodule.exists_sub_one_mem_and_span_image_mkLinearMap_eq_top`, and the passage from "the `xᵢ`
span the localization" to "some `h ^ n` multiple of every element of `M` lies in their span" is
`Submodule.span_image_eq_top_iff`.

The last step is the implication (7) ⇒ (1) ⇒ (2) of Lemma 00NX, spelled out through
`Module.FinitePresentation.of_localizationSpan`, `Module.flat_of_localized_span` and
`Module.Flat.projective_of_finitePresentation` rather than through
`Module.finite_projective_tfae`; Lemma 00NX itself is therefore not used.

## References

* [StacksProject 0FWG](https://stacks.math.columbia.edu/tag/0FWG)
-/

namespace Stacks.FiniteProjective.ConstantFibreRank

open Module PrimeSpectrum TensorProduct



variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A scalar of `R` acting on `1 ⊗ₜ m` through the algebra map of an `R`-algebra `A` is the same
as acting on `m`. -/
private theorem algebraMap_smul_one_tmul (A : Type*) [CommRing A] [Algebra R A] (r : R) (m : M) :
    algebraMap R A r • ((1 : A) ⊗ₜ[R] m) = (1 : A) ⊗ₜ[R] (r • m) := by
  rw [algebraMap_smul, TensorProduct.tmul_smul]

/-- **The fibre at a maximal ideal is the reduction.** For `𝔪` maximal the fibre `κ(𝔪) ⊗_R M` is
`R`-linearly isomorphic to `M ⧸ 𝔪M`: the isomorphism `R ⧸ 𝔪 ≅ κ(𝔪)` identifies it with
`(R ⧸ 𝔪) ⊗_R M`, which is `M ⧸ 𝔪M`. -/
private noncomputable def fiberEquivQuotSMul (𝔪 : Ideal R) [𝔪.IsMaximal] :
    𝔪.Fiber M ≃ₗ[R] M ⧸ 𝔪 • (⊤ : Submodule R M) :=
  (TensorProduct.congr (LinearEquiv.ofBijective
      ((Algebra.linearMap (R ⧸ 𝔪) 𝔪.ResidueField).restrictScalars R)
      𝔪.bijective_algebraMap_quotient_residueField).symm (LinearEquiv.refl R M)).trans
    (TensorProduct.quotTensorEquivQuotSMul M 𝔪)

private theorem fiberEquivQuotSMul_one_tmul (𝔪 : Ideal R) [𝔪.IsMaximal] (m : M) :
    fiberEquivQuotSMul 𝔪 ((1 : 𝔪.ResidueField) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
  have h1 : (LinearEquiv.ofBijective
      ((Algebra.linearMap (R ⧸ 𝔪) 𝔪.ResidueField).restrictScalars R)
      𝔪.bijective_algebraMap_quotient_residueField).symm 1 = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    exact (map_one (algebraMap (R ⧸ 𝔪) 𝔪.ResidueField)).symm
  simp [fiberEquivQuotSMul, h1]

/-- The reduction `M ⧸ 𝔪M` of a finite module at a maximal ideal is generated by the images of
`dim_{κ(𝔪)} κ(𝔪) ⊗_R M` elements of `M`: a `κ(𝔪)`-basis of the fibre lifts to elements
`x₁, …, x_r` of `M`, because `R → κ(𝔪)` is surjective for `𝔪` maximal, and generation transfers
along `fiberEquivQuotSMul`. -/
private theorem exists_span_image_quotient_eq_top (𝔪 : Ideal R) [𝔪.IsMaximal]
    [Module.Finite R M] :
    ∃ x : Fin (finrank 𝔪.ResidueField (𝔪.Fiber M)) → M,
      Submodule.span R (Submodule.Quotient.mk '' Set.range x :
        Set (M ⧸ 𝔪 • (⊤ : Submodule R M))) = ⊤ := by
  classical
  have hsurj : Function.Surjective (algebraMap R 𝔪.ResidueField) :=
    𝔪.algebraMap_residueField_surjective
  have b : Basis (Fin (finrank 𝔪.ResidueField (𝔪.Fiber M))) 𝔪.ResidueField (𝔪.Fiber M) :=
    Module.finBasisOfFinrankEq _ _ rfl
  choose x hx using fun i ↦ TensorProduct.mk_surjective R M 𝔪.ResidueField hsurj (b i)
  refine ⟨x, ?_⟩
  have himg : (Submodule.Quotient.mk '' Set.range x : Set (M ⧸ 𝔪 • (⊤ : Submodule R M)))
      = (fiberEquivQuotSMul 𝔪).toLinearMap '' Set.range b := by
    rw [← Set.range_comp, ← Set.range_comp]
    exact congrArg Set.range (funext fun i ↦ by
      simp only [Function.comp_apply, ← hx i, TensorProduct.mk_apply, LinearEquiv.coe_coe,
        fiberEquivQuotSMul_one_tmul])
  rw [himg, Submodule.span_image, ← Submodule.restrictScalars_span R 𝔪.ResidueField hsurj,
    b.span_eq, Submodule.restrictScalars_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (fiberEquivQuotSMul 𝔪).surjective

/-- **Base change of a family that generates up to units.** If the `R`-span of `s ⊆ M` contains a
multiple `t • m` of every `m : M` by an element `t` of `R` whose image in an `R`-algebra `A` is a
unit, then the elements `1 ⊗ y`, `y ∈ s`, span `A ⊗_R M` over `A`.

For `A` a localization of `R` this is `Submodule.span_image_eq_top_iff`; the use here is with `A`
a residue field `κ(𝔮)`, where the units are the elements of `R ∖ 𝔮`. -/
private theorem span_image_mk_one_eq_top (A : Type*) [CommRing A] [Algebra R A] {s : Set M}
    (hs : ∀ m : M, ∃ t : R, IsUnit (algebraMap R A t) ∧ t • m ∈ Submodule.span R s) :
    Submodule.span A (TensorProduct.mk R A M 1 '' s) = ⊤ := by
  rw [← Submodule.baseChange_span, eq_top_iff]
  rintro y -
  induction y using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
      obtain ⟨t, ⟨u, hu⟩, hmem⟩ := hs m
      have h1 : algebraMap R A t • ((1 : A) ⊗ₜ[R] m) ∈ (Submodule.span R s).baseChange A := by
        rw [algebraMap_smul_one_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem 1 hmem
      have h2 : (1 : A) ⊗ₜ[R] m ∈ (Submodule.span R s).baseChange A := by
        have := Submodule.smul_mem _ ((u⁻¹ : Aˣ) : A) h1
        rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at this
      rw [show a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ h2
  | add y z hy hz => exact add_mem hy hz

/-- **A generating family of the size of a fibre is independent modulo every prime.** If
`x₁, …, x_r` generate `M` after inverting some element outside the prime `𝔮`, and the fibre
`κ(𝔮) ⊗_R M` has dimension `r`, then every relation `∑ bᵢ xᵢ = 0` over `R` has all its
coefficients in `𝔮`.

Base changing to `κ(𝔮)` turns the family into a spanning family of `r` vectors in an
`r`-dimensional `κ(𝔮)`-vector space, hence into a basis. -/
private theorem mem_of_sum_smul_eq_zero (𝔮 : Ideal R) [𝔮.IsPrime] {r : ℕ}
    (x : Fin r → M) (hgen : ∀ m : M, ∃ t ∉ 𝔮, t • m ∈ Submodule.span R (Set.range x))
    (hrank : finrank 𝔮.ResidueField (𝔮.Fiber M) = r) {b : Fin r → R}
    (hb : ∑ i, b i • x i = 0) (i : Fin r) : b i ∈ 𝔮 := by
  have hli : LinearIndependent 𝔮.ResidueField fun i ↦ (1 : 𝔮.ResidueField) ⊗ₜ[R] x i := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_
      (by rw [Fintype.card_fin, hrank])
    rw [show (Set.range fun i ↦ (1 : 𝔮.ResidueField) ⊗ₜ[R] x i)
      = TensorProduct.mk R 𝔮.ResidueField M 1 '' Set.range x by rw [← Set.range_comp]; rfl]
    exact (span_image_mk_one_eq_top _ fun m ↦
      let ⟨t, ht, htm⟩ := hgen m
      ⟨t, isUnit_iff_ne_zero.2 fun h0 ↦ ht (Ideal.algebraMap_residueField_eq_zero.1 h0), htm⟩).ge
  have h0 : ∑ j, algebraMap R 𝔮.ResidueField (b j) • ((1 : 𝔮.ResidueField) ⊗ₜ[R] x j) = 0 := by
    simp only [algebraMap_smul_one_tmul, ← TensorProduct.tmul_sum, hb, TensorProduct.tmul_zero]
  exact Ideal.algebraMap_residueField_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i)

/-- **Over a reduced ring, `h` kills every relation among a family that generates after inverting
`h`.** If `x₁, …, x_r` generate `M` after inverting `h` and the fibre dimension of `M` is constant
equal to `r` on `D(h)`, then every relation `∑ bᵢ xᵢ = 0` in `M` satisfies `h bᵢ = 0`.

Indeed `h bᵢ` lies in every prime `𝔮` of `R`: in those containing `h` because of the factor `h`,
and in the others by `mem_of_sum_smul_eq_zero`. So `h bᵢ` is nilpotent, hence zero. This is the
step at which reducedness is used, and it is what makes the surjection `R_h^{⊕ r} → M_h`
injective. -/
private theorem mul_eq_zero_of_sum_smul_eq_zero [IsReduced R] {r : ℕ} {h : R}
    (x : Fin r → M) (hgen : ∀ m : M, ∃ n : ℕ, h ^ n • m ∈ Submodule.span R (Set.range x))
    (hrank : ∀ 𝔮 : PrimeSpectrum R, h ∉ 𝔮.asIdeal →
      finrank 𝔮.asIdeal.ResidueField (𝔮.asIdeal.Fiber M) = r)
    {b : Fin r → R} (hb : ∑ i, b i • x i = 0) (i : Fin r) : h * b i = 0 := by
  refine (nilpotent_iff_mem_prime.2 fun 𝔮 h𝔮 ↦ ?_).eq_zero
  have : 𝔮.IsPrime := h𝔮
  by_cases hh : h ∈ 𝔮
  · exact Ideal.mul_mem_right _ _ hh
  · exact Ideal.mul_mem_left _ _ (mem_of_sum_smul_eq_zero 𝔮 x
      (fun m ↦ let ⟨n, hn⟩ := hgen m; ⟨h ^ n, fun hmem ↦ hh (h𝔮.mem_of_pow_mem n hmem), hn⟩)
      (hrank ⟨𝔮, h𝔮⟩ hh) hb i)

/-- **Freeness on a standard open.** If `x₁, …, x_r` generate `M` after inverting `h` and the
fibre dimension of `M` is constant equal to `r` on `D(h)`, then `M_h` is free over `R_h`, provided
`R` is reduced.

The `xᵢ` give a surjection `Ψ : R_h^{⊕ r} → M_h`, and it is injective: an element of its kernel is
cleared of denominators into a relation `∑ bᵢ xᵢ = 0` over `R`, which `h` kills by
`mul_eq_zero_of_sum_smul_eq_zero`, and `h` is invertible in `R_h`. -/
private theorem free_localizedModule_away [IsReduced R] {r : ℕ} {h : R}
    (x : Fin r → M) (hgen : ∀ m : M, ∃ n : ℕ, h ^ n • m ∈ Submodule.span R (Set.range x))
    (hrank : ∀ 𝔮 : PrimeSpectrum R, h ∉ 𝔮.asIdeal →
      finrank 𝔮.asIdeal.ResidueField (𝔮.asIdeal.Fiber M) = r) :
    Module.Free (Localization.Away h) (LocalizedModule.Away h M) := by
  set S := Submonoid.powers h with hS
  set R' := Localization.Away h with hR'
  set Ψ : (Fin r → R') →ₗ[R'] LocalizedModule.Away h M :=
    Fintype.linearCombination R' fun i ↦ LocalizedModule.mkLinearMap S M (x i) with hΨ
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top, hΨ, Fintype.range_linearCombination,
      show (Set.range fun i ↦ LocalizedModule.mkLinearMap S M (x i))
        = LocalizedModule.mkLinearMap S M '' Set.range x from Set.range_comp _ _]
    exact (Submodule.span_image_eq_top_iff R' S _ _).2 fun m ↦
      let ⟨n, hn⟩ := hgen m
      ⟨⟨h ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers h) n⟩, hn⟩
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    -- clear denominators: `d • z` comes from `a : Fin r → R`
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples S Finset.univ z
    choose a ha using fun i ↦ hd i (Finset.mem_univ i)
    have hmk : LocalizedModule.mkLinearMap S M (∑ i, a i • x i) = 0 := by
      have hdz : (fun i ↦ algebraMap R R' (a i)) = algebraMap R R' (d : R) • z := by
        funext i; rw [ha i, Pi.smul_apply, algebraMap_smul]
      calc LocalizedModule.mkLinearMap S M (∑ i, a i • x i)
          = Ψ (fun i ↦ algebraMap R R' (a i)) := by
            simp only [hΨ, Fintype.linearCombination_apply, map_sum, map_smul, algebraMap_smul]
        _ = 0 := by rw [hdz, map_smul, hz, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S (LocalizedModule.mkLinearMap S M)).1 hmk
    -- the relation `∑ (t aᵢ) xᵢ = 0` holds in `M` itself
    have hb : ∑ i, ((t : R) * a i) • x i = 0 := by
      rw [show (∑ i, ((t : R) * a i) • x i) = (t : R) • ∑ i, a i • x i by
        simp [Finset.smul_sum, smul_smul]]
      exact ht
    refine funext fun i ↦ ?_
    have hu : IsUnit (algebraMap R R' (h * (t : R) * (d : R))) :=
      IsLocalization.map_units R' (⟨h, Submonoid.mem_powers h⟩ * t * d : S)
    refine hu.mul_right_eq_zero.1 ?_
    calc algebraMap R R' (h * (t : R) * (d : R)) * z i
        = algebraMap R R' (h * (t : R)) * ((d : R) • z i) := by
          rw [map_mul, Algebra.smul_def]; ring
      _ = algebraMap R R' (h * ((t : R) * a i)) := by rw [← ha i, ← map_mul, mul_assoc]
      _ = 0 := by rw [mul_eq_zero_of_sum_smul_eq_zero x hgen hrank hb i, map_zero]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩)

/-- A finite module over a reduced ring whose fibre dimension is locally constant is free on a
standard open around every maximal ideal: Nakayama's lemma provides `f ∉ 𝔪` such that a lift of a
basis of the fibre at `𝔪` generates `M_f`, local constancy provides `g ∉ 𝔪` on whose standard open
the fibre dimension is that same `r`, and `h = fg` is free by `free_localizedModule_away`. -/
private theorem exists_free_away [IsReduced R] [Module.Finite R M]
    (hlc : IsLocallyConstant fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M))
    (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] :
    ∃ g ∉ 𝔪, Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  set r := finrank 𝔪.ResidueField (𝔪.Fiber M) with hr
  obtain ⟨x, hx⟩ := exists_span_image_quotient_eq_top (M := M) 𝔪
  -- Nakayama: the `xᵢ` generate `M_f` for some `f ≡ 1 mod 𝔪`, in particular `f ∉ 𝔪`
  obtain ⟨f, hf1, hfspan⟩ :=
    Submodule.exists_sub_one_mem_and_span_image_mkLinearMap_eq_top 𝔪 (Set.range x) hx
  have hf : f ∉ 𝔪 := fun hmem ↦ h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 (by
    simpa using 𝔪.sub_mem hmem hf1))
  -- a standard open around `𝔪` on which the fibre dimension is constant equal to `r`
  obtain ⟨V, ⟨g, rfl⟩, hgm, hVU⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum R) ∈
        {q : PrimeSpectrum R | finrank q.asIdeal.ResidueField (q.asIdeal.Fiber M) = r} from hr.symm)
      (hlc.isOpen_fiber r)
  have hgen : ∀ m : M, ∃ n : ℕ, (f * g) ^ n • m ∈ Submodule.span R (Set.range x) := fun m ↦ by
    obtain ⟨t, ht⟩ := (Submodule.span_image_eq_top_iff (Localization (Submonoid.powers f))
      (Submonoid.powers f) (LocalizedModule.mkLinearMap (Submonoid.powers f) M) _).1 hfspan m
    obtain ⟨n, hn⟩ : ∃ n : ℕ, f ^ n = (t : R) := t.2
    exact ⟨n, by rw [mul_pow, mul_comm, mul_smul, hn]; exact Submodule.smul_mem _ _ ht⟩
  refine ⟨f * g, fun hmem ↦ ?_, free_localizedModule_away x hgen fun 𝔮 hmem ↦ hVU ?_⟩
  · rcases h𝔪.isPrime.mul_mem_iff_mem_or_mem.1 hmem with hh | hh
    exacts [hf hh, hgm hh]
  · simpa only [SetLike.mem_coe, mem_basicOpen] using
      fun hg ↦ hmem (𝔮.asIdeal.mul_mem_left f hg)

/-- A finite module `M` over a reduced ring `R` is projective if and only if the function
`𝔭 ↦ dim_{κ(𝔭)} M ⊗_R κ(𝔭)` on `Spec R` is locally constant. -/
public theorem solution (R : Type u) [CommRing R] [IsReduced R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    Module.Projective R M ↔
      IsLocallyConstant fun p : PrimeSpectrum R ↦
        Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) := by
  constructor
  · intro hproj
    have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    have : Module.Flat R M := Module.Flat.of_projective
    rw [show (fun p : PrimeSpectrum R ↦
        Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M))
        = Module.rankAtStalk (R := R) M from
      funext fun p ↦ p.asIdeal.finrank_fiber_eq_rankAtStalk]
    exact Module.isLocallyConstant_rankAtStalk
  · intro hlc
    obtain ⟨s, hs, hfree⟩ :=
      Stacks.LocallyFree.FiniteProjective.exists_span_eq_top_of_forall_maximal
        (fun g ↦ Module.Free (Localization.Away g) (LocalizedModule.Away g M))
        fun 𝔪 h𝔪 ↦ have := h𝔪; exists_free_away hlc 𝔪
    have : Module.FinitePresentation R M := Module.FinitePresentation.of_localizationSpan s hs
      fun g ↦ have := hfree g.1 g.2; Module.finitePresentation_of_projective _ _
    have : Module.Flat R M := Module.flat_of_localized_span R M s hs fun g ↦
      have := hfree g.1 g.2
      Module.Flat.trans R (Localization.Away g.1) (LocalizedModule.Away g.1 M)
    exact Module.Flat.projective_of_finitePresentation

end Stacks.FiniteProjective.ConstantFibreRank

/-!
# Finite modules of locally constant fibre dimension over a reduced ring

Let `R` be a reduced commutative ring and let `M` be a finite `R`-module. Then `M` is projective
— equivalently, by `Module.finite_projective_tfae`, finitely presented and flat, a direct summand
of a finite free module, finite locally free, … — if and only if the fibre dimension
`ρ_M : Spec(R) → ℕ`, `𝔭 ↦ dim_{κ(𝔭)} M ⊗_R κ(𝔭)`, is locally constant in the Zariski topology.

Over an arbitrary ring local constancy of `ρ_M` is not enough: one must also require that `M` be
free at every prime, which is item (8) of `Module.finite_projective_tfae`. Reducedness of `R` is
exactly what makes that extra condition automatic, because a surjection between modules over a
reduced ring can be tested for injectivity at the minimal primes, where the local ring is a field.

## Main results

* `Module.projective_iff_isLocallyConstant_finrank_fiber`: over a reduced ring, a finite module is
  projective if and only if its fibre dimension is a locally constant function on the spectrum.

## Implementation notes

The source states this as a ninth item, "`M` is finite and `ρ_M` is locally constant", equivalent
to the eight items of `Module.finite_projective_tfae`, every one of which also contains finiteness
of `M`. Finiteness is therefore carried here as the instance hypothesis `[Module.Finite R M]`
common to both sides, and what remains is the equivalence with item (2), `Module.Projective R M`;
`Module.finite_projective_tfae` transports it to the other seven items. The source's conjunctive
form `Module.Finite R M ∧ IsLocallyConstant ρ_M ↔ Module.Finite R M ∧ Module.Projective R M`
follows, both sides being false when `M` is not finite.

The function `ρ_M` is the dimension of the *fibre* `κ(𝔭) ⊗_R M` over the residue field `κ(𝔭)`,
spelled `Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)`, and deliberately not
`Module.rankAtStalk M`, which is `finrank_{R_𝔭} M_𝔭`. The two agree for flat modules
(`Ideal.finrank_fiber_eq_rankAtStalk`, stated under `[Module.Flat R M]`), hence in item (8) of
`Module.finite_projective_tfae`, which also asserts `Module.freeLocus R M = Set.univ`; they differ
in general, and the variant of this lemma with `Module.rankAtStalk M` in place of `ρ_M` is false.
For `R = ℤ` and `M = ℤ/2ℤ` every localization `M_𝔭` is torsion, so `Module.rankAtStalk M` is
identically `0` and in particular locally constant, while `ρ_M` is `1` at `(2)` and `0` at `(0)`;
`M` is finite over the reduced ring `ℤ` and is not projective.

`Ideal.Fiber` is `κ(𝔭) ⊗_R M`, with the residue field on the left, where the source writes
`M ⊗_R κ(𝔭)`; the two are `κ(𝔭)`-linearly isomorphic by `TensorProduct.comm`, so they have the
same dimension. That dimension takes values in `ℕ` where the source takes values in `ℤ`; local
constancy is a condition on the fibres of the function and so is unchanged by composing with the
injection `ℕ → ℤ`.

The left-hand side is `Module.Projective R M`, item (2), and not `Module.Flat R M`: over a reduced
ring a finite flat module need not be projective (Remark 00NY, with `R = C^∞(ℝ)`), and for such a
module `ρ_M` cannot be locally constant, so the left-to-right implication would fail.

Faithfulness. (1) Both hypotheses are used: `[Module.Finite R M]` by each direction (Nakayama for
one, finite presentation for the other) and `[IsReduced R]` by the right-to-left one, where it
cannot be dropped — over `R = k[x]/(x²)` the module `M = R/(x)` is finite with `ρ_M` constant
equal to `1` on the one-point space `Spec(R)`, and is not projective. (2) The scalars are the
source's: projectivity is over `R`, and the fibre `κ(𝔭) ⊗_R M` is formed over `R` with its
dimension taken over `κ(𝔭)`, not over `R_𝔭`. (3) The one function the source names is pinned: the
right-hand side is local constancy of the fibre dimension itself, on `PrimeSpectrum R` with its
Zariski topology, not of some function agreeing with it. (4) The instantiation is not degenerate:
`R = ℤ/6ℤ` is reduced and `M = ℤ/2ℤ`, a module over `R` through `ZMod.castHom`, satisfies both
sides with content — `ρ_M` is `1` at the prime over `2` and `0` at the prime over `3`, hence
locally constant without being constant, and `M` is the summand of `R` cut out by the idempotent
`3`.

## References

* [StacksProject 0FWG](https://stacks.math.columbia.edu/tag/0FWG)

## Tags

finite projective module, reduced ring, fibre dimension, locally constant, rank
-/

@[expose] public section



/-- **A finite module over a reduced ring is projective iff its fibre dimension is locally
constant.** For `R` a reduced commutative ring and `M` a finite `R`-module, `M` is projective
(equivalently, by `Module.finite_projective_tfae`, finite locally free) if and only if the
function `ρ_M : Spec(R) → ℕ`, `𝔭 ↦ dim_{κ(𝔭)} M ⊗_R κ(𝔭)`, is locally constant. This is item (9)
in the list of characterizations of finite projective modules. -/
@[stacks 0FWG,
  sga "6 III 5.6" "affine, E = M in deg 0",
  sga "6 I 6.0" "special case",
  sga "6 III 5.4.1" "special case"]
public theorem Module.projective_iff_isLocallyConstant_finrank_fiber (R : Type u) [CommRing R]
    [IsReduced R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Projective R M ↔
      IsLocallyConstant fun p : PrimeSpectrum R ↦
        Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) :=
    by apply Stacks.FiniteProjective.ConstantFibreRank.solution

end

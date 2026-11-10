module

public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries

/-!
# Characteristic series over the factors of an idempotent splitting

Let `Λ` be a commutative ring and `e` an idempotent of `Λ`, so that `Λ ≅ Λ ⧸ (1 - e) × Λ ⧸ (e)`.
The quotient map `Λ → Λ ⧸ (1 - e)` sends `e` to `1`, and has the `Λ`-linear section
`a ↦ a e`, so `Λ ⧸ (1 - e)` is a finite projective `Λ`-module and so is every finite projective
`Λ ⧸ (1 - e)`-module.

The characteristic series `ProjectiveDeterminant.charSeries` behaves as follows under the two
quotient maps: for a finite projective module `N` over `Λ' = Λ ⧸ (1 - e)`, the image in `Λ'⟦T⟧`
of `det_Λ(1 - φ T)` is `det_{Λ'}(1 - φ T)`, and its image in `(Λ ⧸ (e))⟦T⟧` is `1`. A power
series over `Λ` is determined by its two images, so an identity of characteristic series over a
finite ring reduces to its local factors.

## Main results

* `Ideal.Quotient.mk_span_one_sub_self`: `e` maps to `1` in `Λ ⧸ (1 - e)`.
* `IsIdempotentElem.projective_quotient`: `Λ ⧸ (1 - e)` is a projective `Λ`-module.
* `ProjectiveDeterminant.map_charSeries_restrictScalars`: for a surjection `Λ → Λ'` and a finite
  projective `Λ'`-module, the characteristic series over `Λ` maps to the one over `Λ'`.
* `ProjectiveDeterminant.map_charSeries_eq_one_of_smul_eq_zero`: if an element of `Λ` mapping to
  `1` kills the module, the characteristic series maps to `1`.
* `IsIdempotentElem.powerSeries_ext`: a power series over `Λ` is determined by its images over
  `Λ ⧸ (1 - e)` and `Λ ⧸ (e)`.
* `exists_isIdempotentElem_ne_zero_ne_one`: a nontrivial Artinian commutative ring which is not
  local has an idempotent other than `0` and `1`.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open PowerSeries

universe u u' v w

section Quotient

variable {Λ : Type u} [CommRing Λ]

/-- In `Λ ⧸ (1 - e)` the element `e` is `1`. -/
public theorem Ideal.Quotient.mk_span_one_sub_self (e : Λ) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
  have h : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

variable {e : Λ} (he : IsIdempotentElem e)
include he

/-- The `Λ`-linear section `a ↦ a e` of the quotient map `Λ → Λ ⧸ (1 - e)`. -/
public def IsIdempotentElem.quotientSection : (Λ ⧸ Ideal.span {1 - e}) →ₗ[Λ] Λ :=
  (Ideal.span {1 - e}).liftQ (LinearMap.mulRight Λ e) fun x hx => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    simp [mul_assoc, sub_mul, he.eq]

/-- The section `Λ ⧸ (1 - e) → Λ` sends the class of `a` to `a * e`. -/
public theorem IsIdempotentElem.quotientSection_mk (a : Λ) :
    he.quotientSection (Ideal.Quotient.mk _ a) = a * e :=
  rfl

/-- The section is a section. -/
public theorem IsIdempotentElem.mk_quotientSection (x : Λ ⧸ Ideal.span {1 - e}) :
    Ideal.Quotient.mk _ (he.quotientSection x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he.quotientSection_mk, map_mul, Ideal.Quotient.mk_span_one_sub_self, mul_one]

/-- **`Λ ⧸ (1 - e)` is a projective `Λ`-module**, a direct summand of `Λ`. -/
public theorem IsIdempotentElem.projective_quotient :
    Module.Projective Λ (Λ ⧸ Ideal.span {1 - e}) :=
  Module.Projective.of_split he.quotientSection (Ideal.span {1 - e}).mkQ
    (LinearMap.ext fun x => he.mk_quotientSection x)

end Quotient

/-! ### Base change to a quotient -/

section BaseChange

variable {Λ : Type u} [CommRing Λ] {Λ' : Type u} [CommRing Λ'] [Algebra Λ Λ']
  (N : Type v) [AddCommGroup N] [Module Λ' N] [Module Λ N] [IsScalarTower Λ Λ' N]

/-- For a surjective algebra map `Λ → Λ'` and a `Λ'`-module `N`, the map `n ↦ 1 ⊗ n` is
`Λ'`-linear. -/
public def oneTmulOfSurjective (hs : Function.Surjective (algebraMap Λ Λ')) :
    N →ₗ[Λ'] Λ' ⊗[Λ] N where
  toFun n := 1 ⊗ₜ n
  map_add' _ _ := TensorProduct.tmul_add _ _ _
  map_smul' t n := by
    obtain ⟨a, rfl⟩ := hs t
    rw [RingHom.id_apply, algebraMap_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul, mul_one]

/-- For a surjective algebra map `Λ → Λ'` and a `Λ'`-module `N`, base change does nothing:
`Λ' ⊗_Λ N ≅ N`, `t ⊗ n ↦ t • n`. -/
public def baseChangeEquivOfSurjective (hs : Function.Surjective (algebraMap Λ Λ')) :
    Λ' ⊗[Λ] N ≃ₗ[Λ'] N :=
  LinearEquiv.ofLinearMap ((LinearMap.id : N →ₗ[Λ] N).liftBaseChange Λ')
    (oneTmulOfSurjective N hs)
    (LinearMap.ext fun n => by
      change (LinearMap.id.liftBaseChange Λ') (1 ⊗ₜ[Λ] n) = n
      simp)
    (LinearMap.ext fun x => by
      induction x using TensorProduct.inductionOn with
      | tmul t n =>
        obtain ⟨a, rfl⟩ := hs t
        change 1 ⊗ₜ[Λ] (LinearMap.id.liftBaseChange Λ' (algebraMap Λ Λ' a ⊗ₜ[Λ] n)) = _
        rw [LinearMap.liftBaseChange_tmul, LinearMap.id_apply, algebraMap_smul,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])

/-- Under `Λ' ⊗_Λ N ≅ N`, the base change of a `Λ'`-linear endomorphism is the endomorphism. -/
public theorem baseChangeEquivOfSurjective_symm_conj (hs : Function.Surjective (algebraMap Λ Λ'))
    (φ : N →ₗ[Λ'] N) :
    (baseChangeEquivOfSurjective N hs).symm.conj φ = (φ.restrictScalars Λ).baseChange Λ' := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul t n =>
    change (1 : Λ') ⊗ₜ[Λ] φ (t • n) = t ⊗ₜ[Λ] φ n
    obtain ⟨a, rfl⟩ := hs t
    rw [map_smul, algebraMap_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The equivalence `Λ' ⊗_Λ N ≅ N` sends `t ⊗ n` to `t • n`. -/
@[simp]
public theorem baseChangeEquivOfSurjective_tmul (hs : Function.Surjective (algebraMap Λ Λ'))
    (t : Λ') (n : N) : baseChangeEquivOfSurjective N hs (t ⊗ₜ n) = t • n :=
  rfl

end BaseChange

/-- If an element of `Λ` mapping to `1` in `Λ'` kills `N`, the base change `Λ' ⊗_Λ N` is zero. -/
public theorem TensorProduct.subsingleton_of_smul_eq_zero {Λ : Type u} [CommRing Λ]
    {Λ' : Type u'} [CommRing Λ'] [Algebra Λ Λ'] {N : Type v} [AddCommGroup N] [Module Λ N] {a : Λ}
    (ha : algebraMap Λ Λ' a = 1) (hN : ∀ n : N, a • n = 0) : Subsingleton (Λ' ⊗[Λ] N) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ z : Λ' ⊗[Λ] N, z = 0 := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul t n =>
      have hat : a • t = t := by rw [_root_.Algebra.smul_def, ha, one_mul]
      rw [← hat, TensorProduct.smul_tmul, hN, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [h0 x, h0 y]

/-! ### Characteristic series under a quotient map -/

namespace ProjectiveDeterminant

variable {Λ : Type u} [CommRing Λ] {Λ' : Type u} [CommRing Λ'] [Algebra Λ Λ']
  {N : Type v} [AddCommGroup N] [Module Λ N] [Module.Finite Λ N] [Module.Projective Λ N]

/-- **The characteristic series over `Λ` of an endomorphism of a `Λ'`-module, for a surjection
`Λ → Λ'`, maps to its characteristic series over `Λ'`.** Base change along `Λ → Λ'` does
nothing to a `Λ'`-module. -/
public theorem map_charSeries_restrictScalars [Module Λ' N] [IsScalarTower Λ Λ' N]
    [Module.Finite Λ' N] [Module.Projective Λ' N]
    (hs : Function.Surjective (algebraMap Λ Λ')) (φ : N →ₗ[Λ'] N) (d : ℕ) :
    PowerSeries.map (algebraMap Λ Λ') (charSeries (φ.restrictScalars Λ) d) = charSeries φ d := by
  rw [← charSeries_baseChange Λ' (φ.restrictScalars Λ) d,
    ← baseChangeEquivOfSurjective_symm_conj N hs, charSeries_conj]

/-- **If an element of `Λ` mapping to `1` in `Λ'` kills `N`, the characteristic series of any
endomorphism of `N` maps to `1` over `Λ'`**: the base change `Λ' ⊗_Λ N` is zero. -/
public theorem map_charSeries_eq_one_of_smul_eq_zero {a : Λ} (ha : algebraMap Λ Λ' a = 1)
    (hN : ∀ n : N, a • n = 0) (φ : N →ₗ[Λ] N) (d : ℕ) :
    PowerSeries.map (algebraMap Λ Λ') (charSeries φ d) = 1 := by
  have := TensorProduct.subsingleton_of_smul_eq_zero (Λ' := Λ') ha hN
  rw [← charSeries_baseChange Λ' φ d]
  have : φ.baseChange Λ' = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
  rw [this, charSeries_zero]

end ProjectiveDeterminant

/-! ### Power series over the two factors -/

section Ext

variable {Λ : Type u} [CommRing Λ] {e : Λ}

/-- **A power series over `Λ` is determined by its images over `Λ ⧸ (1 - e)` and `Λ ⧸ (e)`**, for
an idempotent `e`: the two ideals meet in `0`. -/
public theorem IsIdempotentElem.powerSeries_ext (he : IsIdempotentElem e) {x y : PowerSeries Λ}
    (h₁ : PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) x =
      PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) y)
    (h₂ : PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {1 - (1 - e)})) x =
      PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {1 - (1 - e)})) y) : x = y := by
  ext n
  have key : ∀ c : Λ, PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {c})) x =
      PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {c})) y →
      ∃ a, a * c = PowerSeries.coeff n x - PowerSeries.coeff n y := fun c h => by
    simpa only [PowerSeries.coeff_map, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq,
      Ideal.mem_span_singleton'] using congrArg (PowerSeries.coeff n) h
  obtain ⟨a, ha⟩ := key _ h₁
  obtain ⟨b, hb⟩ := key _ h₂
  linear_combination (-e) * ha - (1 - e) * hb - (a + b) * he.eq

end Ext

/-! ### Idempotents of non-local Artinian rings -/

/-- **A nontrivial Artinian commutative ring which is not local has an idempotent other than `0`
and `1`**: its prime spectrum is discrete, so a single maximal ideal is a clopen subset. -/
public theorem exists_isIdempotentElem_ne_zero_ne_one (R : Type u) [CommRing R]
    [IsArtinianRing R] [Nontrivial R] (hR : ¬ IsLocalRing R) :
    ∃ e : R, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal R
  have : ∃ m₂ : Ideal R, m₂.IsMaximal ∧ m₂ ≠ m₁ := by
    by_contra! h
    exact hR (IsLocalRing.of_unique_max_ideal ⟨m₁, hm₁, fun m hm => h m hm⟩)
  obtain ⟨m₂, hm₂, hne⟩ := this
  let p₁ : PrimeSpectrum R := ⟨m₁, hm₁.isPrime⟩
  let p₂ : PrimeSpectrum R := ⟨m₂, hm₂.isPrime⟩
  obtain ⟨e, he, hs⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (isClopen_discrete ({p₁} : Set (PrimeSpectrum R)))
  refine ⟨e, he, ?_, ?_⟩
  · rintro rfl
    have : p₁ ∈ (PrimeSpectrum.basicOpen (0 : R) : Set (PrimeSpectrum R)) := by
      rw [← hs]; rfl
    simp at this
  · rintro rfl
    have : p₂ ∈ (PrimeSpectrum.basicOpen (1 : R) : Set (PrimeSpectrum R)) := by simp
    rw [← hs, Set.mem_singleton_iff] at this
    exact hne (congrArg PrimeSpectrum.asIdeal this)

end

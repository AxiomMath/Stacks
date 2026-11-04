module

public import StacksFrontier.RingTheory.DiscreteValuationRing.PolynomialAtXInfinity

/-!
# The rational function field `k(X)` inside `k'(x)` with `X = 1/x`

Let `k ⊆ k'` be fields and `K'` a fraction field of `k'[x]`. The ring map `k[X] → K'`, `X ↦ x⁻¹`,
is injective, so it extends to `K = Frac k[X] → K'`; then `K' = K(k')`. When `k'` is finite and `A`
is a discrete valuation ring of `K'` not containing `k'[x]` (a place at `∞`), the local ring
`k[X]_(X)` maps into `A` and `X` maps into the maximal ideal of `A`. These are the data
hypotheses of
`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_sub_eq_of_constantExtension`
for the place at `∞` of `𝔸¹_{k'}`, used in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Polynomial.liftInvX`: the map `Frac k[X] → K'`, `X ↦ x⁻¹`.

## Main results

* `Polynomial.liftInvX_algebraMap_mem_range`: `k[X]_(X)` lands in `A`.
* `Polynomial.liftInvX_algebraMap_X_mem_maximalIdeal`: `X` lands in the maximal ideal of `A`.
* `Polynomial.adjoin_range_eq_top_of_liftInvX`: `K' = K(k')`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Polynomial

section Map

variable (k : Type*) [Field k] (k' : Type*) [Field k'] [Algebra k k'] (K' : Type*) [Field K']
  [Algebra k'[X] K'] [IsFractionRing k'[X] K']

/-- The ring map `k[X] → K'`, `X ↦ x⁻¹`, for `x` the image of `X` in a fraction field `K'` of
`k'[x]`. -/
def evalInvX : k[X] →+* K' :=
  eval₂RingHom ((algebraMap k'[X] K').comp (C.comp (algebraMap k k'))) (algebraMap k'[X] K' X)⁻¹

/-- The image of `X` in a fraction field `K'` of `k'[X]` is nonzero. -/
theorem algebraMap_X_ne_zero : algebraMap k'[X] K' X ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective k'[X] K')).2 X_ne_zero

omit [IsFractionRing k'[X] K'] in
/-- `evalInvX` sends the constant `C a` to the image of `C a` in `K'`. -/
theorem evalInvX_C (a : k) : evalInvX k k' K' (C a) = algebraMap k'[X] K' (C (algebraMap k k' a)) :=
  eval₂_C _ _

omit [IsFractionRing k'[X] K'] in
/-- `evalInvX` sends `X` to the inverse of the image of `X` in `K'`. -/
theorem evalInvX_X : evalInvX k k' K' X = (algebraMap k'[X] K' X)⁻¹ :=
  eval₂_X _ _

/-- `X ↦ x⁻¹` is injective: `f(x⁻¹) xᵈ` is the reverse of `f` evaluated at `x`. -/
theorem evalInvX_injective : Function.Injective (evalInvX k k' K') := by
  have hx := algebraMap_X_ne_zero k' K'
  rw [injective_iff_map_eq_zero]
  intro f hf
  let : Invertible (algebraMap k'[X] K' X)⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := eval₂_reverse_mul_pow ((algebraMap k'[X] K').comp (C.comp (algebraMap k k')))
    (algebraMap k'[X] K' X)⁻¹ f
  rw [invOf_eq_inv, inv_inv] at h
  have hf' : eval₂ ((algebraMap k'[X] K').comp (C.comp (algebraMap k k')))
      (algebraMap k'[X] K' X)⁻¹ f = 0 := hf
  rw [hf'] at h
  have h0 := (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ (inv_ne_zero hx))
  rw [← hom_eval₂] at h0
  have h1 : (reverse f).map (algebraMap k k') = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective k'[X] K')).1 h0
  rw [Polynomial.map_eq_zero_iff (algebraMap k k').injective, reverse_eq_zero] at h1
  exact h1

/-- The map `Frac k[X] → K'`, `X ↦ x⁻¹`. -/
def liftInvX : FractionRing k[X] →+* K' :=
  IsFractionRing.lift (evalInvX_injective k k' K')

/-- `liftInvX` restricts to `evalInvX` on `k[X]`. -/
theorem liftInvX_algebraMap (f : k[X]) :
    liftInvX k k' K' (algebraMap k[X] (FractionRing k[X]) f) = evalInvX k k' K' f :=
  IsFractionRing.lift_algebraMap _ _

end Map

section Infinity

variable (k : Type*) [Field k] {k' : Type*} [Field k'] [Finite k'] [Algebra k k'] {K' : Type*}
  [Field K'] [Algebra k'[X] K'] [IsFractionRing k'[X] K']
  {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K']
  [IsFractionRing A K']

/-- A ring map from a polynomial ring lands in a subring if it does on `C a` and on `X`. -/
private theorem map_mem_subring_of_C_X {R T : Type*} [Semiring R] [Ring T] (φ : R[X] →+* T)
    (S : Subring T) (hC : ∀ a, φ (C a) ∈ S) (hX : φ X ∈ S) (p : R[X]) : φ p ∈ S := by
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | monomial n a h => rw [pow_succ, ← mul_assoc, map_mul]; exact S.mul_mem h hX

omit [IsFractionRing k'[X] K'] in
variable {k} in
/-- If `A` does not contain the image of `k'[X]`, then `evalInvX` maps `k[X]` into `A`. -/
theorem evalInvX_mem_range
    (hA : ∃ g : k'[X], algebraMap k'[X] K' g ∉ Set.range (algebraMap A K')) (r : k[X]) :
    evalInvX k k' K' r ∈ Set.range (algebraMap A K') := by
  obtain ⟨b, hb, -⟩ := exists_eq_inv_X_mem_maximalIdeal hA
  let S : Subring K' := (algebraMap A K').range
  exact map_mem_subring_of_C_X (evalInvX k k' K') S
    (fun a => by rw [evalInvX_C]; exact algebraMap_C_mem_range A _)
    ⟨b, by rw [hb, evalInvX_X]⟩ r

omit [IsFractionRing k'[X] K'] in
variable {k} in
/-- The image of a polynomial with nonzero constant term is a unit of `A`. -/
theorem isUnit_of_algebraMap_eq_evalInvX
    (hA : ∃ g : k'[X], algebraMap k'[X] K' g ∉ Set.range (algebraMap A K')) {s : k[X]}
    (hs : s.coeff 0 ≠ 0) {u : A} (hu : algebraMap A K' u = evalInvX k k' K' s) : IsUnit u := by
  obtain ⟨b, hb, hbm⟩ := exists_eq_inv_X_mem_maximalIdeal hA
  obtain ⟨w, hw⟩ := evalInvX_mem_range hA (divX s)
  obtain ⟨c₀, hc₀⟩ := algebraMap_C_mem_range A (K' := K') (algebraMap k k' (s.coeff 0))
  obtain ⟨c₁, hc₁⟩ := algebraMap_C_mem_range A (K' := K') (algebraMap k k' (s.coeff 0))⁻¹
  have hinj := IsFractionRing.injective A K'
  have hc : IsUnit c₀ := by
    refine isUnit_iff_exists_inv.2 ⟨c₁, hinj ?_⟩
    rw [map_mul, map_one, hc₀, hc₁, ← map_mul, ← map_mul, mul_inv_cancel₀, C_1, map_one]
    exact (map_ne_zero_iff _ (algebraMap k k').injective).2 hs
  have hsum : u = b * w + c₀ := by
    apply hinj
    rw [hu, map_add, map_mul, hb, hw, hc₀, ← evalInvX_X k k' K', ← evalInvX_C k k' K', ← map_mul,
      ← map_add,
      X_mul_divX_add]
  by_contra hnu
  have hum : u ∈ IsLocalRing.maximalIdeal A := hnu
  have : c₀ ∈ IsLocalRing.maximalIdeal A := by
    have :=
      (IsLocalRing.maximalIdeal A).sub_mem hum ((IsLocalRing.maximalIdeal A).mul_mem_right w hbm)
    rwa [hsum, add_sub_cancel_left] at this
  exact (IsLocalRing.mem_maximalIdeal _).1 this hc

/-- **`k[X]_(X)` maps into the discrete valuation ring `A` at `∞` of `k'(x)`.** -/
theorem liftInvX_algebraMap_mem_range
    (hA : ∃ g : k'[X], algebraMap k'[X] K' g ∉ Set.range (algebraMap A K'))
    (a : LocalizationAtX k) :
    liftInvX k k' K' (algebraMap (LocalizationAtX k) (FractionRing k[X]) a) ∈
      Set.range (algebraMap A K') := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(X : k[X])}).primeCompl a
  have hs : (s : k[X]).coeff 0 ≠ 0 := fun h =>
    s.2 (Ideal.mem_span_singleton.2 (X_dvd_iff.2 h))
  obtain ⟨u, hu⟩ := evalInvX_mem_range hA (s : k[X])
  obtain ⟨v, hv⟩ := evalInvX_mem_range hA r
  have hU := isUnit_of_algebraMap_eq_evalInvX hA hs hu
  have hspec := congrArg (fun z => liftInvX k k' K' (algebraMap (LocalizationAtX k)
    (FractionRing k[X]) z)) (IsLocalization.mk'_spec (LocalizationAtX k) r s)
  simp only [map_mul, ← IsScalarTower.algebraMap_apply, liftInvX_algebraMap] at hspec
  refine ⟨v * ↑hU.unit⁻¹, ?_⟩
  have hne : algebraMap A K' u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K')).2 hU.ne_zero
  rw [map_mul, hv, ← hspec, ← hu, mul_assoc, ← map_mul, Units.mul_inv_of_eq hU.unit_spec,
    map_one, mul_one]

/-- **`X` maps into the maximal ideal of the discrete valuation ring `A` at `∞`.** -/
theorem liftInvX_algebraMap_X_mem_maximalIdeal
    (hA : ∃ g : k'[X], algebraMap k'[X] K' g ∉ Set.range (algebraMap A K')) (b : A)
    (hb : algebraMap A K' b = liftInvX k k' K' (algebraMap (LocalizationAtX k)
      (FractionRing k[X]) (algebraMap k[X] (LocalizationAtX k) X))) :
    b ∈ IsLocalRing.maximalIdeal A := by
  obtain ⟨b', hb', hbm⟩ := exists_eq_inv_X_mem_maximalIdeal hA
  rw [← IsScalarTower.algebraMap_apply, liftInvX_algebraMap, evalInvX_X, ← hb'] at hb
  rwa [IsFractionRing.injective A K' hb]

end Infinity

section Adjoin

variable (k : Type*) [Field k] {k' : Type*} [Field k'] [Algebra k k'] {K' : Type*}
  [Field K'] [Algebra k'[X] K'] [IsFractionRing k'[X] K']

/-- **`K' = K(k')` for `K = k(1/x)`.** -/
theorem adjoin_range_eq_top_of_liftInvX [Algebra (FractionRing k[X]) K'] [Algebra k' K']
    (hK : algebraMap (FractionRing k[X]) K' = liftInvX k k' K')
    (hk' : algebraMap k' K' = (algebraMap k'[X] K').comp C) :
    IntermediateField.adjoin (FractionRing k[X]) (Set.range (algebraMap k' K')) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  set F := IntermediateField.adjoin (FractionRing k[X]) (Set.range (algebraMap k' K'))
  have hpol : ∀ g : k'[X], algebraMap k'[X] K' g ∈ F := fun g => by
    refine map_mem_subring_of_C_X (algebraMap k'[X] K') F.toSubring
      (fun a => IntermediateField.subset_adjoin _ _ ⟨a, by rw [hk']; rfl⟩) ?_ g
    have hx : (algebraMap k'[X] K' X)⁻¹ ∈ F := by
      rw [← evalInvX_X k, ← liftInvX_algebraMap, ← hK]
      exact F.algebraMap_mem _
    simpa using F.inv_mem hx
  obtain ⟨g, h, -, rfl⟩ := IsFractionRing.div_surjective (A := k'[X]) z
  exact F.div_mem (hpol g) (hpol h)

end Adjoin

end Polynomial

end

module

public import Mathlib

/-!
# The local ring of the affine line at infinity

Let `k` be a field and `K = Frac k[X]`. The rational functions without pole at infinity form a
discrete valuation ring `Polynomial.ringAtInfinity k ⊆ K`. We realize it as the image of the
localization `k[X]_(X)` under the `k`-algebra map `X ↦ X⁻¹`, so that `X⁻¹` is a uniformizer and
evaluation at `0` of the localization becomes the residue map `ringAtInfinity k → k`.

## Main definitions

* `Polynomial.invMap k : k[X] →ₐ[k] Frac k[X]`, the substitution `X ↦ X⁻¹`.
* `Polynomial.ringAtInfinity k`, the subalgebra of `Frac k[X]` of functions regular at infinity.
* `Polynomial.residueAtInfinity k : ringAtInfinity k →ₐ[k] k`, the value at infinity.

## Main results

* `Polynomial.ringAtInfinity.isDiscreteValuationRing` and
  `Polynomial.ringAtInfinity.isFractionRing`.
* `Polynomial.ringAtInfinity.sub_residue_mem_maximalIdeal`: the residue field is `k`.
* `Polynomial.ringAtInfinity.eq_C_of_algebraMap_mem`: a polynomial regular at infinity is
  constant.
* `Polynomial.ringAtInfinity.exists_derivation_eq`: a derivation of an extension field of
  `Frac k[X]` with `δ (X⁻¹) = -X⁻¹` (that is, `X d/dX`) preserves the ring at infinity.

## Implementation notes

Typeclass search for algebras over the coercion of the subalgebra `ringAtInfinity k` to a type
(for instance integral closures in extensions of `Frac k[X]`) is very slow, so the ring at
infinity is also introduced as a type `Polynomial.AtInfinity k` of its own.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable (k : Type*) [Field k]

/-- The prime ideal `(X)` of `k[X]`. -/
noncomputable abbrev spanX : Ideal k[X] := Ideal.span {X}

/-- The ideal `(X)` of `k[X]` is prime. -/
instance spanX.isPrime : (spanX k).IsPrime :=
  (Ideal.span_singleton_prime X_ne_zero).mpr prime_X

/-- The element `X` of `Frac k[X]`. -/
noncomputable abbrev fracX : FractionRing k[X] := algebraMap k[X] (FractionRing k[X]) X

/-- The element `X` of `Frac k[X]` is nonzero. -/
theorem fracX_ne_zero : fracX k ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective k[X] (FractionRing k[X]))]
  exact X_ne_zero

/-- The substitution `X ↦ X⁻¹`, as a `k`-algebra map `k[X] → Frac k[X]`. -/
noncomputable def invMap : k[X] →ₐ[k] FractionRing k[X] := aeval (fracX k)⁻¹

variable {k}

/-- Reflecting a polynomial of degree at most `N` gives a polynomial of degree at most `N`. -/
private theorem natDegree_reflect_le_of_le {N : ℕ} {p : k[X]} (hp : p.natDegree ≤ N) :
    (reflect N p).natDegree ≤ N :=
  natDegree_reflect_le.trans (max_le le_rfl hp)

/-- The substitution `X ↦ X⁻¹` sends `X` to `X⁻¹`. -/
theorem invMap_X : invMap k X = (fracX k)⁻¹ := by simp [invMap]

/-- `X ^ N * p(X⁻¹)` is the reversed polynomial `reflect N p`, for `N ≥ deg p`. -/
theorem invMap_mul_pow {N : ℕ} {p : k[X]} (hp : p.natDegree ≤ N) :
    invMap k p * fracX k ^ N = algebraMap k[X] (FractionRing k[X]) (reflect N p) := by
  let : Invertible (fracX k) := invertibleOfNonzero (fracX_ne_zero k)
  have h := eval₂_reflect_mul_pow (algebraMap k (FractionRing k[X])) (fracX k) N (reflect N p)
    (natDegree_reflect_le_of_le hp)
  rw [reflect_reflect, invOf_eq_inv] at h
  rw [invMap, aeval_def, h]
  exact eval₂_algebraMap_X (reflect N p) (IsScalarTower.toAlgHom k k[X] (FractionRing k[X]))

/-- The substitution `X ↦ X⁻¹` is injective. -/
theorem invMap_injective : Function.Injective (invMap k) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h := invMap_mul_pow (N := p.natDegree) le_rfl (p := p)
  rwa [hp, zero_mul, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective k[X] _),
    reflect_eq_zero_iff] at h

/-- For a nonzero polynomial `p`, the rational function `p(X⁻¹)` is nonzero. -/
theorem invMap_ne_zero {p : k[X]} (hp : p ≠ 0) : invMap k p ≠ 0 :=
  (map_ne_zero_iff _ invMap_injective).mpr hp

variable (k)

/-- The localization `k[X]_(X)`. -/
abbrev locSpanX : Type _ := Localization.AtPrime (spanX k)

/-- A polynomial outside the ideal `(X)` is nonzero. -/
theorem ne_zero_of_mem_primeCompl (q : (spanX k).primeCompl) : (q : k[X]) ≠ 0 :=
  fun h ↦ q.2 (by simp [h])

/-- For a polynomial `q` outside the ideal `(X)`, `q(X⁻¹)` is a unit of `Frac k[X]`. -/
theorem isUnit_invMap_primeCompl (q : (spanX k).primeCompl) : IsUnit (invMap k q) :=
  (invMap_ne_zero (ne_zero_of_mem_primeCompl k q)).isUnit

/-- The map `k[X]_(X) → Frac k[X]` induced by `X ↦ X⁻¹`. -/
noncomputable def invLoc : locSpanX k →ₐ[k] FractionRing k[X] :=
  { IsLocalization.lift (M := (spanX k).primeCompl) (S := locSpanX k)
      (g := (invMap k).toRingHom) (isUnit_invMap_primeCompl k) with
    commutes' := fun c ↦ by
      change IsLocalization.lift _ (algebraMap k (locSpanX k) c) = _
      rw [IsScalarTower.algebraMap_apply k k[X] (locSpanX k), IsLocalization.lift_eq]
      simp [invMap] }

/-- On the image of a polynomial `p` in `k[X]_(X)`, `invLoc k` is `p ↦ p(X⁻¹)`. -/
theorem invLoc_algebraMap (p : k[X]) : invLoc k (algebraMap k[X] (locSpanX k) p) = invMap k p :=
  IsLocalization.lift_eq _ p

/-- The map `invLoc k` sends the fraction `p / q` of `k[X]_(X)` to `p(X⁻¹) / q(X⁻¹)`. -/
theorem invLoc_mk' (p : k[X]) (q : (spanX k).primeCompl) :
    invLoc k (IsLocalization.mk' (locSpanX k) p q) = invMap k p / invMap k q := by
  rw [eq_div_iff (invMap_ne_zero (ne_zero_of_mem_primeCompl k q)), ← invLoc_algebraMap,
    ← invLoc_algebraMap, ← map_mul, IsLocalization.mk'_spec]

/-- The map `invLoc k : k[X]_(X) → Frac k[X]` is injective. -/
theorem invLoc_injective : Function.Injective (invLoc k) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (spanX k).primeCompl a
  simp only [invLoc_mk', div_eq_zero_iff] at ha
  rcases ha with ha | ha
  · rw [map_eq_zero_iff _ invMap_injective] at ha
    simp [ha]
  · exact absurd ((map_eq_zero_iff _ invMap_injective).mp ha) (ne_zero_of_mem_primeCompl k q)

/-- **The ring of rational functions regular at infinity**, as the subalgebra of `Frac k[X]`
image of `k[X]_(X)` under `X ↦ X⁻¹`. -/
noncomputable def ringAtInfinity : Subalgebra k (FractionRing k[X]) := (invLoc k).range

/-- `k[X]_(X)` is isomorphic to the ring at infinity. -/
noncomputable def locSpanXEquiv : locSpanX k ≃ₐ[k] ringAtInfinity k :=
  AlgEquiv.ofInjective (invLoc k) (invLoc_injective k)

namespace ringAtInfinity

variable {k}

/-- For every polynomial `p`, the rational function `p(X⁻¹)` is regular at infinity. -/
theorem invMap_mem (p : k[X]) : invMap k p ∈ ringAtInfinity k :=
  ⟨algebraMap k[X] (locSpanX k) p, invLoc_algebraMap k p⟩

/-- The rational function `X⁻¹` is regular at infinity. -/
theorem fracX_inv_mem : (fracX k)⁻¹ ∈ ringAtInfinity k := by
  rw [← invMap_X]
  exact invMap_mem X

/-- Every element of the ring at infinity is `p(X⁻¹) / q(X⁻¹)` for polynomials `p`, `q` with
`q(0) ≠ 0`. -/
theorem exists_eq_div (a : ringAtInfinity k) :
    ∃ (p q : k[X]), q.coeff 0 ≠ 0 ∧ (a : FractionRing k[X]) = invMap k p / invMap k q := by
  obtain ⟨b, hb⟩ := a.2
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (spanX k).primeCompl b
  exact ⟨p, q, fun h ↦ q.2 (Ideal.mem_span_singleton.mpr (X_dvd_iff.mpr h)),
    hb.symm.trans (invLoc_mk' k p q)⟩

variable (k)

/-- The ring at infinity is a discrete valuation ring. -/
instance isDiscreteValuationRing : IsDiscreteValuationRing (ringAtInfinity k) := by
  have hX : spanX k ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact X_ne_zero
  have : IsDiscreteValuationRing (locSpanX k) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] hX (locSpanX k)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (locSpanXEquiv k)

/-- The ring at infinity acts faithfully on `Frac k[X]`. -/
instance faithfulSMul : FaithfulSMul (ringAtInfinity k) (FractionRing k[X]) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective

/-- `Frac k[X]` is the fraction field of the ring at infinity. -/
instance isFractionRing : IsFractionRing (ringAtInfinity k) (FractionRing k[X]) := by
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := k[X]) z
  set N := max f.natDegree g.natDegree
  refine ⟨⟨_, invMap_mem (reflect N f)⟩, ⟨_, invMap_mem (reflect N g)⟩, ?_⟩
  have hf : (reflect N f).natDegree ≤ N := natDegree_reflect_le.trans (max_le le_rfl
    (le_max_left _ _))
  have hg' : (reflect N g).natDegree ≤ N := natDegree_reflect_le.trans (max_le le_rfl
    (le_max_right _ _))
  have e1 := invMap_mul_pow hf
  have e2 := invMap_mul_pow hg'
  rw [reflect_reflect] at e1 e2
  change _ = invMap k (reflect N f) / invMap k (reflect N g)
  rw [← e1, ← e2, mul_div_mul_right _ _ (pow_ne_zero _ (fracX_ne_zero k))]

/-- Evaluation at `0` on `k[X]_(X)`. -/
noncomputable def residueLoc : locSpanX k →+* k :=
  IsLocalization.lift (M := (spanX k).primeCompl) (S := locSpanX k)
    (g := (Polynomial.evalRingHom 0 : k[X] →+* k)) fun q ↦ Ne.isUnit fun h ↦
      q.2 (Ideal.mem_span_singleton.mpr (X_dvd_iff.mpr (by simpa [coeff_zero_eq_eval_zero]
        using h)))

/-- On the image of a polynomial `p` in `k[X]_(X)`, `residueLoc k` is `p ↦ p(0)`. -/
theorem residueLoc_algebraMap (p : k[X]) :
    residueLoc k (algebraMap k[X] (locSpanX k) p) = p.eval 0 :=
  IsLocalization.lift_eq _ p

/-- The value at infinity, as a `k`-algebra map `ringAtInfinity k → k`. -/
noncomputable def residue : ringAtInfinity k →ₐ[k] k :=
  ({ residueLoc k with
    commutes' := fun c ↦ by
      change residueLoc k (algebraMap k (locSpanX k) c) = _
      rw [IsScalarTower.algebraMap_apply k k[X] (locSpanX k), residueLoc_algebraMap]
      simp } : locSpanX k →ₐ[k] k).comp (locSpanXEquiv k).symm.toAlgHom

variable {k}

/-- The value of `X⁻¹` at infinity is `0`. -/
theorem residue_fracX_inv : residue k ⟨_, fracX_inv_mem⟩ = 0 := by
  have : (⟨_, fracX_inv_mem⟩ : ringAtInfinity k) =
      locSpanXEquiv k (algebraMap k[X] (locSpanX k) X) := by
    ext
    change _ = invLoc k _
    rw [invLoc_algebraMap, invMap_X]
  rw [this]
  change residueLoc k ((locSpanXEquiv k).symm (locSpanXEquiv k _)) = 0
  rw [AlgEquiv.symm_apply_apply, residueLoc_algebraMap]
  simp

/-- An element of the ring at infinity vanishing at infinity lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_residue_eq_zero {a : ringAtInfinity k} (ha : residue k a = 0) :
    a ∈ IsLocalRing.maximalIdeal (ringAtInfinity k) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  simpa [ha] using hu.map (residue k)

/-- **The residue field at infinity is `k`.** Every element `a` of the ring at infinity is
congruent to its value at infinity modulo the maximal ideal. -/
theorem sub_residue_mem_maximalIdeal (a : ringAtInfinity k) :
    a - algebraMap k (ringAtInfinity k) (residue k a) ∈
      IsLocalRing.maximalIdeal (ringAtInfinity k) :=
  mem_maximalIdeal_of_residue_eq_zero (by simp)

/-- The element `X⁻¹` lies in the maximal ideal of the ring at infinity. -/
theorem fracX_inv_mem_maximalIdeal :
    (⟨_, fracX_inv_mem⟩ : ringAtInfinity k) ∈ IsLocalRing.maximalIdeal (ringAtInfinity k) :=
  mem_maximalIdeal_of_residue_eq_zero residue_fracX_inv

/-- **A polynomial regular at infinity is constant.** -/
theorem eq_C_of_algebraMap_mem {f : k[X]}
    (hf : algebraMap k[X] (FractionRing k[X]) f ∈ ringAtInfinity k) : ∃ c : k, f = C c := by
  obtain ⟨p, q, hq, hpq⟩ := exists_eq_div ⟨_, hf⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  set N := max p.natDegree q.natDegree
  have e1 := invMap_mul_pow (le_max_left p.natDegree q.natDegree)
  have e2 := invMap_mul_pow (le_max_right p.natDegree q.natDegree)
  have hq' : invMap k q ≠ 0 := invMap_ne_zero hq0
  change algebraMap k[X] _ f = _ at hpq
  have key : algebraMap k[X] (FractionRing k[X]) (f * reflect N q) =
      algebraMap k[X] (FractionRing k[X]) (reflect N p) := by
    rw [map_mul, ← e1, ← e2, hpq]
    field_simp
  have hdegq : (reflect N q).natDegree = N :=
    le_antisymm (natDegree_reflect_le_of_le (le_max_right _ _))
      (le_natDegree_of_ne_zero (by rwa [coeff_reflect, revAt_le le_rfl, Nat.sub_self]))
  have hrq0 : reflect N q ≠ 0 := by rwa [Ne, reflect_eq_zero_iff]
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by simp⟩
  have hdeg := congrArg natDegree (IsFractionRing.injective k[X] (FractionRing k[X]) key)
  rw [natDegree_mul hf0 hrq0, hdegq] at hdeg
  have : f.natDegree = 0 := by
    have := natDegree_reflect_le_of_le (N := N) (p := p) (le_max_left _ _)
    omega
  exact ⟨_, eq_C_of_natDegree_eq_zero this⟩

/-- **The derivation `X d/dX` preserves the ring at infinity.** Let `L` be a field extension
of `Frac k[X]` and `δ` a `k`-derivation of `L` with `δ (X⁻¹) = -X⁻¹`. Then `δ` maps the ring at
infinity into itself. -/
theorem exists_derivation_eq {L : Type*} [Field L] [Algebra (FractionRing k[X]) L] [Algebra k L]
    [IsScalarTower k (FractionRing k[X]) L] (δ : Derivation k L L)
    (hδ : δ (algebraMap _ L (fracX k)⁻¹) = -algebraMap _ L (fracX k)⁻¹)
    (a : ringAtInfinity k) :
    ∃ b : ringAtInfinity k, δ (algebraMap _ L (a : FractionRing k[X])) =
      algebraMap _ L (b : FractionRing k[X]) := by
  obtain ⟨p, q, hq, hpq⟩ := exists_eq_div a
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  set s : L := algebraMap _ L (fracX k)⁻¹
  have hinv (r : k[X]) : algebraMap _ L (invMap k r) = aeval s r := by
    rw [invMap, aeval_algebraMap_apply]
  have hδinv (r : k[X]) : δ (aeval s r) = -(s * aeval s (derivative r)) := by
    rw [Derivation.map_aeval, hδ, smul_eq_mul]
    ring
  have hqL : aeval s q ≠ 0 := by
    rw [← hinv]
    exact (map_ne_zero_iff _ (algebraMap (FractionRing k[X]) L).injective).mpr
      (invMap_ne_zero hq0)
  have hqmem : q ∈ (spanX k).primeCompl := fun h ↦
    hq (X_dvd_iff.mp (Ideal.mem_span_singleton.mp h))
  refine ⟨⟨invLoc k (IsLocalization.mk' (locSpanX k) (-(X * (derivative p * q - p * derivative q)))
    (⟨q, hqmem⟩ ^ 2)), ⟨_, rfl⟩⟩, ?_⟩
  change _ = algebraMap _ L (invLoc k _)
  rw [invLoc_mk', hpq, map_div₀ (algebraMap (FractionRing k[X]) L),
    map_div₀ (algebraMap (FractionRing k[X]) L), hinv, hinv, hinv, hinv, Derivation.leibniz_div,
    hδinv, hδinv, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  simp only [SubmonoidClass.coe_pow, map_neg, map_mul, map_sub, map_pow, aeval_X]
  field_simp
  ring

end ringAtInfinity

/-! ### The ring at infinity as a type -/

/-- The ring of rational functions regular at infinity, as a type. -/
def AtInfinity : Type _ := ringAtInfinity k

namespace AtInfinity

/-- The commutative ring structure of `AtInfinity k`, that of `ringAtInfinity k`. -/
noncomputable instance : CommRing (AtInfinity k) := inferInstanceAs (CommRing (ringAtInfinity k))

/-- The ring at infinity is an integral domain. -/
instance : IsDomain (AtInfinity k) := inferInstanceAs (IsDomain (ringAtInfinity k))

/-- The `k`-algebra structure of the ring at infinity. -/
noncomputable instance : Algebra k (AtInfinity k) :=
  inferInstanceAs (Algebra k (ringAtInfinity k))

/-- The inclusion of the ring at infinity into `Frac k[X]`. -/
noncomputable instance : Algebra (AtInfinity k) (FractionRing k[X]) :=
  inferInstanceAs (Algebra (ringAtInfinity k) (FractionRing k[X]))

/-- The tower `k → AtInfinity k → Frac k[X]` is a scalar tower. -/
instance : IsScalarTower k (AtInfinity k) (FractionRing k[X]) :=
  inferInstanceAs (IsScalarTower k (ringAtInfinity k) (FractionRing k[X]))

/-- The ring at infinity is a discrete valuation ring. -/
instance : IsDiscreteValuationRing (AtInfinity k) :=
  inferInstanceAs (IsDiscreteValuationRing (ringAtInfinity k))

/-- The ring at infinity acts faithfully on `Frac k[X]`. -/
instance : FaithfulSMul (AtInfinity k) (FractionRing k[X]) :=
  inferInstanceAs (FaithfulSMul (ringAtInfinity k) (FractionRing k[X]))

/-- `Frac k[X]` is the fraction field of the ring at infinity. -/
instance : IsFractionRing (AtInfinity k) (FractionRing k[X]) :=
  inferInstanceAs (IsFractionRing (ringAtInfinity k) (FractionRing k[X]))

variable {k}

/-- An element of `Frac k[X]` lies in the image of `AtInfinity k` if and only if it lies in
`ringAtInfinity k`. -/
theorem mem_range_iff {z : FractionRing k[X]} :
    z ∈ Set.range (algebraMap (AtInfinity k) (FractionRing k[X])) ↔ z ∈ ringAtInfinity k :=
  ⟨fun ⟨a, ha⟩ ↦ ha ▸ (show ringAtInfinity k from a).2, fun h ↦ ⟨(⟨z, h⟩ : ringAtInfinity k), rfl⟩⟩

variable (k)

/-- The uniformizer `X⁻¹` of the ring at infinity. -/
noncomputable def uniformizer : AtInfinity k :=
  (⟨(fracX k)⁻¹, ringAtInfinity.fracX_inv_mem⟩ : ringAtInfinity k)

/-- The value at infinity. -/
noncomputable def residue : AtInfinity k →ₐ[k] k := ringAtInfinity.residue k

variable {k}

/-- The image of the uniformizer in `Frac k[X]` is `X⁻¹`. -/
@[simp]
theorem algebraMap_uniformizer :
    algebraMap (AtInfinity k) (FractionRing k[X]) (uniformizer k) = (fracX k)⁻¹ := rfl

/-- The uniformizer lies in the maximal ideal of the ring at infinity. -/
theorem uniformizer_mem_maximalIdeal :
    uniformizer k ∈ IsLocalRing.maximalIdeal (AtInfinity k) :=
  ringAtInfinity.fracX_inv_mem_maximalIdeal

/-- Every element `a` of the ring at infinity is congruent to its value at infinity modulo the
maximal ideal. -/
theorem sub_residue_mem_maximalIdeal (a : AtInfinity k) :
    a - algebraMap k (AtInfinity k) (residue k a) ∈ IsLocalRing.maximalIdeal (AtInfinity k) :=
  ringAtInfinity.sub_residue_mem_maximalIdeal (k := k) a

/-- For `deg f ≤ N`, the rational function `f(X) X⁻ᴺ` is regular at infinity. -/
theorem exists_algebraMap_eq_mul_inv_pow {N : ℕ} {f : k[X]} (hf : f.natDegree ≤ N) :
    ∃ a : AtInfinity k, algebraMap (AtInfinity k) (FractionRing k[X]) a =
      algebraMap k[X] (FractionRing k[X]) f * (fracX k)⁻¹ ^ N := by
  have h := invMap_mul_pow (N := N) (p := reflect N f) (natDegree_reflect_le_of_le hf)
  rw [reflect_reflect] at h
  refine mem_range_iff.mpr ?_
  rw [← h, inv_pow, mul_inv_cancel_right₀ (pow_ne_zero _ (fracX_ne_zero k))]
  exact ringAtInfinity.invMap_mem _

/-- **A polynomial regular at infinity is constant.** -/
theorem eq_C_of_mem_range {f : k[X]}
    (hf : algebraMap k[X] (FractionRing k[X]) f ∈
      Set.range (algebraMap (AtInfinity k) (FractionRing k[X]))) : ∃ c : k, f = C c :=
  ringAtInfinity.eq_C_of_algebraMap_mem (mem_range_iff.mp hf)

/-- **The derivation `X d/dX` preserves the ring at infinity.** -/
theorem exists_derivation_eq {L : Type*} [Field L] [Algebra (FractionRing k[X]) L] [Algebra k L]
    [IsScalarTower k (FractionRing k[X]) L] [Algebra (AtInfinity k) L]
    [IsScalarTower (AtInfinity k) (FractionRing k[X]) L] (δ : Derivation k L L)
    (hδ : δ (algebraMap _ L (fracX k)⁻¹) = -algebraMap _ L (fracX k)⁻¹) (a : AtInfinity k) :
    ∃ b : AtInfinity k, δ (algebraMap (AtInfinity k) L a) = algebraMap (AtInfinity k) L b := by
  obtain ⟨b, hb⟩ := ringAtInfinity.exists_derivation_eq δ hδ a
  have h (c : AtInfinity k) : algebraMap (AtInfinity k) L c =
      algebraMap (FractionRing k[X]) L (algebraMap (AtInfinity k) (FractionRing k[X]) c) :=
    IsScalarTower.algebraMap_apply _ _ _ c
  exact ⟨b, (congrArg δ (h a)).trans (hb.trans (h b).symm)⟩

end AtInfinity

end Polynomial

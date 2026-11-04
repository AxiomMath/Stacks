module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.AffineBlowup.Valuation
public import StacksFrontier.RingTheory.Blowup.Basic

/-!
# Reconciling the two models of the affine blowup chart `R[I/a]`

For a commutative ring `R`, an ideal `I ⊆ R` and an element `a ∈ I`, the repository
carries several models of the affine blowup chart `R[I/a]` of Stacks 052Q:

* the **quotient model** `Blowup I a` of `StacksFrontier.RingTheory.Blowup.Basic`, a
  quotient of the type `BlowupRepr I` of formal fractions `x / aⁿ` with `x ∈ Iⁿ` by the
  relation `x/aⁿ = y/aᵐ ↔ ∃ k, aᵏ (aᵐ x - aⁿ y) = 0`;
* the **subalgebra model** `Stacks.AffineBlowup.affineBlowupAlgebra I a ha` of
  `StacksFrontier.RingTheory.AffineBlowup.Valuation`, the `R`-subalgebra
  `{ y ∈ R_a | ∃ n x, x ∈ Iⁿ ∧ y aⁿ = x }` of the localization `R_a = Localization.Away a`;
* the **image model** `Stacks.AffineBlowup.affineBlowupImage I a ha`, the subring
  `{ x/aⁿ ∈ K | x ∈ Iⁿ }` of the fraction field `K` of a domain `R`, which is the model
  used in the statement of Stacks 052M.

This module reconciles the quotient model with the other two. The point is that the
relation defining `Blowup I a` is *literally* the equality relation of
`Localization.Away a` on the fractions `x / aⁿ`, so the comparison map is injective with
no integrality or domain hypothesis whatsoever, and its range is exactly the subalgebra
model.

The statement of Stacks 053I needs this bridge: clauses (1)–(3) of that lemma are phrased
through `Stacks.AffineBlowup.IsAdmissiblePair`, hence through `affineBlowupAlgebra` and
`affineBlowupImage`, whereas clause (4) speaks about the strict transform, which is built
over the quotient model `Blowup I a` in
`StacksFrontier.RingTheory.Blowup.StrictTransform`. The Lean statement of 053I deviates from its
source in two ways: it adds the hypothesis `𝔪 ≠ 0`, without which the conclusion is
unsatisfiable, and it reads clause (4) over `R[I/a]` rather than over `R`.

## Main definitions

* `Stacks.AffineBlowup.awayDiv a n x`: the element `x / aⁿ` of `Localization.Away a`.
* `Stacks.AffineBlowup.blowupToAway`: the comparison `R`-algebra map `Blowup I a →
  Localization.Away a`,
  `x/aⁿ ↦ x/aⁿ`.
* `Stacks.AffineBlowup.blowupEquivAffineBlowupAlgebra`: the bridge
  `Blowup I a ≃ₐ[R] affineBlowupAlgebra I a ha`.
* `Stacks.AffineBlowup.affineBlowupImageAlg`: the image model, a subring of `K`, viewed as an
  `R`-subalgebra of `K`.
* `Stacks.AffineBlowup.blowupToFractionField`: the comparison map `Blowup I a → K` into the
  fraction field of `R`, for `a` of nonzero image in `K`.
* `Stacks.AffineBlowup.blowupEquivAffineBlowupImage`,
  `Stacks.AffineBlowup.blowupEquivAffineBlowupImage'`: the
  bridge `Blowup I a ≃ₐ[R] affineBlowupImageAlg I a ha` for a domain `R` and `a ≠ 0`.
  (The underlying subring of the target is `Stacks.AffineBlowup.affineBlowupImage I a ha`.)

## Main results

* `Stacks.AffineBlowup.awayDiv_eq_awayDiv_iff`: equality of `x/aⁿ` and `y/aᵐ` in `Localization.Away
  a`
  is the relation defining `Blowup I a`.
* `Stacks.AffineBlowup.blowupToAway_injective`: the comparison map is injective.
* `Stacks.AffineBlowup.range_blowupToAway`: its range is the subalgebra model.
* `Stacks.AffineBlowup.fibreNonzero_iff`: the nonzero-fibre condition
  `Stacks.AffineBlowup.FibreNonzero`,
  defined through the subalgebra model, is equivalent to its quotient-model form.
* `Stacks.AffineBlowup.awayToFractionField_injective`,
  `Stacks.AffineBlowup.range_blowupToFractionField`: the
  corresponding statements for the image model in the fraction field.

## References

* [Stacks, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q) (the affine blowup algebra)
* [Stacks, Tag 053I](https://stacks.math.columbia.edu/tag/053I) (blowing up and flatness)
-/

@[expose] public section

namespace Stacks.AffineBlowup

variable {R : Type*} [CommRing R]

/-!
### Fractions with a power of `a` as denominator
-/

section AwayDiv

variable (a : R)

/-- The power `aⁿ` belongs to the submonoid `Submonoid.powers a` at which
`Localization.Away a` is the localization. -/
theorem pow_mem_powers (n : ℕ) : a ^ n ∈ Submonoid.powers a :=
  (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩

/-- The element `x / aⁿ` of the localization `R_a = Localization.Away a`, for `x : R` and
`n : ℕ`. This is the value taken by the comparison map `blowupToAway` on the class of the
representative `⟨n, x, _⟩`. -/
noncomputable def awayDiv (n : ℕ) (x : R) : Localization.Away a :=
  IsLocalization.mk' (Localization.Away a) x ⟨a ^ n, pow_mem_powers a n⟩

/-- Clearing the denominator: `(x / aⁿ) · aⁿ = x` in `Localization.Away a`. -/
theorem awayDiv_mul_pow (n : ℕ) (x : R) :
    awayDiv a n x * algebraMap R (Localization.Away a) a ^ n
      = algebraMap R (Localization.Away a) x := by
  simpa [awayDiv, map_pow] using
    IsLocalization.mk'_spec (Localization.Away a) x ⟨a ^ n, pow_mem_powers a n⟩

/-- An element of `Localization.Away a` equals `x / aⁿ` exactly when multiplying it by `aⁿ`
gives `x`. -/
theorem eq_awayDiv_iff {n : ℕ} {x : R} {z : Localization.Away a} :
    z = awayDiv a n x ↔
      z * algebraMap R (Localization.Away a) a ^ n = algebraMap R (Localization.Away a) x := by
  rw [awayDiv, IsLocalization.eq_mk'_iff_mul_eq]
  simp [map_pow]

/-- A fraction with denominator `a⁰ = 1` is the image of its numerator. -/
@[simp] theorem awayDiv_zero (x : R) :
    awayDiv a 0 x = algebraMap R (Localization.Away a) x :=
  ((eq_awayDiv_iff a).mpr (by simp)).symm

/-- **The two relations coincide.** Two fractions `x / aⁿ` and `y / aᵐ` are equal in
`Localization.Away a` exactly when `aᵏ (aᵐ x - aⁿ y) = 0` for some `k`, which is the
relation `BlowupRepr.rel` defining the quotient model `Blowup I a`. -/
theorem awayDiv_eq_awayDiv_iff (n m : ℕ) (x y : R) :
    awayDiv a n x = awayDiv a m y ↔ ∃ k : ℕ, a ^ k * (a ^ m * x - a ^ n * y) = 0 := by
  have hmk : awayDiv a n x = awayDiv a m y ↔
      algebraMap R (Localization.Away a) (a ^ m * x)
        = algebraMap R (Localization.Away a) (a ^ n * y) :=
    IsLocalization.mk'_eq_iff_eq (M := Submonoid.powers a) (S := Localization.Away a)
      (x₁ := x) (x₂ := y) (y₁ := ⟨a ^ n, pow_mem_powers a n⟩) (y₂ := ⟨a ^ m, pow_mem_powers a m⟩)
  rw [hmk, IsLocalization.eq_iff_exists (M := Submonoid.powers a) (S := Localization.Away a)]
  simp only [mul_sub, sub_eq_zero, Subtype.exists, Submonoid.mem_powers_iff, exists_prop,
    exists_exists_eq_and]

end AwayDiv

/-!
### The comparison map into the localization
-/

section Comparison

variable {I : Ideal R} {a : R}

/-- Membership in the subalgebra model `affineBlowupAlgebra I a ha`, unfolded. -/
theorem mem_affineBlowupAlgebra (ha : a ∈ I) {y : Localization.Away a} :
    y ∈ affineBlowupAlgebra I a ha ↔ ∃ (n : ℕ) (x : R), x ∈ I ^ n ∧
      y * algebraMap R (Localization.Away a) a ^ n = algebraMap R (Localization.Away a) x :=
  Iff.rfl

/-- The underlying function of the comparison map, sending the class of the representative
`⟨n, x, _⟩` of `Blowup I a` to the fraction `x / aⁿ` of `Localization.Away a`. It is
well defined by `awayDiv_eq_awayDiv_iff`. -/
noncomputable def blowupToAwayFun : Blowup I a → Localization.Away a :=
  Quotient.lift (fun p : BlowupRepr I => awayDiv a p.deg p.num)
    fun p q h => (awayDiv_eq_awayDiv_iff a p.deg q.deg p.num q.num).mpr h

variable [ha : Fact (a ∈ I)]

/-- **The comparison map.** The `R`-algebra map from the quotient model `Blowup I a` to the
localization `R_a = Localization.Away a` sending the class of `⟨n, x, _⟩` to `x / aⁿ`. -/
noncomputable def blowupToAway : Blowup I a →ₐ[R] Localization.Away a where
  toFun := blowupToAwayFun
  map_one' := (awayDiv_zero a (1 : R)).trans (map_one _)
  map_mul' := by
    intro u v
    induction u using Quotient.inductionOn with | _ p =>
    induction v using Quotient.inductionOn with | _ q =>
    change awayDiv a (p.deg + q.deg) (p.num * q.num)
      = awayDiv a p.deg p.num * awayDiv a q.deg q.num
    refine ((eq_awayDiv_iff a).mpr ?_).symm
    rw [pow_add, map_mul, ← awayDiv_mul_pow a p.deg p.num, ← awayDiv_mul_pow a q.deg q.num]
    ring
  map_zero' := (awayDiv_zero a (0 : R)).trans (map_zero _)
  map_add' := by
    intro u v
    induction u using Quotient.inductionOn with | _ p =>
    induction v using Quotient.inductionOn with | _ q =>
    change awayDiv a (p.deg + q.deg) (a ^ q.deg * p.num + a ^ p.deg * q.num)
      = awayDiv a p.deg p.num + awayDiv a q.deg q.num
    refine ((eq_awayDiv_iff a).mpr ?_).symm
    rw [pow_add, map_add, map_mul, map_mul, map_pow, map_pow,
      ← awayDiv_mul_pow a p.deg p.num, ← awayDiv_mul_pow a q.deg q.num]
    ring
  commutes' r := awayDiv_zero a r

/-- The comparison map sends the class of `⟨n, x, _⟩` to the fraction `x / aⁿ`. -/
@[simp] theorem blowupToAway_mk (p : BlowupRepr I) :
    blowupToAway (Blowup.mk p : Blowup I a) = awayDiv a p.deg p.num := rfl

/-- **The comparison map is injective**, with no integrality or domain hypothesis: by
`awayDiv_eq_awayDiv_iff` the relation defining `Blowup I a` is exactly the equality relation
of `Localization.Away a` on the fractions `x / aⁿ`. -/
theorem blowupToAway_injective :
    Function.Injective (blowupToAway (I := I) (a := a)) := by
  intro u v huv
  induction u using Quotient.inductionOn with | _ p =>
  induction v using Quotient.inductionOn with | _ q =>
  exact Blowup.mk_eq_mk.mpr ((awayDiv_eq_awayDiv_iff a p.deg q.deg p.num q.num).mp huv)

/-- **The range of the comparison map is the subalgebra model.** The image of the class of
`⟨n, x, _⟩` satisfies the defining condition of `affineBlowupAlgebra I a ha` with the same
`n` and `x`; conversely an element `y` of `R_a` with `y aⁿ = x` and `x ∈ Iⁿ` is the image of
the class of `⟨n, x, _⟩`. -/
theorem range_blowupToAway :
    (blowupToAway (I := I) (a := a)).range = affineBlowupAlgebra I a ha.out := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨u, rfl⟩
    induction u using Quotient.inductionOn with | _ p =>
    exact (mem_affineBlowupAlgebra ha.out).mpr
      ⟨p.deg, p.num, p.num_mem, awayDiv_mul_pow a p.deg p.num⟩
  · intro y hy
    obtain ⟨n, x, hx, hyx⟩ := (mem_affineBlowupAlgebra ha.out).mp hy
    exact ⟨Blowup.mk ⟨n, x, hx⟩, ((eq_awayDiv_iff a).mpr hyx).symm⟩

/-- **The bridge between the two models.** The quotient model `Blowup I a` is isomorphic, as
an `R`-algebra, to the subalgebra model `affineBlowupAlgebra I a ha`: the comparison map
`blowupToAway` is injective with range exactly that subalgebra. -/
noncomputable def blowupEquivAffineBlowupAlgebra :
    Blowup I a ≃ₐ[R] affineBlowupAlgebra I a ha.out :=
  (AlgEquiv.ofInjective _ blowupToAway_injective).trans
    (Subalgebra.equivOfEq _ _ range_blowupToAway)

/-- The bridge is the comparison map: its value at `x`, viewed in `Localization.Away a`, is
`blowupToAway x`. -/
@[simp] theorem blowupEquivAffineBlowupAlgebra_coe (x : Blowup I a) :
    (blowupEquivAffineBlowupAlgebra (I := I) (a := a) x : Localization.Away a)
      = blowupToAway x :=
  AlgEquiv.ofInjective_apply _ blowupToAway_injective x

end Comparison

/-!
### Transfer of the nonzero-fibre condition
-/

/-- Extending an ideal of the base along an `R`-algebra isomorphism: the extension is the
whole ring on one side exactly when it is on the other. -/
theorem map_algebraMap_eq_top_iff {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (e : A ≃ₐ[R] B) (J : Ideal R) :
    J.map (algebraMap R B) = ⊤ ↔ J.map (algebraMap R A) = ⊤ := by
  have hcomp : (algebraMap R B) = (e : A →+* B).comp (algebraMap R A) := by
    ext r
    simp
  rw [hcomp, ← Ideal.map_map]
  exact Ideal.map_eq_top_of_bijective (e : A →+* B) e.bijective

/-- **The nonzero-fibre condition in the quotient model.** For a local ring `R`, the fibre
ring of `R → R[I/a]` at the maximal ideal is nonzero — that is, `Stacks.AffineBlowup.FibreNonzero`,
which is phrased through the subalgebra model — exactly when the extension of the maximal
ideal to the quotient model `Blowup I a` is a proper ideal. -/
theorem fibreNonzero_iff [IsLocalRing R] {I : Ideal R} {a : R} [ha : Fact (a ∈ I)] :
    FibreNonzero ha.out ↔
      (IsLocalRing.maximalIdeal R).map (algebraMap R (Blowup I a)) ≠ ⊤ :=
  not_congr (map_algebraMap_eq_top_iff (R := R) (A := Blowup I a)
    (B := affineBlowupAlgebra I a ha.out) blowupEquivAffineBlowupAlgebra
    (IsLocalRing.maximalIdeal R))

/-!
### The comparison map into the fraction field

For `R` a domain with fraction field `K` and `a ≠ 0`, the localization `R_a` embeds in `K`,
and the quotient model is carried onto the image model `affineBlowupImage I a ha` used in
the statement of Stacks 052M — hence clause (2) of Stacks 053I, `A` has center on `R[I/a]`,
can be read off the quotient model as well.
-/

section FractionField

variable {I : Ideal R} {a : R} {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The map `R_a → K` of `awayToFractionField` as an `R`-algebra map. -/
noncomputable def awayToFractionFieldAlgHom (a : R) (haz : algebraMap R K a ≠ 0) :
    Localization.Away a →ₐ[R] K :=
  { awayToFractionField a haz with commutes' := awayToFractionField_comp a haz }

omit [IsFractionRing R K] in
/-- The `R`-algebra map `R_a → K` is the ring map `awayToFractionField`. -/
@[simp] theorem awayToFractionFieldAlgHom_apply (a : R) (haz : algebraMap R K a ≠ 0)
    (z : Localization.Away a) :
    awayToFractionFieldAlgHom a haz z = awayToFractionField a haz z := rfl

/-- If `z * r = x` in `R_a`, then the image of `z` in a field `L` satisfies the same equation. -/
private theorem awayToFractionField_mul_eq {L : Type*} [Field L] [Algebra R L] (a : R)
    (haz : algebraMap R L a ≠ 0) {z : Localization.Away a} {r x : R}
    (h : z * algebraMap R (Localization.Away a) r = algebraMap R (Localization.Away a) x) :
    awayToFractionField a haz z * algebraMap R L r = algebraMap R L x := by
  have h := congrArg (awayToFractionField a haz) h
  rwa [map_mul, awayToFractionField_comp, awayToFractionField_comp] at h

/-- **`R_a → K` is injective** when `R` is a domain with fraction field `K` and `a ≠ 0`:
the powers of `a` are nonzerodivisors, so both `R_a` and `K` are localizations of `R` at
submonoids of nonzerodivisors. -/
theorem awayToFractionField_injective (a : R) (haz : algebraMap R K a ≠ 0) :
    Function.Injective (awayToFractionField (K := K) a haz) := by
  have key : ∀ (x : R) (s : Submonoid.powers a),
      awayToFractionField (K := K) a haz (IsLocalization.mk' (Localization.Away a) x s)
        * algebraMap R K (s : R) = algebraMap R K x := fun x s =>
    awayToFractionField_mul_eq a haz (IsLocalization.mk'_spec (Localization.Away a) x s)
  intro u v huv
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers a) u
  obtain ⟨y, t, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers a) v
  have hxt : algebraMap R K ((t : R) * x) = algebraMap R K ((s : R) * y) := by
    rw [map_mul, map_mul]
    linear_combination -algebraMap R K (t : R) * key x s + algebraMap R K (s : R) * key y t
      + algebraMap R K (s : R) * algebraMap R K (t : R) * huv
  exact IsLocalization.mk'_eq_iff_eq.mpr
    (congrArg (algebraMap R (Localization.Away a)) (IsFractionRing.injective R K hxt))

/-- The image model `Stacks.AffineBlowup.affineBlowupImage I a ha`, a subring of `K`, viewed as an
`R`-subalgebra of `K`; the two have the same carrier, and
`affineBlowupImageAlg_toSubring` records that its underlying subring is the original one. -/
def affineBlowupImageAlg (I : Ideal R) (a : R) (ha : a ∈ I) : Subalgebra R K where
  toSubsemiring := (affineBlowupImage I a ha).toSubsemiring
  algebraMap_mem' r := range_le_affineBlowupImage ha ⟨r, rfl⟩

omit [IsFractionRing R K] in
/-- The subalgebra `affineBlowupImageAlg I a ha` has the image model as its underlying
subring. -/
@[simp] theorem affineBlowupImageAlg_toSubring (I : Ideal R) (a : R) (ha : a ∈ I) :
    (affineBlowupImageAlg (K := K) I a ha).toSubring = affineBlowupImage I a ha := rfl

variable [ha : Fact (a ∈ I)]

/-- **The comparison map into the fraction field**, the composite of `blowupToAway` with the
embedding `R_a → K`. It sends the class of `⟨n, x, _⟩` to `x / aⁿ ∈ K`. -/
noncomputable def blowupToFractionField (haz : algebraMap R K a ≠ 0) : Blowup I a →ₐ[R] K :=
  (awayToFractionFieldAlgHom a haz).comp blowupToAway

omit [IsFractionRing R K] in
/-- Clearing the denominator in `K`: the image of `x / aⁿ` multiplied by `aⁿ` is `x`. -/
theorem blowupToFractionField_mul_pow (haz : algebraMap R K a ≠ 0) (n : ℕ) (x : R)
    (hx : x ∈ I ^ n) :
    blowupToFractionField (I := I) haz (Blowup.mk ⟨n, x, hx⟩) * algebraMap R K a ^ n
      = algebraMap R K x := by
  rw [← map_pow]
  exact awayToFractionField_mul_eq a haz (r := a ^ n) (by rw [map_pow]; exact awayDiv_mul_pow a n x)

/-- **The comparison map into `K` is injective**, being the composite of the injective
`blowupToAway` with the injective embedding `R_a → K`. -/
theorem blowupToFractionField_injective (haz : algebraMap R K a ≠ 0) :
    Function.Injective (blowupToFractionField (I := I) (a := a) haz) :=
  (awayToFractionField_injective a haz).comp blowupToAway_injective

omit [IsFractionRing R K] in
/-- **The range of the comparison map into `K` is the image model.** Forward, the image of
the class of `⟨n, x, _⟩` satisfies the defining condition of `affineBlowupImage I a ha` with
the same `n` and `x`; backward, an element `y` of `K` with `y aⁿ = x` and `x ∈ Iⁿ` agrees
with that image after multiplication by the nonzero element `aⁿ`. -/
theorem range_blowupToFractionField (haz : algebraMap R K a ≠ 0) :
    (blowupToFractionField (I := I) (a := a) haz).range
      = affineBlowupImageAlg (K := K) I a ha.out := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨u, rfl⟩
    induction u using Quotient.inductionOn with | _ p =>
    exact ⟨p.deg, p.num, p.num_mem, blowupToFractionField_mul_pow haz p.deg p.num p.num_mem⟩
  · rintro y ⟨n, x, hx, hyx⟩
    exact ⟨Blowup.mk ⟨n, x, hx⟩, mul_right_cancel₀ (pow_ne_zero n haz)
      ((blowupToFractionField_mul_pow haz n x hx).trans hyx.symm)⟩

/-- **The bridge to the image model.** For `R` a domain with fraction field `K` and `a ≠ 0`,
the quotient model `Blowup I a` is isomorphic, as an `R`-algebra, to the image model
`affineBlowupImage I a ha` of Stacks 052M, viewed as a subalgebra of `K` through
`affineBlowupImageAlg`. -/
noncomputable def blowupEquivAffineBlowupImage (haz : algebraMap R K a ≠ 0) :
    Blowup I a ≃ₐ[R] affineBlowupImageAlg (K := K) I a ha.out :=
  (AlgEquiv.ofInjective _ (blowupToFractionField_injective haz)).trans
    (Subalgebra.equivOfEq _ _ (range_blowupToFractionField haz))

/-- The bridge to the image model is the comparison map: its value at `x`, viewed in `K`, is
`blowupToFractionField haz x`. -/
@[simp] theorem blowupEquivAffineBlowupImage_coe (haz : algebraMap R K a ≠ 0)
    (x : Blowup I a) :
    (blowupEquivAffineBlowupImage (I := I) (a := a) haz x : K)
      = blowupToFractionField haz x :=
  AlgEquiv.ofInjective_apply _ (blowupToFractionField_injective haz) x

/-- The variant of `blowupEquivAffineBlowupImage` whose hypothesis is `a ≠ 0`: for a ring
`R` with fraction field `K` a nonzero element of `R` has nonzero image in `K`. (This is
`Stacks.AffineBlowup.algebraMap_ne_zero_of_ne_zero` without its redundant `IsDomain R` hypothesis:
`IsFractionRing R K` with `K` a field already makes `algebraMap R K` injective, hence `R` a
domain.) -/
noncomputable def blowupEquivAffineBlowupImage' (ha0 : a ≠ 0) :
    Blowup I a ≃ₐ[R] affineBlowupImageAlg (K := K) I a ha.out :=
  blowupEquivAffineBlowupImage (K := K)
    (fun h => ha0 (IsFractionRing.to_map_eq_zero_iff.mp h))

end FractionField

end Stacks.AffineBlowup

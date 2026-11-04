module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import StacksCore.Tactic.StacksAttribute

/-!
# A valuation ring dominating a local domain as a union of affine blowups

Throughout, `(R, 𝔪)` is a local domain: a commutative integral domain that is
also a local ring, with unique maximal ideal `𝔪`. Let `K = Frac R` be its
fraction field, encoded by `IsFractionRing R K`, with `R` regarded as a subring of
`K` via `r ↦ r / 1`.

The main case `𝔪 ≠ 0` states: if `R ⊂ A ⊂ K` is a valuation ring dominating `R`,
then `A` is the directed union of those affine blowup algebras `R[I/a]`, realized
as subrings of `K`, for which

1. `a ∈ I ⊆ 𝔪`,
2. `I` is finitely generated,
3. the fibre ring of `R → R[I/a]` at `𝔪` is nonzero, and
4. `R[I/a] ⊆ A`.

The degenerate field case `𝔪 = 0` is stated separately: there `A = R = K`.

## Conventions

The blowup algebra `Bl_I(R) = ⊕_{n ≥ 0} Iⁿ`, with `Iⁿ` in degree `n`, is
Mathlib's `reesAlgebra I`, the `R`-subalgebra of `R[X]` of polynomials `∑ aᵢ Xⁱ`
with `aᵢ ∈ Iⁱ`.

The affine blowup algebra `R[I/a]` is modelled as the `R`-subalgebra
`{y ∈ R_a | ∃ n x, x ∈ Iⁿ ∧ y aⁿ = x}` of the localization
`R_a = Localization.Away a`. This is faithful in the degenerate case: for `a = 0`
the ring `Localization.Away 0` is the zero ring, since `0` is a unit there, so
`R[I/0]` is the zero ring, as in the source.

For `a ≠ 0` the element `a` is a nonzerodivisor and `R[I/a] → K` is injective; its
image is recorded as the subring `affineBlowupImage I a = {x/aⁿ ∈ K | x ∈ Iⁿ}` of
`K`, and the union theorem is phrased in terms of these subrings of `K`.

The fibre ring of `R → R[I/a]` at `𝔪` is nonzero exactly when the extension
`𝔪 · R[I/a]` is a proper ideal, that is `(𝔪).map (algebraMap R R[I/a]) ≠ ⊤`. For
`a = 0` the algebra is the zero ring and the condition fails, so condition (3)
genuinely excludes the members with `a = 0`.

That `A` dominates `R` means `R ⊆ A` and `𝔪 ⊆ 𝔪_A`, expressed concretely as: the
image of `R` in `K` is a subring of `A`, and every element of `𝔪` maps to a
non-unit of `A`. A valuation ring is a term of `ValuationSubring K`, so that for
every nonzero `x : K` either `x ∈ A` or `x⁻¹ ∈ A`.

The assertion that one may take `(L, c) = (IJ, ab)` as an explicit common
refinement is stated through the predicate `IsAdmissiblePair`, applied to the
displayed pairs `(I, a)` and `(J, b)` and concluding it for the displayed product
pair `(I J, a b)`; it is the displayed pairs themselves that are assumed to satisfy
(1)–(4). Since `IsAdmissiblePair` includes the nonzero-fibre condition, all such
pairs have `a ≠ 0`, so `affineBlowupImage` is only ever applied to nonzero
denominators.
-/

@[expose] public section

namespace Stacks.AffineBlowup

open Localization

variable {R : Type*} [CommRing R]

/-- **Definition 3 (Rees / blowup algebra).** The blowup algebra `Bl_I(R)` of the
pair `(R, I)`, realized by Mathlib's `reesAlgebra I` as the `R`-subalgebra of
`R[X]` of polynomials whose `i`-th coefficient lies in `Iⁱ`. -/
noncomputable abbrev blowupAlgebra (I : Ideal R) : Subalgebra R (Polynomial R) :=
  reesAlgebra I

/-- **Definition 4 (affine blowup algebra `R[I/a]`).** For an ideal `I` and
`a ∈ I`, the affine blowup algebra `R[I/a]`, realized as an honest `R`-subalgebra
of the localization `R_a = Localization.Away a`:
`R[I/a] = { y ∈ R_a : ∃ n x, x ∈ Iⁿ ∧ y · aⁿ = x }`.

This is faithful including the degenerate case `a = 0`: then `R_a` is the zero
ring, so `R[I/a]` is the zero ring (`affineBlowupAlgebra_subsingleton_of_zero`). -/
noncomputable def affineBlowupAlgebra (I : Ideal R) (a : R) (ha : a ∈ I) :
    Subalgebra R (Localization.Away a) where
  carrier := { y | ∃ (n : ℕ) (x : R), x ∈ I ^ n ∧
      y * (algebraMap R (Localization.Away a) a) ^ n = algebraMap R (Localization.Away a) x }
  one_mem' := ⟨0, 1, by simp, by simp⟩
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  mul_mem' := by
    rintro p q ⟨n, x, hx, hpx⟩ ⟨m, z, hz, hqz⟩
    refine ⟨n + m, x * z, by rw [pow_add]; exact Ideal.mul_mem_mul hx hz, ?_⟩
    rw [map_mul, pow_add]
    calc p * q * ((algebraMap R (Localization.Away a) a) ^ n
          * (algebraMap R (Localization.Away a) a) ^ m)
        = (p * (algebraMap R (Localization.Away a) a) ^ n)
            * (q * (algebraMap R (Localization.Away a) a) ^ m) := by ring
      _ = (algebraMap R (Localization.Away a) x) * (algebraMap R (Localization.Away a)
          z) := by rw [hpx, hqz]
  add_mem' := by
    rintro p q ⟨n, x, hx, hpx⟩ ⟨m, z, hz, hqz⟩
    have ham : a ^ m ∈ I ^ m := Ideal.pow_mem_pow ha m
    have han : a ^ n ∈ I ^ n := Ideal.pow_mem_pow ha n
    refine ⟨n + m, x * a ^ m + z * a ^ n, ?_, ?_⟩
    · refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]; exact Ideal.mul_mem_mul hx ham
      · rw [pow_add, mul_comm (I ^ n)]; exact Ideal.mul_mem_mul hz han
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, pow_add]
      calc (p + q) * ((algebraMap R (Localization.Away a) a) ^ n
            * (algebraMap R (Localization.Away a) a) ^ m)
          = (p * (algebraMap R (Localization.Away a) a) ^ n) * (algebraMap R (Localization.Away a)
              a) ^ m
            + (q * (algebraMap R (Localization.Away a) a) ^ m)
              * (algebraMap R (Localization.Away a) a) ^ n := by ring
        _ = (algebraMap R (Localization.Away a) x) * (algebraMap R (Localization.Away a) a) ^ m
            + (algebraMap R (Localization.Away a) z)
              * (algebraMap R (Localization.Away a) a) ^ n := by rw [hpx, hqz]
  algebraMap_mem' := by
    intro r
    exact ⟨0, r, by simp, by simp⟩

/-- **Faithfulness of Definition 4 in the degenerate case.** When `a = 0`, the
affine blowup algebra `R[I/0]` is the zero ring, exactly as in Stacks 052Q:
localizing the Rees algebra at the degree-1 element `0` yields the zero ring. -/
theorem affineBlowupAlgebra_subsingleton_of_zero (I : Ideal R) (ha : (0 : R) ∈ I) :
    Subsingleton (affineBlowupAlgebra I 0 ha) := by
  have : Subsingleton (Localization.Away (0 : R)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, by simp⟩
  infer_instance

/-- **Definition 6 (fibre ring at `𝔪` is nonzero).** For the structure map
`R → R[I/a]` of Definition 4, the fibre ring at `𝔪` is nonzero iff the extension
`𝔪 · R[I/a]` is a proper ideal of `R[I/a]`, i.e. `(𝔪).map (algebraMap R R[I/a]) ≠ ⊤`.
When `a = 0` the algebra `R[I/a]` is the zero ring, so `⊤ = ⊥` and this fails;
hence this condition forces `a ≠ 0`. -/
def FibreNonzero [IsLocalRing R] {I : Ideal R} {a : R} (ha : a ∈ I) : Prop :=
  (IsLocalRing.maximalIdeal R).map (algebraMap R (affineBlowupAlgebra I a ha)) ≠ ⊤

/-- **Condition (3) forces `a ≠ 0`.** If `a = 0`, the affine blowup algebra is the
zero ring (`affineBlowupAlgebra_subsingleton_of_zero`), so its fibre ring at `𝔪`
vanishes and `FibreNonzero` is false. Hence every member of the family `𝒮`
(Definition 7) has `a ≠ 0`, and the field case `𝒮 = ∅` holds exactly as in the
source — `a ≠ 0` is *derived* from (3), not assumed. -/
theorem not_fibreNonzero_of_zero [IsLocalRing R] (I : Ideal R) (ha : (0 : R) ∈ I) :
    ¬ FibreNonzero (I := I) ha := by
  have hss := affineBlowupAlgebra_subsingleton_of_zero I ha
  intro h
  apply h
  have htop : (⊤ : Ideal (affineBlowupAlgebra I (0 : R) ha)) = ⊥ := Subsingleton.elim _ _
  rw [htop]
  exact Subsingleton.elim _ _

/-- The element `a` of a pair `(I, a)` satisfying `FibreNonzero` is nonzero. -/
private theorem ne_zero_of_fibreNonzero [IsLocalRing R] {I : Ideal R} {a : R} (ha : a ∈ I)
    (h : FibreNonzero ha) : a ≠ 0 := by
  rintro rfl
  exact not_fibreNonzero_of_zero I ha h

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Definition 5 (the image of `R[I/a]` in `K`).** For an ideal `I` and `a ∈ I`,
the image of the affine blowup algebra inside `K = Frac(R)`, identified with the
`R`-subring `{ x/aⁿ ∈ K : n ≥ 0, x ∈ Iⁿ }`. (For `a ≠ 0` this is exactly the
image of the injective map `R[I/a] → K`; this is the realization used in the
colimit theorem.) -/
def affineBlowupImage (I : Ideal R) (a : R) (ha : a ∈ I) : Subring K where
  carrier := { y : K | ∃ (n : ℕ) (x : R), x ∈ I ^ n ∧ y * (algebraMap R K a) ^ n = algebraMap R K x
      }
  one_mem' := ⟨0, 1, by simp, by simp⟩
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  mul_mem' := by
    rintro p q ⟨n, x, hx, hpx⟩ ⟨m, z, hz, hqz⟩
    refine ⟨n + m, x * z, by rw [pow_add]; exact Ideal.mul_mem_mul hx hz, ?_⟩
    rw [map_mul, pow_add]
    calc p * q * ((algebraMap R K a) ^ n * (algebraMap R K a) ^ m)
        = (p * (algebraMap R K a) ^ n) * (q * (algebraMap R K a) ^ m) := by ring
      _ = (algebraMap R K x) * (algebraMap R K z) := by rw [hpx, hqz]
  add_mem' := by
    rintro p q ⟨n, x, hx, hpx⟩ ⟨m, z, hz, hqz⟩
    have ham : a ^ m ∈ I ^ m := Ideal.pow_mem_pow ha m
    have han : a ^ n ∈ I ^ n := Ideal.pow_mem_pow ha n
    refine ⟨n + m, x * a ^ m + z * a ^ n, ?_, ?_⟩
    · refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]; exact Ideal.mul_mem_mul hx ham
      · rw [pow_add, mul_comm (I ^ n)]; exact Ideal.mul_mem_mul hz han
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, pow_add]
      calc (p + q) * ((algebraMap R K a) ^ n * (algebraMap R K a) ^ m)
          = (p * (algebraMap R K a) ^ n) * (algebraMap R K a) ^ m
            + (q * (algebraMap R K a) ^ m) * (algebraMap R K a) ^ n := by ring
        _ = (algebraMap R K x) * (algebraMap R K a) ^ m
            + (algebraMap R K z) * (algebraMap R K a) ^ n := by rw [hpx, hqz]
  neg_mem' := by
    rintro p ⟨n, x, hx, hpx⟩
    exact ⟨n, -x, neg_mem hx, by rw [map_neg, ← hpx]; ring⟩

omit [IsFractionRing R K] in
/-- Membership characterization of the image subring `affineBlowupImage`. -/
theorem mem_affineBlowupImage {I : Ideal R} {a : R} (ha : a ∈ I) {y : K} :
    y ∈ affineBlowupImage I a ha ↔
      ∃ (n : ℕ) (x : R), x ∈ I ^ n ∧ y * (algebraMap R K a) ^ n = algebraMap R K x :=
  Iff.rfl

omit [IsFractionRing R K] in
/-- The canonical image of `R` (as `algebraMap R K`) is contained in
`affineBlowupImage I a` (via `r = r / a⁰`). -/
theorem range_le_affineBlowupImage {I : Ideal R} {a : R} (ha : a ∈ I) :
    (algebraMap R K).range ≤ (affineBlowupImage I a ha : Subring K) := by
  rintro _ ⟨r, rfl⟩
  exact ⟨0, r, by simp, by simp⟩

omit [IsFractionRing R K] in
/-- Containment of affine blowup images: if `b ∈ J`, then
`affineBlowupImage I a ⊆ affineBlowupImage (I*J) (a*b)` (the denominator picks up
the factor `b`, and the numerator the factor `bⁿ`). -/
theorem affineBlowupImage_le_mul {I J : Ideal R} {a b : R} (ha : a ∈ I) (hb : b ∈ J)
    (hab : a * b ∈ I * J) :
    (affineBlowupImage I a ha : Subring K) ≤ affineBlowupImage (I * J) (a * b) hab := by
  rintro y ⟨n, x, hx, hyx⟩
  refine ⟨n, x * b ^ n, ?_, ?_⟩
  · rw [mul_pow]
    have hbn : b ^ n ∈ J ^ n := Ideal.pow_mem_pow hb n
    exact Ideal.mul_mem_mul hx hbn
  · rw [map_mul, mul_pow, ← mul_assoc, hyx, map_mul, map_pow]

omit [IsFractionRing R K] in
/-- If every element of `I`, divided by `a`, lands in the subring `S` of `K`
(precisely: `algebraMap i = wᵢ · algebraMap a` with `wᵢ ∈ S`), and `algebraMap a`
is nonzero, then for every `z ∈ Iⁿ` we have `algebraMap z = (algebraMap a)ⁿ · W`
with `W ∈ S`. -/
theorem exists_mem_of_mem_pow {I : Ideal R} {a : R} (S : Subring K)
    (hR : (algebraMap R K).range ≤ S)
    (hgen : ∀ i ∈ I, ∃ w ∈ S, algebraMap R K i = w * algebraMap R K a) :
    ∀ (n : ℕ), ∀ z ∈ I ^ n, ∃ w ∈ S, algebraMap R K z = (algebraMap R K a) ^ n * w := by
  intro n
  induction n with
  | zero =>
    intro z _
    exact ⟨algebraMap R K z, hR ⟨z, rfl⟩, by simp⟩
  | succ n ih =>
    intro z hz
    rw [pow_succ] at hz
    -- z ∈ Iⁿ * I
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro p hp q hq
      obtain ⟨wp, hwp, hpeq⟩ := ih p hp
      obtain ⟨wq, hwq, hqeq⟩ := hgen q hq
      refine ⟨wp * wq, mul_mem hwp hwq, ?_⟩
      rw [map_mul, hpeq, hqeq, pow_succ]
      ring
    · intro x y hx hy
      obtain ⟨wx, hwx, hxeq⟩ := hx
      obtain ⟨wy, hwy, hyeq⟩ := hy
      refine ⟨wx + wy, add_mem hwx hwy, ?_⟩
      rw [map_add, hxeq, hyeq, mul_add]

omit [IsFractionRing R K] in
/-- It suffices to check the "generator divisibility" condition on a generating
set: if for every `g` in a generating set `gens` of `I` we have
`algebraMap g = wg · algebraMap a` with `wg ∈ S` (and `R`-image ⊆ S), then the
same holds for every element of `I = span gens`. -/
theorem gen_cond_of_span {a : R} (S : Subring K)
    (hR : (algebraMap R K).range ≤ S)
    (gens : Set R)
    (hgens : ∀ g ∈ gens, ∃ w ∈ S, algebraMap R K g = w * algebraMap R K a) :
    ∀ i ∈ Ideal.span gens, ∃ w ∈ S, algebraMap R K i = w * algebraMap R K a := by
  intro i hi
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
  · intro g hg
    exact hgens g hg
  · exact ⟨0, zero_mem S, by simp⟩
  · rintro x y _ _ ⟨wx, hwx, hxeq⟩ ⟨wy, hwy, hyeq⟩
    exact ⟨wx + wy, add_mem hwx hwy, by rw [map_add, hxeq, hyeq, add_mul]⟩
  · rintro r x _ ⟨wx, hwx, hxeq⟩
    refine ⟨algebraMap R K r * wx, mul_mem (hR ⟨r, rfl⟩) hwx, ?_⟩
    rw [smul_eq_mul, map_mul, hxeq, mul_assoc]

omit [IsFractionRing R K] in
/-- If every element of `I`, divided by `a`, lands in the subring `S` of `K`, and
`algebraMap a ≠ 0`, then `affineBlowupImage I a ⊆ S`. -/
theorem affineBlowupImage_le_of_gen {I : Ideal R} {a : R} (ha : a ∈ I) (S : Subring K)
    (haz : algebraMap R K a ≠ 0)
    (hR : (algebraMap R K).range ≤ S)
    (hgen : ∀ i ∈ I, ∃ w ∈ S, algebraMap R K i = w * algebraMap R K a) :
    (affineBlowupImage I a ha : Subring K) ≤ S := by
  rintro y ⟨n, z, hz, hyz⟩
  obtain ⟨w, hw, hweq⟩ := exists_mem_of_mem_pow S hR hgen n z hz
  -- y * (algebraMap a)^n = algebraMap z = (algebraMap a)^n * w, cancel
  have hpow : (algebraMap R K a) ^ n ≠ 0 := pow_ne_zero n haz
  have : y * (algebraMap R K a) ^ n = w * (algebraMap R K a) ^ n := by
    rw [hyz, hweq]; ring
  have : y = w := mul_right_cancel₀ hpow this
  rw [this]; exact hw

/-- The canonical image of `R` in `K` is a local ring (isomorphic to the local
ring `R`). -/
theorem isLocalRing_range [IsLocalRing R] :
    IsLocalRing (algebraMap R K).range :=
  RingEquiv.isLocalRing
    (RingEquiv.ofLeftInverse (Function.leftInverse_invFun (IsFractionRing.injective R K)))

/- The five `@[nolint unusedArguments]` attributes below are deliberate. The standing
setting of Stacks Tags 052M and 053I is a local *domain* `R` with *fraction field* `K`,
so `[IsDomain R]` and `[IsFractionRing R K]` are part of what these statements say,
even where the elaborated proof term happens not to mention them. Stripping them would
drift the statements away from the source and would cascade into the tagged
`stacks052M_main`, generalising a tagged entity as a side effect of a lint fix. -/
/-- **Definition 1 (domination).** `A` dominates the local domain `R` (Stacks Tag
00I9) iff `R ⊆ A` (the image of `R` in `K` is contained in `A`) and
`𝔪 ⊆ 𝔪_A`: every element of the maximal ideal `𝔪` of `R` maps to a non-unit of
`A`. (By locality of both rings this is equivalent to the original definition
`𝔪 = R ∩ 𝔪_A`.) -/
@[nolint unusedArguments]
def Dominates (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (A : ValuationSubring K) : Prop :=
  (algebraMap R K).range ≤ A.toSubring ∧
    ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R K r ∈ A.nonunits

/-- **Definition 7' (admissible pair).** A *pair* `(I, a)` with `a ∈ I` is
*admissible* (for the valuation ring `A`) if it satisfies the four source
properties (1)–(4) directly:
  1. `I ⊆ 𝔪` (together with the built-in `a ∈ I`, this is `a ∈ I ⊆ 𝔪`),
  2. `I` is finitely generated,
  3. the fibre ring of `R → R[I/a]` at `𝔪` is nonzero (Definition 6 / 4), and
  4. `affineBlowupImage I a ⊆ A` (the source proof's selection criterion).

This predicate refers to the *displayed* pair `(I, a)`, not merely to the subring
it represents; the explicit common refinement of Theorem 1 is stated and proven
about such displayed pairs. Note (3) forces `a ≠ 0`, so `affineBlowupImage` is
only ever applied to nonzero denominators (Definition 5). -/
@[nolint unusedArguments]
def IsAdmissiblePair (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (A : ValuationSubring K) (I : Ideal R) (a : R) (ha : a ∈ I) : Prop :=
  I ≤ IsLocalRing.maximalIdeal R ∧
    I.FG ∧
    FibreNonzero ha ∧
    (affineBlowupImage I a ha : Subring K) ≤ A.toSubring

/-- **Definition 7 (membership in the directed system `𝒮`).** A subring `B ⊆ K`
is an *admissible blowup* (a member of `𝒮`) if `B = affineBlowupImage I a`
(Definition 5) for some *admissible pair* `(I, a)` (Definition 7'). -/
def IsAdmissibleBlowup (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (A : ValuationSubring K) (B : Subring K) : Prop :=
  ∃ (I : Ideal R) (a : R) (ha : a ∈ I),
    B = affineBlowupImage I a ha ∧ IsAdmissiblePair R A I a ha

/-- The canonical ring hom from the localization `Localization.Away a` to `K`,
existing because `a` maps to a unit of `K` (when `a ≠ 0`). -/
noncomputable def awayToFractionField (a : R) (haz : algebraMap R K a ≠ 0) :
    Localization.Away a →+* K :=
  IsLocalization.Away.lift (S := Localization.Away a) a (isUnit_iff_ne_zero.mpr haz)

omit [IsFractionRing R K] in
/-- The localization map followed by `awayToFractionField` is `algebraMap R K`. -/
theorem awayToFractionField_comp (a : R) (haz : algebraMap R K a ≠ 0) (r : R) :
    awayToFractionField a haz (algebraMap R (Localization.Away a) r) = algebraMap R K r := by
  unfold awayToFractionField
  rw [IsLocalization.Away.lift]
  rw [IsLocalization.lift_eq]

omit [IsFractionRing R K] in
/-- `awayToFractionField` sends the localized element `algebraMap a` to `algebraMap a`. -/
theorem awayToFractionField_a (a : R) (haz : algebraMap R K a ≠ 0) :
    awayToFractionField a haz (algebraMap R (Localization.Away a) a) = algebraMap R K a :=
  awayToFractionField_comp a haz a

omit [IsFractionRing R K] in
/-- The image of `affineBlowupAlgebra I a` under `awayToFractionField` is contained
in `affineBlowupImage I a` (as subsets of `K`). -/
theorem awayToFractionField_mem_image {I : Ideal R} {a : R} (ha : a ∈ I)
    (haz : algebraMap R K a ≠ 0)
    {y : Localization.Away a} (hy : y ∈ affineBlowupAlgebra I a ha) :
    awayToFractionField a haz y ∈ affineBlowupImage I a ha := by
  obtain ⟨n, x, hx, hyx⟩ := hy
  refine ⟨n, x, hx, ?_⟩
  have := congrArg (awayToFractionField a haz) hyx
  rw [map_mul, map_pow, awayToFractionField_a, awayToFractionField_comp] at this
  exact this

/-- **FibreNonzero follows from condition (4) + domination.**
If `a ≠ 0`, `I ≤ 𝔪`, and `affineBlowupImage I a ≤ A` with `A` dominating `R`,
then the fibre ring of `R → R[I/a]` at `𝔪` is nonzero. -/
theorem fibreNonzero_of_le [IsLocalRing R] {I : Ideal R} {a : R} (ha : a ∈ I)
    (haz : algebraMap R K a ≠ 0)
    (A : ValuationSubring K) (hdom : Dominates R A)
    (h4 : (affineBlowupImage I a ha : Subring K) ≤ A.toSubring) :
    FibreNonzero ha := by
  have : IsLocalRing A.toSubring := A.isLocalRing
  -- the ring hom B = affineBlowupAlgebra I a → A.toSubring
  set B := affineBlowupAlgebra I a ha
  -- map B → K landing in A
  have himg : ∀ y : B, awayToFractionField a haz (y : Localization.Away a) ∈ A.toSubring :=
    fun y => h4 (awayToFractionField_mem_image ha haz y.property)
  let g : B →+* A.toSubring :=
    RingHom.codRestrict ((awayToFractionField a haz).comp B.subtype) A.toSubring himg
  -- g composed with algebraMap R B equals algebraMap-into-A of r
  have hg_alg : ∀ m : R, g (algebraMap R B m) =
      ⟨algebraMap R K m, h4 (range_le_affineBlowupImage ha ⟨m, rfl⟩)⟩ := by
    intro m
    apply Subtype.ext
    show awayToFractionField a haz ((algebraMap R B m : Localization.Away a)) = algebraMap R K m
    have : (algebraMap R B m : Localization.Away a) = algebraMap R (Localization.Away a) m := rfl
    rw [this, awayToFractionField_comp]
  intro (htop : (IsLocalRing.maximalIdeal R).map (algebraMap R B) = ⊤)
  -- 1 ∈ 𝔪.map (algebraMap R B)
  have h1 : (1 : B) ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R B) := by
    rw [htop]; trivial
  -- apply Ideal.map g
  have h2 : g 1 ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R B)).map g :=
    Ideal.mem_map_of_mem g h1
  -- the mapped ideal is ≤ maximalIdeal of A.toSubring
  have hle : ((IsLocalRing.maximalIdeal R).map (algebraMap R B)).map g ≤
      IsLocalRing.maximalIdeal A.toSubring := by
    rw [Ideal.map_map]
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap]
    -- (g.comp (algebraMap R B)) m = algebraMap-into-A m, a nonunit
    rw [RingHom.comp_apply, hg_alg m]
    -- nonunit in A
    have hlt : A.valuation (algebraMap R K m) < 1 :=
      (A.mem_nonunits_iff).mp (hdom.right m hm)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have : A.valuation (algebraMap R K m) = 1 := (A.valuation_eq_one_iff _).mp hunit
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have : g 1 ∈ IsLocalRing.maximalIdeal A.toSubring := hle h2
  rw [map_one] at this
  exact (IsLocalRing.maximalIdeal A.toSubring).ne_top_iff_one.mp
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top this

/-! ### Decomposition of the main theorem `stacks052M_main` (`𝔪 ≠ 0`)

The 4-way conjunction is split into four named sub-lemmas, one per conjunct:
`stacks052M_C1_nonempty` (nonemptiness), `stacks052M_C3_refinement` (the explicit
product-pair common refinement), `stacks052M_C2_directed` (abstract directedness,
*derived from C3*), and `stacks052M_C4_union` (directed union `= A`). The genuine
mathematical crux is the reverse direction of C4 (every `x ∈ A` lies in some
admissible blowup), which is isolated as `stacks052M_C4_reverse`.

A small shared helper `exists_nonzero_mem_maximalIdeal` produces a nonzero
`a₀ ∈ 𝔪` from `𝔪 ≠ 0`; it powers both C1 and the `I ⊆ 𝔪` arrangement in the C4
crux. -/

/-- **Helper: a nonzero element of `𝔪`.** Since `𝔪 ≠ ⊥`, the maximal ideal (as a
submodule) is not the bottom submodule, so it contains a nonzero element. This is
the only place `hm : 𝔪 ≠ ⊥` is used; it supplies the `a₀` that makes the indexing
ideals land inside `𝔪`. -/
theorem exists_nonzero_mem_maximalIdeal [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) :
    ∃ a₀ : R, a₀ ∈ IsLocalRing.maximalIdeal R ∧ a₀ ≠ 0 := by
  -- `Submodule.exists_mem_ne_zero_of_ne_bot` : `p ≠ ⊥ → ∃ b ∈ p, b ≠ 0`.
  -- The maximal ideal is a submodule; `hm` says it is not `⊥`. The result is the
  -- existence of a nonzero member.  (Mathlib: `Submodule.exists_mem_ne_zero_of_ne_bot`.)
  obtain ⟨a₀, ha₀mem, ha₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  exact ⟨a₀, ha₀mem, ha₀ne⟩

/-- **Helper: `algebraMap R K` is nonzero on nonzero inputs.** Since `R` is a
domain and `K = Frac(R)`, the structure map `R → K` is injective, so it sends
nonzero elements to nonzero elements. Used to discharge the `algebraMap a ≠ 0`
side conditions of `affineBlowupImage_le_of_gen` and `fibreNonzero_of_le`. -/
@[nolint unusedArguments]
theorem algebraMap_ne_zero_of_ne_zero [IsDomain R] {a : R} (ha : a ≠ 0) :
    algebraMap R K a ≠ 0 := by
  -- `IsFractionRing.injective R K : Function.Injective (algebraMap R K)`.
  -- Hence `algebraMap a = 0 = algebraMap 0 ⇒ a = 0`, contradicting `ha`.
  -- (Mathlib: `IsFractionRing.injective`, `map_eq_zero_iff` / `RingHom.injective`.)
  intro h
  exact ha (IsFractionRing.injective R K (by rw [h, map_zero]))

omit [IsFractionRing R K] in
/-- If `affineBlowupImage I a ⊆ S` and `algebraMap a ≠ 0`, then every `i ∈ I` satisfies
`algebraMap i = w · algebraMap a` for some `w ∈ S`. -/
private theorem exists_mul_eq_of_affineBlowupImage_le {I : Ideal R} {a : R} (ha : a ∈ I)
    {S : Subring K} (haz : algebraMap R K a ≠ 0)
    (hS : (affineBlowupImage I a ha : Subring K) ≤ S) :
    ∀ i ∈ I, ∃ w ∈ S, algebraMap R K i = w * algebraMap R K a := by
  intro i hi
  have hy : algebraMap R K i * (algebraMap R K a)⁻¹ ∈ affineBlowupImage I a ha := by
    refine ⟨1, i, by simpa using hi, ?_⟩
    rw [pow_one]
    field_simp
  exact ⟨algebraMap R K i * (algebraMap R K a)⁻¹, hS hy, by field_simp⟩

omit [IsFractionRing R K] in
/-- Containment of affine blowup images for the right factor: if `a ∈ I`, then
`affineBlowupImage J b ⊆ affineBlowupImage (I*J) (a*b)`. -/
private theorem affineBlowupImage_le_mul_left {I J : Ideal R} {a b : R} (ha : a ∈ I) (hb : b ∈ J)
    (hab : a * b ∈ I * J) :
    (affineBlowupImage J b hb : Subring K) ≤ affineBlowupImage (I * J) (a * b) hab := by
  rintro y ⟨n, x, hx, hyx⟩
  refine ⟨n, x * a ^ n, ?_, ?_⟩
  · rw [mul_pow, mul_comm (I ^ n) (J ^ n)]
    exact Ideal.mul_mem_mul hx (Ideal.pow_mem_pow ha n)
  · simp only [map_mul, map_pow, mul_pow]
    linear_combination (algebraMap R K a ^ n) * hyx

/-- **C1 (nonemptiness).** `𝒮 ≠ ∅`: there is an admissible blowup. Take the
principal pair `(I, a) = ((a₀), a₀)` for a nonzero `a₀ ∈ 𝔪` (from
`exists_nonzero_mem_maximalIdeal`). Then `affineBlowupImage (a₀) a₀ = R` (the image
of `R`), because every element `x/a₀ⁿ` with `x ∈ (a₀)ⁿ` is already in `R`. The four
admissibility conditions:
  (1) `(a₀) ≤ 𝔪` since `a₀ ∈ 𝔪` (`Ideal.span_le` / `Ideal.span_singleton_le_iff_mem`);
  (2) `(a₀)` is finitely generated (principal: `Ideal.fg_span_singleton` / `⟨{a₀}, …⟩`);
  (4) `affineBlowupImage (a₀) a₀ ≤ A`: since the image is `R`'s image, this is
      `hdom.1` after identifying `affineBlowupImage (a₀) a₀ = (algebraMap R K).range`;
  (3) `FibreNonzero` via `fibreNonzero_of_le` (needs `a₀ ≠ 0 ⇒ algebraMap a₀ ≠ 0`
      by `algebraMap_ne_zero_of_ne_zero`, `(a₀) ≤ 𝔪`, and (4) + `hdom`).
The witness blowup is `B = affineBlowupImage (Ideal.span {a₀}) a₀ _`. -/
theorem stacks052M_C1_nonempty
    [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥)
    (A : ValuationSubring K) (hdom : Dominates R A) :
    ∃ B, IsAdmissibleBlowup R A B := by
  obtain ⟨a₀, ha₀mem, ha₀ne⟩ := exists_nonzero_mem_maximalIdeal hm
  have ha : a₀ ∈ Ideal.span {a₀} := Ideal.mem_span_singleton_self a₀
  have haz : algebraMap R K a₀ ≠ 0 := algebraMap_ne_zero_of_ne_zero ha₀ne
  have hgen : ∀ i ∈ Ideal.span {a₀}, ∃ w ∈ A.toSubring,
      algebraMap R K i = w * algebraMap R K a₀ := by
    refine gen_cond_of_span A.toSubring hdom.left {a₀} ?_
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨1, one_mem _, by rw [one_mul]⟩
  have h4 : (affineBlowupImage (Ideal.span {a₀}) a₀ ha : Subring K) ≤ A.toSubring :=
    affineBlowupImage_le_of_gen ha A.toSubring haz hdom.left hgen
  have h3 : FibreNonzero ha := fibreNonzero_of_le ha haz A hdom h4
  refine ⟨affineBlowupImage (Ideal.span {a₀}) a₀ ha, Ideal.span {a₀}, a₀, ha, rfl, ?_, ?_, h3, h4⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact ha₀mem
  · exact ⟨{a₀}, by rw [Finset.coe_singleton]⟩

/-- **C3 (explicit common refinement).** For two admissible pairs `(I, a)`,
`(J, b)`, the displayed product pair `(I*J, a*b)` is admissible and its subring
contains both factors. The membership `hab : a*b ∈ I*J` is `Ideal.mul_mem_mul ha hb`.
Admissibility of `(I*J, a*b)`:
  (1) `I*J ≤ 𝔪`: `I*J ≤ J ≤ 𝔪` via `Ideal.mul_le_right` and the (1)-component of
      the `(J,b)` pair;
  (2) `(I*J).FG`: `Ideal.FG.mul` of the two (2)-components;
  (4) `affineBlowupImage (I*J) (a*b) ≤ A`: use `affineBlowupImage_le_of_gen` with
      `S = A.toSubring`. Need `algebraMap (a*b) ≠ 0` (from `a,b ≠ 0` derived from
      the two `FibreNonzero` components via `not_fibreNonzero_of_zero`, then
      `algebraMap_ne_zero_of_ne_zero` and `map_mul`), `range ≤ A` (`hdom.1`), and
      the generator-divisibility `∀ k ∈ I*J, ∃ w ∈ A, algebraMap k = w·algebraMap(a*b)`.
      The latter is proven by `Submodule.mul_induction_on`: on a product `k = i*j`
      with `i ∈ I, j ∈ J`, write `algebraMap i = wᵢ·algebraMap a` and
      `algebraMap j = wⱼ·algebraMap b` (the (4)-components of the two pairs give
      `i/a, j/b ∈ A`; concretely apply `affineBlowupImage_le_of_gen`-style
      divisibility, or directly: `i/a ∈ affineBlowupImage I a ⊆ A`), so
      `algebraMap (i*j) = (wᵢwⱼ)·algebraMap (a*b)` with `wᵢwⱼ ∈ A`; closed under
      `+` and `R`-scaling.
  (3) `FibreNonzero (I*J) (a*b)` via `fibreNonzero_of_le`.
The two containments are `affineBlowupImage_le_mul ha hb hab` (for the `(I,a)`
factor) and its symmetric variant for `(J,b)` (which needs `b ∈ J`, `a ∈ I`, and
`a*b ∈ I*J = J*I` after `mul_comm`; reuse `affineBlowupImage_le_mul hb ha` into
`affineBlowupImage (J*I) (b*a)` then transport along `mul_comm` for both `I*J` and
`a*b`). -/
theorem stacks052M_C3_refinement
    [IsDomain R] [IsLocalRing R]
    (A : ValuationSubring K) (hdom : Dominates R A) :
    ∀ (I J : Ideal R) (a b : R) (ha : a ∈ I) (hb : b ∈ J),
        IsAdmissiblePair R A I a ha →
        IsAdmissiblePair R A J b hb →
        ∃ (hab : a * b ∈ I * J),
          IsAdmissiblePair R A (I * J) (a * b) hab ∧
          (affineBlowupImage I a ha : Subring K) ≤ affineBlowupImage (I * J) (a * b) hab ∧
          (affineBlowupImage J b hb : Subring K) ≤ affineBlowupImage (I * J) (a * b) hab := by
  intro I J a b ha hb hIadm hJadm
  obtain ⟨hI_le, hI_fg, hI_fib, hI_4⟩ := hIadm
  obtain ⟨hJ_le, hJ_fg, hJ_fib, hJ_4⟩ := hJadm
  refine ⟨Ideal.mul_mem_mul ha hb, ?_, ?_, ?_⟩
  · have hane := ne_zero_of_fibreNonzero ha hI_fib
    have hbne := ne_zero_of_fibreNonzero hb hJ_fib
    have haz : algebraMap R K (a * b) ≠ 0 := algebraMap_ne_zero_of_ne_zero (mul_ne_zero hane hbne)
    have hdivI := exists_mul_eq_of_affineBlowupImage_le ha
      (algebraMap_ne_zero_of_ne_zero hane) hI_4
    have hdivJ := exists_mul_eq_of_affineBlowupImage_le hb
      (algebraMap_ne_zero_of_ne_zero hbne) hJ_4
    have hgen : ∀ k ∈ I * J, ∃ w ∈ A.toSubring,
        algebraMap R K k = w * algebraMap R K (a * b) := by
      intro k hk
      refine Submodule.mul_induction_on hk ?_ ?_
      · intro i hi j hj
        obtain ⟨wi, hwi, hieq⟩ := hdivI i hi
        obtain ⟨wj, hwj, hjeq⟩ := hdivJ j hj
        refine ⟨wi * wj, mul_mem hwi hwj, ?_⟩
        rw [map_mul, hieq, hjeq, map_mul]
        ring
      · rintro x y ⟨wx, hwx, hxeq⟩ ⟨wy, hwy, hyeq⟩
        refine ⟨wx + wy, add_mem hwx hwy, ?_⟩
        rw [map_add, hxeq, hyeq, add_mul]
    have h4 : (affineBlowupImage (I * J) (a * b) (Ideal.mul_mem_mul ha hb) : Subring K) ≤
        A.toSubring :=
      affineBlowupImage_le_of_gen (Ideal.mul_mem_mul ha hb) A.toSubring haz hdom.left hgen
    refine ⟨?_, hI_fg.mul hJ_fg, ?_, h4⟩
    · exact le_trans Ideal.mul_le_right hJ_le
    · exact fibreNonzero_of_le (Ideal.mul_mem_mul ha hb) haz A hdom h4
  · exact affineBlowupImage_le_mul ha hb (Ideal.mul_mem_mul ha hb)
  · exact affineBlowupImage_le_mul_left ha hb (Ideal.mul_mem_mul ha hb)

/-- **C2 (abstract directedness).** `{B | IsAdmissibleBlowup R A B}` is directed
under `≤`. Unfolding `DirectedOn`: given `B₁, B₂` in the set, produce `B₃` in the
set with `B₁ ≤ B₃`, `B₂ ≤ B₃`. Destructure `B₁ = affineBlowupImage I a`,
`B₂ = affineBlowupImage J b` from their `IsAdmissibleBlowup` witnesses (with
admissible pairs `(I,a)`, `(J,b)`), feed them to `stacks052M_C3_refinement` to get
the product pair `(I*J, a*b)` — admissible, hence `B₃ := affineBlowupImage (I*J)(a*b)`
is in the set — together with the two containments `B₁ ≤ B₃`, `B₂ ≤ B₃`. This is a
pure assembly step; no new mathematical content beyond C3. -/
theorem stacks052M_C2_directed
    [IsDomain R] [IsLocalRing R]
    (A : ValuationSubring K) (hdom : Dominates R A) :
    DirectedOn (· ≤ ·) {B | IsAdmissibleBlowup R A B} := by
  intro B₁ hB₁ B₂ hB₂
  obtain ⟨I, a, ha, hBeq, hIadm⟩ := hB₁
  obtain ⟨J, b, hb, hBeq2, hJadm⟩ := hB₂
  obtain ⟨hab, hadm3, hle1, hle2⟩ :=
    stacks052M_C3_refinement A hdom I J a b ha hb hIadm hJadm
  refine ⟨affineBlowupImage (I * J) (a * b) hab, ⟨I * J, a * b, hab, rfl, hadm3⟩, ?_, ?_⟩
  · rw [hBeq]; exact hle1
  · rw [hBeq2]; exact hle2

/-- **C4 reverse — the crux.** Every `x ∈ A`
lies in some admissible blowup. Construction: write `x = algebraMap f / algebraMap a`
with `f, a ∈ R`, `a ≠ 0` (common denominator from
`IsFractionRing.div_surjective`/`IsLocalization.mk'`, giving `x * algebraMap a = algebraMap f`).
Pick a nonzero `a₀ ∈ 𝔪` (`exists_nonzero_mem_maximalIdeal`) and replace `(f, a)`
by `(f·a₀, a·a₀)` — this does not change the fraction `x = f/a = (f·a₀)/(a·a₀)`.
Set `I = Ideal.span {f·a₀, a·a₀}` and denominator `c = a·a₀ ∈ I`. Then:
  • `a·a₀ ≠ 0` (domain, `a,a₀ ≠ 0`) so `algebraMap c ≠ 0`;
  • `I ≤ 𝔪`: both generators are multiples of `a₀ ∈ 𝔪`, so lie in `𝔪`
    (`Ideal.span_le`, `Ideal.mul_mem_left`/`Ideal.mul_mem_right` of `a₀ ∈ 𝔪`);
  • `I.FG`: span of a finite set (`Ideal.fg_span` of a finite set);
  • `affineBlowupImage I c ≤ A`: by `affineBlowupImage_le_of_gen` + `gen_cond_of_span`
    with generating set `{f·a₀, a·a₀}`. The divisibility witnesses:
      – for `f·a₀`: `algebraMap (f·a₀) = x · algebraMap (a·a₀)`, since
        `x·algebraMap(a·a₀) = x·algebraMap a·algebraMap a₀ = algebraMap f·algebraMap a₀
        = algebraMap (f·a₀)`; witness `w = x ∈ A` (`x ∈ A` is the hypothesis);
      – for `a·a₀`: `algebraMap (a·a₀) = 1 · algebraMap (a·a₀)`; witness `w = 1 ∈ A`.
  • `FibreNonzero I c` via `fibreNonzero_of_le`.
This gives an admissible pair `(I, c)`. Finally `x ∈ affineBlowupImage I c`: take
`n = 1`, numerator `f·a₀ ∈ I¹ = I`, and `x · algebraMap c = algebraMap (f·a₀)` (the
first divisibility identity), i.e. `x ∈ affineBlowupImage I c` by `mem_affineBlowupImage`.
Witness `B = affineBlowupImage I c`. -/
theorem stacks052M_C4_reverse
    [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥)
    (A : ValuationSubring K) (hdom : Dominates R A) :
    ∀ x : K, x ∈ A → ∃ B, IsAdmissibleBlowup R A B ∧ x ∈ B := by
  intro x hx
  -- Step 1: write x as a fraction f / a over R
  obtain ⟨f, a, hane, hfa⟩ : ∃ (f a : R), a ≠ 0 ∧ x * algebraMap R K a = algebraMap R K f := by
    have h := IsLocalization.surj (M := nonZeroDivisors R) x
    obtain ⟨fa, hfa⟩ := h
    refine ⟨fa.fst, (fa.snd : R), nonZeroDivisors.ne_zero fa.snd.property, hfa⟩
  -- Step 2: nonzero element of the maximal ideal
  obtain ⟨a₀, ha₀mem, ha₀ne⟩ := exists_nonzero_mem_maximalIdeal hm
  -- Step 3: c = a * a₀
  set c : R := a * a₀ with hc
  have hcne : c ≠ 0 := mul_ne_zero hane ha₀ne
  have hcz : algebraMap R K c ≠ 0 := algebraMap_ne_zero_of_ne_zero hcne
  -- Step 4: the ideal I and membership of c
  set I : Ideal R := Ideal.span {f * a₀, a * a₀} with hI
  have hcI : c ∈ I := by
    rw [hI, hc]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  -- The first divisibility identity: algebraMap (f*a₀) = x * algebraMap (a*a₀)
  have hdiv1 : algebraMap R K (f * a₀) = x * algebraMap R K (a * a₀) := by
    rw [map_mul, map_mul]
    rw [show x * (algebraMap R K a * algebraMap R K a₀)
          = (x * algebraMap R K a) * algebraMap R K a₀ by ring]
    rw [hfa]
  -- generator divisibility condition
  have hgen : ∀ i ∈ I, ∃ w ∈ A.toSubring, algebraMap R K i = w * algebraMap R K c := by
    rw [hI]
    refine gen_cond_of_span A.toSubring hdom.left {f * a₀, a * a₀} ?_
    intro g hg
    rcases hg with hg | hg
    · subst hg
      exact ⟨x, hx, by rw [hc]; exact hdiv1⟩
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact ⟨1, one_mem _, by rw [hc, one_mul]⟩
  -- condition (4)
  have h4 : (affineBlowupImage I c hcI : Subring K) ≤ A.toSubring :=
    affineBlowupImage_le_of_gen hcI A.toSubring hcz hdom.left hgen
  -- condition (3)
  have h3 : FibreNonzero hcI := fibreNonzero_of_le hcI hcz A hdom h4
  -- final membership x ∈ affineBlowupImage I c
  have hxmem : x ∈ affineBlowupImage I c hcI := by
    rw [mem_affineBlowupImage hcI]
    refine ⟨1, f * a₀, ?_, ?_⟩
    · rw [pow_one, hI]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [pow_one, hc]
      exact hdiv1.symm
  refine ⟨affineBlowupImage I c hcI, ⟨I, c, hcI, rfl, ?_, ?_, h3, h4⟩, hxmem⟩
  · -- condition (1): I ≤ 𝔪
    rw [hI, Ideal.span_le]
    intro y hy
    rcases hy with hy | hy
    · subst hy
      exact Ideal.mul_mem_left _ _ ha₀mem
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Ideal.mul_mem_left _ _ ha₀mem
  · -- condition (2): I.FG
    rw [hI]
    exact Submodule.fg_span ((Set.finite_singleton _).insert _)
/-- **C4 (directed union `= A`).** `x ∈ A ↔ ∃ B ∈ 𝒮, x ∈ B`.
  • Forward (`x ∈ A → ∃ B`): this is exactly `stacks052M_C4_reverse`.
  • Backward (`∃ B ∈ 𝒮, x ∈ B → x ∈ A`): if `x ∈ B = affineBlowupImage I a` with
    `(I,a)` admissible, then condition (4) of admissibility says
    `affineBlowupImage I a ≤ A.toSubring`, so `x ∈ A`. (Easy direction; just
    destructure the `IsAdmissibleBlowup` witness and apply its (4)-component.) -/
theorem stacks052M_C4_union
    [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥)
    (A : ValuationSubring K) (hdom : Dominates R A) :
    ∀ x : K, x ∈ A ↔ ∃ B, IsAdmissibleBlowup R A B ∧ x ∈ B := by
  intro x
  constructor
  · -- forward: this is exactly stacks052M_C4_reverse
    exact fun hx => stacks052M_C4_reverse hm A hdom x hx
  · -- backward: condition (4) of admissibility gives x ∈ A
    rintro ⟨B, ⟨I, a, ha, rfl, _, _, _, h4⟩, hxB⟩
    exact h4 hxB

/-- **Theorem 1 (Stacks Tag 052M, main case `𝔪 ≠ 0`).**
Let `(R, 𝔪)` be a local domain with fraction field `K`, and assume `𝔪 ≠ 0`.
Let `A` be a valuation ring of `K` which dominates `R`. Then the family `𝒮` of
admissible affine blowup algebras of Definition 7:

1. is **nonempty** and **directed** under inclusion, and moreover for any two
   *admissible pairs* `(I, a)`, `(J, b)` (Definition 7'), the explicit displayed
   product pair `(I*J, a*b)` is again an admissible pair, and its associated
   subring `affineBlowupImage (I*J) (a*b)` contains both
   `affineBlowupImage I a` and `affineBlowupImage J b`; and
2. has **directed union equal to `A`**: an element `x ∈ K` lies in `A` iff it
   lies in some member of `𝒮`.

Assembled from the four conjunct lemmas `stacks052M_C1_nonempty`,
`stacks052M_C2_directed`, `stacks052M_C3_refinement`, `stacks052M_C4_union`. -/
@[stacks 052M]
theorem stacks052M_main
    [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥)
    (A : ValuationSubring K) (hdom : Dominates R A) :
    -- (1a) nonemptiness
    (∃ B, IsAdmissibleBlowup R A B) ∧
    -- (1b) abstract directedness under inclusion
    DirectedOn (· ≤ ·) {B | IsAdmissibleBlowup R A B} ∧
    -- (1c) the explicit common refinement `R[IJ/(ab)]` of two admissible pairs:
    -- the displayed product pair `(I*J, a*b)` is itself an admissible pair, and
    -- its subring contains both factors.
    (∀ (I J : Ideal R) (a b : R) (ha : a ∈ I) (hb : b ∈ J),
        IsAdmissiblePair R A I a ha →
        IsAdmissiblePair R A J b hb →
        ∃ (hab : a * b ∈ I * J),
          IsAdmissiblePair R A (I * J) (a * b) hab ∧
          (affineBlowupImage I a ha : Subring K) ≤ affineBlowupImage (I * J) (a * b) hab ∧
          (affineBlowupImage J b hb : Subring K) ≤ affineBlowupImage (I * J) (a * b) hab) ∧
    -- (2) the directed union equals A
    (∀ x : K, x ∈ A ↔ ∃ B, IsAdmissibleBlowup R A B ∧ x ∈ B) :=
  ⟨stacks052M_C1_nonempty hm A hdom,
   stacks052M_C2_directed A hdom,
   stacks052M_C3_refinement A hdom,
   stacks052M_C4_union hm A hdom⟩

/-- **Theorem 2 (degenerate field case `𝔪 = 0`).**
Let `(R, 𝔪)` be a local domain with `𝔪 = 0` (equivalently `R` is a field, so
the canonical image of `R` in `K` is all of `K`). Let `A` be a valuation ring of
`K` dominating `R`. Then `A = R = K`: the underlying subring of `A` equals the
image of `R`, which equals the whole field. -/
@[nolint unusedArguments]
theorem stacks052M_field
    [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R = ⊥)
    (A : ValuationSubring K) (hdom : Dominates R A) :
    A.toSubring = (algebraMap R K).range ∧ (algebraMap R K).range = (⊤ : Subring K) := by
  have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  have hsurj : Function.Surjective (algebraMap R K) := by
    let : Field R := hfield.toField
    intro z
    obtain ⟨r, s, -, hrs⟩ := IsFractionRing.div_surjective (A := R) z
    exact ⟨r * s⁻¹, by rw [map_mul, map_inv₀, ← hrs, div_eq_mul_inv]⟩
  have hrange : (algebraMap R K).range = ⊤ := RingHom.range_eq_top.mpr hsurj
  refine ⟨le_antisymm ?_ hdom.left, hrange⟩
  rw [hrange]
  exact le_top

/-- **No admissible pair exists when `𝔪 = 0`.**
Let `(R, 𝔪)` be a local domain with `𝔪 = 0` (equivalently, `R` is a field) and let
`A` be a valuation ring of its fraction field `K`. Then no pair `(I, a)` with
`a ∈ I` is admissible in the sense of Definition 7': from `I ⊆ 𝔪 = 0` we get
`I = 0`, hence `a = 0`, and then the affine blowup algebra `R[I/a]` is the zero
ring, so its fibre ring at `𝔪` vanishes and condition (3) fails
(`not_fibreNonzero_of_zero`). Note that the argument does not need the
nonvanishing of `a` as a separate hypothesis: condition (3) alone is already
contradictory.

This records a gap in the source statement of Stacks Tag 053I. That lemma asserts,
for a local domain `(R, 𝔪)` with fraction field `K`, a finite type `R`-algebra `S`,
a finite `S`-module `M` and a valuation ring `A ⊆ K` dominating `R`, the
*existence* of an ideal `I ⊆ 𝔪` and a nonzero `a ∈ I` satisfying conditions
(1)–(4), without excluding the case `𝔪 = 0`. The hypotheses of 053I are
satisfiable there — for `R` a field, `R = A = K` is a local domain dominated by
the valuation ring `K` — while by this lemma the conclusion is not, so the source
statement needs the extra hypothesis `𝔪 ≠ 0`; the formalization of 053I carries
it.

This mirrors the precedent set for the immediately preceding lemma 052M, whose
main case `stacks052M_main` assumes `𝔪 ≠ ⊥` and whose degenerate case is recorded
separately in `stacks052M_field`. -/
@[nolint unusedArguments]
theorem no_admissiblePair_of_maximalIdeal_eq_bot
    [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R = ⊥)
    (A : ValuationSubring K) :
    ∀ (I : Ideal R) (a : R) (ha : a ∈ I), ¬ IsAdmissiblePair R A I a ha := by
  rintro I a ha ⟨h1, -, h3, -⟩
  -- Condition (1) gives `a ∈ I ≤ 𝔪 = ⊥`, hence `a = 0`, contradicting condition (3).
  have hmem : a ∈ (⊥ : Ideal R) := by rw [← hm]; exact h1 ha
  exact ne_zero_of_fibreNonzero ha h3 (by simpa using hmem)

/-- **No admissible blowup exists when `𝔪 = 0`.**
The subring form of `no_admissiblePair_of_maximalIdeal_eq_bot`: for a local domain
`(R, 𝔪)` with `𝔪 = 0` and `A` a valuation ring of `K`, the family `𝒮` of
Definition 7 is empty, since every member of it is presented by an admissible pair.

As with `no_admissiblePair_of_maximalIdeal_eq_bot`, this records the gap in the
source statement of Stacks Tag 053I, which asserts the existence of a pair
satisfying conditions (1)–(4) without excluding `𝔪 = 0`. -/
theorem not_isAdmissibleBlowup_of_maximalIdeal_eq_bot
    [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R = ⊥)
    (A : ValuationSubring K) :
    ∀ B : Subring K, ¬ IsAdmissibleBlowup R A B := by
  rintro B ⟨I, a, ha, -, hpair⟩
  exact no_admissiblePair_of_maximalIdeal_eq_bot hm A I a ha hpair

end Stacks.AffineBlowup

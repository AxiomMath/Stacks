module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecTruncation

/-!
# The graded localization theorem for the truncation algebra

Let `A` be an `ℕ`-graded ring, `B` its truncation algebra and `f ∈ A` homogeneous of degree `d`.
We compare the degree-zero part `(B_{ψ f})₀` of the localization of `B` at `ψ f` with the
localization `A_f`, and their graded pieces.

## Main definitions

* `Stacks.Truncation.awayFrac`: the fraction `a / f ^ k` in `A_f`.
* `Stacks.Truncation.forgetDegree`: the ring map `B → A` sending `a⁽ᵈ⁾` to `a`.
* `Stacks.Truncation.awayElt`: the element `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` of `(B_{ψ f})₀`.
* `Stacks.Truncation.awayToLocalization`: the ring map `(B_{ψ f})₀ → A_f`.
* `Stacks.Truncation.awayPiece`: the degree-`m` part `(A_f)_m` of `A_f`.
* `Stacks.Truncation.awayGrading`: the degree-`m` part of `(B_{ψ f})₀`.

## Main results

* `Stacks.Truncation.awayElt_surjective`: every element of `(B_{ψ f})₀` is of the form
  `a⁽ᵏᵈ⁾ / (ψ f)ᵏ`.
* `Stacks.Truncation.awayToLocalization_injective`: the map `(B_{ψ f})₀ → A_f` is injective.
* `Stacks.Truncation.exists_mem_awayGrading`: the map `(B_{ψ f})₀ → A_f` carries the degree-`m`
  part of `(B_{ψ f})₀` onto `(A_f)_m`.
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.Truncation

universe u

/-! ### Fractions with a power of a fixed element as denominator -/

section Fractions

variable {A : Type u} [CommRing A] (f : A)

/-- The element `f ^ 0` of `Submonoid.powers f` is `1`. -/
private theorem powers_mk_zero : (⟨f ^ 0, 0, rfl⟩ : Submonoid.powers f) = 1 :=
  Subtype.ext (pow_zero f)

/-- Multiplying the elements `f ^ k` and `f ^ l` of `Submonoid.powers f` gives `f ^ (k + l)`. -/
private theorem powers_mk_mul (k l : ℕ) :
    (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) * ⟨f ^ l, l, rfl⟩ = ⟨f ^ (k + l), k + l, rfl⟩ :=
  Subtype.ext (pow_add f k l).symm

/-- The fraction `a / f ^ k`, as an element of the localization `A_f`. -/
def awayFrac (k : ℕ) (a : A) : Localization.Away f :=
  Localization.mk a ⟨f ^ k, k, rfl⟩

/-- `0 / f ^ k = 0`. -/
@[simp]
theorem awayFrac_zero (k : ℕ) : awayFrac f k 0 = 0 :=
  Localization.mk_zero _

/-- `1 / f ^ 0 = 1`. -/
theorem awayFrac_one : awayFrac f 0 1 = 1 := by
  rw [awayFrac, powers_mk_zero f,
    Localization.mk_one]

/-- Adding two fractions clears the denominators: `a / f ^ k + b / f ^ l` is the fraction
with numerator `f ^ k * b + f ^ l * a` and denominator `f ^ (k + l)`. -/
theorem awayFrac_add (k l : ℕ) (a b : A) :
    awayFrac f k a + awayFrac f l b = awayFrac f (k + l) (f ^ k * b + f ^ l * a) := by
  rw [awayFrac, awayFrac, Localization.add_mk, awayFrac,
    powers_mk_mul f k l]

/-- `-(a / f ^ k) = (-a) / f ^ k`. -/
theorem awayFrac_neg (k : ℕ) (a : A) : -awayFrac f k a = awayFrac f k (-a) :=
  Localization.neg_mk _ _

/-- `(a / f ^ k) * (b / f ^ l) = (a * b) / f ^ (k + l)`. -/
theorem awayFrac_mul (k l : ℕ) (a b : A) :
    awayFrac f k a * awayFrac f l b = awayFrac f (k + l) (a * b) := by
  rw [awayFrac, awayFrac, Localization.mk_mul, awayFrac,
    powers_mk_mul f k l]

/-- Enlarging the denominator: `a / f ^ k = (f ^ n * a) / f ^ (k + n)`. -/
theorem awayFrac_shift (k n : ℕ) (a : A) :
    awayFrac f k a = awayFrac f (k + n) (f ^ n * a) := by
  rw [awayFrac, awayFrac, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [pow_add]; ring⟩

/-- A fraction vanishes exactly when a power of `f` kills its numerator. -/
theorem awayFrac_eq_zero_iff (k : ℕ) (a : A) :
    awayFrac f k a = 0 ↔ ∃ n : ℕ, f ^ n * a = 0 := by
  rw [awayFrac, Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨⟨f ^ n, n, rfl⟩, hn⟩⟩
  obtain ⟨⟨v, n, hn⟩, h⟩ := h
  exact ⟨n, by rw [show f ^ n = v from hn]; simpa using h⟩

/-- A fraction with denominator `f ^ 0` is the image of its numerator. -/
theorem awayFrac_zero_eq_algebraMap (a : A) :
    awayFrac f 0 a = algebraMap A (Localization.Away f) a := by
  rw [awayFrac, powers_mk_zero f,
    Localization.mk_one_eq_algebraMap]

/-- `f / f = 1`. -/
theorem awayFrac_self : awayFrac f 1 f = 1 := by
  rw [awayFrac, show (⟨f ^ 1, 1, rfl⟩ : Submonoid.powers f) = ⟨f, 1, pow_one f⟩ from
    Subtype.ext (pow_one f)]
  exact Localization.mk_self (⟨f, 1, pow_one f⟩ : Submonoid.powers f)

/-- Powers of the inverse `1 / f` of `f`. -/
theorem awayFrac_one_one_pow (n : ℕ) : awayFrac f 1 (1 : A) ^ n = awayFrac f n 1 := by
  induction n with
  | zero => rw [pow_zero, awayFrac_one]
  | succ n ih => rw [pow_succ, ih, awayFrac_mul, mul_one, add_comm]

/-- A finite sum of fractions with a common denominator. -/
theorem awayFrac_sum (S : Finset ℕ) (k : ℕ) (c : ℕ → A) :
    ∑ m ∈ S, awayFrac f k (c m) = awayFrac f k (∑ m ∈ S, c m) :=
  (Localization.mk_sum c S _).symm

end Fractions

/-! ### Forgetting the degree of an element of the truncation algebra -/

section Forget

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜]

/-- The ring map `B → A` forgetting the degree: it sends `a⁽ᵈ⁾` to `a`. -/
def forgetDegree : TruncationRing 𝒜 →+* A :=
  DirectSum.toSemiring (fun e ↦ AddSubgroupClass.subtype (truncation 𝒜 e)) rfl fun _ _ ↦ rfl

omit [AddSubgroupClass σ A] in
/-- Forgetting the degree sends `a⁽ᵈ⁾` to `a`. -/
@[simp]
theorem forgetDegree_degElt (d : ℕ) (a : A) (ha : a ∈ truncation 𝒜 d) :
    forgetDegree 𝒜 (degElt 𝒜 d a ha) = a :=
  DirectSum.toSemiring_of _ _ _ _ _

end Forget

/-! ### The comparison ring map `(B_{ψ f})₀ → A_f` -/

section Compare

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

omit [CommRing A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- Two homogeneous parts in equal degrees have the same elements. -/
private theorem mem_graded_of_eq {i j : ℕ} (h : i = j) {a : A} (ha : a ∈ 𝒜 i) : a ∈ 𝒜 j :=
  h ▸ ha

/-- Forgetting the degree undoes `ψ`. -/
@[simp]
theorem forgetDegree_psi (a : A) : forgetDegree 𝒜 (psi 𝒜 a) = a := by
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_ a
  · rw [map_zero, map_zero]
  · intro e x
    rw [psi_eq_degElt 𝒜 (x : A) x.2, forgetDegree_degElt]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

variable (d : ℕ) {f : A}

/-- `(ψ f)ᵏ = (f ᵏ)⁽ᵏᵈ⁾` for `f` homogeneous of degree `d`. -/
theorem psi_pow_eq_degElt (hf : f ∈ 𝒜 d) (k : ℕ) :
    psi 𝒜 f ^ k =
      degElt 𝒜 (k * d) (f ^ k)
        (pow_mem_truncation 𝒜 (mem_truncation_of_mem 𝒜 le_rfl hf) k) := by
  rw [psi_eq_degElt 𝒜 f hf, degElt_pow]

/-- `(ψ f)ᵏ` is homogeneous of degree `k * d`. -/
theorem psi_pow_mem_grading (hf : f ∈ 𝒜 d) (k : ℕ) :
    psi 𝒜 f ^ k ∈ grading 𝒜 (k * d) := by
  rw [psi_pow_eq_degElt 𝒜 d hf k]
  exact degElt_mem_grading _ _ _ _

/-- The element `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` of the degree-zero part `(B_{ψ f})₀` of the localization of
the truncation algebra at `ψ f`. -/
def awayElt (hf : f ∈ 𝒜 d) (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * d)) :
    HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f) :=
  HomogeneousLocalization.mk
    ⟨k * d, ⟨degElt 𝒜 (k * d) a ha, degElt_mem_grading 𝒜 (k * d) a ha⟩,
      ⟨psi 𝒜 f ^ k, psi_pow_mem_grading 𝒜 d hf k⟩, ⟨k, rfl⟩⟩

/-- The image of `ψ f` under the composite `B → A → A_f` times `1 / f` is `1`. -/
theorem comp_psi_mul_awayFrac :
    ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜)) (psi 𝒜 f) *
      awayFrac f 1 1 = 1 := by
  rw [RingHom.comp_apply, forgetDegree_psi, ← awayFrac_zero_eq_algebraMap, awayFrac_mul,
    mul_one, zero_add, awayFrac_self]

/-- The comparison map `(B_{ψ f})₀ → A_f`: the composite of the inclusion of `(B_{ψ f})₀` into
`B_{ψ f}` with the map induced on localizations by `forgetDegree`. -/
def awayToLocalization :
    HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f) →+* Localization.Away f :=
  (Localization.awayLift ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜))
      (psi 𝒜 f)
      (isUnit_iff_exists_inv.mpr ⟨awayFrac f 1 1, comp_psi_mul_awayFrac 𝒜⟩)).comp
    (algebraMap (HomogeneousLocalization (grading 𝒜) (Submonoid.powers (psi 𝒜 f)))
      (Localization (Submonoid.powers (psi 𝒜 f))))

/-- The comparison map sends `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` to `a / f ᵏ`. -/
theorem awayToLocalization_awayElt (hf : f ∈ 𝒜 d) (k : ℕ) (a : A)
    (ha : a ∈ truncation 𝒜 (k * d)) :
    awayToLocalization 𝒜 (awayElt 𝒜 d hf k a ha) = awayFrac f k a := by
  rw [awayToLocalization, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    awayElt, HomogeneousLocalization.val_mk,
    Localization.awayLift_mk _ _ _ _ (comp_psi_mul_awayFrac 𝒜) k, RingHom.comp_apply,
    forgetDegree_degElt, ← awayFrac_zero_eq_algebraMap, awayFrac_one_one_pow, awayFrac_mul,
    mul_one, zero_add]

omit [AddSubgroupClass σ A] in
/-- A homogeneous element of `B` of degree `e` is of the form `a⁽ᵉ⁾`. -/
theorem exists_eq_degElt {e : ℕ} {x : TruncationRing 𝒜} (hx : x ∈ grading 𝒜 e) :
    ∃ (a : A) (ha : a ∈ truncation 𝒜 e), x = degElt 𝒜 e a ha := by
  obtain ⟨a, ha⟩ := (mem_grading_iff 𝒜).mp hx
  exact ⟨(a : A), a.2, by rw [degElt_eq_of, ← ha]⟩

/-- Every element of `(B_{ψ f})₀` is a fraction `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` with `a ∈ A_{≥ kd}`. -/
theorem awayElt_surjective (hf : f ∈ 𝒜 d)
    (y : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :
    ∃ (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * d)), awayElt 𝒜 d hf k a ha = y := by
  obtain ⟨k, x, hx, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading 𝒜) (GradedRingHom.map_mem (psi 𝒜) hf) y
  obtain ⟨a, ha, rfl⟩ := exists_eq_degElt 𝒜 (mem_graded_of_eq (grading 𝒜) (nsmul_eq_mul k d) hx)
  exact ⟨k, a, ha, congrArg HomogeneousLocalization.mk
    (HomogeneousLocalization.NumDenSameDeg.ext _ (nsmul_eq_mul k d).symm rfl rfl)⟩

/-- A fraction `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` vanishes as soon as a power of `f` kills `a`. -/
theorem awayElt_eq_zero (hf : f ∈ 𝒜 d) (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * d)) (n : ℕ)
    (hn : f ^ n * a = 0) : awayElt 𝒜 d hf k a ha = 0 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [awayElt, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨psi 𝒜 f ^ n, n, rfl⟩, ?_⟩
  change psi 𝒜 f ^ n * degElt 𝒜 (k * d) a ha = 0
  rw [psi_pow_eq_degElt 𝒜 d hf n, degElt_mul, degElt_congr 𝒜 rfl hn _ (zero_mem _),
    degElt_zero]

/-- The comparison map `(B_{ψ f})₀ → A_f` is injective. -/
theorem awayToLocalization_injective (hf : f ∈ 𝒜 d) :
    Function.Injective (awayToLocalization 𝒜 (f := f)) := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_
  obtain ⟨k, a, ha, rfl⟩ := awayElt_surjective 𝒜 d hf y
  rw [awayToLocalization_awayElt 𝒜 d hf k a ha, awayFrac_eq_zero_iff] at hy
  exact awayElt_eq_zero 𝒜 d hf k a ha _ hy.choose_spec

/-! ### The graded pieces of `A_f` and of `(B_{ψ f})₀` -/

/-- The degree-`m` part `(A_f)_m` of the localization of `A` at a homogeneous element `f` of
degree `d`: the fractions `a / f ᵏ` whose numerator is homogeneous of degree `m + kd`. -/
def awayPiece (hf : f ∈ 𝒜 d) (m : ℕ) : AddSubgroup (Localization.Away f) where
  carrier := {z | ∃ (k : ℕ) (a : A), a ∈ 𝒜 (m + k * d) ∧ z = awayFrac f k a}
  add_mem' := by
    rintro _ _ ⟨k, a, ha, rfl⟩ ⟨l, b, hb, rfl⟩
    refine ⟨k + l, f ^ k * b + f ^ l * a, add_mem ?_ ?_, awayFrac_add f k l a b⟩
    · exact mem_graded_of_eq 𝒜 (by ring)
        (SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf) hb)
    · exact mem_graded_of_eq 𝒜 (by ring)
        (SetLike.mul_mem_graded (SetLike.pow_mem_graded l hf) ha)
  zero_mem' := ⟨0, 0, zero_mem _, (awayFrac_zero f 0).symm⟩
  neg_mem' := by
    rintro _ ⟨k, a, ha, rfl⟩
    exact ⟨k, -a, neg_mem ha, awayFrac_neg f k a⟩

/-- `(A_f)_m` consists of the fractions with homogeneous numerator of degree `m + kd`. -/
theorem mem_awayPiece_iff (hf : f ∈ 𝒜 d) (m : ℕ) (z : Localization.Away f) :
    z ∈ awayPiece 𝒜 d hf m ↔ ∃ (k : ℕ) (a : A), a ∈ 𝒜 (m + k * d) ∧ z = awayFrac f k a :=
  Iff.rfl

/-- `a / f ᵏ` lies in `(A_f)_m` for `a` homogeneous of degree `m + kd`. -/
theorem awayFrac_mem_awayPiece (hf : f ∈ 𝒜 d) {m k : ℕ} {a : A} (ha : a ∈ 𝒜 (m + k * d)) :
    awayFrac f k a ∈ awayPiece 𝒜 d hf m :=
  ⟨k, a, ha, rfl⟩

/-- The pieces `(A_f)_m` form a graded monoid of additive subgroups of `A_f`. -/
instance instGradedMonoidAwayPiece (hf : f ∈ 𝒜 d) :
    SetLike.GradedMonoid (awayPiece 𝒜 d hf) where
  one_mem :=
    ⟨0, 1, mem_graded_of_eq 𝒜 (by ring) (SetLike.one_mem_graded 𝒜), (awayFrac_one f).symm⟩
  mul_mem := by
    rintro m n _ _ ⟨k, a, ha, rfl⟩ ⟨l, b, hb, rfl⟩
    exact ⟨k + l, a * b, mem_graded_of_eq 𝒜 (by ring) (SetLike.mul_mem_graded ha hb),
      awayFrac_mul f k l a b⟩

/-- The degree-`m` part of `(B_{ψ f})₀`: the elements whose image in `A_f` is homogeneous of
degree `m`. -/
def awayGrading (hf : f ∈ 𝒜 d) (m : ℕ) :
    AddSubgroup (HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :=
  AddSubgroup.comap (awayToLocalization 𝒜).toAddMonoidHom (awayPiece 𝒜 d hf m)

/-- An element of `(B_{ψ f})₀` is of degree `m` exactly when its image in `A_f` is. -/
theorem mem_awayGrading_iff (hf : f ∈ 𝒜 d) (m : ℕ)
    (y : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :
    y ∈ awayGrading 𝒜 d hf m ↔ awayToLocalization 𝒜 y ∈ awayPiece 𝒜 d hf m :=
  Iff.rfl

/-- The pieces of `(B_{ψ f})₀` form a graded monoid of additive subgroups. -/
instance instGradedMonoidAwayGrading (hf : f ∈ 𝒜 d) :
    SetLike.GradedMonoid (awayGrading 𝒜 d hf) where
  one_mem := by
    rw [mem_awayGrading_iff, map_one]
    exact SetLike.one_mem_graded (awayPiece 𝒜 d hf)
  mul_mem := @fun m n x y hx hy ↦ by
    rw [mem_awayGrading_iff, map_mul]
    exact SetLike.mul_mem_graded hx hy

/-- The fraction `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` has degree `m` when `a` is homogeneous of degree `m + kd`. -/
theorem awayElt_mem_awayGrading (hf : f ∈ 𝒜 d) {m k : ℕ} {a : A} (ha : a ∈ 𝒜 (m + k * d)) :
    awayElt 𝒜 d hf k a (mem_truncation_of_mem 𝒜 (Nat.le_add_left _ _) ha) ∈
      awayGrading 𝒜 d hf m := by
  rw [mem_awayGrading_iff, awayToLocalization_awayElt]
  exact awayFrac_mem_awayPiece 𝒜 d hf ha

/-- The comparison map carries the degree-`m` part of `(B_{ψ f})₀` onto `(A_f)_m`. -/
theorem exists_mem_awayGrading (hf : f ∈ 𝒜 d) (m : ℕ) {z : Localization.Away f}
    (hz : z ∈ awayPiece 𝒜 d hf m) :
    ∃ y ∈ awayGrading 𝒜 d hf m, awayToLocalization 𝒜 y = z := by
  obtain ⟨k, a, ha, rfl⟩ := hz
  exact ⟨_, awayElt_mem_awayGrading 𝒜 d hf ha, awayToLocalization_awayElt 𝒜 d hf k a _⟩

end Compare

end Stacks.Truncation

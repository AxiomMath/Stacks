module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The local ring of an infinite bouquet of thickened curves

This file constructs a concrete local ring `R` whose prime spectrum is a closed point together
with countably many pairwise distinct points `q n`, each of them alone in the basic open
`D(y n)`, and which carries nilpotents `ε n` of order exactly `n + 1` that survive in the
localization at `y n`. Geometrically, `Spec R` is the germ at the common point of an infinite
bouquet of curves, the `n`-th of them thickened to order `n + 1`.

## The construction

Let `V = ℚ⟦t⟧`, a discrete valuation ring with uniformizer `t`, and let
`S n = V[ε] / (ε ^ (n + 1))`. The ring `S n` is local, with residue field `ℚ` (the augmentation
`aug n : S n → ℚ` sends `t` and `ε` to `0`), and it has exactly two primes, the kernel of
`S n → V` and the maximal ideal. The ring `R` is the subring of `∀ n, S n` of the families `f`
for which there is `c : ℚ` with `aug n (f n) = c` for every `n` and `f n = c` for all but
finitely many `n`.

* `R` is local, with maximal ideal the kernel of the augmentation `augR : R → ℚ`: a family with
  non-zero augmentation is invertible slot by slot, and its inverse is again in `R`.
* A prime `p` that omits an element `s` concentrated in slot `n` contains every element
  concentrated in another slot (their product with `s` vanishes), hence every family vanishing in
  slot `n` (such a family is a finite sum of elements concentrated in single slots); so `p` is
  pulled back from a prime of `S n`, which omits the maximal ideal, and `p` is the kernel `q n` of
  `R → S n → V`.
* A non-maximal prime omits an element of the maximal ideal, hence an element concentrated in a
  single slot. So the primes are the closed point and the `q n`.

## Main definitions

* `AlgebraicGeometry.BouquetRing.R`: the ring.
* `AlgebraicGeometry.BouquetRing.y`, `AlgebraicGeometry.BouquetRing.ε`: the uniformizer and the
  nilpotent of the `n`-th branch.
* `AlgebraicGeometry.BouquetRing.q`: the generic point of the `n`-th branch.

## Main results

* `AlgebraicGeometry.BouquetRing.instIsLocalRingR`: `R` is local.
* `AlgebraicGeometry.BouquetRing.eq_closedPoint_or_exists_eq_q`: every prime is the closed point
  or some `q n`.
* `AlgebraicGeometry.BouquetRing.mem_basicOpen_y_iff`: `D(y n) = {q n}`.
* `AlgebraicGeometry.BouquetRing.q_injective`, `AlgebraicGeometry.BouquetRing.q_ne_closedPoint`.
* `AlgebraicGeometry.BouquetRing.ε_pow_succ`,
  `AlgebraicGeometry.BouquetRing.algebraMap_ε_pow_ne_zero`: `ε n ^ (n + 1) = 0`, while
  `ε n ^ M` is non-zero in `R[1 / y n]` for `M ≤ n`.

## Implementation notes

The ring is an input for a counterexample around the ideals of definition of Stacks 0AIW: its
nilpotents `ε n` have unbounded order, and each `ε n ^ n` survives on the basic open `D(y n)`,
a single point. The ring `R` is a `Subring` of the product, so that its ring structure and its
elements are the families themselves; the two slot constructions `single` (concentrated in one
slot) and `incl` (a ring section of the evaluation at one slot) do the work.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public noncomputable section

open Polynomial

namespace AlgebraicGeometry.BouquetRing

/-- The discrete valuation ring `V = ℚ⟦t⟧`. -/
abbrev V : Type := PowerSeries ℚ

/-- The ring `S n = V[ε] / (ε ^ (n + 1))`, the `n`-th branch of the bouquet. -/
abbrev S (n : ℕ) : Type := V[X] ⧸ Ideal.span {(X : V[X]) ^ (n + 1)}

/-- The nilpotent `ε` of `S n = V[ε] / (ε ^ (n + 1))`. -/
def eps (n : ℕ) : S n := Ideal.Quotient.mk _ X

/-- The nilpotent `ε` of `S n` satisfies `ε ^ (n + 1) = 0`. -/
theorem eps_pow_succ (n : ℕ) : eps n ^ (n + 1) = 0 := by
  rw [eps, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- The element `ε` of `S n` is nilpotent. -/
theorem isNilpotent_eps (n : ℕ) : IsNilpotent (eps n) :=
  ⟨n + 1, eps_pow_succ n⟩

/-- The structure map `V → S n` sends `v` to the class of the constant polynomial `v`. -/
theorem algebraMap_eq_mk (n : ℕ) (v : V) :
    algebraMap V (S n) v = Ideal.Quotient.mk _ (C v) :=
  rfl

/-- The retraction `S n → V` of the structure map, sending `ε` to `0`. -/
def toV (n : ℕ) : S n →+* V :=
  Ideal.Quotient.lift _ Polynomial.constantCoeff fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp

/-- The retraction `S n → V` sends the class of a polynomial to its constant coefficient. -/
@[simp]
theorem toV_mk (n : ℕ) (p : V[X]) : toV n (Ideal.Quotient.mk _ p) = p.coeff 0 :=
  rfl

/-- The retraction `S n → V` is a left inverse of the structure map `V → S n`. -/
@[simp]
theorem toV_algebraMap (n : ℕ) (v : V) : toV n (algebraMap V (S n) v) = v := by
  simp [algebraMap_eq_mk]

/-- The retraction `S n → V` sends `ε` to `0`. -/
@[simp]
theorem toV_eps (n : ℕ) : toV n (eps n) = 0 := by
  simp [eps]

/-- The augmentation `S n → ℚ`, sending `t` and `ε` to `0`. -/
def aug (n : ℕ) : S n →+* ℚ :=
  PowerSeries.constantCoeff.comp (toV n)

/-- The augmentation of `S n` is the constant coefficient of the retraction to `V`. -/
theorem aug_apply (n : ℕ) (s : S n) : aug n s = PowerSeries.constantCoeff (toV n s) :=
  rfl

/-- The augmentation `S n → ℚ` is a left inverse of the structure map `ℚ → S n`. -/
@[simp]
theorem aug_algebraMap (n : ℕ) (c : ℚ) : aug n (algebraMap ℚ (S n) c) = c :=
  DFunLike.congr_fun (RingHom.ext_rat ((aug n).comp (algebraMap ℚ (S n))) (RingHom.id ℚ)) c

/-- The augmentation of `S n` kills `ε`. -/
@[simp]
theorem aug_eps (n : ℕ) : aug n (eps n) = 0 := by
  simp [aug_apply]

/-- The augmentation of `S n` kills the uniformizer `t` of `V`. -/
@[simp]
theorem aug_algebraMap_X (n : ℕ) : aug n (algebraMap V (S n) PowerSeries.X) = 0 := by
  simp [aug_apply]

/-- Every element of `S n` is its image under `S n → V → S n` plus a multiple of `ε`. -/
theorem exists_eq_algebraMap_add (n : ℕ) (s : S n) :
    ∃ r : S n, s = algebraMap V (S n) (toV n s) + eps n * r := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
  refine ⟨Ideal.Quotient.mk _ p.divX, ?_⟩
  conv_lhs => rw [← X_mul_divX_add p]
  rw [map_add, map_mul, add_comm, toV_mk, algebraMap_eq_mk, eps]

/-- An element of `S n` with non-zero augmentation is a unit: `S n` is local. -/
theorem isUnit_of_aug_ne_zero {n : ℕ} {s : S n} (h : aug n s ≠ 0) : IsUnit s := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_add n s
  rw [hr]
  exact IsNilpotent.isUnit_add_left_of_commute
    ((Commute.all _ _).isNilpotent_mul_right (isNilpotent_eps n))
    ((PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 h)).map _) (Commute.all _ _)

/-- If `x - y` lies in an ideal `I`, then `x` lies in `I` iff `y` does. -/
private theorem mem_iff_of_sub_mem {A : Type*} [CommRing A] {I : Ideal A} {x y : A}
    (h : x - y ∈ I) : x ∈ I ↔ y ∈ I :=
  ⟨fun hx => by simpa using I.sub_mem hx h, fun hy => by simpa using I.add_mem h hy⟩

/-- An element of `S n` lies in a prime `P` iff its image under `S n → V → S n` does, since the
difference is a multiple of the nilpotent `ε`. -/
theorem mem_iff_algebraMap_toV_mem {n : ℕ} (P : Ideal (S n)) [hP : P.IsPrime] (s : S n) :
    s ∈ P ↔ algebraMap V (S n) (toV n s) ∈ P := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_add n s
  have he : eps n * r ∈ P :=
    P.mul_mem_right r (hP.mem_of_pow_mem (n + 1) (by simp [eps_pow_succ]))
  exact mem_iff_of_sub_mem (by rwa [sub_eq_of_eq_add' hr])

/-- An element of `V = ℚ⟦t⟧` lies in the maximal ideal iff its constant coefficient vanishes. -/
theorem mem_maximalIdeal_V_iff (v : V) :
    v ∈ IsLocalRing.maximalIdeal V ↔ PowerSeries.constantCoeff v = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

/-- A prime of the discrete valuation ring `V` is `⊥` or the maximal ideal. -/
theorem eq_bot_or_eq_maximalIdeal_V (P : Ideal V) [P.IsPrime] :
    P = ⊥ ∨ P = IsLocalRing.maximalIdeal V := by
  by_cases h : P = ⊥
  · exact Or.inl h
  · exact Or.inr (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal h))

/-- In `S n`, `t ^ k * ε ^ M ≠ 0` for `M ≤ n`. -/
theorem algebraMap_X_pow_mul_eps_pow_ne_zero {n M : ℕ} (h : M ≤ n) (k : ℕ) :
    algebraMap V (S n) PowerSeries.X ^ k * eps n ^ M ≠ 0 := by
  rw [← map_pow, algebraMap_eq_mk, eps, ← map_pow, ← map_mul, Ne,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rintro ⟨g, hg⟩
  have hc := congrArg (Polynomial.coeff · M) hg
  simp only [coeff_C_mul_X_pow, if_true, coeff_X_pow_mul', show ¬ n + 1 ≤ M by omega,
    if_false] at hc
  exact pow_ne_zero k PowerSeries.X_ne_zero hc

/-- The subring of `∀ n, S n` of the families `f` for which there is `c : ℚ` with
`aug n (f n) = c` for every `n` and `f n = c` for all but finitely many `n`. -/
def bouquetSubring : Subring (∀ n, S n) where
  carrier := {f | ∃ c : ℚ, (∀ n, aug n (f n) = c) ∧
    ∀ᶠ n in Filter.cofinite, f n = algebraMap ℚ (S n) c}
  mul_mem' := by
    rintro f g ⟨c, hc, hf⟩ ⟨d, hd, hg⟩
    exact ⟨c * d, fun n => by simp [hc, hd], (hf.and hg).mono fun n h => by simp [h.1, h.2]⟩
  one_mem' := ⟨1, fun n => by simp, Filter.Eventually.of_forall fun n => by simp⟩
  add_mem' := by
    rintro f g ⟨c, hc, hf⟩ ⟨d, hd, hg⟩
    exact ⟨c + d, fun n => by simp [hc, hd], (hf.and hg).mono fun n h => by simp [h.1, h.2]⟩
  zero_mem' := ⟨0, fun n => by simp, Filter.Eventually.of_forall fun n => by simp⟩
  neg_mem' := by
    rintro f ⟨c, hc, hf⟩
    exact ⟨-c, fun n => by simp [hc], hf.mono fun n h => by simp [h]⟩

/-- The local ring of the infinite bouquet of thickened curves. -/
abbrev R : Type := bouquetSubring

/-- The augmentation `R → ℚ`, the residue map of the local ring `R`. -/
def augR : R →+* ℚ :=
  (aug 0).comp ((Pi.evalRingHom S 0).comp bouquetSubring.subtype)

/-- Every slot of an element `f` of `R` has the augmentation `augR f`. -/
theorem aug_val (f : R) (n : ℕ) : aug n (f.1 n) = augR f := by
  obtain ⟨c, hc, -⟩ := f.2
  show aug n (f.1 n) = aug 0 (f.1 0)
  rw [hc, hc]

/-- All but finitely many slots of an element `f` of `R` are the constant `augR f`. -/
theorem eventually_eq_algebraMap (f : R) :
    ∀ᶠ n in Filter.cofinite, f.1 n = algebraMap ℚ (S n) (augR f) := by
  obtain ⟨c, hc, hf⟩ := f.2
  rwa [← aug_val f 0, hc]

/-- An element of `R` with non-zero augmentation is a unit. -/
theorem isUnit_of_augR_ne_zero {f : R} (hf : augR f ≠ 0) : IsUnit f := by
  have hu : ∀ n, IsUnit (f.1 n) := fun n => isUnit_of_aug_ne_zero (by rwa [aug_val])
  let g : R := ⟨fun n => Ring.inverse (f.1 n), (augR f)⁻¹, fun n => by
      have := congrArg (aug n) (Ring.mul_inverse_cancel _ (hu n))
      rw [map_mul, map_one, aug_val] at this
      exact eq_inv_of_mul_eq_one_right this,
    (eventually_eq_algebraMap f).mono fun n h => by
      show Ring.inverse (f.1 n) = _
      rw [h]
      have hc : IsUnit (algebraMap ℚ (S n) (augR f)) := (isUnit_iff_ne_zero.2 hf).map _
      simpa using (Ring.inverse_mul_eq_iff_eq_mul _ 1 (algebraMap ℚ (S n) (augR f)⁻¹) hc).2
        (by rw [← map_mul, mul_inv_cancel₀ hf, map_one])⟩
  exact IsUnit.of_mul_eq_one g (Subtype.ext <| funext fun n => Ring.mul_inverse_cancel _ (hu n))

/-- The ring `R` is nontrivial: its augmentation separates `0` and `1`. -/
instance : Nontrivial R :=
  nontrivial_of_ne 0 1 fun h => by simpa using congrArg augR h

/-- The ring `R` is local: of `a` and `1 - a`, one has non-zero augmentation. -/
instance : IsLocalRing R :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : augR a = 0
    · exact Or.inr (isUnit_of_augR_ne_zero (by simp [h]))
    · exact Or.inl (isUnit_of_augR_ne_zero h)

/-- The maximal ideal of `R` is the kernel of the augmentation. -/
theorem mem_maximalIdeal_iff (f : R) : f ∈ IsLocalRing.maximalIdeal R ↔ augR f = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h => by_contra fun h' => h (isUnit_of_augR_ne_zero h'),
    fun h hu => (hu.map augR).ne_zero h⟩

/-- The element of `R` which is `s` in slot `n` and `0` elsewhere, for `s` of augmentation `0`. -/
def single (n : ℕ) (s : S n) (hs : aug n s = 0) : R :=
  ⟨Pi.single n s, 0, fun m => by
      obtain rfl | h := eq_or_ne m n
      · simpa using hs
      · simp [h],
    (Filter.eventually_cofinite_ne n).mono fun m h => by simp [h]⟩

/-- The underlying family of `single n s hs` is `Pi.single n s`. -/
@[simp]
theorem single_val (n : ℕ) (s : S n) (hs : aug n s = 0) : (single n s hs).1 = Pi.single n s :=
  rfl

/-- The element concentrated in slot `n` with value `0` is `0`. -/
theorem single_zero (n : ℕ) (hs : aug n 0 = 0) : single n 0 hs = 0 :=
  Subtype.ext (by simp)

/-- Elements concentrated in distinct slots have product `0`. -/
theorem single_mul_single_of_ne {m n : ℕ} (h : m ≠ n) (x : S m) (hx : aug m x = 0) (s : S n)
    (hs : aug n s = 0) : single m x hx * single n s hs = 0 := by
  refine Subtype.ext <| funext fun k => ?_
  obtain rfl | hk := eq_or_ne k m
  · simp [h]
  · simp [hk]

/-- An element of `R` of augmentation `0` lies in an ideal `I` as soon as each of its slots
does: it is the finite sum of its slots. -/
theorem mem_of_forall_single_mem (I : Ideal R) (f : R) (hf : augR f = 0)
    (h : ∀ m (hm : aug m (f.1 m) = 0), single m (f.1 m) hm ∈ I) : f ∈ I := by
  have hev := eventually_eq_algebraMap f
  rw [hf, Filter.eventually_cofinite] at hev
  have key : f = ∑ m ∈ hev.toFinset, single m (f.1 m) (by rw [aug_val, hf]) := by
    refine Subtype.ext <| funext fun k => ?_
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    simp only [single_val, Finset.sum_pi_single, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    split_ifs with hk
    · rfl
    · simpa using hk
  rw [key]
  exact sum_mem fun m _ => h m _

/-- Evaluation `R → S n` at slot `n`. -/
def ev (n : ℕ) : R →+* S n :=
  (Pi.evalRingHom S n).comp bouquetSubring.subtype

/-- The evaluation at slot `n` of `f : R` is the `n`-th component of `f`. -/
@[simp]
theorem ev_apply (n : ℕ) (f : R) : ev n f = f.1 n :=
  rfl

/-- The family which is `s` in slot `n` and the augmentation of `s` elsewhere. -/
def inclFun (n : ℕ) (s : S n) : ∀ m, S m :=
  Function.update (fun m => algebraMap ℚ (S m) (aug n s)) n s

/-- The family `inclFun n s` is `s` in slot `n`. -/
@[simp]
theorem inclFun_self (n : ℕ) (s : S n) : inclFun n s n = s :=
  Function.update_self _ _ _

/-- The family `inclFun n s` is the augmentation of `s` outside slot `n`. -/
theorem inclFun_of_ne {m n : ℕ} (h : m ≠ n) (s : S n) :
    inclFun n s m = algebraMap ℚ (S m) (aug n s) :=
  Function.update_of_ne h _ _

/-- The ring map `S n → R`, a section of the evaluation at slot `n`. -/
def incl (n : ℕ) : S n →+* R where
  toFun s := ⟨inclFun n s, aug n s, fun m => by
      obtain rfl | h := eq_or_ne m n
      · simp
      · simp [inclFun_of_ne h],
    (Filter.eventually_cofinite_ne n).mono fun m h => inclFun_of_ne h s⟩
  map_one' := Subtype.ext <| funext fun m => by
    obtain rfl | h := eq_or_ne m n <;> simp [inclFun_of_ne, *]
  map_mul' x y := Subtype.ext <| funext fun m => by
    obtain rfl | h := eq_or_ne m n <;> simp [inclFun_of_ne, *]
  map_zero' := Subtype.ext <| funext fun m => by
    obtain rfl | h := eq_or_ne m n <;> simp [inclFun_of_ne, *]
  map_add' x y := Subtype.ext <| funext fun m => by
    obtain rfl | h := eq_or_ne m n <;> simp [inclFun_of_ne, *]

/-- The underlying family of `incl n s` is `inclFun n s`. -/
@[simp]
theorem incl_val (n : ℕ) (s : S n) : (incl n s).1 = inclFun n s :=
  rfl

/-- For `s` of augmentation `0`, `incl n s` is the element concentrated in slot `n` at `s`. -/
theorem incl_eq_single (n : ℕ) (s : S n) (hs : aug n s = 0) : incl n s = single n s hs := by
  refine Subtype.ext <| funext fun m => ?_
  obtain rfl | h := eq_or_ne m n
  · simp
  · simp [inclFun_of_ne h, h, hs]

/-- The ring map `R → V`, the `n`-th branch followed by `S n → V`. -/
def ρ (n : ℕ) : R →+* V :=
  (toV n).comp (ev n)

/-- The map `ρ n : R → V` is the `n`-th component followed by `S n → V`. -/
theorem ρ_apply (n : ℕ) (f : R) : ρ n f = toV n (f.1 n) :=
  rfl

/-- A prime `p` of `R` omitting an element concentrated in slot `n` is the kernel of `ρ n`. -/
theorem eq_ker_of_single_notMem (p : Ideal R) [hp : p.IsPrime] {n : ℕ} {s : S n}
    (hs : aug n s = 0) (hsp : single n s hs ∉ p) : p = RingHom.ker (ρ n) := by
  have h1 : ∀ m, m ≠ n → ∀ x hx, single m x hx ∈ p := fun m hm x hx =>
    (hp.mem_or_mem (by simp [single_mul_single_of_ne hm])).resolve_right hsp
  have h2 : ∀ f : R, f.1 n = 0 → f ∈ p := by
    intro f hf
    refine mem_of_forall_single_mem p f (by rw [← aug_val f n, hf, map_zero]) fun m hm => ?_
    obtain rfl | h := eq_or_ne m n
    · rw [show single m (f.1 m) hm = 0 from Subtype.ext (by simp [hf])]
      exact p.zero_mem
    · exact h1 m h _ hm
  have h3 : ∀ f : R, f ∈ p ↔ incl n (f.1 n) ∈ p := fun f =>
    mem_iff_of_sub_mem (h2 _ (by simp))
  set J := (p.comap (incl n)).comap (algebraMap V (S n))
  have h4 : ∀ s : S n, incl n s ∈ p ↔ toV n s ∈ J := fun s => by
    rw [← Ideal.mem_comap, mem_iff_algebraMap_toV_mem, ← Ideal.mem_comap]
  have hPV : J = ⊥ := by
    rcases eq_bot_or_eq_maximalIdeal_V J with h | h
    · exact h
    · refine absurd ?_ hsp
      rwa [← incl_eq_single, h4, h, mem_maximalIdeal_V_iff]
  ext f
  rw [h3 f, h4, hPV, Ideal.mem_bot, RingHom.mem_ker, ρ_apply]

/-- The uniformizer of the `n`-th branch: `t` in slot `n`, `0` elsewhere. -/
def y (n : ℕ) : R :=
  single n (algebraMap V (S n) PowerSeries.X) (aug_algebraMap_X n)

/-- The nilpotent of the `n`-th branch: `ε` in slot `n`, `0` elsewhere. -/
def ε (n : ℕ) : R :=
  single n (eps n) (aug_eps n)

/-- The generic point of the `n`-th branch, the kernel of `ρ n : R → V`. -/
def q (n : ℕ) : PrimeSpectrum R :=
  ⟨RingHom.ker (ρ n), RingHom.ker_isPrime _⟩

/-- The prime ideal of `q n` is the kernel of `ρ n : R → V`. -/
theorem q_asIdeal (n : ℕ) : (q n).asIdeal = RingHom.ker (ρ n) :=
  rfl

/-- The uniformizer `y n` lies in the maximal ideal: its augmentation is `0`. -/
theorem augR_y (n : ℕ) : augR (y n) = 0 := by
  rw [← aug_val _ n]
  simp [y]

/-- The uniformizer `y n` does not lie in `q n`. -/
theorem y_notMem_q (n : ℕ) : y n ∉ (q n).asIdeal := by
  rw [q_asIdeal, RingHom.mem_ker, ρ_apply]
  simp [y]

/-- The uniformizer `y n` lies in `q m` for `m ≠ n`. -/
theorem y_mem_q_of_ne {m n : ℕ} (h : m ≠ n) : y n ∈ (q m).asIdeal := by
  rw [q_asIdeal, RingHom.mem_ker, ρ_apply]
  simp [y, h]

/-- The basic open `D(y n)` of `Spec R` is the single point `q n`. -/
theorem mem_basicOpen_y_iff (n : ℕ) (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.basicOpen (y n) ↔ p = q n := by
  rw [PrimeSpectrum.mem_basicOpen]
  refine ⟨fun h => PrimeSpectrum.ext (eq_ker_of_single_notMem p.asIdeal _ h), ?_⟩
  rintro rfl
  exact y_notMem_q n

/-- The points `q n` of `Spec R` are pairwise distinct. -/
theorem q_injective : Function.Injective q := by
  intro m n h
  by_contra hmn
  exact y_notMem_q n (h ▸ y_mem_q_of_ne hmn)

/-- No `q n` is the closed point of `Spec R`. -/
theorem q_ne_closedPoint (n : ℕ) : q n ≠ IsLocalRing.closedPoint R := by
  intro h
  apply y_notMem_q n
  rw [h]
  exact (mem_maximalIdeal_iff _).2 (augR_y n)

/-- Every point of `Spec R` is the closed point or one of the `q n`. -/
theorem eq_closedPoint_or_exists_eq_q (p : PrimeSpectrum R) :
    p = IsLocalRing.closedPoint R ∨ ∃ n, p = q n := by
  by_cases h : p.asIdeal = IsLocalRing.maximalIdeal R
  · exact Or.inl (PrimeSpectrum.ext h)
  · right
    have hle : ¬ IsLocalRing.maximalIdeal R ≤ p.asIdeal := fun hle =>
      h (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) hle)
    obtain ⟨a, ha, hap⟩ := Set.not_subset.1 hle
    rw [SetLike.mem_coe, mem_maximalIdeal_iff] at ha
    by_contra! hne
    refine hap (mem_of_forall_single_mem _ a ha fun m hm => ?_)
    by_contra hm'
    exact hne m (PrimeSpectrum.ext (eq_ker_of_single_notMem _ hm hm'))

/-- The nilpotent `ε n` of the `n`-th branch satisfies `ε n ^ (n + 1) = 0`. -/
theorem ε_pow_succ (n : ℕ) : ε n ^ (n + 1) = 0 := by
  refine Subtype.ext <| funext fun m => ?_
  obtain rfl | h := eq_or_ne m n
  · simp [ε, eps_pow_succ]
  · simp [ε, h]

/-- For `M ≤ n`, the power `ε n ^ M` survives in the localization `R[1 / y n]`. -/
theorem algebraMap_ε_pow_ne_zero {n M : ℕ} (h : M ≤ n) :
    algebraMap R (Localization.Away (y n)) (ε n ^ M) ≠ 0 := by
  rw [Ne, IsLocalization.map_eq_zero_iff (Submonoid.powers (y n))]
  rintro ⟨⟨_, k, rfl⟩, hk⟩
  have := congrArg (fun f : R => f.1 n) hk
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Pi.mul_apply, Pi.pow_apply, y, ε,
    single_val, Pi.single_eq_same, ZeroMemClass.coe_zero, Pi.zero_apply] at this
  exact algebraMap_X_pow_mul_eps_pow_ne_zero h k this

end AlgebraicGeometry.BouquetRing

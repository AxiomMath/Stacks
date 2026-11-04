module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClassLocallyFree

/-!
# The target of the total Chern class, and the universal property of `K₀(Vect(X))`

Tag 0FI5 asks for a rule
`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`
which turns addition in the Grothendieck group into the product of the target. The product of
`∏_{i ≥ 0} A^i(X)` is the convolution `(a b)_n = ∑_{i + j = n} a_i b_j`, so the target is a ring
of power series; and since `−[ℰ]` must go to a formal inverse, the part of it that the rule lands
in has to be a *group*. This file builds that group and extends a rule from the generators
`[ℰ]` to all of `K₀(Vect(X))`.

The coefficients are taken in the **centre** of `A(X)`. That is not a restriction: the source
proves that the classes `c_i^A(ℰ)` are central — here
`Stacks.WeilCohomology.ChernSetup.chernClass_central` — and it is what makes the convolution
commutative in a ring `A(X)` which is "not necessarily commutative". Property (1) of Tag 0FI5
forces commutativity on the image of the rule anyway, `K₀(Vect(X))` being abelian, so nothing is
lost; and a commutative group is exactly what the universal property of `K₀(Vect(X))` consumes.

## Main definitions

* `Stacks.WeilCohomology.UnitalCentralSeries`: **the group `∏_{i ≥ 0} A^i(X)` acts in**, namely
  the power series over the centre of a ring with constant term `1`, a commutative group under
  the convolution product whose inverse is the formal inverse of a power series.
* `Stacks.WeilCohomology.UnitalCentralSeries.coeff`: the `n`-th component, as an element of the
  ring itself.
* `Stacks.WeilCohomology.UnitalCentralSeries.ofCoeff`: the series with prescribed central
  components and constant term `1`.
* `Stacks.WeilCohomology.kZeroSeriesHom`, `Stacks.WeilCohomology.kZeroSeries`: **the extension to
  `K₀(Vect(X))`** of an assignment of a unital central series to every finite locally free
  module which is multiplicative in short exact sequences.

## Main results

* `Stacks.WeilCohomology.UnitalCentralSeries.coeff_mul`: the convolution formula, which is
  property (1) of Tag 0FI5 read on components.
* `Stacks.WeilCohomology.kZeroSeries_classOf`, `Stacks.WeilCohomology.kZeroSeries_add`,
  `Stacks.WeilCohomology.kZeroSeries_zero`: the extension takes the prescribed value on a
  generator, is multiplicative on sums and unital.
* `Stacks.WeilCohomology.eq_of_convolutive_of_eq_classOf`: **a rule satisfying property (1) of
  Tag 0FI5 is determined by its values on the classes of modules.** This is what makes
  uniqueness on the generators the same thing as uniqueness on all of `K₀(Vect(X))`: property
  (1) makes the rule a monoid homomorphism from `(K₀(Vect(X)), +)` to the convolution monoid, and
  `−[ℰ]` is forced to the inverse of `[ℰ]` because a monoid has at most one two-sided inverse of
  an element.

## Implementation notes

`∏_{i ≥ 0} A^i(X)` is read as `PowerSeries` over `Subring.center (A X)`, whose multiplication is
already the convolution by `PowerSeries.coeff_mul`; that is what makes associativity,
commutativity and the formal inverse `PowerSeries.invOfUnit` available rather than something to
be built. The components are read back into `A(X)` along the inclusion of the centre, which is a
ring homomorphism and so carries the convolution formula with it.

The grading is not part of the target here: that the `n`-th component lies in `A^n(X)` is a
separate clause of `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree` and is proved where the
components are produced.

`Stacks.WeilCohomology.eq_of_convolutive_of_eq_classOf` does not use the group structure, only
the monoid of all power series over `A(X)`: it is an induction over the presentation of
`K₀(Vect(X))` as a quotient of the free abelian group on sheaves of modules, in which the only
step needing an argument is `−[ℰ]`, and there the uniqueness of a two-sided inverse in a monoid
suffices.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace Stacks.WeilCohomology

/-! ### The group of unital central series -/

variable {R : Type v} [Ring R]

/-- **The group `∏_{i ≥ 0} A^i(X)` of Tag 0FI5 acts in.** A power series over the centre of `R`
whose constant term is `1`; the convolution product makes these a commutative group, the inverse
being the formal inverse of the power series.

The total Chern class of a finite locally free module is one of these: its constant term is
`c_0^A(ℰ) = 1` and its components are central in `A(X)`. -/
def UnitalCentralSeries (R : Type v) [Ring R] : Type v :=
  {f : PowerSeries (Subring.center R) // PowerSeries.constantCoeff f = 1}

namespace UnitalCentralSeries

/-- The underlying power series over the centre. -/
def val (a : UnitalCentralSeries R) : PowerSeries (Subring.center R) := a.1

/-- Its constant term is `1`. -/
theorem constantCoeff_val (a : UnitalCentralSeries R) :
    PowerSeries.constantCoeff a.val = 1 := a.2

/-- Two unital central series with the same underlying power series are equal. -/
theorem val_injective : Function.Injective (val : UnitalCentralSeries R → _) :=
  fun _ _ h => Subtype.ext h

/-- The convolution product. -/
protected def mul (a b : UnitalCentralSeries R) : UnitalCentralSeries R :=
  ⟨a.val * b.val, by rw [map_mul, a.constantCoeff_val, b.constantCoeff_val, one_mul]⟩

/-- The unit series. -/
protected def one : UnitalCentralSeries R := ⟨1, map_one _⟩

/-- The formal inverse. -/
protected def inv (a : UnitalCentralSeries R) : UnitalCentralSeries R :=
  ⟨PowerSeries.invOfUnit a.val 1, by
    rw [PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]⟩

/-- The convolution product is associative. -/
protected theorem mul_assoc' (a b c : UnitalCentralSeries R) :
    (a.mul b).mul c = a.mul (b.mul c) := val_injective (mul_assoc a.val b.val c.val)

/-- The unit series is a left identity for the convolution product. -/
protected theorem one_mul' (a : UnitalCentralSeries R) :
    UnitalCentralSeries.one.mul a = a := val_injective (one_mul a.val)

/-- The unit series is a right identity for the convolution product. -/
protected theorem mul_one' (a : UnitalCentralSeries R) :
    a.mul UnitalCentralSeries.one = a := val_injective (mul_one a.val)

/-- The convolution product is commutative. -/
protected theorem mul_comm' (a b : UnitalCentralSeries R) :
    a.mul b = b.mul a := val_injective (mul_comm a.val b.val)

/-- The formal inverse is a left inverse for the convolution product. -/
protected theorem inv_mul_cancel' (a : UnitalCentralSeries R) :
    a.inv.mul a = UnitalCentralSeries.one :=
  val_injective (by
    show PowerSeries.invOfUnit a.val 1 * a.val = 1
    rw [mul_comm]
    exact PowerSeries.mul_invOfUnit a.val 1 (by rw [a.constantCoeff_val, Units.val_one]))

/-- Unital central series form a commutative group under the convolution product. -/
instance : CommGroup (UnitalCentralSeries R) where
  mul := UnitalCentralSeries.mul
  one := UnitalCentralSeries.one
  inv := UnitalCentralSeries.inv
  mul_assoc := UnitalCentralSeries.mul_assoc'
  one_mul := UnitalCentralSeries.one_mul'
  mul_one := UnitalCentralSeries.mul_one'
  mul_comm := UnitalCentralSeries.mul_comm'
  inv_mul_cancel := UnitalCentralSeries.inv_mul_cancel'

/-- The underlying power series of a product is the product of the underlying power series. -/
@[simp] theorem val_mul (a b : UnitalCentralSeries R) : (a * b).val = a.val * b.val := rfl

/-- The underlying power series of the unit series is `1`. -/
@[simp] theorem val_one : (1 : UnitalCentralSeries R).val = 1 := rfl

/-- **The `n`-th component of a unital central series**, as an element of `R`. -/
def coeff (a : UnitalCentralSeries R) (n : ℕ) : R :=
  ((PowerSeries.coeff n a.val : Subring.center R) : R)

/-- Every component of a unital central series is central in `R`. -/
theorem coeff_mem_center (a : UnitalCentralSeries R) (n : ℕ) :
    a.coeff n ∈ Subring.center R := (PowerSeries.coeff n a.val).2

/-- The constant term is `1`. -/
@[simp] theorem coeff_zero (a : UnitalCentralSeries R) : a.coeff 0 = 1 := by
  show ((PowerSeries.coeff 0 a.val : Subring.center R) : R) = 1
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, a.constantCoeff_val]
  rfl

/-- **The convolution formula**: this is property (1) of Tag 0FI5 read on components. -/
theorem coeff_mul (a b : UnitalCentralSeries R) (n : ℕ) :
    (a * b).coeff n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a.coeff p.1 * b.coeff p.2 := by
  show ((PowerSeries.coeff n (a.val * b.val) : Subring.center R) : R) = _
  rw [PowerSeries.coeff_mul]
  exact map_sum (Subring.center R).subtype
    (fun p : ℕ × ℕ => PowerSeries.coeff p.1 a.val * PowerSeries.coeff p.2 b.val)
    (Finset.HasAntidiagonal.antidiagonal n)

/-- The components of the unit series: `1` in degree `0` and `0` elsewhere. -/
theorem coeff_one (n : ℕ) : (1 : UnitalCentralSeries R).coeff n = if n = 0 then 1 else 0 := by
  show ((PowerSeries.coeff n (1 : PowerSeries (Subring.center R)) : Subring.center R) : R) = _
  rw [PowerSeries.coeff_one]
  split_ifs <;> rfl

/-- A unital central series is determined by its components. -/
@[ext] theorem ext {a b : UnitalCentralSeries R} (h : ∀ n, a.coeff n = b.coeff n) : a = b :=
  val_injective (PowerSeries.ext fun n => Subtype.ext (h n))

/-- Over the zero ring there is only one unital central series. -/
theorem subsingleton (h : Subsingleton R) : Subsingleton (UnitalCentralSeries R) :=
  ⟨fun a b => ext fun n => h.elim _ _⟩

/-- **The components of the inverse satisfy the inverting recursion.** Comparing the coefficients
of `a a⁻¹ = 1` in degree `n + 1` and using `a_0 = 1` solves for the `(n+1)`-st component of the
inverse. -/
theorem coeff_inv_succ (a : UnitalCentralSeries R) (n : ℕ) :
    (a⁻¹).coeff (n + 1) =
      -∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a.coeff (p.1 + 1) * (a⁻¹).coeff p.2 := by
  have h := coeff_mul a a⁻¹ (n + 1)
  rw [mul_inv_cancel, coeff_one, if_neg (Nat.succ_ne_zero n),
    Finset.Nat.sum_antidiagonal_succ, a.coeff_zero, one_mul] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **The components of the formal inverse stay in a graded family of additive subgroups.** If
`G` contains `1` in degree zero and `G i · G j ⊆ G (i + j)`, and every component of `a` lies in
its degree, then so does every component of `a⁻¹`: the recursion of
`Stacks.WeilCohomology.UnitalCentralSeries.coeff_inv_succ` expresses the `(n+1)`-st component as a
sum of products of components of total degree `n + 1`. -/
theorem coeff_inv_mem (G : ℕ → AddSubgroup R) (hone : (1 : R) ∈ G 0)
    (hmulG : ∀ (i j : ℕ) {x y : R}, x ∈ G i → y ∈ G j → x * y ∈ G (i + j))
    (a : UnitalCentralSeries R) (ha : ∀ n, a.coeff n ∈ G n) (n : ℕ) :
    (a⁻¹).coeff n ∈ G n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        rw [coeff_zero]
        exact hone
    | succ k =>
        rw [coeff_inv_succ]
        refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun p hp => ?_)
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have hmem := hmulG (p.1 + 1) p.2 (ha (p.1 + 1)) (ih p.2 (by omega))
        rwa [show p.1 + 1 + p.2 = k + 1 by omega] at hmem

/-- **The unital central series with prescribed components.** -/
def ofCoeff (a : ℕ → R) (hmem : ∀ n, a n ∈ Subring.center R) (h0 : a 0 = 1) :
    UnitalCentralSeries R :=
  ⟨PowerSeries.mk fun n => ⟨a n, hmem n⟩, by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact Subtype.ext h0⟩

/-- The components of `ofCoeff a hmem h0` are the prescribed values `a n`. -/
@[simp] theorem coeff_ofCoeff (a : ℕ → R) (hmem : ∀ n, a n ∈ Subring.center R) (h0 : a 0 = 1)
    (n : ℕ) : (ofCoeff a hmem h0).coeff n = a n := by
  show ((PowerSeries.coeff n (PowerSeries.mk fun k => (⟨a k, hmem k⟩ : Subring.center R)) :
    Subring.center R) : R) = a n
  rw [PowerSeries.coeff_mk]

end UnitalCentralSeries

/-! ### Extending a rule from the generators to `K₀(Vect(X))` -/

/-- Induction on `K₀(Vect(X))` over the generators `[ℰ]`, their negatives, `0` and sums. -/
private theorem kZero_induction {X : Scheme.{u}} {P : VectorBundleKZero X → Prop} (h0 : P 0)
    (hof : ∀ M : X.Modules, P (VectorBundleKZero.classOf X M))
    (hneg : ∀ M : X.Modules, P (-VectorBundleKZero.classOf X M))
    (hadd : ∀ a b, P a → P b → P (a + b)) (a : VectorBundleKZero X) : P a := by
  induction a using QuotientAddGroup.induction_on with
  | H z =>
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact h0
    | of M => exact hof M
    | neg M => exact hneg M
    | add z w hz hw => exact hadd _ _ hz hw

section Lift

open Stacks.FiniteLocallyFree

variable {X : Scheme.{u}} {R : Type v} [Ring R] (ch : X.Modules → UnitalCentralSeries R)
  (hzero : ∀ M : X.Modules, ¬ IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M → ch M = 1)
  (hmul : ∀ {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G →
          Mono f → Epi g → (ShortComplex.mk f g w).Exact → ch F = ch E * ch G)

/-- **The extension to `K₀(Vect(X))`, as a homomorphism of groups.** An assignment `ch` of a
unital central series to every sheaf of modules which takes the unit series off the finite
locally free ones and is multiplicative in short exact sequences of finite locally free modules
descends to the Grothendieck group, by its universal property
`AlgebraicGeometry.VectorBundleKZero.liftAddHom`; the target is written additively, which is what
turns "multiplicative in short exact sequences" into "additive", and what makes the value on
`−[ℰ]` the formal inverse of the value on `[ℰ]`. -/
def kZeroSeriesHom : VectorBundleKZero X →+ Additive (UnitalCentralSeries R) :=
  VectorBundleKZero.liftAddHom (fun M => Additive.ofMul (ch M))
    (fun M hM => congrArg Additive.ofMul (hzero M hM))
    (fun f g w hE hF hG hmono hepi hex => by
      rw [← ofMul_mul]
      exact congrArg Additive.ofMul (hmul f g w hE hF hG hmono hepi hex))

/-- **The rule on `K₀(Vect(X))` of Tag 0FI5**: the extension of `ch` to the Grothendieck group. -/
def kZeroSeries : VectorBundleKZero X → UnitalCentralSeries R :=
  fun a => Additive.toMul (kZeroSeriesHom ch hzero hmul a)

/-- The rule takes the prescribed value on the class of a module. -/
@[simp] theorem kZeroSeries_classOf (M : X.Modules) :
    kZeroSeries ch hzero hmul (VectorBundleKZero.classOf X M) = ch M := by
  rw [kZeroSeries, kZeroSeriesHom, VectorBundleKZero.liftAddHom_classOf]
  rfl

/-- **Property (1) of Tag 0FI5 for the extension**: a sum in `K₀(Vect(X))` goes to the
convolution product. -/
theorem kZeroSeries_add (a b : VectorBundleKZero X) :
    kZeroSeries ch hzero hmul (a + b) =
      kZeroSeries ch hzero hmul a * kZeroSeries ch hzero hmul b := by
  rw [kZeroSeries, map_add, toMul_add]
  rfl

/-- **Property (1) of Tag 0FI5 for the extension**: `0` goes to the unit series. -/
theorem kZeroSeries_zero : kZeroSeries ch hzero hmul 0 = 1 := by
  rw [kZeroSeries, map_zero]
  rfl

/-- A negative in `K₀(Vect(X))` goes to the formal inverse. -/
theorem kZeroSeries_neg (a : VectorBundleKZero X) :
    kZeroSeries ch hzero hmul (-a) = (kZeroSeries ch hzero hmul a)⁻¹ := by
  rw [kZeroSeries, map_neg, toMul_neg]
  rfl

/-- **The components of every value of the extension lie in a graded family of subgroups as soon
as the components of the generators do.** The unit series and the convolution stay in the family
because it contains `1` in degree zero and multiplication adds degrees; the formal inverse stays
in it by `Stacks.WeilCohomology.UnitalCentralSeries.coeff_inv_mem`. This is what makes the clause
`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` of Tag 0FI5 hold on all of `K₀(Vect(X))`. -/
theorem coeff_kZeroSeries_mem (G : ℕ → AddSubgroup R) (hone : (1 : R) ∈ G 0)
    (hmulG : ∀ (i j : ℕ) {x y : R}, x ∈ G i → y ∈ G j → x * y ∈ G (i + j))
    (hG : ∀ (M : X.Modules) (n : ℕ), (ch M).coeff n ∈ G n)
    (a : VectorBundleKZero X) (n : ℕ) : (kZeroSeries ch hzero hmul a).coeff n ∈ G n := by
  have hunit : ∀ k : ℕ, (1 : UnitalCentralSeries R).coeff k ∈ G k := by
    intro k
    rw [UnitalCentralSeries.coeff_one]
    split_ifs with hk
    · subst hk
      exact hone
    · exact AddSubgroup.zero_mem _
  induction a using kZero_induction generalizing n with
  | h0 => rw [kZeroSeries_zero]; exact hunit n
  | hof M => rw [kZeroSeries_classOf]; exact hG M n
  | hneg M =>
      rw [kZeroSeries_neg, kZeroSeries_classOf]
      exact UnitalCentralSeries.coeff_inv_mem G hone hmulG (ch M) (hG M) n
  | hadd z w hz hw =>
      rw [kZeroSeries_add, UnitalCentralSeries.coeff_mul]
      refine AddSubgroup.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact hp ▸ hmulG p.1 p.2 (hz p.1) (hw p.2)

end Lift

/-! ### A rule satisfying property (1) is determined on the generators -/

variable {X : Scheme.{u}}

/-- The power series whose components are the values of a rule at one class. -/
def seriesAt {R : Type v} [Ring R] (c : VectorBundleKZero X → ℕ → R)
    (a : VectorBundleKZero X) : PowerSeries R :=
  PowerSeries.mk (c a)

/-- The components of `seriesAt c a` are the values of `c` at `a`. -/
private theorem coeff_seriesAt {R : Type v} [Ring R] (c : VectorBundleKZero X → ℕ → R)
    (a : VectorBundleKZero X) (n : ℕ) : PowerSeries.coeff n (seriesAt c a) = c a n :=
  PowerSeries.coeff_mk _ _

/-- Property (1) of Tag 0FI5, read as multiplicativity of `Stacks.WeilCohomology.seriesAt`. -/
theorem seriesAt_add {R : Type v} [Ring R] {c : VectorBundleKZero X → ℕ → R}
    (hadd : ∀ (a b : VectorBundleKZero X) (n : ℕ),
      c (a + b) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c a p.1 * c b p.2)
    (a b : VectorBundleKZero X) : seriesAt c (a + b) = seriesAt c a * seriesAt c b :=
  PowerSeries.ext fun n => by
    rw [coeff_seriesAt, PowerSeries.coeff_mul, hadd]
    simp only [coeff_seriesAt]

/-- The unit clause of property (1), read on `Stacks.WeilCohomology.seriesAt`. -/
theorem seriesAt_zero {R : Type v} [Ring R] {c : VectorBundleKZero X → ℕ → R}
    (hzero : ∀ n : ℕ, c 0 n = if n = 0 then 1 else 0) : seriesAt c 0 = 1 :=
  PowerSeries.ext fun n => by
    rw [coeff_seriesAt, hzero, PowerSeries.coeff_one]

/-- **A rule satisfying property (1) of Tag 0FI5 is determined by its values on the classes of
sheaves of modules.** Two rules which turn addition into convolution, send `0` to the unit series
and agree on every class `[ℰ]` agree on all of `K₀(Vect(X))`.

Property (1) makes `α ↦ (c α)_n` a monoid homomorphism from `(K₀(Vect(X)), +)` to the convolution
monoid of power series, so the only generator of the presentation of `K₀(Vect(X))` that needs an
argument is `−[ℰ]`; and there the value is forced, being a two-sided inverse of the value at
`[ℰ]`, of which a monoid has at most one. -/
theorem eq_of_convolutive_of_eq_classOf {R : Type v} [Ring R]
    {c c' : VectorBundleKZero X → ℕ → R}
    (hadd : ∀ (a b : VectorBundleKZero X) (n : ℕ),
      c (a + b) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c a p.1 * c b p.2)
    (hzero : ∀ n : ℕ, c 0 n = if n = 0 then 1 else 0)
    (hadd' : ∀ (a b : VectorBundleKZero X) (n : ℕ),
      c' (a + b) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c' a p.1 * c' b p.2)
    (hzero' : ∀ n : ℕ, c' 0 n = if n = 0 then 1 else 0)
    (hgen : ∀ (M : X.Modules) (n : ℕ),
      c (VectorBundleKZero.classOf X M) n = c' (VectorBundleKZero.classOf X M) n)
    (a : VectorBundleKZero X) (n : ℕ) : c a n = c' a n := by
  suffices h : ∀ a : VectorBundleKZero X, seriesAt c a = seriesAt c' a by
    have hn := congrArg (PowerSeries.coeff n) (h a)
    rwa [coeff_seriesAt, coeff_seriesAt] at hn
  have hgenser : ∀ M : X.Modules, seriesAt c (VectorBundleKZero.classOf X M) =
      seriesAt c' (VectorBundleKZero.classOf X M) := fun M =>
    PowerSeries.ext fun k => by rw [coeff_seriesAt, coeff_seriesAt]; exact hgen M k
  intro a
  induction a using kZero_induction with
  | h0 => rw [seriesAt_zero hzero, seriesAt_zero hzero']
  | hof M => exact hgenser M
  | hneg M =>
      -- the value at `−[ℰ]` is a two-sided inverse of the value at `[ℰ]`, and a monoid has at
      -- most one of those
      have hleft : seriesAt c (-VectorBundleKZero.classOf X M) *
          seriesAt c' (VectorBundleKZero.classOf X M) = 1 := by
        rw [← hgenser M, ← seriesAt_add hadd, neg_add_cancel, seriesAt_zero hzero]
      have hright : seriesAt c' (VectorBundleKZero.classOf X M) *
          seriesAt c' (-VectorBundleKZero.classOf X M) = 1 := by
        rw [← seriesAt_add hadd', add_neg_cancel, seriesAt_zero hzero']
      exact left_inv_eq_right_inv hleft hright
  | hadd z w hz hw => rw [seriesAt_add hadd, seriesAt_add hadd', hz, hw]

end Stacks.WeilCohomology

end

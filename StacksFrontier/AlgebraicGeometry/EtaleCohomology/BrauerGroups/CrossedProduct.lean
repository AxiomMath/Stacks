module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Crossed product algebras

Let `L/K` be a finite extension with `G = Gal(L/K)` its group of `K`-algebra automorphisms, and
let `c : G × G → Lˣ` be any function. The *crossed product* `CrossedProduct c` is the space of
coefficient functions `G → L`, thought of as `⨁_{σ ∈ G} L · u σ`, with the multiplication
determined by the two rules

* `u σ * u τ = c (σ, τ) * u (σ * τ)`, and
* `u σ * a = σ a * u σ` for `a : L`,

which read on coefficients as the twisted convolution
`(x * y) ρ = ∑_{σ} x σ * σ (y (σ⁻¹ * ρ)) * c (σ, σ⁻¹ * ρ)`, recorded as `mul_apply`.

The reason the construction exists is that this multiplication is associative *exactly* when `c`
is a `2`-cocycle, and that is the content of `mul_assoc_iff_isMulCocycle₂` rather than a remark
beside it. Both directions are proved: the cocycle identity rearranges the double sum, and
conversely evaluating associativity on the three elements `u g, u h, u j` returns the identity.
The cocycle condition used is Mathlib's `groupCohomology.IsMulCocycle₂`, the same one as in the
degree-one file `Hilbert90` and in the reduction of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TwoCocycleInflation`.

Everything past the equivalence therefore assumes `[Fact (IsMulCocycle₂ c)]`. Under it the
crossed product is a finite central simple `K`-algebra of `K`-dimension `[L : K]²` containing a
copy of `L`; those are precisely the properties which make it a representative of a Brauer class
of `K` split by `L`, which is how
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.CrossedProductSplit` uses it.

## Main definitions

* `Stacks.GaloisCohomology.CrossedProduct`: the crossed product, as a type.
* `CrossedProduct.single σ a`: the homogeneous element `a * u σ`.
* `CrossedProduct.incl`, `CrossedProduct.inclRingHom`, `CrossedProduct.inclAlgHom`: the copy of
  `L` inside the crossed product. Because a general cocycle is not normalised, the identity
  element is `c (1, 1)⁻¹ * u 1` rather than `u 1`, and the embedding of `L` is
  `a ↦ a * c (1, 1)⁻¹ * u 1`.

## Main results

* `CrossedProduct.mul_assoc_iff_isMulCocycle₂`: associativity of the twisted convolution is the
  `2`-cocycle condition.
* `CrossedProduct.single_mul_single`: the multiplication table of the homogeneous elements.
* `CrossedProduct.finrank_eq`: the crossed product has `K`-dimension `[L : K]²`.
* `CrossedProduct.instIsCentralOfIsGalois`: the crossed product is central over `K`.
* `CrossedProduct.instIsSimpleRing`: the crossed product is a simple ring.

## Implementation notes

`CrossedProduct c` is a type synonym for `Gal(L/K) → L`; the additive and `K`-module structures
are transported from there, while the multiplication is defined from scratch. The cocycle
condition is carried by a `Fact` instance because the ring structure depends on it and instances
cannot take hypotheses.

The `2`-cocycle `c` is not assumed normalised, i.e. `c (1, σ)` and `c (σ, 1)` need not be `1`.
Writing `e = c (1, 1)`, the cocycle identity gives `c (1, σ) = e` and `c (σ, 1) = σ e`, so the
identity element of the crossed product is `e⁻¹ * u 1`; this is the only place where the lack of
normalisation shows up, and it is cheaper than proving that every cocycle is cohomologous to a
normalised one.

Simplicity is proved by the minimal-support argument: left-translating a nonzero element of a
two-sided ideal by some `u σ` puts `1` in its support, and the commutator with an element of `L`
moved by a second point of the support is a nonzero element of the ideal with strictly smaller
support. The base case of the induction is a nonzero homogeneous element, which has a right
inverse.

## References

* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7), whose proof identifies
  `H²(Gal(L/K), Lˣ)` with the relative Brauer group by means of this construction.
-/

@[expose] public noncomputable section

open Module
open groupCohomology

namespace Stacks.GaloisCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

-- The type does not depend on `c`; the twisting enters through the multiplication below.
/-- The underlying additive group of the crossed product. -/
def CrossedProduct (c : Gal(L/K) × Gal(L/K) → Lˣ) : Type _ := Gal(L/K) → L

namespace CrossedProduct

variable {c : Gal(L/K) × Gal(L/K) → Lˣ}

/-- Addition of coefficient functions. -/
instance : AddCommGroup (CrossedProduct c) := inferInstanceAs (AddCommGroup (Gal(L/K) → L))

/-- Two elements agreeing coefficientwise are equal. -/
theorem ext {x y : CrossedProduct c} (h : ∀ σ, x σ = y σ) : x = y := funext h

/-- Coefficients of a sum. -/
@[simp] theorem add_apply (x y : CrossedProduct c) (σ : Gal(L/K)) :
    (x + y) σ = x σ + y σ := rfl

/-- Coefficients of zero. -/
@[simp] theorem zero_apply (σ : Gal(L/K)) : (0 : CrossedProduct c) σ = 0 := rfl

/-- Coefficients of a negative. -/
@[simp] theorem neg_apply (x : CrossedProduct c) (σ : Gal(L/K)) : (-x) σ = -x σ := rfl

/-- The coercion to `L` of the Galois action on `Lˣ` is the Galois action on `L`. -/
theorem val_units_smul (σ : Gal(L/K)) (u : Lˣ) : ((σ • u : Lˣ) : L) = σ (u : L) := rfl

/-- A Galois automorphism carries `u⁻¹` to the inverse of the image of `u`. -/
theorem apply_val_inv_mul_apply_val (σ : Gal(L/K)) (u : Lˣ) :
    σ ((u⁻¹ : Lˣ) : L) * σ (u : L) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

/-- A non-identity automorphism moves some element. -/
theorem exists_apply_ne_of_ne_one {ρ : Gal(L/K)} (hρ : ρ ≠ 1) : ∃ a : L, ρ a ≠ a := by
  by_contra h
  exact hρ (AlgEquiv.ext fun a => by simpa using not_not.1 (not_exists.1 h a))

open Classical in
/-- `single σ a` is the element `a * u σ`: the coefficient of `u σ` is `a` and all others
vanish. -/
def single (σ : Gal(L/K)) (a : L) : CrossedProduct c := fun ρ => if ρ = σ then a else 0

/-- The coefficient of `u σ` in `a * u σ`. -/
@[simp] theorem single_apply_self (σ : Gal(L/K)) (a : L) :
    (single σ a : CrossedProduct c) σ = a := by
  classical simp [single]

/-- The other coefficients of `a * u σ` vanish. -/
theorem single_apply_of_ne {σ ρ : Gal(L/K)} (a : L) (h : ρ ≠ σ) :
    (single σ a : CrossedProduct c) ρ = 0 := by
  classical simp [single, h]

/-- An element vanishes exactly when all of its coefficients do. -/
theorem eq_zero_iff {x : CrossedProduct c} : x = 0 ↔ ∀ σ, x σ = 0 :=
  ⟨fun h σ => by simp [h], ext⟩

/-- `a * u σ` vanishes exactly when `a` does. -/
theorem single_eq_zero_iff {σ : Gal(L/K)} {a : L} :
    (single σ a : CrossedProduct c) = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => ext fun ρ => ?_⟩
  · simpa using congrFun h σ
  · by_cases hρ : ρ = σ
    · subst hρ
      simp [h]
    · simp [single_apply_of_ne _ hρ]

variable [FiniteDimensional K L]

/-- The twisted convolution product, associative exactly when `c` is a `2`-cocycle. -/
instance : Mul (CrossedProduct c) :=
  ⟨fun x y ρ => ∑ σ : Gal(L/K), x σ * σ (y (σ⁻¹ * ρ)) * (c (σ, σ⁻¹ * ρ) : L)⟩

/-- The coefficients of a product: the twisted convolution defining the crossed product. -/
theorem mul_apply (x y : CrossedProduct c) (ρ : Gal(L/K)) :
    (x * y) ρ = ∑ σ : Gal(L/K), x σ * σ (y (σ⁻¹ * ρ)) * (c (σ, σ⁻¹ * ρ) : L) := rfl

/-- The coefficients of a left multiple by `single σ a`. -/
theorem single_mul_apply (σ : Gal(L/K)) (a : L) (x : CrossedProduct c) (ρ : Gal(L/K)) :
    ((single σ a : CrossedProduct c) * x) ρ = a * σ (x (σ⁻¹ * ρ)) * (c (σ, σ⁻¹ * ρ) : L) := by
  rw [mul_apply, Finset.sum_eq_single σ (fun g _ hg => by
    rw [single_apply_of_ne a hg, zero_mul, zero_mul]) (fun h => absurd (Finset.mem_univ σ) h),
    single_apply_self]

/-- The coefficients of a right multiple by `single τ b`. -/
theorem mul_single_apply (x : CrossedProduct c) (τ : Gal(L/K)) (b : L) (ρ : Gal(L/K)) :
    (x * (single τ b : CrossedProduct c)) ρ
      = x (ρ * τ⁻¹) * (ρ * τ⁻¹) b * (c (ρ * τ⁻¹, τ) : L) := by
  rw [mul_apply, Finset.sum_eq_single (ρ * τ⁻¹) (fun g _ hg => ?_)
    (fun h => absurd (Finset.mem_univ _) h)]
  · rw [show (ρ * τ⁻¹)⁻¹ * ρ = τ by group, single_apply_self]
  · rw [single_apply_of_ne b (fun hgτ => hg (by rw [← hgτ]; group)), map_zero, mul_zero, zero_mul]

/-- The product of two `single`s: `(a u σ) (b u τ) = a σ(b) c(σ,τ) u_{στ}`. -/
theorem single_mul_single (σ τ : Gal(L/K)) (a b : L) :
    (single σ a : CrossedProduct c) * single τ b
      = single (σ * τ) (a * σ b * (c (σ, τ) : L)) := by
  refine ext fun ρ => ?_
  rw [single_mul_apply]
  by_cases hρ : ρ = σ * τ
  · subst hρ
    rw [show σ⁻¹ * (σ * τ) = τ by group, single_apply_self, single_apply_self]
  · rw [single_apply_of_ne _ hρ, single_apply_of_ne b
      (fun h => hρ (by rw [← h]; group)), map_zero, mul_zero, zero_mul]

omit [FiniteDimensional K L] in
/-- The `2`-cocycle condition, with the values coerced into `L`. -/
theorem val_isMulCocycle₂ (hc : IsMulCocycle₂ c) (g h j : Gal(L/K)) :
    (c (g * h, j) : L) * (c (g, h) : L) = g (c (h, j) : L) * (c (g, h * j) : L) := by
  simpa only [Units.val_mul, val_units_smul] using congrArg Units.val (hc g h j)

/-- If the twisted convolution product is associative, then `c` is a `2`-cocycle: associativity
on the three basis elements `u g, u h, u j` already gives the cocycle identity at `(g, h, j)`. -/
theorem isMulCocycle₂_of_mul_assoc
    (hassoc : ∀ x y z : CrossedProduct c, x * y * z = x * (y * z)) : IsMulCocycle₂ c := by
  intro g h j
  have hs := hassoc (single g 1) (single h 1) (single j 1)
  simp only [single_mul_single, map_one, one_mul, mul_one] at hs
  rw [mul_assoc g h j] at hs
  have hco := congrFun hs (g * (h * j))
  rw [single_apply_self, single_apply_self] at hco
  refine Units.ext ?_
  simp only [Units.val_mul, val_units_smul]
  linear_combination hco

/-- Under the `2`-cocycle condition the twisted convolution product is associative. -/
theorem mul_assoc_of_isMulCocycle₂ (hc : IsMulCocycle₂ c) (x y z : CrossedProduct c) :
    x * y * z = x * (y * z) := by
  refine ext fun ρ => ?_
  have hR : (x * (y * z)) ρ = ∑ σ : Gal(L/K), ∑ h : Gal(L/K),
      x σ * (σ (y h) * σ (h (z (h⁻¹ * (σ⁻¹ * ρ)))) * σ (c (h, h⁻¹ * (σ⁻¹ * ρ)) : L))
        * (c (σ, σ⁻¹ * ρ) : L) := by
    rw [mul_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => by rw [map_mul, map_mul]
  have hL : (x * y * z) ρ = ∑ σ : Gal(L/K), ∑ h : Gal(L/K),
      x σ * (σ (y h) * σ (h (z (h⁻¹ * (σ⁻¹ * ρ)))) * σ (c (h, h⁻¹ * (σ⁻¹ * ρ)) : L))
        * (c (σ, σ⁻¹ * ρ) : L) := by
    rw [mul_apply]
    have e₁ : ∀ τ : Gal(L/K), (x * y) τ * τ (z (τ⁻¹ * ρ)) * (c (τ, τ⁻¹ * ρ) : L)
        = ∑ σ : Gal(L/K), x σ * σ (y (σ⁻¹ * τ)) * (c (σ, σ⁻¹ * τ) : L)
          * τ (z (τ⁻¹ * ρ)) * (c (τ, τ⁻¹ * ρ) : L) := fun τ => by
      rw [mul_apply, Finset.sum_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) => e₁ τ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    refine Eq.trans (Equiv.sum_comp (Equiv.mulLeft σ) _).symm
      (Finset.sum_congr rfl fun h _ => ?_)
    simp only [Equiv.coe_mulLeft]
    rw [show σ⁻¹ * (σ * h) = h by group, show (σ * h)⁻¹ * ρ = h⁻¹ * (σ⁻¹ * ρ) by group,
      AlgEquiv.mul_apply]
    have hcoc := val_isMulCocycle₂ hc σ h (h⁻¹ * (σ⁻¹ * ρ))
    rw [show h * (h⁻¹ * (σ⁻¹ * ρ)) = σ⁻¹ * ρ by group] at hcoc
    linear_combination (x σ * σ (y h) * σ (h (z (h⁻¹ * (σ⁻¹ * ρ))))) * hcoc
  rw [hL, hR]

/-- **Associativity of the twisted convolution product is exactly the `2`-cocycle condition.**

One direction is the computation that rearranges a double sum; the other direction evaluates
associativity on the three basis elements `u g, u h, u j` and reads off the identity. -/
theorem mul_assoc_iff_isMulCocycle₂ :
    (∀ x y z : CrossedProduct c, x * y * z = x * (y * z)) ↔ IsMulCocycle₂ c :=
  ⟨isMulCocycle₂_of_mul_assoc, mul_assoc_of_isMulCocycle₂⟩

/-- The element `c (1, 1)⁻¹ * u 1` of the crossed product, an identity when `c` is a cocycle. -/
instance : One (CrossedProduct c) := ⟨single 1 (((c (1, 1))⁻¹ : Lˣ) : L)⟩

omit [FiniteDimensional K L] in
/-- The candidate identity element, `c (1, 1)⁻¹ * u 1`. -/
theorem one_def : (1 : CrossedProduct c) = single 1 (((c (1, 1))⁻¹ : Lˣ) : L) := rfl

/-- Left multiplication by `a * c (1, 1)⁻¹ * u 1` scales every coefficient by `a`. -/
private theorem single_one_mul_apply_of_isMulCocycle₂ (hc : IsMulCocycle₂ c) (a : L)
    (x : CrossedProduct c) (ρ : Gal(L/K)) :
    ((single 1 (a * (((c (1, 1))⁻¹ : Lˣ) : L)) : CrossedProduct c) * x) ρ = a * x ρ := by
  rw [single_mul_apply]
  simp only [inv_one, one_mul, AlgEquiv.one_apply]
  rw [map_one_fst_of_isMulCocycle₂ hc ρ]
  linear_combination (a * x ρ) * Units.inv_mul (c (1, 1))

/-- Right multiplication by `a * c (1, 1)⁻¹ * u 1` scales the coefficient of `u ρ` by `ρ a`. -/
private theorem mul_single_one_apply_of_isMulCocycle₂ (hc : IsMulCocycle₂ c) (x : CrossedProduct c)
    (a : L) (ρ : Gal(L/K)) :
    (x * (single 1 (a * (((c (1, 1))⁻¹ : Lˣ) : L)) : CrossedProduct c)) ρ = x ρ * ρ a := by
  rw [mul_single_apply]
  simp only [inv_one, mul_one]
  rw [map_one_snd_of_isMulCocycle₂ hc ρ, val_units_smul, map_mul]
  linear_combination (x ρ * ρ a) * apply_val_inv_mul_apply_val ρ (c (1, 1))

section Cocycle

variable (hc : IsMulCocycle₂ c)
include hc

/-- `single 1 (c (1,1))⁻¹` is a left identity. -/
theorem one_mul_of_isMulCocycle₂ (x : CrossedProduct c) : 1 * x = x := by
  refine ext fun ρ => ?_
  simpa [one_def] using single_one_mul_apply_of_isMulCocycle₂ hc 1 x ρ

/-- `single 1 (c (1,1))⁻¹` is a right identity. -/
theorem mul_one_of_isMulCocycle₂ (x : CrossedProduct c) : x * 1 = x := by
  refine ext fun ρ => ?_
  simpa [one_def] using mul_single_one_apply_of_isMulCocycle₂ hc x 1 ρ

omit hc in
/-- Zero is a left annihilator. -/
theorem zero_mul' (x : CrossedProduct c) : 0 * x = 0 :=
  ext fun ρ => by simp [mul_apply]

omit hc in
/-- Zero is a right annihilator. -/
theorem mul_zero' (x : CrossedProduct c) : x * 0 = 0 :=
  ext fun ρ => by simp [mul_apply]

omit hc in
/-- The product is additive in its right argument. -/
theorem left_distrib' (x y z : CrossedProduct c) : x * (y + z) = x * y + x * z := by
  refine ext fun ρ => ?_
  simp only [add_apply, mul_apply, map_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

omit hc in
/-- The product is additive in its left argument. -/
theorem right_distrib' (x y z : CrossedProduct c) : (x + y) * z = x * z + y * z := by
  refine ext fun ρ => ?_
  simp only [add_apply, mul_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

end Cocycle

open Classical in
/-- The support of an element of the crossed product: the set of group elements whose
coefficient is nonzero. -/
def support (x : CrossedProduct c) : Finset Gal(L/K) := Finset.univ.filter fun σ => x σ ≠ 0

/-- Membership in the support. -/
theorem mem_support {x : CrossedProduct c} {σ : Gal(L/K)} : σ ∈ support x ↔ x σ ≠ 0 := by
  classical simp [support]

/-- An element with empty support is zero. -/
theorem eq_zero_of_card_support_eq_zero {x : CrossedProduct c} (h : (support x).card = 0) :
    x = 0 := by
  rw [Finset.card_eq_zero] at h
  exact eq_zero_iff.2 fun σ => not_not.1 fun hσ => by simpa [h] using mem_support.2 hσ

/-- An element supported in at most one point is a `single`. -/
theorem eq_single_of_support_subset_singleton {x : CrossedProduct c} (τ : Gal(L/K))
    (h : support x ⊆ {τ}) : x = single τ (x τ) := by
  refine ext fun ρ => ?_
  by_cases hρ : ρ = τ
  · subst hρ
    rw [single_apply_self]
  · rw [single_apply_of_ne _ hρ]
    by_contra hx
    exact hρ (Finset.mem_singleton.1 (h (mem_support.2 hx)))

/-- A nonzero homogeneous element `a * u τ` has a right inverse, so it generates the whole
algebra as a two-sided ideal. -/
theorem exists_mul_single_eq_one (τ : Gal(L/K)) {a : L} (ha : a ≠ 0) :
    ∃ w : CrossedProduct c, (single τ a : CrossedProduct c) * w = 1 := by
  refine ⟨single τ⁻¹ (τ⁻¹ ((((c (1, 1))⁻¹ : Lˣ) : L) / (a * ((c (τ, τ⁻¹) : Lˣ) : L)))), ?_⟩
  rw [single_mul_single, mul_inv_cancel, one_def, ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]
  congr 1
  have h1 : ((c (τ, τ⁻¹) : Lˣ) : L) ≠ 0 := Units.ne_zero _
  field_simp

/-- Left multiplication by `u σ` translates the support. -/
theorem support_single_one_mul (σ : Gal(L/K)) (x : CrossedProduct c) :
    support ((single σ 1 : CrossedProduct c) * x)
      = (support x).map (Equiv.mulLeft σ).toEmbedding := by
  ext ρ
  rw [mem_support, Finset.mem_map, single_mul_apply, one_mul]
  simp only [Equiv.coe_toEmbedding, Equiv.coe_mulLeft]
  constructor
  · intro h
    exact ⟨σ⁻¹ * ρ, mem_support.2 fun h0 => h (by rw [h0, map_zero, zero_mul]),
      mul_inv_cancel_left σ ρ⟩
  · rintro ⟨b, hb, rfl⟩
    rw [inv_mul_cancel_left]
    exact mul_ne_zero (fun h0 => mem_support.1 hb ((map_eq_zero σ).1 h0)) (Units.ne_zero _)

section Ring

variable [hcoc : Fact (IsMulCocycle₂ c)]

/-- Under the `2`-cocycle condition the twisted convolution makes the crossed product a ring. -/
instance : Ring (CrossedProduct c) where
  __ := (inferInstance : AddCommGroup (CrossedProduct c))
  mul := (· * ·)
  one := 1
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  mul_assoc := mul_assoc_of_isMulCocycle₂ hcoc.out
  one_mul := one_mul_of_isMulCocycle₂ hcoc.out
  mul_one := mul_one_of_isMulCocycle₂ hcoc.out

/-- The crossed product is nonzero. -/
instance : Nontrivial (CrossedProduct c) := by
  refine ⟨1, 0, fun h => ?_⟩
  rw [one_def] at h
  exact Units.ne_zero _ (single_eq_zero_iff.1 h)

/-- The copy of `L` inside the crossed product: the coefficient of `u 1`, normalised so that
this is a ring homomorphism. -/
def incl (a : L) : CrossedProduct c := single 1 (a * (((c (1, 1))⁻¹ : Lˣ) : L))

omit [FiniteDimensional K L] hcoc in
/-- The defining formula for the copy of `L`. -/
theorem incl_def (a : L) :
    (incl a : CrossedProduct c) = single 1 (a * (((c (1, 1))⁻¹ : Lˣ) : L)) := rfl

/-- Multiplying by an element of `L` on the left scales every coefficient. -/
theorem incl_mul_apply (a : L) (x : CrossedProduct c) (ρ : Gal(L/K)) :
    ((incl a : CrossedProduct c) * x) ρ = a * x ρ := by
  rw [incl_def, single_one_mul_apply_of_isMulCocycle₂ hcoc.out]

/-- Multiplying by an element of `L` on the right scales the coefficient of `u ρ` by `ρ a`. -/
theorem mul_incl_apply (x : CrossedProduct c) (a : L) (ρ : Gal(L/K)) :
    (x * (incl a : CrossedProduct c)) ρ = x ρ * ρ a := by
  rw [incl_def, mul_single_one_apply_of_isMulCocycle₂ hcoc.out]

/-- The homogeneous elements of a fixed degree form a subgroup. -/
theorem single_add (σ : Gal(L/K)) (a b : L) :
    (single σ (a + b) : CrossedProduct c) = single σ a + single σ b := by
  refine ext fun ρ => ?_
  by_cases hρ : ρ = σ
  · subst hρ
    simp
  · simp [single_apply_of_ne _ hρ]

/-- The copy of `L` inside the crossed product, as a ring homomorphism. -/
def inclRingHom : L →+* CrossedProduct c where
  toFun := incl
  map_one' := by rw [incl_def, one_mul, one_def]
  map_mul' a b := by
    rw [incl_def, incl_def, incl_def, single_mul_single, one_mul, AlgEquiv.one_apply]
    congr 1
    linear_combination (-(a * b * (((c (1, 1))⁻¹ : Lˣ) : L))) * Units.inv_mul (c (1, 1))
  map_zero' := by rw [incl_def, zero_mul, single_eq_zero_iff]
  map_add' a b := by rw [incl_def, incl_def, incl_def, add_mul, single_add]

/-- `inclRingHom` is `incl`. -/
@[simp] theorem inclRingHom_apply (a : L) : inclRingHom (c := c) a = incl a := rfl

/-- The product `u σ * a` in the crossed product: `u σ * a = σ(a) * u σ`. -/
theorem single_one_mul_incl (σ : Gal(L/K)) (t : L) :
    (single σ 1 : CrossedProduct c) * incl t = single σ (σ t) := by
  rw [incl_def, single_mul_single, mul_one, one_mul]
  congr 1
  rw [map_mul, map_one_snd_of_isMulCocycle₂ hcoc.out σ, val_units_smul]
  linear_combination (σ t) * apply_val_inv_mul_apply_val σ (c (1, 1))

/-- The product `a * u σ` in the crossed product. -/
theorem incl_mul_single_one (σ : Gal(L/K)) (t : L) :
    (incl t : CrossedProduct c) * single σ 1 = single σ t := by
  rw [incl_def, single_mul_single, one_mul, AlgEquiv.one_apply, mul_one]
  congr 1
  rw [map_one_fst_of_isMulCocycle₂ hcoc.out σ]
  linear_combination t * Units.inv_mul (c (1, 1))

/-- The product of two basis elements: `u σ * u τ = c (σ, τ) * u (σ τ)`. -/
theorem single_one_mul_single_one (σ τ : Gal(L/K)) :
    (single σ 1 : CrossedProduct c) * single τ 1
      = (incl ((c (σ, τ) : Lˣ) : L) : CrossedProduct c) * single (σ * τ) 1 := by
  rw [incl_mul_single_one, single_mul_single, map_one, one_mul, one_mul]

/-- The `K`-algebra structure, through the central copy of `K` inside `L`. -/
instance : Algebra K (CrossedProduct c) :=
  RingHom.toAlgebra' ((inclRingHom (c := c)).comp (algebraMap K L)) fun k x => by
    refine ext fun ρ => ?_
    rw [RingHom.coe_comp, Function.comp_apply, inclRingHom_apply, incl_mul_apply,
      mul_incl_apply, AlgEquiv.commutes, mul_comm]

/-- The structure map of the `K`-algebra is the copy of `L` restricted to `K`. -/
theorem algebraMap_apply (k : K) :
    algebraMap K (CrossedProduct c) k = incl (algebraMap K L k) := rfl

/-- The copy of `L` inside the crossed product, as a `K`-algebra homomorphism. -/
def inclAlgHom : L →ₐ[K] CrossedProduct c where
  __ := inclRingHom (c := c)
  commutes' _ := rfl

/-- `inclAlgHom` is `incl`. -/
@[simp] theorem inclAlgHom_apply (a : L) : inclAlgHom (c := c) a = incl a := rfl

/-- The `K`-action on coefficients. -/
theorem smul_apply (k : K) (x : CrossedProduct c) (ρ : Gal(L/K)) :
    (k • x) ρ = algebraMap K L k * x ρ := by
  rw [Algebra.smul_def, algebraMap_apply, incl_mul_apply]

/-- The crossed product is, as a `K`-vector space, the space of coefficient functions. -/
def toPiLinearMap : CrossedProduct c →ₗ[K] (Gal(L/K) → L) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' k x := funext fun ρ => (smul_apply k x ρ).trans (Algebra.smul_def k (x ρ)).symm

/-- The crossed product is, as a `K`-vector space, the space of coefficient functions. -/
def toPi : CrossedProduct c ≃ₗ[K] (Gal(L/K) → L) :=
  LinearEquiv.ofBijective toPiLinearMap ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

/-- The crossed product is a finite-dimensional `K`-vector space. -/
instance : FiniteDimensional K (CrossedProduct c) :=
  Module.Finite.equiv (toPi (c := c)).symm

/-- **The crossed product has `K`-dimension `[L:K]²`.** -/
theorem finrank_eq [IsGalois K L] :
    finrank K (CrossedProduct c) = finrank K L ^ 2 := by
  rw [(toPi (c := c)).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L, smul_eq_mul,
    ← pow_two]

/-- An element commuting with the copy of `L` is supported on the identity. -/
theorem apply_eq_zero_of_forall_incl_mul_comm {x : CrossedProduct c}
    (hx : ∀ a : L, incl a * x = x * incl a) {ρ : Gal(L/K)} (hρ : ρ ≠ 1) : x ρ = 0 := by
  obtain ⟨a, ha⟩ := exists_apply_ne_of_ne_one hρ
  have h := congrFun (hx a) ρ
  rw [incl_mul_apply, mul_incl_apply] at h
  exact (mul_eq_zero.1 (by linear_combination h : x ρ * (a - ρ a) = 0)).resolve_right
    (sub_ne_zero.2 ha.symm)

/-- **The crossed product is central over `K`.** An element commuting with the copy of `L`
is supported on the identity, and one commuting with every `u σ` has its coefficient fixed by
the whole Galois group, hence lying in `K`. -/
instance [IsGalois K L] : Algebra.IsCentral K (CrossedProduct c) where
  out := by
    intro x hx
    rw [Subalgebra.mem_center_iff] at hx
    have hfix : ∀ σ : Gal(L/K), σ (x 1 * ((c (1, 1) : Lˣ) : L)) = x 1 * ((c (1, 1) : Lˣ) : L) := by
      intro σ
      have h := congrFun (hx (single σ 1)) σ
      rw [single_mul_apply, mul_single_apply] at h
      simp only [one_mul, inv_mul_cancel, mul_inv_cancel, map_one, mul_one] at h
      rw [map_one_snd_of_isMulCocycle₂ hcoc.out σ, map_one_fst_of_isMulCocycle₂ hcoc.out σ,
        val_units_smul] at h
      rwa [map_mul]
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    refine Algebra.mem_bot.2 ⟨k, ?_⟩
    rw [algebraMap_apply, hk, incl_def]
    refine (ext fun ρ => ?_).symm
    by_cases hρ : ρ = 1
    · subst hρ
      rw [single_apply_self]
      linear_combination (-(x 1)) * Units.mul_inv (c (1, 1))
    · rw [single_apply_of_ne _ hρ,
        apply_eq_zero_of_forall_incl_mul_comm (fun a => hx (incl a)) hρ]

/-- A two-sided ideal containing a nonzero element supported in at most one point contains the
identity. -/
theorem one_mem_of_card_support_le_one {I : TwoSidedIdeal (CrossedProduct c)}
    {y : CrossedProduct c} (hyI : y ∈ I) (hy0 : y ≠ 0) (hle : (support y).card ≤ 1) :
    (1 : CrossedProduct c) ∈ I := by
  obtain ⟨τ, hτ⟩ := Finset.card_le_one_iff_subset_singleton.1 hle
  have hyτ : y τ ≠ 0 := fun h0 => hy0 (by
    rw [eq_single_of_support_subset_singleton τ hτ, h0, single_eq_zero_iff])
  obtain ⟨w, hw⟩ := exists_mul_single_eq_one (c := c) τ hyτ
  rw [← eq_single_of_support_subset_singleton τ hτ] at hw
  exact hw ▸ I.mul_mem_right _ _ hyI

/-- In a two-sided ideal, an element whose support has at least two points yields a nonzero
element of strictly smaller support. -/
theorem exists_mem_card_support_lt {I : TwoSidedIdeal (CrossedProduct c)}
    {y : CrossedProduct c} (hyI : y ∈ I) (hlt : 1 < (support y).card) :
    ∃ z ∈ I, z ≠ 0 ∧ (support z).card < (support y).card := by
  classical
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, hne⟩ := Finset.one_lt_card.1 hlt
  obtain ⟨y', hy'def⟩ : ∃ y' : CrossedProduct c,
      y' = (single τ₁⁻¹ 1 : CrossedProduct c) * y := ⟨_, rfl⟩
  have hy'I : y' ∈ I := hy'def ▸ I.mul_mem_left _ _ hyI
  have hcard' : (support y').card = (support y).card := by
    rw [hy'def, support_single_one_mul, Finset.card_map]
  have h1 : (1 : Gal(L/K)) ∈ support y' := by
    rw [hy'def, support_single_one_mul]
    exact Finset.mem_map.2 ⟨τ₁, hτ₁, by simp⟩
  have h2 : τ₁⁻¹ * τ₂ ∈ support y' := by
    rw [hy'def, support_single_one_mul]
    exact Finset.mem_map.2 ⟨τ₂, hτ₂, by simp⟩
  have hne' : τ₁⁻¹ * τ₂ ≠ 1 := fun h => hne (by rw [← mul_one τ₁, ← h]; group)
  obtain ⟨a, ha⟩ := exists_apply_ne_of_ne_one hne'
  obtain ⟨z, hzdef⟩ : ∃ z : CrossedProduct c,
      z = (incl a : CrossedProduct c) * y' - y' * (incl a : CrossedProduct c) := ⟨_, rfl⟩
  have hzapply : ∀ ρ : Gal(L/K), z ρ = (a - ρ a) * y' ρ := by
    intro ρ
    rw [hzdef]
    show (((incl a : CrossedProduct c) * y') ρ - (y' * (incl a : CrossedProduct c)) ρ) = _
    rw [incl_mul_apply, mul_incl_apply]
    ring
  have hzI : z ∈ I := hzdef ▸ I.sub_mem (I.mul_mem_left _ _ hy'I) (I.mul_mem_right _ _ hy'I)
  have hz0 : z ≠ 0 := by
    intro h0
    refine mul_ne_zero (sub_ne_zero.2 (Ne.symm ha)) (mem_support.1 h2) ?_
    rw [← hzapply (τ₁⁻¹ * τ₂), h0, zero_apply]
  have hsub : support z ⊆ (support y').erase 1 := by
    intro ρ hρ
    refine Finset.mem_erase.2 ⟨fun h0 => ?_, mem_support.2 fun h0 => mem_support.1 hρ ?_⟩
    · rw [h0] at hρ
      exact mem_support.1 hρ (by rw [hzapply, AlgEquiv.one_apply, sub_self, zero_mul])
    · rw [hzapply, h0, mul_zero]
  refine ⟨z, hzI, hz0, ?_⟩
  calc (support z).card ≤ ((support y').erase 1).card := Finset.card_le_card hsub
    _ = (support y').card - 1 := Finset.card_erase_of_mem h1
    _ < (support y).card := by omega

/-- **The crossed product is a simple ring.** A nonzero two-sided ideal contains an element of
minimal support; left-translating by some `u σ` makes the identity lie in that support, and then
the commutator with a suitable element of `L` shrinks the support, unless the support is a single
point — in which case the ideal contains a nonzero homogeneous element, hence the identity. -/
instance : IsSimpleRing (CrossedProduct c) where
  simple :=
  { eq_bot_or_eq_top := by
      classical
      intro I
      by_cases hI : I = ⊥
      · exact Or.inl hI
      refine Or.inr ?_
      obtain ⟨x, hxI, hx0⟩ : ∃ x, x ∈ I ∧ x ≠ 0 := by
        by_contra hcon
        refine hI (le_antisymm (fun y hy => (TwoSidedIdeal.mem_bot _).2 ?_) bot_le)
        by_contra hy0
        exact (not_exists.1 hcon y) ⟨hy, hy0⟩
      suffices H : ∀ n : ℕ, ∀ y : CrossedProduct c, y ∈ I → y ≠ 0 → (support y).card ≤ n →
          (1 : CrossedProduct c) ∈ I from
        TwoSidedIdeal.eq_top _ (H (support x).card x hxI hx0 le_rfl)
      intro n
      induction n with
      | zero =>
        intro y hyI hy0 hcard
        exact absurd (eq_zero_of_card_support_eq_zero (Nat.le_zero.1 hcard)) hy0
      | succ n ih =>
        intro y hyI hy0 hcard
        by_cases hle : (support y).card ≤ 1
        · exact one_mem_of_card_support_le_one hyI hy0 hle
        obtain ⟨z, hzI, hz0, hlt⟩ := exists_mem_card_support_lt hyI (not_le.1 hle)
        exact ih z hzI hz0 (by omega) }

end Ring

end CrossedProduct

end Stacks.GaloisCohomology

end

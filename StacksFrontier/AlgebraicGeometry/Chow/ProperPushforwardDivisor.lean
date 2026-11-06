module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Proper pushforward of a principal divisor

Stacks 02RU says that the degree of a principal divisor on a proper curve over a field `K`
vanishes: if `X` is a one-dimensional integral scheme proper over `Spec K` and `f` is an
invertible rational function on `X`, then
`∑_{x ∈ X closed} [κ(x) : K] · ord_{𝒪_{X,x}}(f) = 0`, equivalently `c_*div(f) = 0` for the
structure morphism `c : X → Spec K`.

This file contains the parts of that statement which are independent of the graph construction
of Stacks 02RQ and of the norm formula for a finite extension of function fields (Stacks 02RT,
resting on the determinant computation of Stacks 02MJ).

The first part is the **projective line case**, which is the base case of the reduction: for
the rational function field `K(t)` the finite places are the monic irreducible polynomials
`p ∈ K[t]`, the degree of such a place is `p.natDegree`, the place at infinity has degree one,
and the order of `g ∈ K(t)^*` at `p` is the difference of the multiplicities of `p` in the
numerator and the denominator of `g`. The sum of `ord_p(g) · deg(p)` over the finite places
is the integer degree `RatFunc.intDegree g = deg(num g) - deg(denom g)` of `g`, and the order
at infinity is its negative, so the total degree is zero. This is
`Stacks.Chow.sum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero`.

The second part consists of two facts about Mathlib's pushforward of algebraic cycles,
`AlgebraicGeometry.AlgebraicCycle.map`, which is the operation the Chow-theoretic statement is
phrased with. `AlgebraicCycle.map_apply_eq_zero_of_forall_weight_ne` is the case of Stacks 02R4
in which the weight (the `δ`-dimension) drops at every point of a fibre, so that the
pushforward coefficient there vanishes; this is the "image has smaller dimension" branch of
every pushforward computation. `AlgebraicCycle.map_apply_of_subsingleton` identifies the single
coefficient of a pushforward to a one-point target — such as the spectrum of a field — with the
total weighted degree of the cycle, which is the reduction of `c_*div(f) = 0` to a degree
computation.

## Main results

* `Stacks.Chow.sum_map_natDegree_normalizedFactors` — the degrees of the monic irreducible
  factors of a nonzero polynomial, counted with multiplicity, add up to its degree.
* `Stacks.Chow.ordAt_mul` — the order at a monic irreducible polynomial is additive, i.e.
  `div(gh) = div(g) + div(h)` on the projective line.
* `Stacks.Chow.sum_ordAt_mul_natDegree` — the degree of the finite part of the principal
  divisor of `g` is `RatFunc.intDegree g`.
* `Stacks.Chow.sum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero` and
  `Stacks.Chow.finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero` — the degree of a principal
  divisor on the projective line is zero.
* `AlgebraicGeometry.AlgebraicCycle.map_apply_eq_zero_of_forall_weight_ne` and
  `AlgebraicGeometry.AlgebraicCycle.map_apply_of_subsingleton` — the two elementary
  computations of a pushforward coefficient used by Stacks 02R4.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial UniqueFactorizationMonoid

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] [DecidableEq k]

/-! ### Degrees of the factors of a polynomial -/

/-- The degrees of the monic irreducible factors of a nonzero polynomial over a field, counted
with multiplicity, add up to the degree of the polynomial. -/
theorem sum_map_natDegree_normalizedFactors (q : k[X]) (hq : q ≠ 0) :
    ((normalizedFactors q).map natDegree).sum = q.natDegree := by
  rw [← natDegree_multiset_prod _ fun h => (irreducible_of_normalized_factor _ h).ne_zero rfl]
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hq))

/-- The sum of `(multiplicity of p in q) * deg p` over any finite set of polynomials containing
the monic irreducible factors of a nonzero `q` is the degree of `q`. -/
theorem sum_count_normalizedFactors_mul_natDegree (q : k[X]) (hq : q ≠ 0) (s : Finset k[X])
    (hs : (normalizedFactors q).toFinset ⊆ s) :
    ∑ p ∈ s, ((normalizedFactors q).count p : ℤ) * p.natDegree = q.natDegree := by
  have key : ∑ p ∈ (normalizedFactors q).toFinset,
      ((normalizedFactors q).count p : ℤ) * p.natDegree = q.natDegree := by
    rw [← sum_map_natDegree_normalizedFactors q hq, Finset.sum_multiset_map_count]
    push_cast
    simp [mul_comm]
  rw [← key, Finset.sum_subset hs]
  intro p _ hp
  simp [Multiset.count_eq_zero_of_notMem (fun h => hp (Multiset.mem_toFinset.mpr h))]

/-! ### Orders of a rational function on the projective line -/

/-- The order of vanishing of a rational function `g` at a monic irreducible polynomial `p`:
the multiplicity of `p` in the numerator of `g` minus its multiplicity in the denominator.
For a monic irreducible `p` this is the order of `g` in the discrete valuation ring
`k[X]_{(p)}`, i.e. the coefficient of the corresponding closed point of the affine line in the
principal divisor of `g`. -/
def ordAt (p : k[X]) (g : RatFunc k) : ℤ :=
  ((normalizedFactors g.num).count p : ℤ) - ((normalizedFactors g.denom).count p : ℤ)

/-- The order of vanishing of a rational function at the point at infinity of the projective
line: minus its integer degree `deg(num) - deg(denom)`. -/
def ordAtInfty (g : RatFunc k) : ℤ := -g.intDegree

/-- The zero rational function has order `0` at every polynomial `p`. -/
@[simp]
theorem ordAt_zero (p : k[X]) : ordAt p (0 : RatFunc k) = 0 := by
  simp [ordAt]

/-- The rational function `1` has order `0` at every polynomial `p`. -/
@[simp]
theorem ordAt_one (p : k[X]) : ordAt p (1 : RatFunc k) = 0 := by
  simp [ordAt]

omit [DecidableEq k] in
/-- The zero rational function has order `0` at the point at infinity. -/
@[simp]
theorem ordAtInfty_zero : ordAtInfty (0 : RatFunc k) = 0 := by
  simp [ordAtInfty]

/-- Multiplicities of `p` among the normalized factors add up across an equality of products of
nonzero polynomials. -/
private theorem count_add_count_eq_of_mul_eq (p : k[X]) {x y z w : k[X]} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) (h : x * y = z * w) :
    (normalizedFactors x).count p + (normalizedFactors y).count p =
      (normalizedFactors z).count p + (normalizedFactors w).count p := by
  simpa [normalizedFactors_mul hx hy, normalizedFactors_mul hz hw] using
    congrArg (fun r => (normalizedFactors r).count p) h

/-- The order at `p` of a quotient `a / b` of nonzero polynomials is computed from `a` and `b`
directly; in particular `ordAt` does not depend on the chosen representation. -/
theorem ordAt_div (p : k[X]) {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordAt p (algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b) =
      ((normalizedFactors a).count p : ℤ) - ((normalizedFactors b).count p : ℤ) := by
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) := RatFunc.algebraMap_injective k
  set g : RatFunc k := algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b with hgdef
  have hg : g ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ hinj).mpr ha) ((map_ne_zero_iff _ hinj).mpr hb)
  have hcount := count_add_count_eq_of_mul_eq p (RatFunc.num_ne_zero hg) hb ha
    (RatFunc.denom_ne_zero g) ((RatFunc.num_mul_eq_mul_denom_iff hb).mpr hgdef)
  simp only [ordAt]
  omega

/-- The order at a monic irreducible polynomial is additive in the rational function: the
principal divisor of a product is the sum of the principal divisors. -/
theorem ordAt_mul (p : k[X]) {g h : RatFunc k} (hg : g ≠ 0) (hh : h ≠ 0) :
    ordAt p (g * h) = ordAt p g + ordAt p h := by
  have hgn : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hhn : h.num ≠ 0 := RatFunc.num_ne_zero hh
  have hgd : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hhd : h.denom ≠ 0 := RatFunc.denom_ne_zero h
  have hcount := count_add_count_eq_of_mul_eq p (RatFunc.num_ne_zero (mul_ne_zero hg hh))
    (mul_ne_zero hgd hhd) (mul_ne_zero hgn hhn) (RatFunc.denom_ne_zero (g * h))
    (RatFunc.num_denom_mul g h)
  simp only [normalizedFactors_mul hgd hhd, normalizedFactors_mul hgn hhn,
    Multiset.count_add] at hcount
  simp only [ordAt]
  omega

omit [DecidableEq k] in
/-- The order at infinity is additive in the rational function. -/
theorem ordAtInfty_mul {g h : RatFunc k} (hg : g ≠ 0) (hh : h ≠ 0) :
    ordAtInfty (g * h) = ordAtInfty g + ordAtInfty h := by
  simp [ordAtInfty, RatFunc.intDegree_mul hg hh, add_comm]

/-- For a monic irreducible `p`, the order of `g` at `p` is the difference of the multiplicities
of `p` in the numerator and the denominator of `g`; so `ordAt p g` really is the order of
vanishing of `g` at the closed point of the affine line cut out by `p`. -/
theorem ordAt_eq_multiplicity_sub_multiplicity {p : k[X]} (hp : Irreducible p) (hpm : p.Monic)
    {g : RatFunc k} (hg : g ≠ 0) :
    ordAt p g = (multiplicity p g.num : ℤ) - (multiplicity p g.denom : ℤ) := by
  rw [ordAt,
    multiplicity_eq_count_normalizedFactors hp (RatFunc.num_ne_zero hg),
    multiplicity_eq_count_normalizedFactors hp (RatFunc.denom_ne_zero g), hpm.normalize_eq_self]

/-- A polynomial that is not monic occurs in no set of normalized factors, so the order of every
rational function at it vanishes. -/
theorem ordAt_eq_zero_of_not_monic {p : k[X]} (hp : ¬p.Monic) (g : RatFunc k) :
    ordAt p g = 0 := by
  have key : ∀ q : k[X], (normalizedFactors q).count p = 0 := by
    intro q
    refine Multiset.count_eq_zero_of_notMem fun hmem => hp ?_
    have hp0 : p ≠ 0 := fun h => zero_notMem_normalizedFactors q (h ▸ hmem)
    exact (normalize_eq_self_iff_monic hp0).mp (normalize_normalized_factor p hmem)
  simp [ordAt, key]

/-- Away from the monic irreducible factors of the numerator and the denominator of `g`, the
order of `g` vanishes. -/
theorem ordAt_eq_zero_of_notMem {g : RatFunc k} {p : k[X]}
    (hnum : p ∉ (normalizedFactors g.num).toFinset)
    (hden : p ∉ (normalizedFactors g.denom).toFinset) : ordAt p g = 0 := by
  simp only [Multiset.mem_toFinset] at hnum hden
  simp [ordAt, Multiset.count_eq_zero_of_notMem hnum, Multiset.count_eq_zero_of_notMem hden]

/-- The principal divisor of `g` is supported on the monic irreducible factors of the numerator
and the denominator of `g`. -/
private theorem support_ordAt_mul_natDegree_subset (g : RatFunc k) :
    (Function.support fun p : k[X] => ordAt p g * (p.natDegree : ℤ)) ⊆
      ↑((normalizedFactors g.num).toFinset ∪ (normalizedFactors g.denom).toFinset) := by
  intro p hp
  by_contra hmem
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hmem
  exact hp (by simp [ordAt_eq_zero_of_notMem hmem.1 hmem.2])

/-- The principal divisor of a nonzero rational function has finite support. -/
theorem finite_support_ordAt (g : RatFunc k) :
    (Function.support fun p : k[X] => ordAt p g * (p.natDegree : ℤ)).Finite :=
  (Finset.finite_toSet _).subset (support_ordAt_mul_natDegree_subset g)

/-! ### The degree of a principal divisor on the projective line -/

/-- **Stacks 02RU, the case of the projective line (finite part).** The degree of the finite
part of the principal divisor of a nonzero rational function `g` — the sum of `ord_p(g)`
weighted by the degree `deg p` of the corresponding closed point of the affine line — is the
integer degree `deg(num g) - deg(denom g)` of `g`. -/
theorem sum_ordAt_mul_natDegree (g : RatFunc k) (hg : g ≠ 0) (s : Finset k[X])
    (hnum : (normalizedFactors g.num).toFinset ⊆ s)
    (hden : (normalizedFactors g.denom).toFinset ⊆ s) :
    ∑ p ∈ s, ordAt p g * (p.natDegree : ℤ) = g.intDegree := by
  rw [RatFunc.intDegree,
    ← sum_count_normalizedFactors_mul_natDegree g.num (RatFunc.num_ne_zero hg) s hnum,
    ← sum_count_normalizedFactors_mul_natDegree g.denom (RatFunc.denom_ne_zero g) s hden,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp [ordAt, sub_mul]

/-- **Stacks 02RU, the case of the projective line.** The degree of a principal divisor on the
projective line over a field is zero: the orders of a nonzero rational function at the closed
points of the affine line, weighted by the degrees of those points, together with the order at
infinity (a point of degree one), add up to zero. -/
theorem sum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero (g : RatFunc k) (hg : g ≠ 0)
    (s : Finset k[X]) (hnum : (normalizedFactors g.num).toFinset ⊆ s)
    (hden : (normalizedFactors g.denom).toFinset ⊆ s) :
    (∑ p ∈ s, ordAt p g * (p.natDegree : ℤ)) + ordAtInfty g = 0 := by
  rw [sum_ordAt_mul_natDegree g hg s hnum hden, ordAtInfty, add_neg_cancel]

/-- **Stacks 02RU, the case of the projective line**, as an unrestricted sum over all monic
irreducible polynomials; the sum is finite by `Stacks.Chow.finite_support_ordAt`. -/
theorem finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero (g : RatFunc k) (hg : g ≠ 0) :
    (∑ᶠ p : k[X], ordAt p g * (p.natDegree : ℤ)) + ordAtInfty g = 0 := by
  rw [finsum_eq_sum_of_support_subset _ (support_ordAt_mul_natDegree_subset g)]
  exact sum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero g hg _ Finset.subset_union_left
    Finset.subset_union_right

end Stacks.Chow

namespace AlgebraicGeometry.AlgebraicCycle

variable {X Y : Scheme.{u}} {R : Type*} [Semiring R]

/-- If the weight function drops at every point of the fibre of `f` over `y`, then the
coefficient of the pushforward cycle at `y` vanishes. This is the branch of Stacks 02R4 in
which the image of every component above `y` has strictly smaller `δ`-dimension. -/
theorem map_apply_eq_zero_of_forall_weight_ne (f : X ⟶ Y) [QuasiCompact f]
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N) (c : AlgebraicCycle X R) (y : Y)
    (h : ∀ x : X, f.base x = y → wx x ≠ wy (f.base x)) :
    map f wx wy c y = 0 := by
  rw [map, Function.locallyFinsupp.map_apply]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [mapCoeff, h x hx]

/-- The pushforward of a cycle to a one-point scheme — for instance the spectrum of a field —
has a single coefficient, namely the total weighted degree of the cycle. This is the reduction
of `c_*div(f) = 0` in Stacks 02RU to the vanishing of a degree. -/
theorem map_apply_of_subsingleton (f : X ⟶ Y) [QuasiCompact f] [Subsingleton Y]
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N) (c : AlgebraicCycle X R) (y : Y) :
    map f wx wy c y = ∑ᶠ x : X, c x * (mapCoeff f wx wy x : R) := by
  rw [map, Function.locallyFinsupp.map_apply,
    show f.base ⁻¹' {y} = Set.univ from Set.eq_univ_of_forall fun x => by
      simp [Subsingleton.elim (f.base x) y],
    finsum_mem_univ]

end AlgebraicGeometry.AlgebraicCycle

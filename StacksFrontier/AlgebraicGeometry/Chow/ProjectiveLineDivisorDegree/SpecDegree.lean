module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Inversion
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.ResidueDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.SpecOrder

/-!
# The degree of a principal divisor on the affine line over a field

Let `k` be a field. The closed points of `Spec k[T]` are the points cut out by the monic
irreducible polynomials, the residue degree of the structure morphism at such a point is the
degree of that polynomial, and the order of vanishing there is `Stacks.Chow.ordAt` of it. So the
weighted sum of orders of vanishing over `Spec k[T]` is the sum computed in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardDivisor`, namely the integer degree
`RatFunc.intDegree` of the rational function.

This is the finite part of the degree of a principal divisor on the projective line: the missing
contribution is the one at infinity.

## Main definitions

* `Stacks.Chow.polyPoint` — the point of `Spec k[T]` attached to a polynomial, the junk value
  being the generic point for a non-irreducible polynomial.

## Main results

* `Stacks.Chow.bijOn_polyPoint` — the monic irreducible polynomials are in bijection with the
  points of `Spec k[T]` of codimension one.
* `Stacks.Chow.finsum_ord_mul_residueDegree_specPolynomial` — **the degree of the finite part**:
  the weighted sum of the orders of vanishing of a nonzero rational function over `Spec k[T]` is
  its integer degree.

## Implementation notes

`Stacks.Chow.polyPoint` is defined by case distinction on irreducibility, which is not decidable,
so it is classical; the junk branch is the generic point.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace Polynomial
open UniqueFactorizationMonoid

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k] [DecidableEq k]

/-- The structure morphism of the affine line over a field, `Spec k[T] ⟶ Spec k`. -/
abbrev specPolynomialOver : specPolynomial k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

open scoped Classical in
/-- The point of `Spec k[T]` cut out by a polynomial, with the generic point as junk value when
the polynomial is not irreducible. -/
def polyPoint (p : Polynomial k) : specPolynomial k :=
  if h : Irreducible p then irreduciblePoint (CommRingCat.of (Polynomial k)) h
  else (⊥ : PrimeSpectrum (Polynomial k))

omit [DecidableEq k] in
/-- At an irreducible polynomial `Stacks.Chow.polyPoint` is
`Stacks.Chow.irreduciblePoint`. -/
theorem polyPoint_of_irreducible {p : Polynomial k} (hp : Irreducible p) :
    polyPoint k p = irreduciblePoint (CommRingCat.of (Polynomial k)) hp :=
  dite_eq_left hp

omit [DecidableEq k] in
/-- **The monic irreducible polynomials parametrize the closed points of the affine line.** -/
theorem bijOn_polyPoint :
    Set.BijOn (polyPoint k) {p : Polynomial k | p.Monic ∧ Irreducible p}
      {x : specPolynomial k | coheight x = 1} := by
  classical
  refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_, fun x hx => ?_⟩
  · rw [Set.mem_ofPred_eq, polyPoint_of_irreducible k hp.2]
    exact coheight_irreduciblePoint (CommRingCat.of (Polynomial k)) (Polynomial.not_isField k) hp.2
  · rw [polyPoint_of_irreducible k hp.2, polyPoint_of_irreducible k hq.2] at hpq
    have hspan : (Ideal.span {p} : Ideal (Polynomial k)) = Ideal.span {q} :=
      congrArg PrimeSpectrum.asIdeal hpq
    exact Polynomial.eq_of_monic_of_associated hp.1 hq.1
      (Ideal.span_singleton_eq_span_singleton.1 hspan)
  · obtain ⟨ϖ, hϖ, rfl⟩ :=
      exists_irreducible_eq_irreduciblePoint (CommRingCat.of (Polynomial k)) x hx
    have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
    have hassoc : Associated ϖ (normalize ϖ) := associated_normalize ϖ
    have hnormirr : Irreducible (normalize ϖ) := hassoc.irreducible hϖ
    refine ⟨normalize ϖ, ⟨Polynomial.monic_normalize hϖ0, hnormirr⟩, ?_⟩
    rw [polyPoint_of_irreducible k hnormirr]
    have hspan2 : (irreduciblePoint (CommRingCat.of (Polynomial k)) hnormirr).asIdeal
        = (irreduciblePoint (CommRingCat.of (Polynomial k)) hϖ).asIdeal :=
      Ideal.span_singleton_eq_span_singleton.2 hassoc.symm
    exact PrimeSpectrum.ext hspan2

/-- The degree of the finite part of a principal divisor, as an unrestricted sum over all
polynomials: only the monic irreducible ones contribute, and the total is the integer degree. -/
theorem finsum_ordAt_mul_natDegree (g : RatFunc k) (hg : g ≠ 0) :
    (∑ᶠ p : Polynomial k, ordAt p g * (p.natDegree : ℤ)) = g.intDegree := by
  set s : Finset (Polynomial k) :=
    (normalizedFactors g.num).toFinset ∪ (normalizedFactors g.denom).toFinset with hs
  have hsub : (Function.support fun p : Polynomial k => ordAt p g * (p.natDegree : ℤ)) ⊆
      (s : Set (Polynomial k)) := by
    intro p hp
    by_contra hmem
    simp only [hs, Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hmem
    exact hp (by simp [ordAt_eq_zero_of_notMem hmem.1 hmem.2])
  rw [finsum_eq_sum_of_support_subset _ hsub]
  exact sum_ordAt_mul_natDegree g hg s Finset.subset_union_left Finset.subset_union_right

omit [DecidableEq k] in
/-- **The degree of a principal divisor on the affine line over a field.** The weighted sum of the
orders of vanishing of a nonzero rational function over the points of `Spec k[T]`, each weighted
by the residue degree of the structure morphism, is the integer degree of the rational function.
-/
theorem finsum_ord_mul_residueDegree_specPolynomial
    (g : (specPolynomial k).functionField) (hg : g ≠ 0) :
    (∑ᶠ x : specPolynomial k, (specPolynomial k).ord g x
        * ((specPolynomialOver k).residueDegree x : ℤ))
      = (ratFuncEquivFunctionField k g).intDegree := by
  classical
  set G : RatFunc k := ratFuncEquivFunctionField k g with hG
  have hGne : G ≠ 0 := by
    rw [hG]
    exact fun h => hg ((ratFuncEquivFunctionField k).map_eq_zero_iff.1 h)
  set F : specPolynomial k → ℤ := fun x =>
    (specPolynomial k).ord g x * ((specPolynomialOver k).residueDegree x : ℤ) with hF
  set H : Polynomial k → ℤ := fun p => ordAt p G * (p.natDegree : ℤ) with hH
  have hFsupp : ∀ x ∈ Function.support F, x ∈ Set.univ ↔
      x ∈ {x : specPolynomial k | coheight x = 1} := by
    intro x hx
    refine ⟨fun _ => ?_, fun _ => Set.mem_univ x⟩
    by_contra hco
    exact hx (by simp [hF, Scheme.ord_eq_zero_of_coheight_neq_one hco])
  have hHsupp : ∀ p ∈ Function.support H, p ∈ Set.univ ↔
      p ∈ {p : Polynomial k | p.Monic ∧ Irreducible p} := by
    intro p hp
    refine ⟨fun _ => ?_, fun _ => Set.mem_univ p⟩
    by_contra hmi
    rw [Set.mem_ofPred_eq, not_and_or] at hmi
    rcases hmi with h | h
    · exact hp (by simp [hH, ordAt_eq_zero_of_not_monic h])
    · exact hp (by simp [hH, ordAt_eq_zero_of_not_irreducible h])
  have hpoint : ∀ p ∈ {p : Polynomial k | p.Monic ∧ Irreducible p}, H p = F (polyPoint k p) := by
    intro p hp
    have hord : (specPolynomial k).ord g (polyPoint k p) = ordAt p G := by
      rw [polyPoint_of_irreducible k hp.2, hG]
      exact ord_irreduciblePoint_eq_ordAt k hp.2 hp.1 g hg
    have hdeg : (specPolynomialOver k).residueDegree (polyPoint k p) = p.natDegree := by
      rw [polyPoint_of_irreducible k hp.2]
      exact residueDegree_specMap_polynomialC k hp.2 hp.1 _
        (irreduciblePoint_asIdeal (CommRingCat.of (Polynomial k)) hp.2)
    rw [hF, hH]
    simp only
    rw [hord, hdeg]
  calc (∑ᶠ x : specPolynomial k, F x)
      = ∑ᶠ x ∈ (Set.univ : Set (specPolynomial k)), F x := (finsum_mem_univ F).symm
    _ = ∑ᶠ x ∈ {x : specPolynomial k | coheight x = 1}, F x :=
        finsum_mem_inter_support_eq' F _ _ hFsupp
    _ = ∑ᶠ p ∈ {p : Polynomial k | p.Monic ∧ Irreducible p}, H p :=
        (finsum_mem_eq_of_bijOn (polyPoint k) (bijOn_polyPoint k) hpoint).symm
    _ = ∑ᶠ p ∈ (Set.univ : Set (Polynomial k)), H p :=
        (finsum_mem_inter_support_eq' H _ _ hHsupp).symm
    _ = ∑ᶠ p : Polynomial k, H p := finsum_mem_univ H
    _ = G.intDegree := finsum_ordAt_mul_natDegree k G hGne

end Stacks.Chow

end

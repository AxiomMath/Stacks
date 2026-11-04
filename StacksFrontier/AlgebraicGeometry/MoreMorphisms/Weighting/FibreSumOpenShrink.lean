module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm

/-!
# Shrinking the source of a weighted fibre sum to an open neighbourhood of the support

The separable-degree weighted fibre sum of a weight `ω : U → ℤ` along `π : U ⟶ V` is an
unconditional sum over `U`, so a point of `U` at which `ω` vanishes contributes nothing. Hence
the sum only sees the locus where `ω` is nonzero, and restricting `π` to any open subscheme of
`U` containing that locus leaves the sum unchanged.

This is the statement that lets a weighted fibre sum be computed on a conveniently small open
neighbourhood of the support of its weight, with no finiteness hypothesis anywhere: both sides
are sums over possibly infinite types.

## Main results

* `AlgebraicGeometry.separableDegreeWeightedFiberSum_comp_isOpenImmersion_of_support_subset`:
  **the weighted fibre sum is unchanged by shrinking the source along an open immersion whose
  range contains the support of the weight.**
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_opens_ι_of_support_subset`: the same
  statement phrased for an open subscheme `W` of the source, which is the form in which it gets
  applied.

## Implementation notes

The two inputs are already available. The summand at a point is unchanged by restriction along
an open immersion — this is
`AlgebraicGeometry.separableDegreeWeightedFiberTerm_comp_isPreimmersion`, which is where the
isomorphism of residue fields induced by an open immersion is used to transport the separable
degree — and the summand vanishes at a point where the weight does, by
`AlgebraicGeometry.separableDegreeWeightedFiberTerm_of_mem_fiber`. What remains is purely formal:
a sum over a type agrees with the sum read along an injection whose range contains the support of
the summand. That is recorded here as a private lemma about `finsum`, proved from
`finsum_mem_range` by recognising the sum over the range as the sum of the indicator function,
which is the summand itself precisely because of the support hypothesis.

Note that the hypothesis is on the *weight*, not on the summand: a point outside the open
subscheme may well lie in the fibre, and it is the vanishing of the weight there that kills its
contribution.

## References

* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A locally finite sum over a type is the locally finite sum read along an injection, provided
the summand is supported on the range of that injection. -/
private lemma finsum_eq_finsum_comp_of_support_subset_range
    {A B M : Type*} [AddCommMonoid M] {φ : A → B} (hφ : Function.Injective φ)
    (F : B → M) (hsupp : Function.support F ⊆ Set.range φ) :
    (∑ᶠ b : B, F b) = ∑ᶠ a : A, F (φ a) := by
  rw [← finsum_mem_range hφ, finsum_mem_def, Set.indicator_eq_self.2 hsupp]

/-- The summands of a weighted fibre sum are supported on the locus where the weight is
nonzero. -/
private lemma support_separableDegreeWeightedFiberTerm_subset
    {U V : Scheme.{u}} (π : U ⟶ V) (ω : U → ℤ) (v : V) :
    Function.support (separableDegreeWeightedFiberTerm π ω v) ⊆ Function.support ω := by
  intro x hx
  have hterm : separableDegreeWeightedFiberTerm π ω v x ≠ 0 := hx
  refine fun h0 ↦ hterm ?_
  by_cases hπx : π x = v
  · rw [separableDegreeWeightedFiberTerm_of_mem_fiber π ω hπx, h0, zero_mul]
  · exact separableDegreeWeightedFiberTerm_of_notMem_fiber π ω hπx

/-- **The weighted fibre sum does not change when the source is shrunk to an open subscheme
containing the support of the weight.** If `j : U' ⟶ U` is an open immersion whose range contains
every point where `ω` is nonzero, then integrating `ω` over `U` along `π` is the same as
integrating its restriction over `U'` along `j ≫ π`.

No finiteness hypothesis is needed: the points of `U` outside the range of `j` carry weight zero,
hence contribute nothing, and at a point of `U'` the summand is unchanged because an open
immersion induces an isomorphism on residue fields. -/
public theorem separableDegreeWeightedFiberSum_comp_isOpenImmersion_of_support_subset
    {U' U V : Scheme.{u}} (j : U' ⟶ U) [IsOpenImmersion j] (π : U ⟶ V) (ω : U → ℤ)
    (hsupp : ∀ x : U, ω x ≠ 0 → x ∈ Set.range j.base) :
    separableDegreeWeightedFiberSum (j ≫ π) (ω ∘ ⇑j) = separableDegreeWeightedFiberSum π ω := by
  funext v
  have hinj : Function.Injective ⇑j.base := j.isOpenEmbedding.injective
  have hsub : Function.support (separableDegreeWeightedFiberTerm π ω v) ⊆
      Set.range ⇑j.base := fun x hx ↦
    hsupp x (support_separableDegreeWeightedFiberTerm_subset π ω v hx)
  rw [separableDegreeWeightedFiberSum_eq_finsum_term,
    separableDegreeWeightedFiberSum_eq_finsum_term]
  refine Eq.trans ?_ (finsum_eq_finsum_comp_of_support_subset_range hinj
    (separableDegreeWeightedFiberTerm π ω v) hsub).symm
  exact finsum_congr fun x ↦ separableDegreeWeightedFiberTerm_comp_isPreimmersion j π ω v x

/-- **The weighted fibre sum is computed on any open subscheme containing the support of the
weight.** The `AlgebraicGeometry.Scheme.Opens` phrasing of
`AlgebraicGeometry.separableDegreeWeightedFiberSum_comp_isOpenImmersion_of_support_subset`. -/
public theorem separableDegreeWeightedFiberSum_opens_ι_of_support_subset
    {U V : Scheme.{u}} (W : U.Opens) (π : U ⟶ V) (ω : U → ℤ)
    (hsupp : ∀ x : U, ω x ≠ 0 → x ∈ (W : Set U)) :
    separableDegreeWeightedFiberSum (W.ι ≫ π) (ω ∘ ⇑W.ι) =
      separableDegreeWeightedFiberSum π ω :=
  separableDegreeWeightedFiberSum_comp_isOpenImmersion_of_support_subset W.ι π ω fun x hx ↦ by
    rw [Scheme.Opens.range_ι]
    exact hsupp x hx

end AlgebraicGeometry

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesEquivalence
public import StacksFrontier.RingTheory.Depth.FlatLocalHom

/-!
# Purity in the local case for a smooth morphism

Let `f : X ⟶ S` be a morphism of schemes and `U ⊆ X` an open subscheme. Assume

1. `f` is smooth,
2. `S` is Noetherian,
3. for every `s ∈ S` with `depth 𝒪_{S, s} ≤ 1` the fibres agree, `X_s = U_s`,
4. `U_s ⊆ X_s` is dense for every `s ∈ S`.

Then the restriction functor `FÉt_X ⟶ FÉt_U` is an equivalence. This is [Stacks, Tag 0EYB],
proved as `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_of_smooth_of_fibrewise_dense`
in `StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmooth`. This file supplies what
hypotheses (3) and (4) contribute to the fully faithful half, the source's first paragraph:
[Stacks, Tag 0BQF] applied to the dense open `U`, its local hypothesis supplied by
[Stacks, Tag 0BLR] from the depth bound that [Stacks, Tag 0337] extracts from (3).

Hypothesis (3) is spelled as: if the depth of `𝒪_{S, s}` is at most one then the whole fibre
`f⁻¹(s)` is contained in `U`. Hypothesis (4) is spelled as: every point of `f⁻¹(s)` lies in the
closure of `U ∩ f⁻¹(s)`, which is density of `U ∩ f⁻¹(s)` in the subspace `f⁻¹(s)`, the
underlying space of the fibre `X_s`.

## Main results

* `Stacks.FundamentalGroup.two_le_depth_stalk_of_smooth` — [Stacks, Tag 0337] read on the
  stalks of a smooth morphism: the local ring of `X` at `x` has depth at least two as soon as
  the local ring of `S` at `f(x)` does.
* `Stacks.FundamentalGroup.two_le_depth_stalk_of_notMem_of_fibre_subset` — hypothesis (3) turned
  into the depth bound at a point of `X` outside `U`.
* `Stacks.FundamentalGroup.dense_of_fibrewise_dense` — hypothesis (4) turned into density of `U`
  in `X`.

## References

* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR)
* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Topology

universe u

namespace Stacks.FundamentalGroup

/-! ### Depth along the stalks of a smooth morphism -/

/-- **[Stacks, Tag 0337] on the stalks of a smooth morphism.** Let `f : X ⟶ S` be smooth with
`S` locally Noetherian and let `x` be a point of `X`. If `𝒪_{S, f(x)}` has depth at least two
then so does `𝒪_{X, x}`.

A smooth morphism is flat, so `𝒪_{S, f(x)} ⟶ 𝒪_{X, x}` is a flat local homomorphism of
Noetherian local rings, and [Stacks, Tag 0337] writes `depth 𝒪_{X, x}` as `depth 𝒪_{S, f(x)}`
plus the depth of the fibre ring. -/
public theorem two_le_depth_stalk_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [IsLocallyNoetherian S] (x : X)
    (h : (2 : ℕ∞) ≤ Module.depth (S.presheaf.stalk (f.base x))
      (maximalIdeal (S.presheaf.stalk (f.base x))) (S.presheaf.stalk (f.base x))) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have _ : Module.Flat (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    AlgebraicGeometry.Flat.stalkMap f x
  have _ : IsLocalHom (algebraMap (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal
    (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)]
  exact h.trans le_self_add

/-- **Hypothesis (3) of [Stacks, Tag 0EYB] as a depth bound on `X`.** Suppose that for every
`s ∈ S` with `depth 𝒪_{S, s} ≤ 1` the fibre `f⁻¹(s)` is contained in `U`. Then at a point `x`
of `X` outside `U` the local ring `𝒪_{X, x}` has depth at least two.

Indeed `x` lies in the fibre over `s = f(x)` and not in `U`, so the hypothesis forbids
`depth 𝒪_{S, s} ≤ 1`; hence that depth is at least two, and
`two_le_depth_stalk_of_smooth` carries the bound up to `𝒪_{X, x}`. -/
public theorem two_le_depth_stalk_of_notMem_of_fibre_subset {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsLocallyNoetherian S] (U : X.Opens)
    (hfib : ∀ s : S, Module.depth (S.presheaf.stalk s) (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s) ≤ 1 → f.base ⁻¹' {s} ⊆ (U : Set X))
    (x : X) (hx : x ∉ U) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) := by
  refine two_le_depth_stalk_of_smooth f x ?_
  have hnot : ¬ Module.depth (S.presheaf.stalk (f.base x))
      (maximalIdeal (S.presheaf.stalk (f.base x))) (S.presheaf.stalk (f.base x)) ≤ 1 := by
    intro hle
    exact hx (hfib (f.base x) hle rfl)
  exact Order.add_one_le_of_lt (by simpa using not_le.1 hnot)

/-! ### Density of `U` in `X` from density in the fibres -/

/-- **Hypothesis (4) of [Stacks, Tag 0EYB] implies that `U` is dense in `X`.** If every point of
every fibre `f⁻¹(s)` lies in the closure of `U ∩ f⁻¹(s)`, then `U` is dense in `X`: a point `x`
belongs to the fibre over `f(x)`, and the closure of `U ∩ f⁻¹(f(x))` is contained in the closure
of `U`. -/
public theorem dense_of_fibrewise_dense {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (hdense : ∀ s : S, f.base ⁻¹' {s} ⊆ closure ((U : Set X) ∩ f.base ⁻¹' {s})) :
    Dense (U : Set X) := fun x =>
  closure_mono Set.inter_subset_left (hdense (f.base x) rfl)

/-! ### Tag 0EYB -/

end Stacks.FundamentalGroup

end

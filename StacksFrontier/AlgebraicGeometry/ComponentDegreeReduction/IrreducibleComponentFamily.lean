module

public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.IrreducibleComponentStalk
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.SupportBounds
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# [Stacks, Tag 0AYW], paragraph 1 at the dévissage's own family

`StacksFrontier/AlgebraicGeometry/ComponentDegreeReduction/SupportBounds.lean` proves paragraph 1 of
[Stacks, Tag 0AYW] for a finite family `iⱼ : Zⱼ ⟶ X` of closed subschemes,

`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`,

from two inputs: finite dimensionality of the cohomology of every coherent module on `X`, which
is [Stacks, Tag 02O6] over a field and is now a theorem, and the geometric statement that the
comparison map `𝒪_X ⟶ ⊕_{j<N} (iⱼ)_*𝒪_{Zⱼ}` is bijective on stalks away from a finite set of
closed points. Until now the only family at which the second was known was the one-member
family `fun _ => 𝟙 X`, which proves nothing about several components.

This file supplies both at the family the source actually uses — the irreducible components of
`X` with the subscheme structure of `AlgebraicGeometry.Scheme.irreducibleComponent` — and so
proves paragraph 1 outright for a nonempty scheme proper over a field of dimension at most one.

## Main results

* `AlgebraicGeometry.exists_curveDegree_eq_sum_irreducibleComponent`: the degree is the sum of
  the degrees on the irreducible components, each with its own subscheme structure, for an
  enumeration of them listing each of the `N` components exactly once among the first `N`
  indices.

## Implementation notes

**`[IsNoetherian X]` is a binder although `[IsProper f]` implies it.** The conclusion names
`AlgebraicGeometry.Scheme.irreducibleComponent`, whose elaboration needs the instance, so it
has to be present before the proof starts;
`Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field` is a theorem and
instance search does not find it. It is not a weakening: that theorem inhabits it from the
binders already there.

**`[Nonempty X]` is not removable at this shape.** The conclusion asserts the existence of an
enumeration `C : ℕ → Set X` of the irreducible components with `C j` a component for *every*
`j`, which an empty scheme cannot provide — it has no irreducible components at all. The
statement for an empty `X` is the degenerate `deg(ℰ) = 0`, which
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective` gives at
`N = 0` directly.

**What is still owed for [Stacks, Tag 0AYW] itself.** Paragraph 1 is here in the shape of a sum
over `Finset.range N`. Turning it into the source's sum over the generic points of the
one-dimensional components, weighted by multiplicities, needs the two remaining inputs of
`curveDegree_eq_finsum_componentDegree_of_stalk_bijective` in the namespace
`Stacks.AlgebraicGeometry.ComponentDegrees`: the injection `σ` of the one-dimensional components
into the family together with the vanishing `hzero` of the members it misses, and paragraph 2's
`hirreducible`. Neither is proved here.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0BA8](https://stacks.math.columbia.edu/tag/0BA8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0AYW], paragraph 1, at the family of irreducible components.** On a nonempty
scheme proper over a field of dimension at most one the degree of a finite locally free module
of constant rank is the sum of its degrees on the irreducible components, each taken with the
subscheme structure of `AlgebraicGeometry.Scheme.irreducibleComponent`.

Both inputs of
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective` are
discharged: [Stacks, Tag 02O6] by
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`, and the stalkwise
bijectivity of the comparison map by
`AlgebraicGeometry.exists_finite_bijective_stalk_pushforwardUnitSeriesMap_irreducibleComponent`.
So the statement carries no hypothesis beyond the standing ones. -/
theorem exists_curveDegree_eq_sum_irreducibleComponent (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsNoetherian X] [Nonempty X]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    ∃ (N : ℕ) (C : ℕ → Set X) (hC : ∀ j, C j ∈ irreducibleComponents X),
      0 < N ∧ (∀ W ∈ irreducibleComponents X, ∃ j < N, C j = W) ∧
        curveDegree k f hX E n =
          ∑ j ∈ Finset.range N,
            @curveDegree k _ (X.irreducibleComponent (C j) (hC j))
              (X.irreducibleComponentι (C j) (hC j) ≫ f) _
              (le_trans (IsClosedImmersion.isClosedEmbedding
                (X.irreducibleComponentι (C j) (hC j))).isInducing.topologicalKrullDim_le hX)
              ((Scheme.Modules.pullback (X.irreducibleComponentι (C j) (hC j))).obj E) n
              (isFiniteLocallyFreeOfRank_pullback
                (X.irreducibleComponentι (C j) (hC j)) E n) := by
  obtain ⟨N, C, hNpos, hC, hCinj, hCsurj⟩ := exists_enumeration_irreducibleComponents X
  obtain ⟨Z, hZfin, hZcl, hbij⟩ :=
    exists_finite_bijective_stalk_pushforwardUnitSeriesMap_irreducibleComponent X C hC hCinj
      hCsurj hX
  exact ⟨N, C, hC, hNpos, hCsurj,
    curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective k f
      (fun j => X.irreducibleComponentι (C j) (hC j)) hX E n N Z hZfin hZcl hbij
      (forall_finiteDimensional_cohomologyOverField_of_isProper k f)⟩

end AlgebraicGeometry

end

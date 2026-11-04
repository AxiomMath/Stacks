module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksCore.Tactic.StacksAttribute

/-!
# The geometric genus of a proper scheme of dimension at most one over a field

Let `k` be a field with algebraic closure `k̄` and let `X` be a proper scheme of dimension at
most one over `k`.  The *geometric genus* `g_geom(X/k)` is the sum of the geometric genera of
those irreducible components of the base change `X_{k̄}` that have dimension one.  Each such
component is taken with its reduced closed subscheme structure, and the geometric genus of a
one-dimensional reduced irreducible proper scheme over an algebraically closed field is the
genus of its normalization.

The invariant is defined for every proper scheme over `k`, without a dimension hypothesis:
components of dimension other than one simply contribute nothing.  In particular a proper
scheme all of whose components have dimension zero has geometric genus zero.

## Main definitions

* `AlgebraicGeometry.irreducibleComponentIdeal` is the ideal sheaf of functions vanishing on an
  irreducible component, whose closed subscheme is that component with its reduced structure.
* `AlgebraicGeometry.geometricGenus` is the geometric genus of a proper scheme over a field.

## Main results

* `AlgebraicGeometry.geometricGenus_eq_zero_of_dim_lt_one`: a proper scheme of dimension less
  than one over a field has geometric genus zero.

## Implementation notes

The geometric genus of a one-dimensional geometric irreducible component is encoded here as the
genus `AlgebraicGeometry.genus` of its normalization, that is as `dim H¹` of its nonsingular
projective model.  For a curve over an algebraically closed field this is the standard
definition of the geometric genus, and it is the description the invariant is used through: the
geometric genus of a one-dimensional proper scheme is read off from a nonsingular projective
model, so two such schemes with isomorphic nonsingular projective models have the same
geometric genus.

The base change is the categorical pullback of the structure morphism along the map of spectra
induced by `k → k̄`.  A proper scheme over a field is Noetherian, hence so is its base change,
so the set of irreducible components of the base change is finite and the sum is a finite one;
the required `Fintype` instance is produced inside the definition rather than demanded of the
caller.

The dimension of a component is measured by the Krull dimension of its underlying topological
space, `topologicalKrullDim`, which for a scheme of finite type over a field is the dimension
in the sense of the source.

## References

* [Stacks Project, Tag 0CE0](https://stacks.math.columbia.edu/tag/0CE0), Section 53.21 (Genus
  versus geometric genus)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The ideal sheaf of the functions vanishing on an irreducible component `C` of a scheme `X`.
Its closed subscheme is `C` equipped with its reduced induced structure. -/
public abbrev irreducibleComponentIdeal {X : Scheme.{u}} (C : irreducibleComponents X) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩ : Closeds X)

/-- The geometric genus `g_geom(X/k)` of a proper scheme `X` over a field `k`: the sum, over the
irreducible components of dimension one of the base change of `X` to an algebraic closure of
`k`, of the genus of the normalization of that component with its reduced structure.

This is the invariant introduced in the preamble of the source's section on genus versus
geometric genus. -/
@[stacks 0CE0 "definition of the geometric genus g_geom(X/k)"]
public def geometricGenus (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsProper g] : ℕ :=
  let Y : Scheme.{u} :=
    pullback g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
  let p : Y ⟶ Spec (.of (AlgebraicClosure k)) :=
    pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
  letI : IsNoetherian Y := {}
  letI : Finite (irreducibleComponents Y) :=
    (finite_irreducibleComponents_of_isNoetherian (X := Y)).to_subtype
  letI : Fintype (irreducibleComponents Y) := Fintype.ofFinite _
  ∑ Z : irreducibleComponents Y,
    let c := (irreducibleComponentIdeal Z).subschemeι ≫ p
    if topologicalKrullDim (irreducibleComponentIdeal Z).subscheme = 1 then
      genus (normalizationOverField (AlgebraicClosure k) c ≫ c)
    else 0

/-- A proper scheme of dimension less than one over a field has geometric genus zero: extending
the ground field does not change the dimension, so no irreducible component of the base change
has dimension one. -/
public theorem geometricGenus_eq_zero_of_dim_lt_one {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim X < 1) :
    geometricGenus k g = 0 := by
  classical
  have hd : topologicalKrullDim
      (pullback (C := Scheme.{u}) g
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) =
      topologicalKrullDim X :=
    topologicalKrullDim_baseChange k (AlgebraicClosure k) _ _ g (.of_hasPullback _ _)
  unfold geometricGenus
  refine Finset.sum_eq_zero fun Z _ ↦ ?_
  have hZ : topologicalKrullDim (irreducibleComponentIdeal Z).subscheme < 1 :=
    lt_of_le_of_lt
      (irreducibleComponentIdeal
        Z).subschemeι.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
      (hd ▸ hdim)
  exact ite_eq_right hZ.ne

end AlgebraicGeometry

end

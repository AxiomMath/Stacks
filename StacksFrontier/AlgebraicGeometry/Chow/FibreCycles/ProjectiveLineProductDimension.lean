module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.GeometricRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension

/-!
# The family of projective lines over a variety has finite dimension

Let `X` be a variety over a field `K`, in the base situation `C` of chapter 42 with
`C.S = Spec K`. The family of projective lines `X ×_S 𝐏¹_S` is then a scheme of finite Krull
dimension, so a natural number bound

`topologicalKrullDim (X ×_S 𝐏¹_S) ≤ d`

always exists.

## Main results

* `Stacks.Chow.topologicalKrullDim_projectiveLineProduct_ne_top`: the dimension is not `⊤`.
* `Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le`: hence the bound exists.

## Implementation notes

Finiteness is read off the local rings, by way of
`AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType`: the family is proper over
`X` by `Stacks.Chow.isProper_projectiveLineProduct_fst`, hence locally of finite type over `X`,
and `X` is locally of finite type over `K` because it is a variety, so the family is locally of
finite type over `K`; it is quasi-compact by
`Stacks.Chow.compactSpace_projectiveLineProduct`.

No integrality of the family is needed, and none is claimed: the bound comes from the local
rings of finitely many affine charts, not from a chain argument on an irreducible space.

This is the input that lets the dimension hypothesis

`hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞)`

carried by the fibre-cycle files for Stacks Tag 0B07 be discharged rather than assumed: the
source states no such bound, and none is needed, because every variety's projective-line family
satisfies one.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The structure morphism of the projective-line family of a variety down to the spectrum of the
ground field. -/
def projectiveLineProductToSpec (K : Type u) [Field K] (C : ChowSituation.{u})
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of K)) {X : Scheme.{u}} (p : X ⟶ C.S) :
    projectiveLineProduct p ⟶ AlgebraicGeometry.Spec (CommRingCat.of K) :=
  pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p ≫ eqToHom hC

/-- The projective-line family of a variety is locally of finite type over the ground field: it is
proper, hence locally of finite type, over the variety, which is itself locally of finite type
over the field. -/
instance locallyOfFiniteType_projectiveLineProductToSpec (K : Type u) [Field K]
    (C : ChowSituation.{u}) (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of K))
    {X : Scheme.{u}} (p : X ⟶ C.S) [AlgebraicGeometry.IsVariety K (p ≫ eqToHom hC)] :
    LocallyOfFiniteType (projectiveLineProductToSpec K C hC p) := by
  have h : LocallyOfFiniteType (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) :=
    inferInstance
  rw [projectiveLineProductToSpec]
  infer_instance

/-- **The dimension of the projective-line family of a variety is finite.** -/
theorem topologicalKrullDim_projectiveLineProduct_ne_top (K : Type u) [Field K]
    (C : ChowSituation.{u}) (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of K))
    {X : Scheme.{u}} (p : X ⟶ C.S) [AlgebraicGeometry.IsVariety K (p ≫ eqToHom hC)] :
    topologicalKrullDim (projectiveLineProduct p) ≠ ⊤ :=
  have : CompactSpace (projectiveLineProduct p) := compactSpace_projectiveLineProduct K C hC p
  AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType K
    (projectiveLineProductToSpec K C hC p)

/-- **A natural number bounding the dimension of the projective-line family of a variety always
exists.** This is the dimension hypothesis the fibre-cycle statements of Stacks Tag 0B07 carry,
proved rather than assumed. -/
theorem exists_topologicalKrullDim_projectiveLineProduct_le (K : Type u) [Field K]
    (C : ChowSituation.{u}) (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of K))
    {X : Scheme.{u}} (p : X ⟶ C.S) [AlgebraicGeometry.IsVariety K (p ≫ eqToHom hC)] :
    ∃ d : ℕ, topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞) :=
  AlgebraicGeometry.exists_natCast_le_of_ne_top
    (topologicalKrullDim_projectiveLineProduct_ne_top K C hC p)

end Stacks.Chow

end

module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleIrreducible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType

/-!
# The δ-dimension of an affine-space bundle over an integral base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be an integral
scheme locally of finite type over `S` of δ-dimension `n`, and let `f : X ⟶ Y` be an
affine-space bundle of rank `r`. Then `X` has δ-dimension `n + r`.

`Stacks.Chow.schemeDeltaDimension_eq_add_of_flat` is the statement for a flat morphism of
relative dimension `r`, and it asks the source only to be irreducible — not integral. An
affine-space bundle supplies all four of its hypotheses: locally of finite type, flat and of
relative dimension `r` were already derived in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic`, and irreducibility of the source is
`Stacks.Chow.irreducibleSpace_of_isAffineSpaceBundle`.

## Main results

* `Stacks.Chow.schemeDeltaDimension_eq_add_of_isAffineSpaceBundle`: **an affine-space bundle of
  rank `r` over an integral base of δ-dimension `n` has δ-dimension `n + r`.**
* `Stacks.LineBundle.Situation.schemeDeltaDimension_totalSpaceToBase_comp`: **the total space of
  a line bundle over an integral scheme of δ-dimension `n` has δ-dimension `n + 1`**, the rank-one
  case that the dévissage of [Stacks, Tag 0F98] applies to each of the two branches of the
  diagram of [Stacks, Tag 0F97].

## References

* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **An affine-space bundle of rank `r` over an integral base of δ-dimension `n` has
δ-dimension `n + r`.** -/
theorem schemeDeltaDimension_eq_add_of_isAffineSpaceBundle (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y) (r : ℕ) (h : IsAffineSpaceBundle f r)
    (hbase : f ≫ sY = sX) {n : ℤ} (hY : schemeDeltaDimension C sY = (n : EInt)) :
    schemeDeltaDimension C sX = ((n + (r : ℤ) : ℤ) : EInt) :=
  have := locallyOfFiniteType_of_isAffineSpaceBundle f r h
  have := flat_of_isAffineSpaceBundle f r h
  have := irreducibleSpace_of_isAffineSpaceBundle f r h
  schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r
    (relativeDimension_of_isAffineSpaceBundle f r h) hY

end Stacks.Chow

namespace Stacks.LineBundle

/-- **The total space of a line bundle over an integral scheme of δ-dimension `n` has
δ-dimension `n + 1`.** -/
theorem Situation.schemeDeltaDimension_totalSpaceToBase_comp (C : Stacks.Chow.ChowSituation.{u})
    (D : Situation.{u}) (sX : D.X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral D.X] {n : ℤ}
    (hn : Stacks.Chow.schemeDeltaDimension C sX = (n : EInt)) :
    Stacks.Chow.schemeDeltaDimension C (D.totalSpaceToBase ≫ sX) = ((n + 1 : ℤ) : EInt) := by
  have := D.locallyOfFiniteType_totalSpaceToBase
  simpa using Stacks.Chow.schemeDeltaDimension_eq_add_of_isAffineSpaceBundle C
    (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase 1
    D.isAffineSpaceBundle_totalSpaceToBase rfl hn

end Stacks.LineBundle

end

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Split

/-!
# The unique splitting of a simplicial set

A simplicial set `X` has a unique splitting with `N(X_m)` equal to the set of nondegenerate
`m`-simplices. Existence is Mathlib's `SSet.splitting`, whose `N m` is `X.nonDegenerate m` and whose
`ι m` is the inclusion; uniqueness is `SSet.Splitting.existsUnique_equiv_nonDegenerate`: for every
splitting `s` of `X`, the map `s.ι n` is a bijection onto the nondegenerate `n`-simplices.

## Main results

* `SSet.exists_splitting_and_forall_existsUnique_equiv_nonDegenerate`: a simplicial set has a
  splitting, and every splitting `s` identifies `s.N n` with the nondegenerate `n`-simplices by a
  unique bijection compatible with the maps to `X _⦋n⦌`.

## References

* [Stacks, Tag 017R](https://stacks.math.columbia.edu/tag/017R)
-/

open CategoryTheory Simplicial

universe u

namespace SSet

/-- **Stacks 017R**. A simplicial set `X` has a unique splitting with `N(X_m)` equal to the set of
nondegenerate `m`-simplices: there is a splitting `s` of `X` (Mathlib's `SSet.splitting`, whose
`N m` is literally `X.nonDegenerate m` and whose `ι m` is the inclusion), and every splitting `s`
of `X` identifies `s.N n`, through `s.ι n`, with the nondegenerate `n`-simplices, by a unique
compatible bijection. -/
@[stacks 017R "existence (the canonical splitting `SSet.splitting`) and uniqueness: every \
  splitting's `ι n` is a bijection onto the nondegenerate `n`-simplices"]
public theorem exists_splitting_and_forall_existsUnique_equiv_nonDegenerate (X : SSet.{u}) :
    (∃ s : X.Splitting, ∀ n, ∃! e : s.N n ≃ X.nonDegenerate n,
      ∀ x, (e x : X _⦋n⦌) = s.ι n x) ∧
    ∀ (s : X.Splitting) (n : ℕ), ∃! e : s.N n ≃ X.nonDegenerate n,
      ∀ x, (e x : X _⦋n⦌) = s.ι n x :=
  ⟨⟨X.splitting, fun n => Splitting.existsUnique_equiv_nonDegenerate _ n⟩,
    fun s n => Splitting.existsUnique_equiv_nonDegenerate s n⟩

end SSet

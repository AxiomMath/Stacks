module

public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Stratifications by closed subspaces with finite étale covers

Stacks 0GUP asserts that a quasi-compact and quasi-separated algebraic space `X` admits a chain
`X ⊃ Z₀ ⊃ Z₁ ⊃ … ⊃ Z_t = ∅` of closed subspaces of finite presentation, with `Z₀` a thickening of
`X`, such that each `Z_i` receives a surjective, finite and finitely presented morphism from a
scheme which is finite étale over `Z_i ∖ Z_{i+1}`. This file names the data of one step of such a
chain and the chain itself, the latter relative to a subfunctor `W` of `X` which `Z₀` is to
thicken.

## Main definitions

* `AlgebraicGeometry.Space.IsFiniteEtaleCoverStep`: the condition on two consecutive members
  `Z ⊇ Z'` of the chain.
* `AlgebraicGeometry.Space.HasFiniteEtaleCoverStratification`: a chain as in Stacks 0GUP whose
  first member is contained in `W` and has the same points as `W`.

## Implementation notes

The open subspace `Z_i ∖ Z_{i+1}` of `Z_i` is named by an open subspace `U` of `Z_i` whose point
set, read in `|X|`, is the difference of the point sets of `Z_i` and `Z_{i+1}`. An open subspace is
determined by its point set (Stacks 03BZ), so this pins `U` down. "Finite étale over `U`" is
finiteness and étaleness of the base change of the cover to `U`. The last member `Z_t = ∅` is the
closed subspace without points; the empty presheaf is not a sheaf, so "empty" is read on points.

The chain is indexed by all natural numbers; only the members of index at most `t` are
constrained beyond the inclusions `Z_{i+1} ⊆ Z_i`.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **One step of the chain of Stacks 0GUP.** For subfunctors `Z' ⊆ Z` of `X`, there is a scheme
`Y` with a surjective, finite and finitely presented morphism `f : Y ⟶ Z` which is finite étale
over the open subspace `U` of `Z` whose points are those of `Z` not in `Z'`. -/
def IsFiniteEtaleCoverStep (Z Z' : Subfunctor X) : Prop :=
  ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ Z.toFunctor) (U : Subfunctor Z.toFunctor),
    IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f ∧
    IsOpenSubspace B S hS U ∧
    Set.range (pointsMap B S hS U.toFunctor (U.ι ≫ Z.ι)) =
      Set.range (pointsMap B S hS Z.toFunctor Z.ι) \
        Set.range (pointsMap B S hS Z'.toFunctor Z'.ι) ∧
    IsFinite B S hS (pullback.fst U.ι f) ∧ IsEtale B S hS (pullback.fst U.ι f)

/-- **A chain as in Stacks 0GUP, thickening a subfunctor `W`.** Closed subspaces
`Z₀ ⊇ Z₁ ⊇ ⋯` of `X` of finite presentation with `Z₀ ⊆ W` having the points of `W`, `Z_t`
without points, and a finite étale cover step between consecutive members up to `t`. -/
def HasFiniteEtaleCoverStratification (W : Subfunctor X) : Prop :=
  ∃ (t : ℕ) (Z : ℕ → Subfunctor X),
    (∀ i, IsClosedSubspace B S hS (Z i)) ∧ (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
    (∀ i, Z (i + 1) ≤ Z i) ∧ Z 0 ≤ W ∧
    Set.range (pointsMap B S hS (Z 0).toFunctor (Z 0).ι) =
      Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
    IsEmpty (points B S hS (Z t).toFunctor) ∧
    ∀ i < t, IsFiniteEtaleCoverStep B S hS (Z i) (Z (i + 1))

end AlgebraicGeometry.Space

end

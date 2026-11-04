module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.EnlargementAboveCardinal

/-!
# Enlarging a big fppf site so that it contains given schemes

A construction on algebraic spaces defined using a fixed big fppf site `B` may produce schemes
which are too large to be objects of `B`; the remedy of the Stacks project is to pass to a big
fppf site containing `B` and the schemes produced. This file supplies such an enlargement: for
every set of schemes which is small in the working universe there is a big fppf site `B'`
containing `B` in the sense of `AlgebraicGeometry.IsContained` and containing every scheme of
the set.

## Main results

* `AlgebraicGeometry.BigFppfSite.exists_isContained_contains`: every big fppf site is contained
  in one which contains a prescribed small set of schemes.

## Implementation notes

The enlargement is the common enlargement of Stacks 022J,
`AlgebraicGeometry.exists_common_bigFppfSite`, applied to `B` and to a big fppf site containing
the prescribed schemes, which `AlgebraicGeometry.BigFppfSite.exists_containing` supplies. The
common enlargement is only asserted to dominate the cutoffs and the covering bounds of the
given sites; that this makes it contain them is `isContained_of_le` (of
`StacksFrontier.AlgebraicGeometry.Topologies.Fppf.EnlargementAboveCardinal`), because a chosen
covering family of a big fppf site is an fppf covering family below the cutoff with an index set
bounded by the covering bound, and both conditions survive enlarging the two cardinals.

## References

* [Stacks Project, Tag 022J](https://stacks.math.columbia.edu/tag/022J)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.BigFppfSite

/-- **Every big fppf site is contained in one containing a prescribed small set of schemes.**
The site is the common enlargement of Stacks 022J of `B` and of a big fppf site containing the
schemes of `S₀`. -/
theorem exists_isContained_contains (B : BigFppfSite.{u}) (S₀ : Set Scheme.{u})
    [Small.{u} S₀] :
    ∃ B' : BigFppfSite.{u}, IsContained (τ := .fppf) B B' ∧ ∀ X ∈ S₀, B'.Contains X := by
  obtain ⟨B₁, hB₁⟩ := exists_containing S₀
  obtain ⟨C, hC⟩ := exists_common_bigFppfSite.{u, 0} (fun b : Bool => if b then B₁ else B)
  refine ⟨C, isContained_of_le (hC false).1 (hC false).2, fun X hX => ?_⟩
  exact lt_of_lt_of_le (hB₁ X hX) (hC true).1

/-- **Every big fppf site is contained in one containing a given scheme of it and a prescribed
small set of schemes**, with the base scheme read in the larger site through the containment.
This is `exists_isContained_contains` together with the transport of the containment of the base
scheme along it. -/
theorem exists_isContained_contains_base (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (S₀ : Set Scheme.{u}) [Small.{u} S₀] :
    ∃ (B' : BigFppfSite.{u}) (_ : IsContained (τ := .fppf) B B'),
      B'.Contains S ∧ ∀ X ∈ S₀, B'.Contains X := by
  obtain ⟨B', h, hX⟩ := exists_isContained_contains B S₀
  exact ⟨B', h, largerContains h hS, hX⟩

end AlgebraicGeometry.BigFppfSite

end

module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.IdealTrivialization

/-!
# Trivializations of the ideal sheaf of an effective Cartier divisor exist locally

Let `Y ⊆ X` be the closed subscheme cut out by `I : X.IdealSheafData`, and suppose `Y` is an
effective Cartier divisor, that is, its ideal sheaf `ℐ = Stacks.Divisors.negativeTwist I` is an
invertible `𝒪_X`-module. Clause 2 of [Stacks, Tag 0B8M] says that an invertible module on a
locally ringed space is locally free of rank one; in its sectionwise form it gives, around every
point `x ∈ X`, an open `U ∋ x` and a restriction-compatible family of `𝒪_X(W)`-linear
isomorphisms `ℐ(W) ≅ 𝒪_X(W)` for the opens `W ≤ U`, that is, a
`Stacks.Divisors.IdealTrivialization I U`. The open can moreover be taken affine, by restricting
the trivialization to an affine open neighbourhood of `x` inside `U`.

Such a trivialization carries a local equation of `Y` on `U`
(`Stacks.Divisors.IdealTrivialization.equation`), so this is the existence of local equations
of an effective Cartier divisor around every point of `X`.

## Main results

* `Stacks.Divisors.IdealTrivialization.exists_mem_nonempty`: every point of `X` has an open
  neighbourhood over which `ℐ` is sectionwise trivial.
* `Stacks.Divisors.IdealTrivialization.exists_isAffineOpen_mem_nonempty`: the same with an
  affine open neighbourhood.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors.IdealTrivialization

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- **The ideal sheaf of an effective Cartier divisor is locally trivial.** Every point of `X`
has an open neighbourhood over which the ideal sheaf `ℐ` of the divisor is sectionwise
isomorphic to `𝒪_X`. This is clause 2 of [Stacks, Tag 0B8M], in sectionwise form, applied to
the invertible module `ℐ`. -/
theorem exists_mem_nonempty (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (Stacks.Divisors.IdealTrivialization I U) := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (Stacks.Divisors.negativeTwist I) := hI
  obtain ⟨U, hU, t⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) (structureSheafRing X.toRingedSpace).property
      (Stacks.Divisors.negativeTwist I)
  obtain ⟨y, hy⟩ := Opens.mem_iSup.mp (hU ▸ Opens.mem_top x)
  exact ⟨U y, hy, t y⟩

/-- **The ideal sheaf of an effective Cartier divisor is trivial on affine opens around every
point.** The trivializing open of `exists_mem_nonempty` can be taken affine: restrict the
trivialization to an affine open neighbourhood of the point inside it. -/
theorem exists_isAffineOpen_mem_nonempty (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty (Stacks.Divisors.IdealTrivialization I U) := by
  obtain ⟨U, hxU, ⟨t⟩⟩ := exists_mem_nonempty hI x
  obtain ⟨V, hxV, hVU⟩ := Stacks.CartierAffineLocal.exists_affineOpens_le U hxU
  exact ⟨V, V.2, hxV, ⟨t.comp (homOfLE hVU)⟩⟩

end Stacks.Divisors.IdealTrivialization

end

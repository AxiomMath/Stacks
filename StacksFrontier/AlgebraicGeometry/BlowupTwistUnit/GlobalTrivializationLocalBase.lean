module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.PicardUFD.AffineScheme

/-!
# The top relative forms over a local affine base are trivial

Let `q : S ⟶ S₀` be a morphism of schemes with `S` affine and `Γ(S, ⊤)` a local ring, and suppose
the sheaf of relative differentials `Ω_{S/S₀}` is finite locally free of rank `r`. Then the top
relative forms `Ω^r_{S/S₀}` are isomorphic to the structure sheaf.

The proof is the composition of three statements from the library. First, `Ω^r_{S/S₀}` is the `r`-th
exterior power of `Ω_{S/S₀}`, so its rank is `binom(r, r) = 1` by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower`. Second, clause 1 of
[Stacks, Tag 0B8M] makes a rank-one finite locally free module on a scheme invertible; the form of
it used here is
`Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one`, which
already speaks the `Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2` spelling that
the affine triviality statement consumes. Third, an invertible module on an affine scheme whose
ring of functions has trivial Picard group is trivial
(`Stacks.PicardUFD.isTrivial_of_isInvertible_of_isAffine`), and the Picard group of a local ring
is trivial by Mathlib's instance for `CommRing.Pic`.

The conclusion is stated as a `Nonempty` of isomorphisms rather than as a chosen isomorphism:
nothing canonical picks a generator of the module of top forms, the choice being exactly the
choice of a basis of `Ω_{S/S₀}` over the local ring, and the consumers of this statement need
only that one exists.

## Main results

* `Stacks.BlowupTwistUnit.nonempty_relativeDifferentialForms_iso_unit_of_isLocalRing_sections`:
  **`Ω^r_{S/S₀} ≅ 𝒪_S`** for `S` affine with local ring of global functions and `Ω_{S/S₀}` finite
  locally free of rank `r`.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms` is a reducible wrapper around the degree
piece of the exterior algebra, so the statement about the top forms and the statement about
`AlgebraicGeometry.Scheme.Modules.exteriorPower` are the same statement and the proof moves
between them with no transport.

The site of the rank hypothesis is named explicitly, `(C := S.Opens)` and
`(J := TopologicalSpace.Opens.grothendieckTopology S)`, because writing the class with the sheaf
of rings left to unification elaborates the module against a metavariable and fixes the universes
at their defaults.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.BlowupTwistUnit

/-- **The top relative forms of a morphism out of an affine scheme with local ring of global
functions are trivial.** If `Ω_{S/S₀}` is finite locally free of rank `r` and `Γ(S, ⊤)` is a local
ring, then `Ω^r_{S/S₀} ≅ 𝒪_S`.

The `r`-th exterior power of a rank-`r` module has rank `binom(r, r) = 1`, hence is invertible by
clause 1 of [Stacks, Tag 0B8M], and an invertible module on an affine scheme whose functions form
a ring with trivial Picard group is trivial, which is the case for a local ring. -/
theorem nonempty_relativeDifferentialForms_iso_unit_of_isLocalRing_sections
    {S₀ S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] (q : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials q) r] :
    Nonempty (Scheme.Hom.relativeDifferentialForms q (r : ℤ) ≅
      SheafOfModules.unit S.ringCatSheaf) := by
  have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := S.Opens)
      (J := Opens.grothendieckTopology S)
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q) (r : ℤ)) 1 := by
    simpa only [Nat.choose_self] using
      Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
        (Scheme.Hom.relativeDifferentials q) r r
  have hinv : Stacks.SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q) (r : ℤ)) :=
    (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one S
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q) (r : ℤ))).mpr hrank
  exact Stacks.PicardUFD.isTrivial_of_isInvertible_of_isAffine S
    (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q) (r : ℤ))

end Stacks.BlowupTwistUnit

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSmoothFiniteLocallyFree

/-!
# Stacks 0CK5 with the 04CS site transport supplied

`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials` proves Stacks 0CK5 —
the sheaf of differentials `Ω_{X/Y}` of a smooth morphism `f : X ⟶ Y` of algebraic spaces is
finite locally free on the small étale site of `X` — taking as its argument the comparison
`AlgebraicGeometry.Space.SheafOfDifferentialsSchemeSiteComparison`, the transport of finite local
freeness across the small Zariski and small étale sites of a morphism of schemes of the site.
This file proves that comparison and states 0CK5 with it supplied.

The comparison is proved from three results of the tree: Stacks 04CS in the form
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`, which identifies the
spaces-level `Ω_{U/V}` with the associated module `(Ω_{U/V})^a` of Stacks 03DU (4); Stacks 05VG
for the clause 03DL (2) at `τ = étale`,
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`, which is finite local
freeness of `𝓕^a` on the small étale site of a *scheme* from finite local freeness of `𝓕`; and
Stacks 03DM at the comparison equivalence of Stacks 03DX (2),
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff`, which moves
that between the small étale site of the scheme `U` and the small étale site of the algebraic
space it represents.

## Main results

* `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeSiteComparison`: that transport, proved.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth`:
  **Stacks 0CK5**, with that transport supplied rather than taken as an argument.

## References

* [Stacks Project, Tag 0CK5](https://stacks.math.columbia.edu/tag/0CK5).
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS).
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM), the invariance of the
  local conditions of 03DL under an equivalence of ringed topoi.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU) and
  [Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), the associated module on the small étale
  site and the comparison it induces.
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG), finite local freeness
  across the small Zariski and small étale sites of a scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of Stacks 04CS transports finite local freeness across the two sites, with
no hypothesis.**  For a morphism `ψ : U ⟶ V` of schemes of the big fppf site over `S`, finite
local freeness of the Zariski sheaf of relative differentials `Ω_{U/V}` gives finite local
freeness of the sheaf of differentials of `ψ` read as a morphism of represented algebraic spaces,
on the small étale site.

Three steps.  Clause (2) of Stacks 03DL on the small Zariski site of `U` is the local-generators
condition of Stacks 01C6 (2),
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`; Stacks 05VG
for that clause at `τ = étale`,
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`, carries it to the
associated module of Stacks 03DU (4) on the small étale site of the *scheme* `U`; and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff`, Stacks 03DM
at the comparison equivalence of Stacks 03DX (2) between that site and the small étale site of
the represented algebraic space, reads it there.  Stacks 04CS,
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`, identifies the module so obtained
with the sheaf of differentials of `ψ`. -/
theorem sheafOfDifferentialsSchemeSiteComparison :
    SheafOfDifferentialsSchemeSiteComparison B S hS := by
  intro U V ψ h
  obtain ⟨e⟩ := sheafOfDifferentialsSchemeComparison B S hS U V ψ
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e.symm ?_
  exact (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS U _).2
    (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property _
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite _ h))

/-- **Stacks 0CK5, asking nothing beyond smoothness.** The sheaf of differentials `Ω_{X/Y}` of a
smooth morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is finite locally free on the
small étale site of `X`.

This is `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials`, the reduction
of Stacks 0CK5 to Stacks 02G1, applied to
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeSiteComparison`, which proves the comparison
of Stacks 04CS that the reduction takes as its argument `hsite`.  The mathematics is that of the
reduction; only the argument is supplied. -/
@[stacks 0CK5 "the unconditional form, with the 04CS site transport of finite local freeness
  discharged by `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeSiteComparison`; smoothness of
  `f` is the only thing this asks"]
theorem isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsSmooth B S hS f.hom) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (sheafOfDifferentials B S hS f) :=
  isFiniteLocallyFreeOnSite_sheafOfDifferentials B S hS f hf
    (sheafOfDifferentialsSchemeSiteComparison B S hS)

end AlgebraicGeometry.Space

end

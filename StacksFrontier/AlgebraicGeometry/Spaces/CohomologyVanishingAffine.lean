module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishing

/-!
# Vanishing of cohomology on a space affine over one with vanishing cohomology

Let `X` be a quasi-compact, quasi-separated algebraic space all of whose quasi-coherent modules
have vanishing first cohomology, that is the data of Stacks 07UY, and let `f : X' ⟶ X` be an
affine morphism of algebraic spaces.  Clause (1) of Stacks 07V0 asserts that then
`H¹(X', 𝓕') = 0` for every quasi-coherent `𝒪_{X'}`-module `𝓕'`.  The source's proof is two
citations: the higher direct images of `𝓕'` vanish along an affine morphism, so the Leray
spectral sequence identifies `H¹(X', 𝓕')` with `H¹(X, f_*𝓕')`, and `f_*𝓕'` is quasi-coherent,
so the hypothesis of the situation applies to it.

## Main definitions

* `AlgebraicGeometry.Space.FirstCohomologyVanishingAtRingUniverse` is the vanishing hypothesis
  of Stacks 07UY, read at the module universe of the structure rings.

## Main results

* Clause (1) of Stacks 07V0 itself is
  `…CohomologyVanishingSituation.isZero_rightDerived_one_globalSectionsFunctor_of_isAffineHom`,
  in `StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffineMorphism`.

## Implementation notes

*Which cohomology.*  The first cohomology on `X'` is the first right derived functor of the
composite `Γ(X, f_*−)`, exactly as in `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`
(the library's form of Stacks 0D2U) and
`AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage` (Stacks 08EX), and for the
same reason: the identification of `Γ(X, f_*−)` with `Γ(X', −)` is
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, which is stated for a
`Stacks.Sheaves.RingedToposModules.RingedToposHom` built from the adjunction between inverse and
direct image, whereas `AlgebraicGeometry.Space.smallEtaleRingedToposHom` carries the
direct-image form of the structure map only.

*Why the vanishing hypothesis of the situation is restated.*  The field
`AlgebraicGeometry.Space.CohomologyVanishingSituation.firstCohomologyVanishing` is stated for
`AlgebraicGeometry.Space.QuasicoherentSheaves.{u, max (u + 1) m}` through
`Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, m}`, whose module universe
contains the universe `u + 1` of the objects of the small étale site.  The direct image
`AlgebraicGeometry.Space.modulePushforward` exists only at the module universe `u` of the
structure rings, for the reasons given in
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage`, so `f_*𝓕'` is never an argument the
field can be applied to: `max (u + 1) m = u` is impossible.  The hypothesis
`AlgebraicGeometry.Space.FirstCohomologyVanishingAtRingUniverse` below is that same vanishing —
the situation's own hypothesis, which the source states with no universes at all — at the module
universe where the direct image lives, and it is the only form in which the situation can be
consumed here.  It is named in the clause string.

*The three further carried hypotheses* are not content of Stacks 07V0 and are all inherited.
`h03DW` and `h072Z` are the hypotheses of
`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`, the library's form of Stacks 0D2U,
namely the affine case of Stacks 073H on the small étale site (Stacks 03DW) and the acyclicity
of Stacks 072Z read through part (3) of Stacks 0731; `h07U8` is the hypothesis
`AlgebraicGeometry.Space.SchemeTargetAffinePushforwardQuasicoherent` of the library's form of
Stacks 07U8, the quasi-coherence of the direct image over a target represented by a scheme of
the site.  Each is documented at its point of definition.

*Why `h072Z` is carried even though Stacks 072Z is proved unqualified.*
`Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective` is stated for a source
ringed topos `RingedTopos.{u, u, u}`, with all three of its universes equal, and for a
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, which is built from the adjunction between
inverse and direct image.  The small étale ringed site of an algebraic space over a `Scheme.{u}`
is a `RingedTopos.{u + 1, u, u}` — its objects lie one universe above its morphisms, structure
sheaf and modules — and the morphism of ringed topoi attached to a morphism of algebraic spaces
by `AlgebraicGeometry.Space.smallEtaleRingedToposHom` carries the direct-image form of the
structure map only, with no inverse image and no adjunction.  So neither of the two shapes the
existing statement needs is available here, which is what
`StacksFrontier/AlgebraicGeometry/Spaces/AffineMorphismCohomologyCollapse.lean` records at the
point where the hypothesis is defined.

*Why `h03DW` is carried even though Stacks 03DW has an attribute site.*  The one site is
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModuleCohomologyDegreeZero.lean`, which is
clause-qualified to the case `q = 0` of clause (1) of that tag.  `h03DW` is needed in the
degrees `n > 0`, which is exactly what that site excludes.

*Quasi-compactness and quasi-separatedness* of the space of the situation are not used: they
enter the section only through its later results.

*Clause (2) of Stacks 07V0 is treated separately*, in
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChange`, which proves its affineness
assertion.  The remaining assertion of that clause, `Γ(X', 𝒪_{X'}) = A'`, is not proved: it needs
the identification of `(X' → X)_*𝒪_{X'}` with `A' ⊗_A 𝒪_X`, which is an assertion of Stacks 07U8
that the library's form of that tag does not carry.

## References

* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The vanishing hypothesis of Stacks 07UY, read at the module universe of the structure
rings: every quasi-coherent `𝒪_X`-module with sections in the universe of the schemes has
vanishing first cohomology on `X`.

This is the hypothesis of the situation at the one module universe at which the direct image of
modules exists; see the implementation notes of this file. -/
def FirstCohomologyVanishingAtRingUniverse (X : AlgebraicSpaces B S hS) : Prop :=
  have := enoughInjectives_modules B S hS X.1 X.2
  ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1
          X.2).O))).rightDerived 1).obj M)

namespace CohomologyVanishingSituation

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end

end

module

public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparison
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global small étale cohomology of a quasi-coherent module

Let `X` be a scheme and `ℱ` a quasi-coherent `𝒪_X`-module. In positive degree the cohomology of
`ℱ` computed in `Mod(𝒪_X)` as a right derived functor of global sections agrees with Mathlib's
`CategoryTheory.Sheaf.H` of the associated abelian sheaf `ℱᵃ` on the small étale site:

  `H ^ (n + 1) (X, ℱ) ≅ H ^ (n + 1) (X_étale, ℱᵃ)`.

This is [Stacks, Tag 03P2] for `𝒞 = X_étale` restated in the shape its consumers want. The
tag is already proved, as `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`, but
between `CategoryTheory.Sheaf.H'` over an object of each site, and the two vanishing theorems
that consume it speak of `Hgroup` on the Zariski side and of `CategoryTheory.Sheaf.H` on the
étale side. Both ends are bridged by results already in the library and this file only composes
them: `AlgebraicGeometry.hgroupIsoSheafCohomology` on the Zariski side, and on the étale side
`Stacks.Cohomology.TerminalCohomology.h'IsoH` at the final object
`(opensToEtale X).obj ⊤` of `AlgebraicGeometry.isTerminal_opensToEtale_top`.

## Main definitions

* `AlgebraicGeometry.hgroupIsoSmallEtaleGlobalCohomology`: the isomorphism above.

## Main results

* `AlgebraicGeometry.isZero_hgroup_iff_subsingleton_sheafH_smallEtaleAssociatedSheaf`: the same
  as an equivalence of vanishing statements.
* `AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup`: the
  left-to-right implication in every positive degree, which is the vanishing transfer the
  Artin–Schreier argument of [Stacks, Tag 0A3K] carries as a hypothesis.

## Implementation notes

**No `@[stacks 03P2]` attribute is attached.** The covering set of that tag is already complete:
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` for `𝒞 = X_étale` and
`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` for `𝒞 = (Sch/X)_τ`. What is here is
a restatement of the first in a second shape, not a further case.

**The degree is positive.** `AlgebraicGeometry.hgroupIsoSheafCohomology`, which identifies
`Hgroup` with the cohomology presheaf, is proved in positive degree only, that being where the
derived functor of a corepresented functor is `Ext`. Every degree in which the Artin–Schreier
argument uses the comparison is positive, so nothing is lost there.

**The coefficient universe is `u`, the morphism universe of the small étale site**, and so is the
`Ext` universe on both sides. That is forced: Mathlib's `CategoryTheory.Sheaf.H'` pins its
coefficients to the morphism universe of the site, so [Stacks, Tag 03P2] is stated at `u`. The
Artin–Schreier sequence of the `ArtinSchreierSequence` directory of this chapter is at
coefficients `u + 1` instead, so this file does not discharge the `hcomp` hypothesis of
[Stacks, Tag 0A3K] and [Stacks, Tag 0A3N] as those are stated. Of the two ways to close that
last gap only one is open. A coefficient-universe comparison of `Ext` on this site is not
available, and the obvious route to it is circular, for the reason set out at length in
`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequencePageTwo.lean`: the only
comparisons of `Ext` along a fully faithful exact functor,
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` and its projective
counterpart, each need enough injectives in the *source* category, which is the very thing
missing. Rereading those two statements at coefficients `u` is open: sheafification is available
there, Mathlib's instance for the small étale site being stated at the morphism universe.

`CategoryTheory.IsGrothendieckAbelian.hasExt` has its priority raised locally, exactly as in
`SmallEtaleQuasiCoherentCohomology.lean`: `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology`
gives `HasExt.{u + 1}` and is declared later, so it otherwise wins the search for the étale
`Ext` universe.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0A3K](https://stacks.math.columbia.edu/tag/0A3K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u})]

/-- **Zariski cohomology of a quasi-coherent module is global small étale cohomology of its
associated sheaf**, in positive degree:

  `H ^ (n + 1) (X, ℱ) ≅ H ^ (n + 1) (X_étale, ℱᵃ)`,

the left side computed in `Mod(𝒪_X)` and the right side Mathlib's `CategoryTheory.Sheaf.H`.

The three steps are `AlgebraicGeometry.hgroupIsoSheafCohomology`, which turns the left side into
the cohomology presheaf of the underlying abelian sheaf at `⊤`;
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`, which is [Stacks, Tag 03P2] for
`𝒞 = X_étale`; and `Stacks.Cohomology.TerminalCohomology.h'IsoH`, which identifies the cohomology
presheaf at a final object with global cohomology, applied at the final object
`(opensToEtale X).obj ⊤`. -/
@[sga "4 VII 4.3" "Isomorphism H^{n+1}(X"]
def hgroupIsoSmallEtaleGlobalCohomology (n : ℕ) :
    Hgroup X.ringCatSheaf ⊤ (n + 1) F ≅
      AddCommGrpCat.of (Sheaf.H.{u, u} (smallEtaleAssociatedSheaf X F) (n + 1)) :=
  hgroupIsoSheafCohomology F ⊤ n ≪≫
    smallEtaleQuasiCoherentGlobalCohomologyIso X F (n + 1) ≪≫
      Stacks.Cohomology.TerminalCohomology.h'IsoH (Scheme.smallEtaleTopology X)
        (smallEtaleAssociatedSheaf X F) (n + 1) _ (isTerminal_opensToEtale_top X)

/-- **Vanishing of the Zariski cohomology of a quasi-coherent module is vanishing of the global
small étale cohomology of its associated sheaf**, in positive degree. This is
`AlgebraicGeometry.hgroupIsoSmallEtaleGlobalCohomology` read as an equivalence of vanishing
statements, the two sides following their sources in spelling vanishing as `Limits.IsZero` on the
module side and as `Subsingleton` on the étale side. -/
theorem isZero_hgroup_iff_subsingleton_sheafH_smallEtaleAssociatedSheaf (n : ℕ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ (n + 1) F) ↔
      Subsingleton (Sheaf.H.{u, u} (smallEtaleAssociatedSheaf X F) (n + 1)) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact (hgroupIsoSmallEtaleGlobalCohomology X F n).addCommGroupIsoToAddEquiv.toEquiv
    |>.subsingleton_congr

/-- **The vanishing transfer of the Artin–Schreier argument, as a theorem.** If the cohomology of
a quasi-coherent module `ℱ` on `X` vanishes in a positive degree `i`, then so does the global
small étale cohomology of `ℱᵃ`.

This is the implication that [Stacks, Tag 0A3K] and [Stacks, Tag 0A3N] carry as the hypothesis
`hcomp`, for the associated sheaf of `ℱ` and at coefficient universe `u`. -/
theorem subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup (i : ℕ) (hi : 0 < i)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ i F)) :
    Subsingleton (Sheaf.H.{u, u} (smallEtaleAssociatedSheaf X F) i) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  exact (isZero_hgroup_iff_subsingleton_sheafH_smallEtaleAssociatedSheaf X F n).mp h

end AlgebraicGeometry

end

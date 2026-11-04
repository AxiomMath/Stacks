module

public import StacksFrontier.AlgebraicGeometry.Divisors.Modification.InvertibleFiltration
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Proper
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Sections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.PullbackStable

/-!
# Assembling the splitting datum of a projective bundle

`Stacks.Divisors.BundleSplittingDatum` is the fifteen-field record that Tag 0AYP reads off the
projective bundle of a module of rank `r + 1`. This file assembles it on the presentation
`Stacks.RelativeProj.projectiveBundle` of `𝐏(ℰ)`, the one built from a
`Stacks.RelativeProj.Situation`, where properness of the projection is Tag 0800's
`Stacks.RelativeProj.isProper_projectiveBundleToBase` and the tautological pair
`(𝒪(1), π^*ℰ ↠ 𝒪(1))` is `Stacks.RelativeProj.TautologicalDatum`.

## Main results

* `Stacks.ProjectiveBundleSplitting.bundleSplittingDatumOfTautological`: the splitting datum of
  `𝐏(ℰ)`, from the tautological datum of the bundle, the rank of the tautological kernel, and a
  section over a nonempty open.
* `Stacks.ProjectiveBundleSplitting.nonempty_bundleSplittingDatum_of_tautological`: the same,
  with the section over a nonempty open given existentially.

## Implementation notes

**Which presentation.** There are two constructions of `𝐏(ℰ)`:
`Stacks.RelativeProj.projectiveBundle`, from a `Situation`, and
`Stacks.SymGraded.schemeProjectiveBundle`, from a `SheafGradedAlgebra`. Properness of the
projection, Tag 0800, is stated for the first, and so is `TautologicalDatum`; assembling the record
there needs no transport across `AlgebraicGeometry.projectiveBundlePresentationsAgree`.

**The kernel.** `Scheme.Modules` is abelian, so the fields `sub`, `incl` and `incl_comp_quot`
are the categorical kernel of the tautological surjection, its inclusion, and the kernel
condition; nothing is assumed about them. The field `shortExact_pullback` comes with them:
the tautological datum's surjection is an epimorphism onto an invertible module, which by
`Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible` is all that
keeping the kernel sequence short exact under every pullback needs.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 0800](https://stacks.math.columbia.edu/tag/0800)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundleSplitting

open Stacks.RelativeProj Stacks.Divisors

variable {Y : Scheme.{u}} (E : Y.Modules) [E.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The splitting datum of `𝐏(ℰ)`.** The bundle, its projection and the properness of that
projection are `Stacks.RelativeProj.projectiveBundle`,
`Stacks.RelativeProj.projectiveBundleToBase` and Tag 0800's
`Stacks.RelativeProj.isProper_projectiveBundleToBase`; the twist, its invertibility and the
tautological surjection onto it are the four fields of the tautological datum; the tautological
kernel and its inclusion are the categorical kernel of that surjection. -/
def bundleSplittingDatumOfTautological (r : ℕ) (D : TautologicalDatum Y E)
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel D.univ) r)
    (U : Y.Opens) (hU : Nonempty U) (σ : U.toScheme ⟶ projectiveBundle Y E)
    (hσ : σ ≫ projectiveBundleToBase Y E = U.ι) :
    BundleSplittingDatum Y E r where
  bundle := projectiveBundle Y E
  proj := projectiveBundleToBase Y E
  isProper_proj := isProper_projectiveBundleToBase Y E
  sub := kernel D.univ
  twist := D.twist
  incl := kernel.ι D.univ
  quot := D.univ
  incl_comp_quot := kernel.condition D.univ
  shortExact_pullback := fun h =>
    shortExact_map_pullback_of_epi_isInvertible h D.univ D.epi_univ D.invertible
  twist_isInvertible := D.invertible
  sub_rank := hrank
  trivialOpen := U
  nonempty_trivialOpen := hU
  sect := σ
  sect_comp_proj := hσ

/-- **The splitting datum of `𝐏(ℰ)` exists**, given a section of the bundle over some nonempty
open of `Y`. -/
theorem nonempty_bundleSplittingDatum_of_tautological (r : ℕ) (D : TautologicalDatum Y E)
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel D.univ) r)
    (hsect : ∃ (U : Y.Opens) (_ : Nonempty U) (σ : U.toScheme ⟶ projectiveBundle Y E),
      σ ≫ projectiveBundleToBase Y E = U.ι) :
    Nonempty (BundleSplittingDatum Y E r) := by
  obtain ⟨U, hU, σ, hσ⟩ := hsect
  exact ⟨bundleSplittingDatumOfTautological E r D hrank U hU σ hσ⟩

end Stacks.ProjectiveBundleSplitting

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyBaseCase
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyDimensionShift
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GN3 reduced to the vanishing of cohomology on pointwise injective colimits

Stacks 0GN3 asserts that, for a site carrying a set `S` of quasi-compact sheaves of sets with
enough covers, products and equalizers, the canonical map
`colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism for every filtered diagram of
abelian sheaves and every `p ≥ 0`. Its proof is an induction on `p`: the base case is
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections_zero` and
the step is
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections_succ`.
This file runs the induction, and so isolates the one input neither of those supplies:

> for every filtered diagram `G` of **injective** abelian sheaves and every `n`,
> `H^{n+1}(C, colim G) = 0`.

Granting that, every degree follows, by hypotheses (1), (2), (3) and (5) of the source alone.

## What this file does not contain

The vanishing input is a *hypothesis* here, and it is precisely the half of Stacks 0GN3 that
uses the set `S` beyond degree zero, so no declaration in this file carries the tag 0GN3. It is
proved as
`Stacks.Cohomology.ColimitsOfCohomology.isZero_rightDerived_globalSections_colimit_of_isIso`,
from the identification of cohomology over a sheaf of sets `K` with cohomology on the localized
site `C/K` (Stacks 07A0, `Stacks.Cohomology.SheafOfSets.cohomologyOnSheafIso`) applied to the
self-products of a `K ∈ S` covering the final sheaf. Stacks 0GN3 itself is
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections`.

**Stacks 0GN3 is not proved from the induction below.** The induction
here is run at a *fixed* site `J` and a *fixed* index category `I`, and takes `hacyclic` as a
hypothesis quantified over all degrees. The source's recursion instead varies the site: the
vanishing input at degree `n + 1` over `C` is produced from Stacks 0GN3 in degrees `q ≤ n` over
the localized sites `C/Kʳ`. So the inductive hypothesis of this lemma — which is about `J` — is
not what discharging `hacyclic` needs, and this lemma cannot be used to prove Stacks 0GN3 by
supplying its own conclusion. `isIso_colimit_post_rightDerived_globalSections` therefore runs a
strong induction on the degree with the site generalised, and consumes the degree-stratified
`isZero_rightDerived_globalSections_colimit_of_isIso` rather than this lemma. What is below
remains the right statement for a consumer that already has the vanishing input in hand at a
fixed site.

## Main results

* `isIso_colimit_post_rightDerived_globalSections_of_acyclic`, in the namespace
  `Stacks.Cohomology.ColimitsOfCohomology`: the induction, i.e. Stacks 0GN3 for all degrees from
  its degree-zero hypotheses plus the vanishing input.

## Implementation notes

The induction is on the degree with the diagram generalised, at a fixed site and a fixed filtered
index category; the source instead performs a strong induction which also varies the site, since
it produces its vanishing input on the localized sites `C/K^n`. Moving between the site and its
localizations is `Stacks.Cohomology.CoveringSet.exists_localized_coveringSet`; it is needed only
where the vanishing input is proved rather than assumed.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] ColimitsOfCohomology.enoughInjectives_sheaf_ab
  ColimitsOfCohomology.additive_globalSections_ab

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Stacks 0GN3, granting the vanishing input.** Let `S` be a set of sheaves of sets satisfying
hypotheses (1), (2), (3) and (5) of Stacks 0GN3, and suppose that degree-`n + 1` cohomology
vanishes on the colimit of every filtered diagram of injective abelian sheaves. Then degree-`p`
cohomology commutes with filtered colimits of abelian sheaves for every `p`.

The vanishing hypothesis is the only residue: it is what the source derives from the set `S` by
the Čech spectral sequence of Stacks 079Z and the localization comparison of Stacks 07A0. -/
lemma isIso_colimit_post_rightDerived_globalSections_of_acyclic (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (hacyclic : ∀ (n : ℕ) (G : I ⥤ Sheaf J Ab.{u}), (∀ i, Injective (G.obj i)) →
      IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit G)))
    (p : ℕ) (F : I ⥤ Sheaf J Ab.{u}) :
    IsIso (colimit.post F ((Sheaf.Γ J Ab.{u}).rightDerived p)) := by
  induction p generalizing F with
  | zero =>
      exact isIso_colimit_post_rightDerived_globalSections_zero J S h_terminal h_lift
        h_product h_quasiCompact F
  | succ n ih =>
      exact isIso_colimit_post_rightDerived_globalSections_succ J n ih (hacyclic n) F

end Stacks.Cohomology.ColimitsOfCohomology

end

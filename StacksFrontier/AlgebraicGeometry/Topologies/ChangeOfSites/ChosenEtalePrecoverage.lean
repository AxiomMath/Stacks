module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage

/-!
# The precoverage of the chosen big étale site, and the families inside a covering sieve

The étale covering families chosen on the underlying category of a big fppf site `B` were
specified by hand, as the families selected by `B` which are in addition étale coverings.
`AlgebraicGeometry.etalePrecoverage_eq_comap` identifies the precoverage they present with the
étale precoverage of all schemes comapped along the site's inclusion; this file turns the
stability properties that identification yields into instances, and reads off from them the two
facts about the members of a chosen étale covering family that the comparison of sites consumes.

## Main results

* `AlgebraicGeometry.map_mem_schemeEtalePrecoverage_of_mem_etalePrecoverage`: the image of a
  chosen étale covering family is an étale covering family of schemes — the hypothesis the étale
  case of **Stacks 07AK** takes.
* `AlgebraicGeometry.etale_of_mem_etalePrecoverage`: every member of a chosen étale covering
  family is étale.
* The instances record that the chosen étale precoverage has isomorphisms and is stable under
  composition and base change.

## Implementation notes

`AlgebraicGeometry.Scheme.etalePrecoverage` is already known to Mathlib to be stable under base
change; `CategoryTheory.Precoverage.HasIsos` and
`CategoryTheory.Precoverage.IsStableUnderComposition` have to be supplied, and both are one step
over facts the library already has — an isomorphism of schemes is an étale covering family on its
own, and étaleness is multiplicative.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An isomorphism of schemes is a one-member étale covering family. -/
public lemma schemeEtalePrecoverage_hasIsos :
    Precoverage.HasIsos Scheme.etalePrecoverage.{u} := ⟨by
  intro X Y f hf
  change Presieve.singleton f ∈ Scheme.etalePretopology Y
  exact Scheme.etalePretopology.has_isos f⟩

/-- Étale covering families of schemes are stable under composition, étaleness being
multiplicative. -/
private alias schemeEtalePrecoverage_isStableUnderComposition :=
  Scheme.etalePrecoverage_isStableUnderComposition

/-- The chosen étale precoverage of a big fppf site has isomorphisms. -/
instance etalePrecoverage_chosen_hasIsos (B : BigFppfSite.{u}) :
    (etalePrecoverage B).HasIsos := by
  let := schemeEtalePrecoverage_hasIsos.{u}
  rw [etalePrecoverage_eq_comap B]
  infer_instance

/-- The chosen étale precoverage of a big fppf site is stable under composition. -/
instance etalePrecoverage_chosen_isStableUnderComposition (B : BigFppfSite.{u}) :
    (etalePrecoverage B).IsStableUnderComposition := by
  let := schemeEtalePrecoverage_isStableUnderComposition.{u}
  rw [etalePrecoverage_eq_comap B]
  infer_instance

/-- The chosen étale precoverage of a big fppf site is stable under base change. -/
instance etalePrecoverage_chosen_isStableUnderBaseChange (B : BigFppfSite.{u}) :
    (etalePrecoverage B).IsStableUnderBaseChange := by
  rw [etalePrecoverage_eq_comap B]
  infer_instance

/-- **The image of a chosen étale covering family is an étale covering family of schemes.** This
is the hypothesis `AlgebraicGeometry.Stack.isContinuous_ι_etaleTopology` and its cocontinuous
sibling take, for the chosen étale precoverage. -/
theorem map_mem_schemeEtalePrecoverage_of_mem_etalePrecoverage (B : BigFppfSite.{u})
    ⦃V : B.Schemes⦄ (R : Presieve V) (hR : R ∈ etalePrecoverage B V) :
    R.map B.inclusion ∈ Scheme.etalePrecoverage (B.inclusion.obj V) := by
  rw [etalePrecoverage_eq_comap B, Precoverage.mem_comap_iff] at hR
  exact hR

/-- **Every member of a chosen étale covering family is étale.** -/
theorem etale_of_mem_etalePrecoverage (B : BigFppfSite.{u}) ⦃V : B.Schemes⦄ (R : Presieve V)
    (hR : R ∈ etalePrecoverage B V) ⦃W : B.Schemes⦄ (g : W ⟶ V) (hg : R g) :
    Etale (B.inclusion.map g) :=
  (map_mem_schemeEtalePrecoverage_of_mem_etalePrecoverage B R hR).2 (Presieve.map_map hg)

end AlgebraicGeometry

end

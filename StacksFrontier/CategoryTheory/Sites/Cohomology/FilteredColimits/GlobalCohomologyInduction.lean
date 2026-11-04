module

public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Filtered colimits and global cohomology (Stacks 0GN3): the induction

Stacks 0GN3 says that if a site carries a collection `S` of quasi-compact sheaves of sets which
covers the final sheaf and is stable in the four senses (1)-(4) of the source, then global
cohomology commutes with filtered colimits of abelian sheaves in every degree.

Its proof is an induction on the degree whose inductive step is the long exact cohomology
sequence of a functorial injective embedding of a *system*.  That induction is carried out for
an arbitrary cohomological δ-functor in
`CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero`; this file plugs in the δ-functor
of the right derived functors of global sections, so that Stacks 0GN3 is reduced to exactly two
inputs:

* the degree-zero statement, that global sections commute with filtered colimits of abelian
  sheaves — this is Stacks 0GMR part (4), available for sheaves of *sets* as
  `CategoryTheory.Sheaf.injective_and_bijective_colimit_post_globalSections`, plus the passage
  from sets to abelian groups; and
* the vanishing `Hⁿ⁺¹(C, colimᵢ Iᵢ) = 0` for a filtered system of injective abelian sheaves,
  which the source proves by the spectral sequence of the covering `K ⟶ *` together with the
  induction hypothesis applied to the localized sites `C/Kᵖ⁺¹`.

Both inputs are now available, and the tag `0GN3` itself is carried by
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections`. What
remains here is the
reduction, which is still worth having on its own: it is the whole of Stacks 0GN3 modulo the two
inputs, named precisely in `isIso_colimit_post_rightDerived_globalSections_of_degreeZero_of_isZero`
and in the implementation notes below.

## Main results

* `isIso_colimit_post_rightDerived_globalSections_of_degreeZero_of_isZero`:
  Stacks 0GN3 modulo its two external inputs.
* `Stacks.Cohomology.GlobalCohomologyColimits.isQuasiCompact_prod_self`: the easy half of the base
  case, namely that
  hypotheses (3) and (5) of the source make `K ⨯ K` quasi-compact for every `K ∈ S`.  This is
  the second conjunct of the hypothesis of Stacks 0GMR part (4).

## Implementation notes

The base case is complete.  Both halves are in the
`Stacks.Cohomology.GlobalCohomologyColimits` namespace: the other half of
the base case is `exists_hom_isLocallySurjective_terminal_from`, and the passage of the
degree-zero statement from sheaves of sets to abelian sheaves is
`preservesColimitsOfShape_globalSections`, over
`preservesColimitsOfShape_globalSections_type_of_coveringSet`.  The comparison itself is
`isIso_colimit_post_rightDerived_globalSections_of_isZero`.

Nothing is missing.  The vanishing input, in exact shape

```
theorem isZero_rightDerived_globalSections_succ_colimit_of_injective
    (E : I ⥤ Sheaf J Ab.{u}) (hE : ∀ i, Injective (E.obj i)) (n : ℕ) :
    IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit E))
```

under the hypotheses (1)-(5) of the source, is
`Stacks.Cohomology.ColimitsOfCohomology.isZero_rightDerived_globalSections_colimit_of_isIso`,
and the tag itself is registered on
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections`.

The source obtains the vanishing input from the Čech-to-cohomology spectral sequence
`E₁^{p,q} = Hᑫ(Kᵖ⁺¹, I)` of Stacks 079Z.  That is not the route taken here, and 079Z is not used: the dévissage of the `ExtTowerVanishing`
development along the opcycles tower of the free abelian Čech
resolution (Stacks 01GB, 01GC) replaces the spectral sequence.  What the proof does use is the
identification `Hᑫ(Kᵖ⁺¹, F) = Hᑫ(C/Kᵖ⁺¹, j⁻¹F)` of Stacks 07A0 — proved as
`Stacks.Cohomology.SheafOfSets.cohomologyOnSheafIso`, whose proof supplies the preservation of
injectivity by `j⁻¹` of Stacks 03F3 as an instance — together with a recursive application of
0GN3 itself to the localized sites, which is why the induction there is strong in the degree and
generalised over the site.

The universes are collapsed: the site, the coefficient category and the index category all use
one `u`, which is forced by Mathlib's `IsGrothendieckAbelian` instance for `Sheaf J Ab`.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 0GMP](https://stacks.math.columbia.edu/tag/0GMP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.GlobalCohomologyColimits

attribute [local instance] ColimitsOfCohomology.enoughInjectives_sheaf_ab
  ColimitsOfCohomology.additive_globalSections_ab

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)





/-- **The second conjunct of the hypothesis of Stacks 0GMR (4), from hypotheses (3) and (5) of
Stacks 0GN3.**  If every member of `S` is quasi-compact and every pair of members of `S` is
covered by a member of `S` mapping onto their product, then `K ⨯ K` is quasi-compact for every
`K ∈ S`.

This is Stacks 0GMP (2): quasi-compactness passes along a surjection. -/
theorem isQuasiCompact_prod_self (S : Set (Sheaf J (Type u)))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    (K : Sheaf J (Type u)) (hK : K ∈ S) : Sheaf.IsQuasiCompact (K ⨯ K) := by
  obtain ⟨K'', hK''S, f, hf⟩ := h_product K hK K hK
  exact Sheaf.isQuasiCompact_of_isLocallySurjective f hf (h_quasiCompact K'' hK''S)

variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- **Stacks 0GN3, modulo its two external inputs.**  Let `C` be a site and `I` a filtered index
category.  Assume

* `h0`: the canonical map `colimᵢ Γ(C, Gᵢ) ⟶ Γ(C, colimᵢ Gᵢ)` is an isomorphism for every
  system `G : I ⥤ Ab(C)` — this is Stacks 0GMR (4) together with the passage from sheaves of
  sets to abelian sheaves; and
* `hvan`: `Hⁿ⁺¹(C, colimᵢ Eᵢ) = 0` for every system `E` of injective abelian sheaves — this is
  what the source proves from the spectral sequence of a covering of the final sheaf by a
  member of `S`.

Then `colimᵢ Hᵖ(C, Fᵢ) ⟶ Hᵖ(C, colimᵢ Fᵢ)` is an isomorphism in every degree `p`.

The proof is the induction of the source on `p`, performed for an arbitrary cohomological
δ-functor in `CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero`; the long exact
sequence it consumes is `Stacks.Cohomology.CechDelta.rightDerivedDeltaFunctor` of the global
sections functor, whose degree-`n` component is `(Sheaf.Γ J Ab).rightDerived n` on the nose.
The third input of the engine, that `Hⁿ⁺¹(C, -)` kills injectives, is automatic because it is a
right derived functor; and the degree-zero hypothesis is phrased on `Γ` itself rather than on
`R⁰Γ` because `Γ` is left exact, so `Functor.rightDerivedZeroIsoSelf` identifies the two. -/
theorem isIso_colimit_post_rightDerived_globalSections_of_degreeZero_of_isZero
    (h0 : ∀ G : I ⥤ Sheaf J Ab.{u}, IsIso (colimit.post G (Sheaf.Γ J Ab.{u})))
    (hvan : ∀ E : I ⥤ Sheaf J Ab.{u}, (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit E)))
    (p : ℕ) (F : I ⥤ Sheaf J Ab.{u}) :
    IsIso (colimit.post F ((Sheaf.Γ J Ab.{u}).rightDerived p)) :=
  DeltaFunctor.isIso_colimit_post_of_isIso_zero
    (Stacks.Cohomology.CechDelta.rightDerivedDeltaFunctor (Sheaf.Γ J Ab.{u}))
    (fun G =>
      have := h0 G
      Limits.isIso_colimit_post_of_natIso G (Sheaf.Γ J Ab.{u}).rightDerivedZeroIsoSelf)
    (fun Y hY n => have := hY;
      (Sheaf.Γ J Ab.{u}).isZero_rightDerived_obj_injective_succ n Y)
    hvan p F

end Stacks.Cohomology.GlobalCohomologyColimits

end

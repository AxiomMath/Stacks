module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance

/-!
# The types of modules of Stacks 03DE and 03DL are invariant under isomorphism

Each of the fifteen conditions on a sheaf of modules that Stacks 03DE, 03DL and 03ER define
depends only on the isomorphism class of the module.  For four of them the library already has
the statement — `Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso`,
`.isFinitePresentation_of_iso` and `.isLocallyGeneratedByOnSite_of_iso` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence`,
`SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison` — and coherence is
`Stacks.SheafOfModules.isCoherentOnSite_of_iso`.  Local freeness and local generation by
sections (03DL (1), (3)) are `Stacks.SheafOfModules.Intrinsic.isLocallyFreeOnSite_of_iso` and
`.isLocallyGeneratedBySectionsOnSite_of_iso` in
`StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance`, which this file imports.
**This file supplies the four that were missing**, so that the whole list is available here.

## Main results

* `Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso` and
  `.isGeneratedByGlobalSectionsOfCard_of_iso`: Stacks 03DE (3) and (4).  The generating family
  is carried across by `SheafOfModules.GeneratingSections.equivOfIso`, which does not change
  the index type, so the cardinality clause is preserved.
* `Stacks.SheafOfModules.Intrinsic.isPresentedByGlobalSections_of_iso` and
  `.isFinitelyPresentedByGlobalSections_of_iso`: Stacks 03DE (6) and (7).  The two coproducts
  of copies of the structure sheaf are untouched; only the cokernel projection is composed with
  the isomorphism, and the cokernel cofork is moved across by
  `CategoryTheory.Limits.Cofork.ext`.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.Intrinsic

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Having a global presentation is invariant under isomorphism of sheaves of modules**,
Stacks 03DE (6).  The two coproducts of copies of the structure sheaf and the map between them
are unchanged; the cokernel projection is composed with the isomorphism, and the cokernel
cofork is transported by `CategoryTheory.Limits.Cofork.ext`.  Both index types are
preserved. -/
theorem isPresentedByGlobalSections_of_iso {F G : _root_.SheafOfModules.{w} R} (e : F ≅ G)
    (h : F.IsPresentedByGlobalSections) : G.IsPresentedByGlobalSections := by
  obtain ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, ⟨hc⟩⟩ := h
  exact ⟨I, K, P, Q, ι, κ, hP, hQ, a, b ≫ e.hom,
    by rw [← Category.assoc, hab, zero_comp], ⟨hc.ofIsoColimit (Cofork.ext e rfl)⟩⟩

/-- **Having a finite global presentation is invariant under isomorphism of sheaves of
modules**, Stacks 03DE (7).  This is
`Stacks.SheafOfModules.Intrinsic.isPresentedByGlobalSections_of_iso` with the two index types
kept at `Fin n` and `Fin k`, so no finiteness is lost. -/
theorem isFinitelyPresentedByGlobalSections_of_iso {F G : _root_.SheafOfModules.{w} R}
    (e : F ≅ G) (h : F.IsFinitelyPresentedByGlobalSections) :
    G.IsFinitelyPresentedByGlobalSections := by
  obtain ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, ⟨hc⟩⟩ := h
  exact ⟨n, k, P, Q, ι, κ, hP, hQ, a, b ≫ e.hom,
    by rw [← Category.assoc, hab, zero_comp], ⟨hc.ofIsoColimit (Cofork.ext e rfl)⟩⟩

section Generation

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Generation by global sections is invariant under isomorphism of sheaves of modules**,
Stacks 03DE (3).  The generating family is carried across by
`SheafOfModules.GeneratingSections.equivOfIso`. -/
theorem isGeneratedByGlobalSections_of_iso {F G : _root_.SheafOfModules.{w} R} (e : F ≅ G)
    (h : F.IsGeneratedByGlobalSections) : G.IsGeneratedByGlobalSections :=
  ⟨_root_.SheafOfModules.GeneratingSections.equivOfIso e h.some⟩

/-- **Generation by `r` global sections is invariant under isomorphism of sheaves of modules**,
Stacks 03DE (4).  `SheafOfModules.GeneratingSections.equivOfIso` leaves the index type of the
generating family unchanged, so the same `r` works. -/
theorem isGeneratedByGlobalSectionsOfCard_of_iso {F G : _root_.SheafOfModules.{w} R} (e : F ≅ G)
    (r : ℕ) (h : F.IsGeneratedByGlobalSectionsOfCard r) :
    G.IsGeneratedByGlobalSectionsOfCard r :=
  ⟨_root_.SheafOfModules.GeneratingSections.equivOfIso e h.choose, h.choose_spec⟩

end Generation

end Stacks.SheafOfModules.Intrinsic

end

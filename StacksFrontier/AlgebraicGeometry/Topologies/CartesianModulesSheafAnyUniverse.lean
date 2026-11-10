module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# The cartesian sheaf criterion at a value universe independent of the site

`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements` says that a cartesian
presheaf of modules is a sheaf for a topology whose covering sieves are refined by finite flat
coverings.  Its value universe is `max m r v w`: the assembly of the per-covering sheaf axiom
into the sheaf condition goes through `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp`, which
asks the value category to have limits of the size of the site, and so forces the sections to
live at least at the universe of the site's objects and morphisms.

This file repeats that assembly with `Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget` in
place of Mathlib's criterion.  That lemma amalgamates element by element and needs no universe
relation between the site and the sections, so the resulting statement holds at the value
universe `max m r` of the per-covering axiom
`Stacks.PresheafOfModules.isSheafFor_of_cartesian_of_flat_cover` — free of the site's universes.

That freedom is the point.  A presheaf of modules whose sections are the base changes
`C ↦ C ⊗[A] M` of an `A`-module lives at the value universe of `M`, which is not related to the
universe of the category of algebras it is defined on; the criterion of the previous paragraph
is therefore unavailable for it, and this one is not.

## Main results

* `Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'` — **a cartesian presheaf
  of modules is a sheaf for a topology all of whose covering sieves are refined by finite flat
  covering families, at a value universe independent of the site.**

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v r m w i

/-- Flatness of morphisms of schemes, named as a `MorphismProperty` so that the stability
instances of its precoverage can be located by instance search; presented with `@Flat`
eta-expanded, the search does not match. -/
private abbrev AlgebraicGeometry.flatPropertyOfSchemes : MorphismProperty Scheme.{u} :=
  @AlgebraicGeometry.Flat

namespace Stacks.PresheafOfModules

/-- **A cartesian presheaf of modules is a sheaf for a topology all of whose covering sieves are
refined by finite flat covering families**, at a value universe bearing no relation to the
universes of the site.

This is `Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements` with the final
assembly carried out by `Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget` rather than by
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp`, which is what removes the site's universes
from the value universe. -/
public theorem isSheaf_of_cartesian_of_flat_refinements'
    {C : Type v} [Category.{w} C] [HasPullbacks C]
    (L : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan L]
    (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (hff : ∀ {U : C} (E : PreZeroHypercover.{i} U), Finite E.I₀ →
      (E.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj U) →
      (RingHom.pi (fun k => (R.map (E.f k).op).hom)).FaithfullyFlat)
    (hpo : ∀ {X Y Z P : C} {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z},
      IsPullback fst snd a b →
      IsPushout (R.map a.op) (R.map b.op) (R.map fst.op) (R.map snd.op))
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange.{v, w, r, m} M f))
    (J : GrothendieckTopology C)
    (hJ : ∀ {U : C} (S : Sieve U), S ∈ J U →
      ∃ E : PreZeroHypercover.{i} U, Finite E.I₀ ∧
        (E.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj U) ∧ E.sieve₀ ≤ S) :
    Presheaf.IsSheaf J M.presheaf := by
  apply Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget
  intro U S hS
  obtain ⟨E, hfin, hE, hES⟩ := hJ S hS
  let _ := hfin
  apply Presieve.isSheafFor_subsieve _ hES
  intro V f
  let K := (Scheme.precoverage @Flat).comap L
  let _ : K.IsStableUnderBaseChange :=
    inferInstanceAs (Precoverage.IsStableUnderBaseChange
      ((Scheme.precoverage AlgebraicGeometry.flatPropertyOfSchemes.{u}).comap L))
  have he : E.presieve₀ ∈ K U := by
    change E.presieve₀.map L ∈ (Scheme.precoverage @Flat) (L.obj U)
    simpa only [PreZeroHypercover.presieve₀_map] using hE
  have he' : (E.pullback₂ f).presieve₀ ∈ K V :=
    K.mem_coverings_of_isPullback _ he _ _ _
      (fun i => (IsPullback.of_hasPullback (E.f i) f).flip)
  let _ : Finite (E.pullback₂ f).I₀ := hfin
  have h := isSheafFor_of_cartesian_of_flat_cover L R hff hpo M hM (E.pullback₂ f)
    (by simpa only [K, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map] using he')
  rwa [PreZeroHypercover.presieve₀_pullback₁, Presieve.isSheafFor_iff_generate,
    Sieve.pullbackArrows_comm] at h

end Stacks.PresheafOfModules

end

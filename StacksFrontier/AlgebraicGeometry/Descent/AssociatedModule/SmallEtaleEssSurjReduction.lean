module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful

/-!
# Essential surjectivity of `𝓕 ↦ 𝓕^a` on the small étale site, over its globalization step

This file reduces essential surjectivity of `𝓕 ↦ 𝓕^a` on the small étale site of a scheme `S`,
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`, to the *globalization*
step of the proof of Stacks 03DX (2) at `τ = étale`: a module on `S_étale` which has a global
presentation on each member of **some** covering family of the final object is an `𝓕^a`. The two
are equivalent, `AlgebraicGeometry.SmallEtale.essImageAssociatedModuleGlue_iff`.

Essential surjectivity itself is proved with no hypothesis, from the counit of the
associated-module adjunction, as
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`; so
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue` holds as well.

The small étale site is essentially small, so a global presentation on it is a
`SheafOfModules.Presentation`, and a module with a global presentation on all of `S_étale` is an
`𝓕^a` with no hypothesis. Every object of the small étale site is étale over `S`, so a covering
family of the final object is an étale, hence fpqc, covering family of `S` itself.

## Main definitions

* `AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue`: **the globalization step of
  Stacks 03DX (2) at `τ = étale`** as a hypothesis.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_of_presentation`,
  `AlgebraicGeometry.SmallEtale.essImage_associatedModule_of_presentation` and
  `AlgebraicGeometry.SmallEtale.essImage_associatedModule_of_hasGlobalPresentation`: **a globally
  presented module on `S_étale` is the associated module of a quasi-coherent `𝒪_S`-module**, with
  no hypothesis.
* `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule_of_glue`: essential
  surjectivity over the globalization step.
* `AlgebraicGeometry.SmallEtale.essImageAssociatedModuleGlue_iff`: the globalization step is
  *equivalent* to essential surjectivity, so the reduction neither loses nor smuggles in content.
* `AlgebraicGeometry.SmallEtale.hasSheafify_smallEtale`: abelian presheaves on `S_étale` have a
  left exact sheafification.

## Implementation notes

Nothing here carries a `stacks` attribute: the statements about the clause of Stacks 03DX are
conditional on the globalization step, and a hypothesis is part of a citation.

The index type of the covering family lives in `Type (u + 1)`, the universe of the objects of the
small étale site, because that is what Stacks 03DN
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`) produces.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A globally presented module on `S_étale` is an associated module -/

/-- Abelian presheaves on the small étale site of `S` have a left exact sheafification, the site
being essentially small. -/
public instance hasSheafify_smallEtale : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, local step, at a
`SheafOfModules.Presentation`.**  A module on `S_étale` carrying a presentation in Mathlib's sense
is the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`. -/
public theorem exists_isQuasicoherent_iso_associatedModule_of_presentation
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (P : G.Presentation) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((associatedModule B S hS).obj G' ≅ G) :=
  exists_isQuasicoherent_iso_associatedModule_of_cokernelFree B S hS
    ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)
    (by simp) P.isColimit

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, local step at a presentation**, in
the form of a membership in the essential image of `𝓕 ↦ 𝓕^a`. -/
public theorem essImage_associatedModule_of_presentation
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (P : G.Presentation) :
    (associatedModuleQcoh B S hS).essImage G := by
  obtain ⟨G', hG', h⟩ := exists_isQuasicoherent_iso_associatedModule_of_presentation B S hS P
  exact ⟨⟨G', hG'⟩, h⟩

/-- **A module on `S_étale` with a global presentation is an associated module**, with no
hypothesis. -/
public theorem essImage_associatedModule_of_hasGlobalPresentation
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (h : G.HasGlobalPresentation) :
    (associatedModuleQcoh B S hS).essImage G :=
  essImage_associatedModule_of_presentation B S hS
    (Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation h).some

/-! ### The globalization step -/

/-- **The globalization step of Stacks 03DX (2) at `τ = étale`**, as a hypothesis: a module on
`S_étale` whose restriction to each member of some covering family of the final object has a
global presentation is the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`. -/
public abbrev EssImageAssociatedModuleGlue : Prop :=
  ∀ (G : SheafOfModules.{u} (structureSheaf B S hS)) (I : Type (u + 1))
      (X : I → SmallEtale B S hS), (topology B S hS).CoversTop X →
      (∀ i, (G.over (X i)).HasGlobalPresentation) →
    (associatedModuleQcoh B S hS).essImage G

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, over the globalization step.**
Every quasi-coherent `𝒪`-module on `S_étale` is isomorphic to `𝓕^a` for a quasi-coherent
`𝒪_S`-module `𝓕`. -/
public theorem quasicoherentIsEssImageAssociatedModule_of_glue
    (h : EssImageAssociatedModuleGlue B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS := by
  intro G hG
  obtain ⟨I, X, hX, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation G).1 hG
  exact h G I X hX hP

/-- The globalization step at `τ = étale` follows from essential surjectivity of `𝓕 ↦ 𝓕^a`. -/
public theorem essImageAssociatedModuleGlue_of_quasicoherentIsEssImage
    (h : QuasicoherentIsEssImageAssociatedModule B S hS) :
    EssImageAssociatedModuleGlue B S hS := fun G I X hX hP =>
  h G ((Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation G).2
    ⟨I, X, hX, hP⟩)

/-- **The globalization step and essential surjectivity at `τ = étale` are equivalent.** -/
public theorem essImageAssociatedModuleGlue_iff :
    EssImageAssociatedModuleGlue B S hS ↔ QuasicoherentIsEssImageAssociatedModule B S hS :=
  ⟨quasicoherentIsEssImageAssociatedModule_of_glue B S hS,
    essImageAssociatedModuleGlue_of_quasicoherentIsEssImage B S hS⟩

/-! ### A covering family of the final object is an fpqc covering family of `S` -/

/-- A family covering the final object of the small étale site of `S` is an étale covering family
of `S` itself. -/
public theorem presieve₀_mem_etalePrecoverage_of_coversTop {I : Type w}
    (X : I → SmallEtale B S hS) (hX : (topology B S hS).CoversTop X) :
    Presieve.ofArrows (fun i => (toScheme B S hS).obj (X i))
        (fun i => (toScheme B S hS).map ((finalIsTerminal B S hS).from (X i))) ∈
      Scheme.etalePrecoverage ((toScheme B S hS).obj (final B S hS)) := by
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2
    ⟨fun x => ?_, fun i => etale_toScheme_map B S hS _⟩
  obtain ⟨E, hE, hle⟩ := exists_isCovering_sieve₀_le B S hS (hX (final B S hS))
  obtain ⟨k, hk⟩ := jointlySurjective_of_isCovering B S hS hE x
  obtain ⟨i, ⟨b⟩⟩ := hle _ ⟨_, 𝟙 _, E.f k, Presieve.ofArrows.mk k, Category.id_comp _⟩
  have key : (toScheme B S hS).map (E.f k) =
      (toScheme B S hS).map b ≫
        (toScheme B S hS).map ((finalIsTerminal B S hS).from (X i)) := by
    rw [← Functor.map_comp]
    exact congrArg _ ((finalIsTerminal B S hS).hom_ext _ _)
  change x ∈ Set.range ⇑((toScheme B S hS).map (E.f k)) at hk
  rw [key] at hk
  exact ⟨i, Set.range_comp_subset_range _ _ hk⟩

/-- The scheme of the final object of the small étale site of `S` is `S`. -/
public theorem toScheme_obj_final : (toScheme B S hS).obj (final B S hS) = S := rfl

/-- A family covering the final object of the small étale site of `S` is an fpqc covering family
of `S`. -/
public theorem presieve₀_mem_fpqcPrecoverage_of_coversTop {I : Type w}
    (X : I → SmallEtale B S hS) (hX : (topology B S hS).CoversTop X) :
    Presieve.ofArrows (fun i => (toScheme B S hS).obj (X i))
        (fun i => (toScheme B S hS).map ((finalIsTerminal B S hS).from (X i))) ∈
      Scheme.fpqcPrecoverage ((toScheme B S hS).obj (final B S hS)) :=
  Scheme.etalePrecoverage_le_fpqcPrecoverage _
    (presieve₀_mem_etalePrecoverage_of_coversTop B S hS X hX)

end AlgebraicGeometry.SmallEtale

end

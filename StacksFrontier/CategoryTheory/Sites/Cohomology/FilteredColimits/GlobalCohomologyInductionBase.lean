module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyInduction

/-!
# Filtered colimits and global cohomology (Stacks 0GN3): the base case

This file supplies the degree-zero input of Stacks 0GN3, that is, the hypothesis `h0` of
`isIso_colimit_post_rightDerived_globalSections_of_degreeZero_of_isZero`:
if a site carries a collection `S` of quasi-compact sheaves of sets which covers the final sheaf
and is stable under lifting surjections and under products, then global sections of *abelian*
sheaves commutes with filtered colimits.

The mathematics for sheaves of **sets** is Stacks 0GMR, available as
`CategoryTheory.Sheaf.injective_and_bijective_colimit_post_globalSections`; part (4) of it asks
for a set `S` of sheaves such that

* (a) every sheaf `G` surjecting onto the final sheaf receives a map from some `K ∈ S` which
  itself surjects onto the final sheaf; and
* (b) `K ⨯ K` is quasi-compact for every `K ∈ S`.

Hypothesis (b) is `Stacks.Cohomology.GlobalCohomologyColimits.isQuasiCompact_prod_self`, already
  available.  Hypothesis (a) is
`exists_hom_isLocallySurjective_terminal_from` below, which is the source's own argument: base
change `G ⟶ *` along `K ⟶ *` and apply the lifting hypothesis to `G ⨯ K ⟶ K`.  The passage from
sheaves of sets to abelian sheaves is `preservesColimitsOfShape_globalSections`.

What is still missing for the tag `0GN3` itself is only the *vanishing* input, the hypothesis
`hvan` of the conditional theorem: `Hⁿ⁺¹(C, colimᵢ Iᵢ) = 0` for a filtered system of injective
abelian sheaves.  The source proves it with the spectral sequence `E₁^{p,q} = Hᑫ(Kᵖ⁺¹, I)` of
Stacks 079Z, the identification `Hᑫ(Kᵖ⁺¹, F) = Hᑫ(C/Kᵖ⁺¹, j⁻¹F)` of Stacks 07A0, the preservation
of injectivity by `j⁻¹` of Stacks 03F3, and a recursive application of 0GN3 itself to the
localized sites; none of those four is available, so the tag `0GN3` is deliberately *not* placed
and `isIso_colimit_post_rightDerived_globalSections_of_isZero` below, which carries `hvan` as a
hypothesis, is the strongest statement this file can make.

## Main results

* `Stacks.Cohomology.GlobalCohomologyColimits.exists_hom_isLocallySurjective_terminal_from`:
  hypothesis (4)(a) of Stacks 0GMR
  from the hypotheses (1) and (2) of Stacks 0GN3.
* `preservesColimitsOfShape_globalSections_type_of_coveringSet`: Stacks 0GMR (4)
  as a colimit-preservation statement for global sections of sheaves of sets.
* `Stacks.Cohomology.GlobalCohomologyColimits.preservesColimitsOfShape_globalSections`: the passage
  from sheaves of sets to
  abelian sheaves.
* `isIso_colimit_post_rightDerived_globalSections_of_isZero`: Stacks 0GN3 under the
  hypotheses of the source together with the vanishing input, which is the only thing left
  unproved.

## Implementation notes

The base change of a surjection is
`CategoryTheory.Sheaf.isLocallySurjective_prod_snd`, the generalization to `prod.snd : G ⨯ K ⟶ K`
of a step of the proof of Stacks 0GMR (4).

The sets-to-abelian-groups transfer is the pattern of
`Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_of_isCompact`: the forgetful
functor `Ab ⥤ Set` reflects isomorphisms and preserves filtered colimits, so it suffices that
`Γ` followed by it preserve them, and that composite is `sheafCompose J (forget Ab)` followed by
`Γ` on sheaves of sets.  Unlike for the sections functor on an object of the site, the identity of
those two composites is not a definitional one: `Sheaf.Γ` is defined as an abstract right adjoint
of the constant sheaf functor, so the comparison is assembled from `Sheaf.ΓNatIsoLim`, which
identifies global sections with the limit of the underlying presheaf, together with the fact that
`forget Ab` preserves limits of shape `Cᵒᵖ` (`CategoryTheory.Limits.preservesLimitNatIso`).

The hypothesis `h_equalizer` of the source, (4) of Stacks 0GN3, is not needed here: it enters only
through the spectral sequence used for the vanishing input, which is a hypothesis below.

The universes are those of the statement: the site, the coefficient category and the index
category all use one `u`, which is forced by Mathlib's `IsGrothendieckAbelian` instance for
`Sheaf J Ab`.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 0GMP](https://stacks.math.columbia.edu/tag/0GMP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.GlobalCohomologyColimits

attribute [local instance] ColimitsOfCohomology.enoughInjectives_sheaf_ab
  ColimitsOfCohomology.additive_globalSections_ab

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Hypothesis (4)(a) of Stacks 0GMR, from hypotheses (1) and (2) of Stacks 0GN3.**  Suppose
`S` contains a sheaf surjecting onto the final sheaf, and that every surjection onto a member of
`S` can be covered by a member of `S`.  Then every sheaf `G` surjecting onto the final sheaf
receives a morphism from a member of `S` which itself surjects onto the final sheaf.

This is the argument of the source: pick `K ∈ S` with `K ⟶ *` surjective and base change `G ⟶ *`
along it, so that `prod.snd : G ⨯ K ⟶ K` is surjective
(`CategoryTheory.Sheaf.isLocallySurjective_prod_snd`); the lifting hypothesis applied to it
produces `K' ∈ S` and `g : K' ⟶ G ⨯ K` with `g ≫ prod.snd` surjective, and then `g ≫ prod.fst`
is the required morphism `K' ⟶ G` while `K' ⟶ *`, being `g ≫ prod.snd` followed by `K ⟶ *`, is
surjective. -/
theorem exists_hom_isLocallySurjective_terminal_from (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (G : Sheaf J (Type u)) (hG : Sheaf.IsLocallySurjective (terminal.from G)) :
    ∃ K ∈ S, Nonempty (K ⟶ G) ∧ Sheaf.IsLocallySurjective (terminal.from K) := by
  obtain ⟨K, hKS, hK⟩ := h_terminal
  obtain ⟨K', hK'S, g, hg⟩ :=
    h_lift (Limits.prod.snd : G ⨯ K ⟶ K) hKS (Sheaf.isLocallySurjective_prod_snd hG)
  refine ⟨K', hK'S, ⟨g ≫ Limits.prod.fst⟩, ?_⟩
  have := hg
  have := hK
  have h : Sheaf.IsLocallySurjective ((g ≫ Limits.prod.snd) ≫ terminal.from K) := inferInstance
  rwa [terminal.hom_ext ((g ≫ Limits.prod.snd) ≫ terminal.from K) (terminal.from K')] at h

variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- **Stacks 0GMR (4), as a colimit-preservation statement.**  If the site admits a set `S` of
sheaves satisfying (4)(a) and (4)(b) of Stacks 0GMR, then the global sections functor on sheaves
of sets preserves filtered colimits.

Part (4) of Stacks 0GMR gives bijectivity of the canonical map
`colimᵢ Γ(C, Fᵢ) ⟶ Γ(C, colimᵢ Fᵢ)`; for sheaves of sets bijectivity is being an isomorphism, and
a functor preserves a colimit as soon as that comparison map is an isomorphism. -/
theorem preservesColimitsOfShape_globalSections_type_of_coveringSet (S : Set (Sheaf J (Type u)))
    (hSa : ∀ G : Sheaf J (Type u), Sheaf.IsLocallySurjective (terminal.from G) →
      ∃ K ∈ S, Nonempty (K ⟶ G) ∧ Sheaf.IsLocallySurjective (terminal.from K))
    (hSb : ∀ K ∈ S, Sheaf.IsQuasiCompact (K ⨯ K)) :
    PreservesColimitsOfShape I (Sheaf.Γ J (Type u)) := by
  constructor
  intro F
  have hbij := (Sheaf.injective_and_bijective_colimit_post_globalSections J F).2.2.2 ⟨S, hSa, hSb⟩
  have : IsIso (colimit.post F (Sheaf.Γ J (Type u))) := (isIso_iff_bijective _).2 hbij
  exact preservesColimit_of_isIso_post _ _

/-- **From sheaves of sets to abelian sheaves.**  If global sections of sheaves of sets preserves
`I`-colimits, then so does global sections of abelian sheaves.

The forgetful functor `Ab ⥤ Set` reflects isomorphisms and preserves filtered colimits, so it
suffices that `Γ J Ab` followed by it preserve `I`-colimits; and that composite is
`sheafCompose J (forget Ab)` followed by `Γ J (Type u)`, which preserves them because both
factors do.  The comparison of the two composites is `Sheaf.ΓNatIsoLim` on both sides together
with the preservation of `Cᵒᵖ`-shaped limits by `forget Ab`. -/
theorem preservesColimitsOfShape_globalSections
    (hT : PreservesColimitsOfShape I (Sheaf.Γ J (Type u))) :
    PreservesColimitsOfShape I (Sheaf.Γ J Ab.{u}) := by
  have := hT
  have hS : PreservesColimitsOfShape I (sheafCompose J (forget Ab.{u})) :=
    Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafCompose J (forget Ab.{u})
  have eW : sheafCompose J (forget Ab.{u}) ⋙ sheafToPresheaf J (Type u) ≅
      sheafToPresheaf J Ab.{u} ⋙
        (Functor.whiskeringRight Cᵒᵖ Ab.{u} (Type u)).obj (forget Ab.{u}) := Iso.refl _
  have e1 : sheafCompose J (forget Ab.{u}) ⋙ Sheaf.Γ J (Type u) ≅
      sheafToPresheaf J Ab.{u} ⋙
        ((Functor.whiskeringRight Cᵒᵖ Ab.{u} (Type u)).obj (forget Ab.{u}) ⋙ lim) :=
    Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoLim J (Type u)) ≪≫
      (Functor.associator (sheafCompose J (forget Ab.{u})) (sheafToPresheaf J (Type u)) lim).symm
        ≪≫ Functor.isoWhiskerRight eW lim ≪≫ Functor.associator _ _ _
  have e2 : sheafToPresheaf J Ab.{u} ⋙
        ((Functor.whiskeringRight Cᵒᵖ Ab.{u} (Type u)).obj (forget Ab.{u}) ⋙ lim) ≅
      Sheaf.Γ J Ab.{u} ⋙ forget Ab.{u} :=
    Functor.isoWhiskerLeft _ (preservesLimitNatIso (forget Ab.{u})).symm ≪≫
      (Functor.associator (sheafToPresheaf J Ab.{u}) lim (forget Ab.{u})).symm ≪≫
      Functor.isoWhiskerRight (Sheaf.ΓNatIsoLim J Ab.{u}).symm (forget Ab.{u})
  have hcomp : PreservesColimitsOfShape I (Sheaf.Γ J Ab.{u} ⋙ forget Ab.{u}) :=
    preservesColimitsOfShape_of_natIso (e1 ≪≫ e2)
  constructor
  intro D
  have : ReflectsColimit (D ⋙ Sheaf.Γ J Ab.{u}) (forget Ab.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact preservesColimit_of_reflects_of_preserves _ (forget Ab.{u})



/-- Global sections of abelian sheaves is an additive functor: it is a right adjoint, so it
preserves binary products. -/
local instance globalSectionsAb_additive : (Sheaf.Γ J (Ab.{u})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Stacks 0GN3 modulo its vanishing input.**  Let `C` be a site carrying a set `S` of
quasi-compact sheaves of sets which covers the final sheaf and is stable under lifting
surjections and under products, in the senses (1), (2), (3) and (5) of the source, and let `I` be
a filtered index category.  Assume moreover

* `hvan`: `Hⁿ⁺¹(C, colimᵢ Eᵢ) = 0` for every filtered system `E` of injective abelian sheaves.

Then `colimᵢ Hᵖ(C, Fᵢ) ⟶ Hᵖ(C, colimᵢ Fᵢ)` is an isomorphism in every degree `p`.

This is `isIso_colimit_post_rightDerived_globalSections_of_degreeZero_of_isZero` with its
degree-zero hypothesis discharged: hypothesis (4)(a) of Stacks 0GMR is
`exists_hom_isLocallySurjective_terminal_from`, hypothesis (4)(b) is
`isQuasiCompact_prod_self`, and the transfer from sheaves of sets to abelian sheaves is
`preservesColimitsOfShape_globalSections`.

Hypothesis (4) of the source, the stability of `S` under equalizers, is not needed: it enters the
source's proof only through the spectral sequence that produces `hvan`. -/
theorem isIso_colimit_post_rightDerived_globalSections_of_isZero (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    (hvan : ∀ E : I ⥤ Sheaf J Ab.{u}, (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit E)))
    (p : ℕ) (F : I ⥤ Sheaf J Ab.{u}) :
    IsIso (colimit.post F ((Sheaf.Γ J Ab.{u}).rightDerived p)) := by
  have hTy : PreservesColimitsOfShape I (Sheaf.Γ J (Type u)) :=
    preservesColimitsOfShape_globalSections_type_of_coveringSet J S
      (fun G hG => exists_hom_isLocallySurjective_terminal_from J S h_terminal h_lift G hG)
      (fun K hK => isQuasiCompact_prod_self J S h_product h_quasiCompact K hK)
  have hAb : PreservesColimitsOfShape I (Sheaf.Γ J Ab.{u}) :=
    preservesColimitsOfShape_globalSections J hTy
  exact isIso_colimit_post_rightDerived_globalSections_of_degreeZero_of_isZero J
    (fun _ => have := hAb; inferInstance) hvan p F

end Stacks.Cohomology.GlobalCohomologyColimits

end

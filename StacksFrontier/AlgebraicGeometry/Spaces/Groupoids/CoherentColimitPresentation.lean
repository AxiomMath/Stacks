module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CoherentColimit

/-!
# Quasi-coherent modules on a Noetherian groupoid as small filtered colimits of coherent submodules

Stacks 0GPS (`AlgebraicGeometry.Space.QuasicoherentModule.exists_filtered_diagram_isCoherent`)
writes a quasi-coherent module `(ℱ, β)` on a groupoid `(U, R, s, t, c)` in algebraic spaces, with
`U`, `R` Noetherian and `s`, `t` flat, quasi-compact and quasi-separated, as a filtered colimit
of coherent modules, indexed by the coherent submodules of `ℱ`.  This file records two further
facts about that very diagram, both visible in the source's construction and both needed when the
result is used (Stacks 0GRF, Stacks 0GRJ):

* the index category is essentially small at the universe of the site, because the category of
  `𝒪_U`-modules is a Grothendieck abelian category at that universe, hence well-powered;
* the colimit maps are monomorphisms: each term is the subobject `ℱ ∩ s_*t^*ℋ` of `(ℱ, β)`.

## Main results

* `AlgebraicGeometry.Space.QuasicoherentModule.exists_colimitPresentation_mono_isCoherent`: a
  colimit presentation of `(ℱ, β)` indexed by a small filtered category, by monomorphisms out of
  modules with coherent underlying `𝒪_U`-module.

## References

* [Stacks Project, Tag 0GPS](https://stacks.math.columbia.edu/tag/0GPS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace QuasicoherentModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

/-- For a coherent subobject `ℋ` of `ℱ`, the module `ℱ ∩ s_*t^*ℋ` is a subobject of `(ℱ, β)`. -/
private theorem exists_subobject_iso_intersectionPushforward
    (source_flat : IsFlat B S hS G.source.hom)
    (source_quasiCompact : IsQuasiCompact B S hS G.source.hom)
    (source_quasiSeparated : IsQuasiSeparated B S hS G.source.hom)
    (target_flat : IsFlat B S hS G.target.hom) (M : QuasicoherentModule B S hS G)
    (H : CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj) :
    ∃ (Q : Subobject M) (e : (Q : QuasicoherentModule B S hS G).F.obj ≅
        intersectionPushforward B S hS G.source (transitionInclusion B S hS M H.obj.arrow)),
      e.hom ≫ intersectionPushforwardι B S hS G.source
          (transitionInclusion B S hS M H.obj.arrow) =
        Hom.hom (M := (Q : QuasicoherentModule B S hS G)) (N := M) Q.arrow := by
  let adj := forgetAdjunction G source_flat source_quasiCompact source_quasiSeparated
  let Hq : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property :=
    ⟨H.obj, H.property.toIsQuasicoherentOnSite⟩
  let ι : Hq ⟶ (forgetQuasicoherent G).obj M := ObjectProperty.homMk H.obj.arrow
  obtain ⟨P, p₁, p₂, -, hP⟩ := exists_isPullback_of_isFlat source_flat (adj.unit.app M)
    ((cofree G source_flat source_quasiCompact source_quasiSeparated).map ι)
  have hmap : ((cofree G source_flat source_quasiCompact source_quasiSeparated).map ι).hom =
      (modulePushforward B S hS (GroupoidInAlgebraicSpaces.targetPairsHom G).objectsMap).map
        ((targetPairsBase G).map ι).hom :=
    comp_groupoidQuasicoherentPushforward_map_hom
      (GroupoidInAlgebraicSpaces.targetPairsHom G) source_quasiCompact source_quasiSeparated
      (GroupoidInAlgebraicSpaces.isPullback_targetPairsHom G) source_flat (targetPairsBase G) ι
  rw [hmap, quasicoherentFromSpaceBase_map, spaceBaseHom_hom, spaceBasePullbackMap_eq] at hP
  obtain ⟨p₂', hP'⟩ := isPullback_sourceUnitInvAlpha_of_heq M
    (Y := (GroupoidInAlgebraicSpaces.targetPairsGroupoid G).objects) rfl
    (GroupoidInAlgebraicSpaces.targetPairsHom G).objectsMap
    (G.target : (GroupoidInAlgebraicSpaces.targetPairsGroupoid G).objects ⟶ G.objects)
    HEq.rfl HEq.rfl H.obj.arrow
    (heq_of_eq (forgetAdjunction_unit_app_hom G source_flat source_quasiCompact
      source_quasiSeparated M)) hP
  exact exists_subobject_of_isPullback target_flat M p₁ H.obj.arrow hP'

/-- **Stacks 0GPS, with a small index and monomorphic colimit maps.**  Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B` such that `U` and `R` are Noetherian and `s` and `t` are
flat, quasi-compact and quasi-separated.  Then every quasi-coherent module `(ℱ, β)` on
`(U, R, s, t, c)` has a colimit presentation indexed by a small filtered category (at the universe
of the site), whose colimit maps are monomorphisms and whose terms have coherent underlying
`𝒪_U`-module.

The construction is that of Stacks 0GPS: the terms are the submodules `ℱ ∩ s_*t^*ℋ` of `(ℱ, β)`
for the coherent submodules `ℋ` of `ℱ`. -/
theorem exists_colimitPresentation_mono_isCoherent (terminal_mem : B.Contains (⊤_ Scheme.{u}))
    (objects_noetherian : IsNoetherian B S hS terminal_mem G.objects.1)
    (arrows_noetherian : IsNoetherian B S hS terminal_mem G.arrows.1)
    (source_flat : IsFlat B S hS G.source.hom)
    (source_quasiCompact : IsQuasiCompact B S hS G.source.hom)
    (source_quasiSeparated : IsQuasiSeparated B S hS G.source.hom)
    (target_flat : IsFlat B S hS G.target.hom)
    (M : QuasicoherentModule B S hS G) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (pres : ColimitPresentation I M),
      (∀ i, Mono (pres.ι.app i)) ∧
        ∀ i, IsCoherent B S hS G.objects.1 G.objects.2 (pres.diag.obj i).F.obj := by
  classical
  choose P e he using exists_subobject_iso_intersectionPushforward source_flat
    source_quasiCompact source_quasiSeparated target_flat M
  have := isGrothendieckAbelian_modules B S hS G.objects.1 G.objects.2
  let I := CoherentSubobject B S hS G.objects.1 G.objects.2 M.F.obj
  have : Fact (HasEtaleLocalProperty B S hS G.objects.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨objects_noetherian.2.2⟩
  have : IsFiltered I := isFiltered_coherentSubobject B S hS _ _ M.F.obj
  have hPle : ∀ {H H' : I}, (H ⟶ H') → P H ≤ P H' := fun {H H'} g =>
    le_of_iso_intersectionPushforward source_flat target_flat H.obj.arrow H'.obj.arrow
      (Subobject.underlying.map g.hom) (Subobject.underlying_arrow g.hom) (P H) (P H') (e H)
      (he H) (e H') (he H')
  let D : I ⥤ QuasicoherentModule B S hS G :=
    { obj := fun H => (P H : QuasicoherentModule B S hS G)
      map := fun g => Subobject.underlying.map (homOfLE (hPle g))
      map_id := fun _ => by
        rw [← Subobject.underlying.map_id]
        exact congrArg _ (Subsingleton.elim _ _)
      map_comp := fun _ _ => by
        rw [← Subobject.underlying.map_comp]
        exact congrArg _ (Subsingleton.elim _ _) }
  let φ : D ⟶ (Functor.const I).obj M :=
    { app := fun H => (P H).arrow
      naturality := fun {H H'} g => by
        show Subobject.underlying.map (homOfLE (hPle g)) ≫ (P H').arrow = (P H).arrow ≫ 𝟙 M
        rw [Category.comp_id, Subobject.underlying_arrow] }
  have hcoh : ∀ H : I, IsCoherent B S hS G.objects.1 G.objects.2 (D.obj H).F.obj := fun H =>
    isCoherent_of_iso B S hS G.objects.2 (e H).symm
      (isCoherent_intersectionPushforward_transitionInclusion objects_noetherian.2.2
        arrows_noetherian.2.2 source_flat source_quasiCompact source_quasiSeparated target_flat M H)
  have hcolim : IsColimit (Cocone.mk M φ) :=
    isColimit_of_iSup_eq_top φ
      (fun H => mono_arrow_hom_of_iso_intersectionPushforward target_flat H.obj.arrow (P H) (e H)
        (he H))
      (iSup_imageSubobject_eq_top_of_iso_intersectionPushforward terminal_mem objects_noetherian
        arrows_noetherian target_flat M P e he)
  -- the index category is essentially small: `Modules(U)` is well-powered at `u`
  have : LocallySmall.{u} (Subobject (M.F.obj : Modules.{u, u} B S hS G.objects.1 G.objects.2)) :=
    ⟨fun _ _ => inferInstance⟩
  have : EssentiallySmall.{u} I :=
    essentiallySmall_of_fully_faithful (coherentSubobjectProperty B S hS _ _ M.F.obj).ι
  exact ⟨SmallModel.{u} I, inferInstance, .of_equivalence (equivSmallModel I),
    (⟨D, φ, hcolim⟩ : ColimitPresentation I M).reindex (equivSmallModel I).inverse,
    fun _ => inferInstanceAs (Mono (P _).arrow), fun _ => hcoh _⟩

end QuasicoherentModule

end AlgebraicGeometry.Space

end

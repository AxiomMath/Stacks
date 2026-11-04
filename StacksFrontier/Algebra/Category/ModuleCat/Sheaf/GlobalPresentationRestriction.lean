module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# Global presentations under restriction along a continuous and cocontinuous functor

Three facts about the global presentations of **Stacks 03DE** (6) that the module-level lower
shriek of **Stacks 0789** needs in order to be applied locally.

* Restriction of sheaves of modules along a continuous and cocontinuous functor of sites carries
  a global presentation to a global presentation, when the sheaf of rings of the source is the
  restriction of the one of the target. Restriction preserves colimits and the structure sheaf,
  so the cokernel diagram travels.
* If the source site has a final object `t`, restriction along such a functor `F` only depends
  on the restriction to the slice at `F(t)`: every object of the source maps to `t`, so `F`
  factors through the slice. Hence a global presentation on the slice at `F(t)` gives a global
  presentation of the restriction.
* On a site with a final object, a global presentation in the sense of
  `SheafOfModules.HasGlobalPresentation`, whose index types lie in the universe of the site,
  gives one in the sense of `SheafOfModules.IsPresentedByGlobalSections`, whose index types lie in
  the universe of the sections. This is the size reduction of
  `SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`, whose hypothesis
  is supplied by `SheafOfModules.small_sections_of_isTerminal`.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_pushforward_of_isCocontinuous`: restriction along
  a continuous and cocontinuous functor preserves global presentations.
* `Stacks.SheafOfModules.hasGlobalPresentation_pushforward_of_isTerminal`: a global presentation
  on the slice at the image of a final object gives a global presentation of the restriction.
* `Stacks.SheafOfModules.isPresentedByGlobalSections_of_presentation` and
  `Stacks.SheafOfModules.isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal`: the
  passage to a global presentation at the universe of the sections.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

section Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}}

/-- The morphism of sheaves of rings `R' ⟶ G^{-1}R` given by an equality `R' = G^{-1}R` of the
underlying presheaves is an isomorphism. -/
theorem isIso_homMk_eqToHom (G : C' ⥤ C) [G.IsContinuous J' J] (h : R'.obj = G.op ⋙ R.obj) :
    IsIso (ObjectProperty.homMk (eqToHom h) :
      R' ⟶ (G.sheafPushforwardContinuous RingCat.{w} J' J).obj R) :=
  ⟨ObjectProperty.homMk (eqToHom h.symm),
    ObjectProperty.hom_ext _ ((eqToHom_trans h h.symm).trans (eqToHom_refl _ _)),
    ObjectProperty.hom_ext _ ((eqToHom_trans h.symm h).trans (eqToHom_refl _ _))⟩

/-- **Restriction along a continuous and cocontinuous functor preserves global presentations**,
when the sheaf of rings of the source is the restriction of the one of the target. This is
`Stacks.SheafOfModules.hasGlobalPresentation_pushforward`, whose colimit hypothesis
cocontinuity supplies. -/
theorem hasGlobalPresentation_pushforward_of_isCocontinuous (G : C' ⥤ C) [G.IsContinuous J' J]
    [G.IsCocontinuous J' J] (h : R'.obj = G.op ⋙ R.obj) (M : _root_.SheafOfModules.{w} R)
    (hM : M.HasGlobalPresentation) :
    ((_root_.SheafOfModules.pushforward.{w}
        (ObjectProperty.homMk (eqToHom h) :
          R' ⟶ (G.sheafPushforwardContinuous RingCat.{w} J' J).obj R)).obj
        M).HasGlobalPresentation := by
  have key : ∀ {D : Type u} [Category.{v} D] (K : GrothendieckTopology D),
      HasSheafify K AddCommGrpCat.{max u v w} ∧
        K.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    fun K ↦ ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u} K,
      AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v} K⟩
  obtain ⟨_, _⟩ := key J
  obtain ⟨_, _⟩ := key J'
  have := isIso_homMk_eqToHom G h
  have : PreservesColimitsOfSize.{max u v w, max u v w}
      (_root_.SheafOfModules.pushforward.{max u v w}
        (ObjectProperty.homMk (eqToHom h) :
          R' ⟶ (G.sheafPushforwardContinuous RingCat.{w} J' J).obj R)) :=
    pushforward_preservesColimits G _
  exact hasGlobalPresentation_pushforward _ M hM

/-- **A global presentation on the slice at the image of a final object gives a global
presentation of the restriction.** Let `F : C' ⥤ C` be a continuous and cocontinuous functor of
sites, let `t` be a final object of `C'`, and let the sheaf of rings of `C'` be the restriction
of the one of `C`. If the restriction of a sheaf of modules `M` on `C` to the slice at `F(t)` has
a global presentation, then so does the restriction of `M` along `F`.

Every object of `C'` maps uniquely to `t`, so `F` factors as `C' ≌ C'/t ⥤ C/F(t) ⥤ C`, the first
functor an equivalence and the second `Over.post F`; both are continuous and cocontinuous, and
restriction along the composite of the last two is restriction to the slice. -/
theorem hasGlobalPresentation_pushforward_of_isTerminal {C : Type (max u v)} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} {C' : Type (max u v)} [Category.{v} C']
    {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}} (F : C' ⥤ C) [F.IsContinuous J' J]
    [F.IsCocontinuous J' J] {t : C'} (ht : IsTerminal t) (h : R'.obj = F.op ⋙ R.obj)
    (M : _root_.SheafOfModules.{w} R) (hM : (M.over (F.obj t)).HasGlobalPresentation) :
    ((_root_.SheafOfModules.pushforward.{w}
        (ObjectProperty.homMk (eqToHom h) :
          R' ⟶ (F.sheafPushforwardContinuous RingCat.{w} J' J).obj R)).obj
        M).HasGlobalPresentation := by
  let e : Over t ≌ C' := Over.equivalenceOfIsTerminal ht
  have hef : e.functor.IsCocontinuous (J'.over t) J' :=
    inferInstanceAs ((Over.forget t).IsCocontinuous (J'.over t) J')
  have hei : e.inverse.IsContinuous J' (J'.over t) :=
    e.toAdjunction.isContinuous_of_isCocontinuous _ _
  have heic : e.inverse.IsCocontinuous J' (J'.over t) :=
    (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (CoverPreserving.of_isContinuous (Over.forget t) (J'.over t) J')
  have hpc : (Over.post (X := t) F).IsContinuous (J'.over t) (J.over (F.obj t)) :=
    Functor.isContinuous_overPost J' J F t
  let G : C' ⥤ Over (F.obj t) := e.inverse ⋙ Over.post (X := t) F
  have hGc : G.IsContinuous J' (J.over (F.obj t)) :=
    Functor.isContinuous_comp _ _ J' (J'.over t) _
  have hGcc : G.IsCocontinuous J' (J.over (F.obj t)) :=
    isCocontinuous_comp (G := e.inverse) (G' := Over.post (X := t) F) (J := J')
      (K := J'.over t) (L := J.over (F.obj t))
  have h' : R'.obj = G.op ⋙ (R.over (F.obj t)).obj := h
  exact SheafOfModules.HasGlobalPresentation.of_iso
    ((_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ by ext; rfl)))
    (hasGlobalPresentation_pushforward_of_isCocontinuous G h' (M.over (F.obj t)) hM)

end Restriction

section Size

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A presentation is a global presentation at the universe of the sections**: the two free
modules of a presentation are coproducts of copies of the structure sheaf indexed by types in the
universe of the sections, and the presentation exhibits the module as their cokernel. -/
theorem isPresentedByGlobalSections_of_presentation {M : _root_.SheafOfModules.{w} R}
    (P : M.Presentation) : M.IsPresentedByGlobalSections :=
  ⟨P.generators.I, P.relations.I, _, _, _, _,
    ⟨_root_.SheafOfModules.isColimitFreeCofan P.generators.I⟩,
    ⟨_root_.SheafOfModules.isColimitFreeCofan P.relations.I⟩, _, _, _, ⟨P.isColimit⟩⟩

/-- **On a site with a final object a global presentation can be taken at the universe of the
sections.** The index types of `SheafOfModules.HasGlobalPresentation` lie in the universe of the
site, those of `SheafOfModules.IsPresentedByGlobalSections` in the universe of the sections; the
global sections of every sheaf of modules are small on a site with a final object, and that is
what the size reduction needs. -/
theorem isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal {t : C}
    (ht : IsTerminal t) {M : _root_.SheafOfModules.{w} R} (h : M.HasGlobalPresentation) :
    M.IsPresentedByGlobalSections :=
  have : ∀ N : _root_.SheafOfModules.{w} R, Small.{w} N.sections :=
    _root_.SheafOfModules.small_sections_of_isTerminal ht
  isPresentedByGlobalSections_of_presentation
    (_root_.SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections h).some

end Size

end Stacks.SheafOfModules

end

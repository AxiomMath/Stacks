module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TerminalObjectPresentationShrink
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetNormalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# Restricting a global presentation over a slice along a functor into the slice

Let `(C, J)` be a site with a sheaf of rings `R`, `y` an object of `C`, and `v : C' ⥤ C/y` a
continuous and cocontinuous functor from a site `(C', J')` with a sheaf of rings `R'`, together
with an isomorphism `ψ : R' ≅ v^{-1}(R|_y)`. If a sheaf of `R`-modules `M` has a global
presentation over `y` (the clause of Stacks 03DL (6)), then the restriction of `M|_y` along `v`
has a global presentation (Stacks 03DE (6)) at the universe of the sections.

The restriction along `v` preserves colimits (`v` being cocontinuous) and carries the structure
sheaf to the structure sheaf (`ψ` being invertible), so it carries a presentation to a
presentation (`Stacks.Sheaves.LocalizedPullback.isPresentedByGlobalSections_map`); and the slice
has the final object `y/y`, over which a global presentation can be taken at the universe of the
sections (`SheafOfModules.isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal`).
This is how a local presentation of a module on the flat-fppf (or lisse-étale) site of an
algebraic stack at an object `y` becomes a global presentation of its pullback along the
1-morphism `y : (Sch/U) → 𝒳`, the step of the proof of Stacks 07B3 which recalls that the
pullback "is" the restriction to `𝒳/y` (Stacks 06W1).

## Main results

* `Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_over`: along a functor into the
  slice.
* `Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal`: along a functor
  `σ : C' ⥤ C` from a site with a terminal object `e` together with a morphism `σ e ⟶ y`, which
  factors through `C/y`.
* `Stacks.SheafOfModules.isContinuous_equivalenceOfIsTerminal_inverse`,
  `Stacks.SheafOfModules.isCocontinuous_equivalenceOfIsTerminal_inverse`: the inverse of the
  forgetful equivalence `C'/e ≌ C'` at a terminal object is continuous and cocontinuous.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  (R : Sheaf J RingCat.{w}) (y : C) (v : C' ⥤ Over y)
  [v.IsContinuous J' (J.over y)] [v.IsCocontinuous J' (J.over y)]
  {R' : Sheaf J' RingCat.{w}}
  (ψ : R' ⟶ (v.sheafPushforwardContinuous RingCat.{w} J' (J.over y)).obj (R.over y)) [IsIso ψ]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify (J.over y) AddCommGrpCat.{w}] [(J.over y).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A global presentation over a slice restricts to a global presentation along a continuous
and cocontinuous functor into the slice that carries the structure sheaf to the structure
sheaf.** -/
theorem isPresentedByGlobalSections_pushforward_over {M : _root_.SheafOfModules.{w} R}
    (hM : (M.over y).HasGlobalPresentation) :
    ((_root_.SheafOfModules.pushforward.{w} ψ).obj (M.over y)).IsPresentedByGlobalSections := by
  have h₀ : (M.over y).IsPresentedByGlobalSections :=
    _root_.SheafOfModules.isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal
      Over.mkIdTerminal hM
  have := @pushforward_preservesColimits.{u₂, v₂, w, max u₁ v₁, v₁, w} C' _ (Over y) _ J'
    (J.over y) inferInstance
    ‹J'.WEqualsLocallyBijective AddCommGrpCat.{w}› inferInstance
    ‹(J.over y).WEqualsLocallyBijective AddCommGrpCat.{w}› v _ _ R' (R.over y) ψ
  have : IsIso ((_root_.SheafOfModules.toSheaf.{w} R').map
      (_root_.SheafOfModules.unitToPushforwardObjUnit ψ)) :=
    isIso_toSheaf_map_unitToPushforwardObjUnit ψ
  have : IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit ψ) :=
    isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf.{w} R')
  exact Stacks.Sheaves.LocalizedPullback.isPresentedByGlobalSections_map
    (_root_.SheafOfModules.pushforward.{w} ψ)
    (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit ψ)).symm (Iso.refl _) h₀

section Terminal

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {C' : Type u₂} [Category.{v₂} C'] (J' : GrothendieckTopology C') {e : C'} (he : IsTerminal e)

/-- The inverse `C' ⥤ C'/e` of the forgetful equivalence at a terminal object is cocontinuous. -/
theorem isCocontinuous_equivalenceOfIsTerminal_inverse :
    (Over.equivalenceOfIsTerminal he).inverse.IsCocontinuous J' (J'.over e) where
  cover_lift {X} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS
    refine J'.superset_covering ?_ hS
    intro Z g hg
    have h₁ := S.downward_closed ((Sieve.overEquiv_iff S g).1 hg)
      (Over.homMk (𝟙 Z) (he.hom_ext _ _) :
        (Over.equivalenceOfIsTerminal he).inverse.obj Z ⟶ Over.mk (g ≫ (Over.mk (he.from X)).hom))
    change S.arrows ((Over.equivalenceOfIsTerminal he).inverse.map g)
    convert h₁ using 1
    ext
    exact (Category.id_comp g).symm

/-- The inverse `C' ⥤ C'/e` of the forgetful equivalence at a terminal object is continuous. -/
theorem isContinuous_equivalenceOfIsTerminal_inverse :
    (Over.equivalenceOfIsTerminal he).inverse.IsContinuous J' (J'.over e) := by
  have := isCocontinuous_equivalenceOfIsTerminal_inverse J' he
  have : (Over.equivalenceOfIsTerminal he).functor.IsCocontinuous (J'.over e) J' :=
    inferInstanceAs ((Over.forget e).IsCocontinuous (J'.over e) J')
  have := Equivalence.isDenseSubsite_inverse_of_isCocontinuous (J'.over e) J'
    (Over.equivalenceOfIsTerminal he)
  infer_instance

end Terminal

section Presentation

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  (R : Sheaf J RingCat.{w}) {R' : Sheaf J' RingCat.{w}} {e : C'} (he : IsTerminal e)
  (σ : C' ⥤ C) [σ.IsContinuous J' J] [σ.IsCocontinuous J' J] (y : C) (φ : σ.obj e ⟶ y)
  (χ : R' ⟶ (σ.sheafPushforwardContinuous RingCat.{w} J' J).obj R) [IsIso χ]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify (J.over y) AddCommGrpCat.{w}] [(J.over y).WEqualsLocallyBijective AddCommGrpCat.{w}]

include he φ in
/-- **A local presentation at `y` restricts to a global presentation along a functor from a site
with a terminal object `e` lying over `y`.** If `σ : C' ⥤ C` is continuous and cocontinuous,
`C'` has a terminal object `e` with a morphism `σ e ⟶ y`, and `σ^{-1} R ≅ R'`, then for every
sheaf of `R`-modules `M` with a global presentation over `y` (Stacks 03DL (6)) the restriction of
`M` along `σ` has a global presentation (Stacks 03DE (6)): `σ` factors through `C/y` by a
continuous and cocontinuous functor, along which
`Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_over` applies. -/
theorem isPresentedByGlobalSections_pushforward_of_isTerminal {M : _root_.SheafOfModules.{w} R}
    (hM : (M.over y).HasGlobalPresentation) :
    ((_root_.SheafOfModules.pushforward.{w} χ).obj M).IsPresentedByGlobalSections := by
  have := isContinuous_equivalenceOfIsTerminal_inverse J' he
  have := isCocontinuous_equivalenceOfIsTerminal_inverse J' he
  have := Functor.isContinuous_overPost J' J σ e
  let v : C' ⥤ Over y := (Over.equivalenceOfIsTerminal he).inverse ⋙ Over.post σ ⋙ Over.map φ
  have : v.IsContinuous J' (J.over y) := Functor.isContinuous_comp _ _ _ (J'.over e) _
  have : (Over.post σ ⋙ Over.map φ).IsCocontinuous (J'.over e) (J.over y) :=
    CategoryTheory.isCocontinuous_comp (L := J.over y) _ _ (J'.over e) (J.over (σ.obj e))
  have : v.IsCocontinuous J' (J.over y) :=
    CategoryTheory.isCocontinuous_comp (L := J.over y) _ _ J' (J'.over e)
  let ψ : R' ⟶ (v.sheafPushforwardContinuous RingCat.{w} J' (J.over y)).obj (R.over y) := χ
  have : IsIso ψ := inferInstanceAs (IsIso χ)
  exact isPresentedByGlobalSections_pushforward_over R y v ψ hM

end Presentation

end Stacks.SheafOfModules

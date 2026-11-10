module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePresentationRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftSectionCorepresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation

/-!
# Lower shriek along a subsite containing a final object preserves global presentations

Let `u : C' ⥤ C` be a continuous and cocontinuous functor of sites, `O` a sheaf of rings on `C`
and `g_! : Mod(u^{-1}O) ⥤ Mod(O)` the lower shriek of Stacks 0797, at a module universe one
above that of the rings. If `C'` has a final object `e` whose image `u(e)` is a final object of
`C`, then `g_!` carries the structure sheaf to the structure sheaf, and hence a module with a
global presentation (Stacks 03DE (6)) to one: `g_!` preserves colimits, being a left adjoint.

The identification `g_! O' ≅ O` is made through corepresentability of the sections over the
final objects: the structure sheaf corepresents the sections over a final object, through `1`
(`Stacks.SheafOfModules.isCorepresentingSection_unit_of_isTerminal`); by adjunction `g_!`
carries a module corepresenting the sections over `e` to one corepresenting the sections over
`u(e)`; and two modules corepresenting the same sections are isomorphic.

This is the step `g_!O = O_𝒳` of the proof of Stacks 07B0, in the situation of the flat-fppf
(or lisse-étale) site of the stack of a scheme `U`, whose final object `U/U` is flat (smooth).

## Main results

* `Stacks.SheafOfModules.isCorepresentingSection_unit_of_isTerminal`.
* `Stacks.SheafOfModules.lowerShriekUliftUnitIso`: `g_!(O') ≅ O` for the universe-lifted structure
  sheaves.
* `Stacks.SheafOfModules.hasGlobalPresentation_lowerShriek_of_isTerminal`: `g_!` preserves global
  presentations.

## References

* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 078A](https://stacks.math.columbia.edu/tag/078A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ u

namespace Stacks.SheafOfModules

section Unit

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- **The structure sheaf corepresents the sections over a final object**, through the section
`1`: a morphism `O ⟶ N` is a global section of `N`, and a global section is determined by, and
can be prescribed through, its value over a final object. -/
theorem isCorepresentingSection_unit_of_isTerminal {V : C} (hV : IsTerminal V) :
    IsCorepresentingSection (T := _root_.SheafOfModules.unit R) V
      (1 : R.obj.obj (op V)) := by
  intro N
  have hev : Function.Bijective (fun s : N.sections => s.val (op V)) := by
    refine ⟨fun s t hst => ?_, fun n => ?_⟩
    · refine PresheafOfModules.sections_ext _ _ fun X => ?_
      rw [← PresheafOfModules.sections_property s (hV.from X.unop).op,
        ← PresheafOfModules.sections_property t (hV.from X.unop).op]
      exact congrArg _ hst
    · refine ⟨PresheafOfModules.sectionsMk (fun X => N.val.map (hV.from X.unop).op n) ?_, ?_⟩
      · intro X Y f
        change (N.val.presheaf.map f) ((N.val.presheaf.map (hV.from X.unop).op) n) =
          N.val.presheaf.map (hV.from Y.unop).op n
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        congr 3
        exact Quiver.Hom.unop_inj (hV.hom_ext _ _)
      · change N.val.presheaf.map (hV.from V).op n = n
        rw [show hV.from V = 𝟙 V from hV.hom_ext _ _, op_id, CategoryTheory.Functor.map_id]
        rfl
  exact hev.comp N.unitHomEquiv.bijective

end Unit

section LowerShriek

variable {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (g : C ⥤ D)
  [g.IsContinuous J K] [g.IsCocontinuous J K] (O : Sheaf K RingCat.{u})
  [HasWeakSheafify K AddCommGrpCat.{u + 1}] [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  {e : C} (he : IsTerminal e) (hge : IsTerminal (g.obj e))

omit [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
include he in
/-- **Lower shriek carries a module corepresenting the sections over `e` to one corepresenting
the sections over `g(e)`**, through the image of the corepresenting section under the unit of
`g_! ⊣ g^{-1}`; here this is stated for the universe-lifted structure sheaf of the subsite, which
corepresents the sections over the final object `e` through `1`. -/
theorem isCorepresentingSection_lowerShriek_uliftUnit :
    IsCorepresentingSection
      (T := (lowerShriek.{u + 1} J K g O).obj
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (_root_.SheafOfModules.unit (inverseImageRing J K g O))))
      (g.obj e)
      ((((lowerShriekAdjunction.{u + 1} J K g O).unit.app
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (_root_.SheafOfModules.unit (inverseImageRing J K g O)))).val.app (op e)).hom
        (ULift.up (1 : (inverseImageRing J K g O).obj.obj (op e)))) := by
  intro N
  exact (isCorepresentingSection_uliftForPresentation.{u, u + 1} J (inverseImageRing J K g O)
      (isCorepresentingSection_unit_of_isTerminal (inverseImageRing J K g O) he)
      ((inverseImage.{u + 1} J K g O).obj N)).comp
    ((lowerShriekAdjunction.{u + 1} J K g O).homEquiv _ N).bijective

include he hge in
/-- **`g_! O' ≅ O`** for a continuous and cocontinuous functor of sites carrying a final object
of the source to a final object of the target, the structure sheaves raised to the module
universe: both sides corepresent the sections over the final object `g(e)` of the target. -/
theorem nonempty_lowerShriekUliftUnitIso :
    Nonempty ((lowerShriek.{u + 1} J K g O).obj
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (_root_.SheafOfModules.unit (inverseImageRing J K g O))) ≅
      _root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (_root_.SheafOfModules.unit O)) := by
  have hT := isCorepresentingSection_lowerShriek_uliftUnit J K g O he
  obtain ⟨φ, hφ⟩ := (hT (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
    (_root_.SheafOfModules.unit O))).2 (ULift.up (1 : O.obj.obj (op (g.obj e))))
  have := isIso_of_isCorepresentingSection hT
    (isCorepresentingSection_uliftForPresentation.{u, u + 1} K O
      (isCorepresentingSection_unit_of_isTerminal O hge)) φ hφ
  exact ⟨asIso φ⟩

include he hge in
/-- **Lower shriek along a functor carrying a final object to a final object preserves global
presentations** (Stacks 03DE (6)): it preserves colimits, being a left adjoint, and carries the
structure sheaf to the structure sheaf. -/
theorem hasGlobalPresentation_lowerShriek_of_isTerminal
    (M : _root_.SheafOfModules.{u + 1} (inverseImageRing J K g O))
    (hM : M.HasGlobalPresentation) :
    ((lowerShriek.{u + 1} J K g O).obj M).HasGlobalPresentation := by
  have adj := lowerShriekAdjunction.{u + 1} J K g O
  have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerShriek.{u + 1} J K g O) :=
    adj.leftAdjoint_preservesColimits
  have : (lowerShriek.{u + 1} J K g O).IsLeftAdjoint := adj.isLeftAdjoint
  obtain ⟨η₁⟩ := nonempty_lowerShriekUliftUnitIso J K g O he hge
  exact hasGlobalPresentation_map M (F₀ := lowerShriek.{u + 1} J K g O)
    (F := lowerShriek.{u + 1} J K g O) η₁
    ((lowerShriek.{u + 1} J K g O).mapIso
        (uliftForPresentationIsoSelf.{u + 1, u, u, u + 1} M).symm ≪≫
      uliftForPresentationIsoSelf.{u + 1, u, u, u + 1} ((lowerShriek.{u + 1} J K g O).obj M)) hM

end LowerShriek

section Restriction

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {C' : Type (u + 1)} [Category.{u} C'] {J' : GrothendieckTopology C'}
  (R : Sheaf J RingCat.{u}) {R' : Sheaf J' RingCat.{u}} {e : C'} (he : IsTerminal e)
  (σ : C' ⥤ C) [σ.IsContinuous J' J] [σ.IsCocontinuous J' J] (y : C) (φ : σ.obj e ⟶ y)
  (χ : R' ⟶ (σ.sheafPushforwardContinuous RingCat.{u} J' J).obj R) [IsIso χ]

include he φ in
/-- **A local presentation at `y` restricts to a global presentation along a functor from a site
with a final object `e` lying over `y`**, for modules whose sections lie one universe above the
rings, the universe in which a global presentation (Stacks 03DE (6)) is taken on these sites.
`σ` factors through `C/y` by a continuous and cocontinuous functor
(`(C' ≌ C'/e) ⋙ C'/e ⥤ C/σ(e) ⥤ C/y`), along which restriction preserves colimits and carries
the structure sheaf to the structure sheaf. This is the module-universe-`u + 1` form of
`Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal`. -/
theorem hasGlobalPresentation_pushforward_of_isTerminal_succ
    (M : _root_.SheafOfModules.{u + 1} R) (hM : (M.over y).HasGlobalPresentation) :
    ((_root_.SheafOfModules.pushforward.{u + 1} χ).obj M).HasGlobalPresentation := by
  have := isContinuous_equivalenceOfIsTerminal_inverse J' he
  have := isCocontinuous_equivalenceOfIsTerminal_inverse J' he
  have := Functor.isContinuous_overPost J' J σ e
  let v : C' ⥤ Over y := (Over.equivalenceOfIsTerminal he).inverse ⋙ Over.post σ ⋙ Over.map φ
  have : v.IsContinuous J' (J.over y) := Functor.isContinuous_comp _ _ _ (J'.over e) _
  have : (Over.post σ ⋙ Over.map φ).IsCocontinuous (J'.over e) (J.over y) :=
    CategoryTheory.isCocontinuous_comp (L := J.over y) _ _ (J'.over e) (J.over (σ.obj e))
  have : v.IsCocontinuous J' (J.over y) :=
    CategoryTheory.isCocontinuous_comp (L := J.over y) _ _ J' (J'.over e)
  let ψ : R' ⟶ (v.sheafPushforwardContinuous RingCat.{u} J' (J.over y)).obj (R.over y) := χ
  have : IsIso ψ := inferInstanceAs (IsIso χ)
  have : HasSheafify J' AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have : J'.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have : HasSheafify (J.over y) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have : (J.over y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have : PreservesColimitsOfSize.{u + 1, u + 1} (_root_.SheafOfModules.pushforward.{u + 1} ψ) :=
    pushforward_preservesColimits v ψ
  exact hasGlobalPresentation_pushforward ψ (M.over y) hM

end Restriction

end Stacks.SheafOfModules

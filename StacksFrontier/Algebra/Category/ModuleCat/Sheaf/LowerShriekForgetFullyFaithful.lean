module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetCounit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized

/-!
# The comparison of the two lower shrieks along a functor with a fully faithful right adjoint

Let `u : C ⥤ D` be a continuous functor of sites, `O` a sheaf of rings on `D` and `u⁻¹O` its
restriction to `C`, with `g^* : Mod(O) ⥤ Mod(u⁻¹O)` and `g^{-1} : Ab(D) ⥤ Ab(C)` the two
restrictions and `g_!`, `g_!^{Ab}` their left adjoints. The canonical comparison
`g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` of Stacks 0798 is the adjoint mate of the identity
`forget ∘ g^* = g^{-1} ∘ forget`. Like every mate it is compatible with the two counits
(`Stacks.SheafOfModules.lowerShriekForgetComparison_app_comp_counit`), so the comparison is
invertible at the restriction `g^* N` of a sheaf of `O`-modules as soon as both counits at `N`
are, in particular as soon as restriction along `u` is fully faithful both on abelian sheaves and
on modules.

That is the case when `u` has a continuous right adjoint `v` with invertible counit `u v ⟶ 1`:
restriction along `u` is then left adjoint to restriction along `v`, with unit the restriction
along that counit, on sheaves with values in any category and on sheaves of modules alike. The
structure sheaf `u⁻¹O` being the restriction of `O`, the comparison is then invertible at the
structure sheaf.

## Main definitions

* `Stacks.SheafOfModules.counitRingMap` and `Stacks.SheafOfModules.modulePushforwardAdjunction`:
  for `u ⊣ v`, the adjunction `g^* ⊣ v^*` between the restrictions of sheaves of modules.

## Main results

* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_pushforward_of_isIso`: the
  comparison is invertible at `g^* N` when the two counits at `N` are.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_pushforward`: the comparison is
  invertible at every `g^* N` when the two restrictions are fully faithful.
* `Stacks.SheafOfModules.fullyFaithfulSheafPushforwardContinuous` and
  `Stacks.SheafOfModules.fullyFaithfulModulePushforward`: restriction along a functor with a
  continuous right adjoint and invertible counit is fully faithful, on sheaves and on modules.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_unit_of_adjunction`: for such a
  functor the comparison is invertible at the structure sheaf.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public section

open CategoryTheory

universe w r u₁ u₂ v₁ v₂

namespace Stacks.SheafOfModules

section Counit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] (O : Sheaf K RingCat.{r})
  [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).IsRightAdjoint]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- **The comparison of Stacks 0798 is invertible at a restricted module `g^* N`** as soon as
the two counits at `N` are: the counit `g_! g^* N ⟶ N` of modules and the counit
`g_!^{Ab} g^{-1}(forget N) ⟶ forget N` of abelian sheaves. -/
theorem isIso_lowerShriekForgetComparison_app_pushforward_of_isIso
    (N : _root_.SheafOfModules.{w} O)
    [hab : IsIso ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).counit.app
      ((_root_.SheafOfModules.toSheaf.{w} O).obj N))]
    [IsIso ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
      (structureMap J K u O)).counit.app N)] :
    IsIso ((lowerShriekForgetComparison u (structureMap J K u O)).app
      ((_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).obj N)) := by
  have h := lowerShriekForgetComparison_app_comp_counit u (structureMap J K u O) N
  have : IsIso ((lowerShriekForgetComparison u (structureMap J K u O)).app
        ((_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).obj N) ≫
      (_root_.SheafOfModules.toSheaf.{w} O).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap J K u O)).counit.app N)) := h.symm ▸ hab
  exact IsIso.of_isIso_comp_right _
    ((_root_.SheafOfModules.toSheaf.{w} O).map
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
        (structureMap J K u O)).counit.app N))

/-- **The comparison of Stacks 0798 is invertible at every restricted module** as soon as
restriction along `u` is fully faithful on abelian sheaves and on sheaves of modules. -/
theorem isIso_lowerShriekForgetComparison_app_pushforward
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Full]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Faithful]
    [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).Full]
    [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).Faithful]
    (N : _root_.SheafOfModules.{w} O) :
    IsIso ((lowerShriekForgetComparison u (structureMap J K u O)).app
      ((_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).obj N)) := by
  have : IsIso (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  have : IsIso (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
      (structureMap J K u O)).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  have : IsIso ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).counit.app
      ((_root_.SheafOfModules.toSheaf.{w} O).obj N)) :=
    NatIso.isIso_app_of_isIso (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).counit _
  exact isIso_lowerShriekForgetComparison_app_pushforward_of_isIso J K u O N

end Counit

section RightAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] (O : Sheaf K RingCat.{r})
  {v : D ⥤ C} (adj : u ⊣ v) [v.IsContinuous K J] [IsIso adj.counit]

/-- A morphism of sheaves is invertible as soon as it is so on every object. -/
private theorem isIso_of_forall_isIso_hom_app {C : Type u₁} [Category.{v₁} C]
    (K : GrothendieckTopology C) {A : Type*} [Category A] {F G : Sheaf K A} (f : F ⟶ G)
    (h : ∀ X, IsIso (f.hom.app X)) : IsIso f := by
  have : IsIso ((sheafToPresheaf K A).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact h
  exact isIso_of_reflects_iso _ (sheafToPresheaf K A)

/-- If `u ⊣ v` is an adjunction between continuous functors of sites whose counit is invertible,
then the unit of the induced adjunction `u^s ⊣ v^s` on sheaves is invertible: at a sheaf `P` and
an object `X` it is `P` applied to the counit of `u ⊣ v` at `X`. -/
theorem isIso_sheafPushforwardContinuous_unit (A : Type*) [Category A] :
    IsIso (adj.sheafPushforwardContinuous (E := A) J K).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  refine isIso_of_forall_isIso_hom_app K _ fun X => ?_
  simp only [Functor.id_obj, Functor.comp_obj,
    Adjunction.sheafPushforwardContinuous_unit_app_hom_app]
  exact (P.obj.mapIso (asIso (adj.counit.app X.unop)).op).isIso_hom

/-- **Restriction of sheaves along a functor with a right adjoint and invertible counit is fully
faithful.** -/
noncomputable def fullyFaithfulSheafPushforwardContinuous (A : Type*) [Category A] :
    (u.sheafPushforwardContinuous A J K).FullyFaithful :=
  have := isIso_sheafPushforwardContinuous_unit J K u adj A
  (adj.sheafPushforwardContinuous (E := A) J K).fullyFaithfulLOfIsIsoUnit

/-- The morphism of sheaves of rings `O ⟶ v_* u⁻¹ O` along which the restriction of modules
along `v` is taken: `O` applied to the counit of `u ⊣ v`. -/
def counitRingMap :
    O ⟶ (v.sheafPushforwardContinuous RingCat.{r} K J).obj (inverseImageRing J K u O) :=
  ⟨Functor.whiskerRight (NatTrans.op adj.counit) O.obj⟩

/-- The adjunction `u^* ⊣ v^*` between the restrictions of sheaves of modules induced by an
adjunction `u ⊣ v` of continuous functors of sites. -/
noncomputable def modulePushforwardAdjunction :
    _root_.SheafOfModules.pushforward.{w} (structureMap J K u O) ⊣
      _root_.SheafOfModules.pushforward.{w} (counitRingMap J K u O adj) :=
  _root_.SheafOfModules.pushforwardPushforwardAdj adj _ _ (by ext; simp [counitRingMap]; rfl)
    (by
      ext X x
      change (O.obj.map (adj.counit.app (u.obj X.unop)).op ≫
        O.obj.map (u.map (adj.unit.app X.unop)).op) x = x
      rw [← Functor.map_comp, ← op_comp]
      have h := congrArg (fun f => (ConcreteCategory.hom (O.obj.map f.op)) x)
        (adj.left_triangle_components X.unop)
      refine h.trans ?_
      simp
      rfl)

/-- The unit of `modulePushforwardAdjunction` is invertible when the counit of `u ⊣ v` is: at a
sheaf of modules `M` and an object `X` it is `M` applied to the counit of `u ⊣ v` at `X`. -/
theorem isIso_modulePushforwardAdjunction_unit :
    IsIso (modulePushforwardAdjunction.{w} J K u O adj).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso ((_root_.SheafOfModules.toSheaf.{w} O).map
      ((modulePushforwardAdjunction.{w} J K u O adj).unit.app M)) :=
    isIso_of_forall_isIso_hom_app K _ fun X =>
      (M.val.presheaf.mapIso (asIso (adj.counit.app X.unop)).op).isIso_hom
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf.{w} O)

/-- **Restriction of sheaves of modules along a functor with a right adjoint and invertible
counit is fully faithful.** -/
noncomputable def fullyFaithfulModulePushforward :
    (_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).FullyFaithful :=
  have := isIso_modulePushforwardAdjunction_unit.{w} J K u O adj
  (modulePushforwardAdjunction.{w} J K u O adj).fullyFaithfulLOfIsIsoUnit

end RightAdjoint

section Unit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] (O : Sheaf K RingCat.{w})
  [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).IsRightAdjoint]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  {v : D ⥤ C} (adj : u ⊣ v) [v.IsContinuous K J] [IsIso adj.counit]

include adj in
/-- **The comparison of Stacks 0798 is invertible at the structure sheaf `u⁻¹O`** for a functor
of sites `u` with a continuous right adjoint whose counit is invertible. -/
theorem isIso_lowerShriekForgetComparison_app_unit_of_adjunction :
    IsIso ((lowerShriekForgetComparison u (structureMap J K u O)).app
      (_root_.SheafOfModules.unit (inverseImageRing J K u O))) := by
  have hab := fullyFaithfulSheafPushforwardContinuous J K u adj AddCommGrpCat.{w}
  have hmod := fullyFaithfulModulePushforward.{w} J K u O adj
  have := hab.full
  have := hab.faithful
  have := hmod.full
  have := hmod.faithful
  exact isIso_lowerShriekForgetComparison_app_pushforward J K u O
    (_root_.SheafOfModules.unit O)

end Unit

end Stacks.SheafOfModules

end

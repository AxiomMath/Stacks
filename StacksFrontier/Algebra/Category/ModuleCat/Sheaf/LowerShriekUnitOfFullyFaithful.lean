module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction
public import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# `g^* g_! = id` on modules for a fully faithful functor, with independent universes

Let `u : C ⥤ D` be a fully faithful, continuous and cocontinuous functor of sites, `O_D` a sheaf
of rings on `D` with rings in `Type r`, and `O_C = g^{-1} O_D`.  On sheaves of modules with
sections in an independent universe `v`, restriction `g^*` has the left adjoint `g_!`
(`Stacks.SheafOfModules.lowerShriekAdjunction`, **Stacks 0797**) and the right adjoint `g_*`
(`Stacks.SheafOfModules.RestrictRan.sheafAdjunction`).  The counit `g^* g_* ⟶ id` is invertible
because the counit of right Kan extension along a fully faithful functor is, and for the adjoint
triple `g_! ⊣ g^* ⊣ g_*` this is equivalent to the unit `id ⟶ g^* g_!` being invertible: the
module form of **Stacks 077I**, the assertion `g^* g_! = id` of **Stacks 0789**.

## Main results

* `Stacks.SheafOfModules.isIso_restrictRanSheafAdjunction_counit_of_full`: the counit of
  `g^* ⊣ g_*` is invertible.
* `Stacks.SheafOfModules.isIso_lowerShriekAdjunction_unit_of_full`: the unit of `g_! ⊣ g^*` is
  invertible.

## References

* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})
  [∀ F : Cᵒᵖ ⥤ RingCat.{r}, f.op.HasPointwiseRightKanExtension F]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{v}, f.op.HasPointwiseRightKanExtension F]

/-- The counit of restriction ⊣ right Kan extension on presheaves of modules is the counit of
right Kan extension, on underlying presheaves of abelian groups. -/
theorem toPresheaf_map_restrictRanAdjunction_counit_app_of_univ
    (M : PresheafOfModules.{v} (f.op ⋙ O.obj)) :
    (PresheafOfModules.toPresheaf _).map
        ((RestrictRan.adjunction.{v} f O.obj).counit.app M) =
      (f.op.ranAdjunction AddCommGrpCat.{v}).counit.app M.presheaf := by
  set adj := RestrictRan.adjunction.{v} f O.obj
  have h1 : adj.homEquiv _ M (adj.counit.app M) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  have h2 := RestrictRan.toPresheaf_map_adjunction_homEquiv f O.obj
    (ranPushforward.{v} f (RestrictRan.unitRingHom f (T := O.obj)) |>.obj M) M
    (adj.counit.app M)
  rw [h1, CategoryTheory.Functor.map_id] at h2
  have h3 : ((f.op.ranAdjunction AddCommGrpCat.{v}).homEquiv _ _).symm (𝟙 _) =
      RestrictRan.sourceMap f _ M (adj.counit.app M) :=
    (congrArg ((f.op.ranAdjunction AddCommGrpCat.{v}).homEquiv _ _).symm h2).trans
      (Equiv.symm_apply_apply _ _)
  rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp] at h3
  exact h3.symm

omit [f.IsContinuous J K] [f.IsCocontinuous J K] in
/-- The counit of restriction ⊣ right Kan extension on presheaves of modules is invertible for a
fully faithful functor. -/
theorem isIso_restrictRanAdjunction_counit_app_of_full [f.Full] [f.Faithful]
    (M : PresheafOfModules.{v} (f.op ⋙ O.obj)) :
    IsIso ((RestrictRan.adjunction.{v} f O.obj).counit.app M) := by
  have : IsIso (f.op.ranAdjunction AddCommGrpCat.{v}).counit :=
    Functor.reflective' (H := AddCommGrpCat.{v}) f.op
  have : IsIso ((PresheafOfModules.toPresheaf _).map
      ((RestrictRan.adjunction.{v} f O.obj).counit.app M)) := by
    rw [toPresheaf_map_restrictRanAdjunction_counit_app_of_univ]
    exact NatIso.isIso_app_of_isIso _ _
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

/-- The counit of `g^* ⊣ g_*` on sheaves of modules is, on underlying presheaves of modules, the
counit on presheaves of modules. -/
theorem forget_map_restrictRanSheafAdjunction_counit_app_of_univ
    (N : _root_.SheafOfModules.{v} (RestrictRan.ringSheaf f J K O)) :
    (_root_.SheafOfModules.forget _).map
        ((RestrictRan.sheafAdjunction.{v} f J K O).counit.app N) =
      (RestrictRan.adjunction.{v} f O.obj).counit.app N.val := by
  have e := Adjunction.map_restrictFullyFaithful_counit_app
    (L := _root_.SheafOfModules.pushforward.{v} (F := f) (R := O)
      (S := RestrictRan.ringSheaf f J K O) (𝟙 (RestrictRan.ringSheaf f J K O)))
    (R := pushforwardCocontinuous.{v} f (RestrictRan.sheafUnit f J K O))
    (RestrictRan.adjunction.{v} f O.obj)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} O)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} (RestrictRan.ringSheaf f J K O))
    (Iso.refl (_root_.SheafOfModules.forget.{v} O ⋙ PresheafOfModules.pushforward₀.{v} f O.obj))
    (Iso.refl (_root_.SheafOfModules.forget.{v} (RestrictRan.ringSheaf f J K O) ⋙
      ranPushforward.{v} f (RestrictRan.unitRingHom f (T := O.obj)))) N
  simp only [Iso.refl_inv, NatTrans.id_app] at e
  exact e

/-- **The counit of `g^* ⊣ g_*` is invertible for a fully faithful functor of sites**, at
independent universes of rings and of module sections. -/
theorem isIso_restrictRanSheafAdjunction_counit_of_full [f.Full] [f.Faithful] :
    IsIso (RestrictRan.sheafAdjunction.{v} f J K O).counit := by
  have : ∀ N, IsIso ((RestrictRan.sheafAdjunction.{v} f J K O).counit.app N) := by
    intro N
    have : IsIso ((_root_.SheafOfModules.forget _).map
        ((RestrictRan.sheafAdjunction.{v} f J K O).counit.app N)) := by
      rw [forget_map_restrictRanSheafAdjunction_counit_app_of_univ]
      exact isIso_restrictRanAdjunction_counit_app_of_full K f O N.val
    exact (_root_.SheafOfModules.fullyFaithfulForget _).isIso_of_isIso_map _
  exact NatIso.isIso_of_isIso_app _

/-- **`g^* g_! = id` on sheaves of modules for a fully faithful continuous and cocontinuous
functor of sites** (**Stacks 077I** for modules, the assertion of **Stacks 0789**), at independent
universes of rings and of module sections: the unit of the adjunction
`Stacks.SheafOfModules.lowerShriekAdjunction` of **Stacks 0797** is invertible. -/
theorem isIso_lowerShriekAdjunction_unit_of_full [f.Full] [f.Faithful]
    [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{v₂, v}] [UnivLE.{u₁, v}]
    [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] :
    IsIso (lowerShriekAdjunction.{v} J K f O).unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨lowerShriekAdjunction.{v} J K f O, RestrictRan.sheafAdjunction.{v} f J K O⟩).2
    (isIso_restrictRanSheafAdjunction_counit_of_full J K f O)

end Stacks.SheafOfModules

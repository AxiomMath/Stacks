module

public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules

import StacksCore.Tactic.StacksAttribute

/-!
# The stalks of the skyscraper sheaf of modules

Let `X` be a topological space, `𝒪_X` a sheaf of commutative rings on `X`, `z` a point of `X`
and `V` an `𝒪_{X,z}`-module. This file computes every stalk of the skyscraper sheaf of
`𝒪_X`-modules `i_{z,*} V` of `Stacks.Modules.skyscraper`, which is the case of sheaves of modules
in [Stacks Project, Tag 009B]:

* at a point `y` of the closure of `{z}`, i.e. with `z ⤳ y`, the stalk is `V`, viewed as an
  `𝒪_{X,y}`-module through the specialization map `𝒪_{X,y} ⟶ 𝒪_{X,z}`
  (`Stacks.Modules.skyscraperStalkIsoOfSpecializes`);
* at a point `y` outside the closure of `{z}` the stalk is zero
  (`Stacks.Modules.isZero_skyscraper_stalk_of_not_specializes`).

The cases of sets, abelian groups and algebraic structures of 009B are Mathlib's
`skyscraperPresheafStalkOfSpecializes` and `skyscraperPresheafStalkOfNotSpecializes`.

## References

* [Stacks Project, Tag 009B](https://stacks.math.columbia.edu/tag/009B)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace Stacks.Modules

variable {X : TopCat.{u}} {z : X}

/-! ### Stalks of the underlying presheaf of abelian groups -/

/-- For `z ⤳ y`, the cocone on the neighbourhood diagram of `y` which evaluates a section of the
skyscraper at `z` at the proof that `z` lies in the neighbourhood. -/
noncomputable def skyscraperAbStalkCoconeOfSpecializes {y : X} (h : z ⤳ y) (V : Ab.{u}) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperAbPresheaf z V) where
  pt := V
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun g : PLift (z ∈ U.unop.1) → V =>
          g ⟨h.mem_open U.unop.1.isOpen U.unop.2⟩) (fun _ _ => rfl))
      naturality := fun _ _ _ => rfl }

/-- For `z ⤳ y`, evaluation of a germ at `y` of the skyscraper presheaf at `z`. -/
noncomputable def skyscraperAbStalkEvalOfSpecializes {y : X} (h : z ⤳ y) (V : Ab.{u}) :
    (skyscraperAbPresheaf z V).stalk y ⟶ V :=
  colimit.desc _ (skyscraperAbStalkCoconeOfSpecializes h V)

/-- Evaluating the germ at `y` of a section `g` over `U ∋ y` gives the value of `g` at the proof
of `z ∈ U`. -/
@[simp]
lemma skyscraperAbStalkEvalOfSpecializes_germ {y : X} (h : z ⤳ y) (V : Ab.{u}) (U : Opens X)
    (hU : y ∈ U) (g : (skyscraperAbPresheaf z V).obj (op U)) :
    skyscraperAbStalkEvalOfSpecializes h V ((skyscraperAbPresheaf z V).germ U y hU g) =
      g ⟨h.mem_open U.isOpen hU⟩ := by
  rw [← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (skyscraperAbStalkCoconeOfSpecializes h V) (op ⟨U, hU⟩)) g

/-- Away from the closure of `{z}`, every stalk of the skyscraper presheaf at `z` is zero. -/
lemma subsingleton_skyscraperAbPresheaf_stalk_of_not_specializes {y : X} (h : ¬z ⤳ y)
    (V : Ab.{u}) : Subsingleton ↑((skyscraperAbPresheaf z V).stalk y) := by
  obtain ⟨S, hS, hyS, hzS⟩ := not_specializes_iff_exists_open.mp h
  have key : ∀ m : ↑((skyscraperAbPresheaf z V).stalk y), m = 0 := by
    intro m
    obtain ⟨W, hW, g, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
    have hT : y ∈ W ⊓ ⟨S, hS⟩ := ⟨hW, hyS⟩
    rw [← map_zero ((skyscraperAbPresheaf z V).germ W y hW).hom]
    exact TopCat.Presheaf.germ_ext _ (W ⊓ ⟨S, hS⟩) hT (Opens.infLELeft _ _)
      (Opens.infLELeft _ _) (funext fun p => absurd p.down.2 hzS)
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-! ### Stalks of the skyscraper presheaf of modules -/

section Presheaf

variable (O : X.Presheaf CommRingCat.{u}) (V : ModuleCat.{u} ↑(O.stalk z))

attribute [local instance] skyscraperModuleSections

/-- For `z ⤳ y`, the stalk at `y` of the skyscraper presheaf of modules at `z` with value `V` is
`V`, as an `𝒪_y`-module through the specialization map `𝒪_y ⟶ 𝒪_z`. -/
noncomputable def skyscraperPresheafStalkLinearEquivOfSpecializes {y : X} (h : z ⤳ y) :
    ↑(TopCat.Presheaf.stalk (skyscraperPresheaf O z V).presheaf y) ≃ₗ[↑(O.stalk y)]
      ↑((ModuleCat.restrictScalars (O.stalkSpecializes h).hom).obj V) where
  toFun := skyscraperAbStalkEvalOfSpecializes h (AddCommGrpCat.of ↑V)
  invFun v := (skyscraperAbPresheaf z (AddCommGrpCat.of ↑V)).germ ⊤ y trivial
    (fun _ => v : PLift (z ∈ (⊤ : Opens X)) → ↑V)
  map_add' := map_add (skyscraperAbStalkEvalOfSpecializes h (AddCommGrpCat.of ↑V)).hom
  map_smul' r m := by
    obtain ⟨U, hU, r', rfl⟩ := TopCat.Presheaf.exists_germ_eq O r
    obtain ⟨W, hW, s, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (skyscraperPresheaf O z V).presheaf m
    have hT : y ∈ U ⊓ W := ⟨hU, hW⟩
    rw [← O.germ_res_apply (Opens.infLELeft U W) y hT r',
      ← TopCat.Presheaf.germ_res_apply _ (Opens.infLERight U W) y hT s, RingHom.id_apply]
    refine Eq.trans (congrArg (fun x => skyscraperAbStalkEvalOfSpecializes h
      (AddCommGrpCat.of ↑V) x) (PresheafOfModules.germ_smul (skyscraperPresheaf O z V) y
        (U ⊓ W) hT _ _).symm) ?_
    refine (skyscraperAbStalkEvalOfSpecializes_germ h _ (U ⊓ W) hT _).trans ?_
    exact (congrArg (fun v : ↑V => O.germ (U ⊓ W) z (h.mem_open (U ⊓ W).isOpen hT)
      (O.map (Opens.infLELeft U W).op r') • v)
      (skyscraperAbStalkEvalOfSpecializes_germ h _ (U ⊓ W) hT _).symm).trans
      (congrArg (fun c : ↑(O.stalk z) => c • (skyscraperAbStalkEvalOfSpecializes h
        (AddCommGrpCat.of ↑V) (TopCat.Presheaf.germ (skyscraperPresheaf O z V).presheaf (U ⊓ W) y
          hT ((skyscraperPresheaf O z V).presheaf.map (Opens.infLERight U W).op s)) : ↑V))
        (TopCat.Presheaf.germ_stalkSpecializes_apply O hT h
          (O.map (Opens.infLELeft U W).op r')).symm)
  left_inv m := by
    obtain ⟨U, hU, g, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (skyscraperPresheaf O z V).presheaf m
    refine (congrArg (fun v => (skyscraperAbPresheaf z (AddCommGrpCat.of ↑V)).germ ⊤ y trivial
      (fun _ => v : PLift (z ∈ (⊤ : Opens X)) → ↑V))
      (skyscraperAbStalkEvalOfSpecializes_germ h _ U hU g)).trans ?_
    exact TopCat.Presheaf.germ_ext _ U hU (homOfLE le_top) (𝟙 U) (funext fun _ => rfl)
  right_inv v := skyscraperAbStalkEvalOfSpecializes_germ h _ ⊤ trivial _

end Presheaf

/-! ### Stalks of the skyscraper sheaf of modules -/

variable (R : TopCat.Sheaf CommRingCat.{u} X) (V : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj z))

attribute [local instance] stalkModule

/-- **Stacks 009B for sheaves of modules, on the closure of `{z}`.** For `z ⤳ y`, i.e. `y` in the
closure of `{z}`, the stalk at `y` of the skyscraper sheaf of `𝒪_X`-modules at `z` with value
`V` is `V`, as an `𝒪_{X,y}`-module through the specialization map `𝒪_{X,y} ⟶ 𝒪_{X,z}`. -/
@[stacks 009B "sheaves of modules, stalk at a point `y` of the closure of `{z}`, i.e. `z ⤳ y`: \
  it is `V`, an `𝒪_{X,y}`-module through the specialization map `𝒪_{X,y} ⟶ 𝒪_{X,z}`"]
noncomputable def skyscraperStalkIsoOfSpecializes {y : X} (h : z ⤳ y) :
    ModuleCat.of ↑(TopCat.Presheaf.stalk R.obj y)
        ↑(TopCat.Presheaf.stalk (skyscraper R z V).val.presheaf y) ≅
      (ModuleCat.restrictScalars (TopCat.Presheaf.stalkSpecializes R.obj h).hom).obj V :=
  (skyscraperPresheafStalkLinearEquivOfSpecializes R.obj V h).toModuleIso

/-- The isomorphism `skyscraperStalkIsoOfSpecializes` sends the germ at `y` of a section `g`
over `U ∋ y` to the value of `g` at the proof of `z ∈ U`. -/
lemma skyscraperStalkIsoOfSpecializes_hom_germ {y : X} (h : z ⤳ y) (U : Opens X) (hU : y ∈ U)
    (g : ↑((skyscraper R z V).val.presheaf.obj (op U))) :
    (skyscraperStalkIsoOfSpecializes R V h).hom
        (TopCat.Presheaf.germ (skyscraper R z V).val.presheaf U y hU g) =
      g ⟨h.mem_open U.isOpen hU⟩ :=
  skyscraperAbStalkEvalOfSpecializes_germ h _ U hU g

/-- **Stacks 009B for sheaves of modules, off the closure of `{z}`.** For `y` not in the closure
of `{z}`, i.e. `¬ z ⤳ y`, the stalk at `y` of the skyscraper sheaf of `𝒪_X`-modules at `z` is
zero. -/
@[stacks 009B "sheaves of modules, stalk at a point `y` outside the closure of `{z}`, i.e. \
  `¬ z ⤳ y`: it is zero"]
lemma isZero_skyscraper_stalk_of_not_specializes {y : X} (h : ¬z ⤳ y) :
    IsZero (ModuleCat.of ↑(TopCat.Presheaf.stalk R.obj y)
      ↑(TopCat.Presheaf.stalk (skyscraper R z V).val.presheaf y)) :=
  haveI : Subsingleton ↑(TopCat.Presheaf.stalk (skyscraper R z V).val.presheaf y) :=
    subsingleton_skyscraperAbPresheaf_stalk_of_not_specializes h (AddCommGrpCat.of ↑V)
  ModuleCat.isZero_of_subsingleton _

end Stacks.Modules

end

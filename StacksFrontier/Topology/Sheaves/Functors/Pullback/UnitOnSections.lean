module

public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SectionsAndStalks

/-!
# The unit of the inverse-image/direct-image adjunction, on sections

For a continuous map `f : X ⟶ Y` and a sheaf `F` on `Y` with values in a concrete category `C`,
`Stacks.Topology.ambientSection` takes a section of `F` on an open `U ⊆ Y` to a section of
`f⁻¹ F` on an open of `X` contained in `f⁻¹ U`, and `Stacks.Topology.germ_ambientSection` computes
its germs. The map of `Mathlib`'s *abstract* adjunction
`TopCat.Sheaf.pullbackPushforwardAdjunction` — the one out of which the base change morphism of
`Stacks.Cohomology.BaseChange.abelianSheafBaseChange` is built as a mate — is a different term,
and nothing related the two.

This file identifies them: `Stacks.Topology.ambientSection_eq_unit`. The missing step was the
value of the unit of the *constructed* adjunction
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` on sections, which
`Stacks.Topology.pullbackConstruction_unit` had for sheaves of **sets** only (by `rfl`, which does
not survive to general coefficients). It is supplied here at arbitrary coefficients, and in fact
over an arbitrary site:
`Stacks.Topology.sheafPullbackConstruction_unit_map`.

## Main results

* `Stacks.Topology.sheafPullbackConstruction_unit_map`: over an arbitrary site and at arbitrary
  coefficients, the unit of the adjunction built from the left Kan extension is the unit of the
  presheaf adjunction followed by sheafification.
* `Stacks.Topology.pullbackConstruction_unit_hom`, `…_app`: the same for `TopCat`, and read on one
  open.
* `Stacks.Topology.ambientSection_eq_unit`: **`ambientSection f F (le_refl _)` is the unit of the
  abstract adjunction, read on sections.**
* `Stacks.Topology.germ_unit_app`: hence the germ of the unit of the abstract adjunction applied
  to a section `s` of `F` is the image of the germ of `s` under the stalk comparison. This is the
  form in which a germwise computation with the abstract adjunction — such as the one proper base
  change for abelian sheaves needs — consumes the unit.

## Implementation notes

`CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app`, out of which
`sheafPullbackConstruction_unit_map` is proved, leaves behind the two comparison isomorphisms of
`CategoryTheory.Adjunction.restrictFullyFaithful`, which the sheaf-pullback construction supplies
as `Iso.refl`. Those `Iso.refl`s sit at a *crossing*: the two sides of each are definitionally but
not syntactically equal (`iD ⋙ R'` against `R ⋙ iC`, the first spelled with
`CategoryTheory.Functor.sheafPushforwardContinuous` and the second through
`CategoryTheory.sheafToPresheaf`), so `Iso.refl_hom` is not type-correct at the `implicit`
transparency level `simp` works at and neither `simp` nor `aesop_cat` can discharge the two
residual identities. Unfolding `Functor.sheafPushforwardContinuous` and `ObjectProperty.lift` by
`dsimp only` makes the two spellings coincide, after which `simp` closes it.

## References

* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

noncomputable section

/-! ### The constructed adjunction, over an arbitrary site -/

section Site

variable {Cc : Type*} [Category Cc] {Dd : Type*} [Category Dd] (G : Cc ⥤ Dd)
  (A : Type*) [Category A] (J : GrothendieckTopology Cc) (K : GrothendieckTopology Dd)
  [G.IsContinuous J K] [∀ P : Ccᵒᵖ ⥤ A, G.op.HasLeftKanExtension P] [HasWeakSheafify K A]

/-- **The unit of the sheaf-pullback adjunction built from the left Kan extension is the unit of
the presheaf adjunction followed by sheafification**, over an arbitrary site and at arbitrary
coefficients.

`Stacks.Topology.pullbackConstruction_unit` is this statement for sheaves of sets on a topological
space, where it holds by `rfl`; it does not hold by `rfl` at general coefficients, composition of
morphisms there not being composition of functions. -/
theorem sheafPullbackConstruction_unit_map (F : Sheaf J A) :
    (sheafToPresheaf J A).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app F) =
      (G.op.lanAdjunction A).unit.app F.obj ≫
        ((Functor.whiskeringLeft Ccᵒᵖ Ddᵒᵖ A).obj G.op).map
          (CategoryTheory.toSheafify K (G.op.lan.obj F.obj)) := by
  refine Eq.trans (Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ F) ?_
  dsimp only [Functor.sheafPushforwardContinuous,
    Functor.sheafPullbackConstruction.sheafPullback, ObjectProperty.lift,
    Functor.id_comp, Functor.comp_id, Functor.comp_obj]
  simp [Adjunction.comp_unit_app]

end Site

/-! ### Sheaves on a topological space -/

universe v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- `sheafPullbackConstruction_unit_map` for sheaves on a topological space. -/
theorem pullbackConstruction_unit_hom (F : Y.Sheaf C) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) C
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app F).hom =
      (Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf ≫
        (Presheaf.pushforward C f).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (inverseImagePresheaf f F)) :=
  sheafPullbackConstruction_unit_map (Opens.map f) C (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) F

/-- `pullbackConstruction_unit_hom` read on one open of `Y`. -/
theorem pullbackConstruction_unit_app (F : Y.Sheaf C) (U : Opens Y) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) C
          (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app F).hom.app (op U) =
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (inverseImagePresheaf f F)).app (op ((Opens.map f).obj U)) :=
  NatTrans.congr_app (pullbackConstruction_unit_hom f F) (op U)

/-- **The canonical map on sections of an inverse image sheaf is the unit of the
inverse-image/direct-image adjunction.** Taken on the whole inverse image `f⁻¹ U` of the open `U`,
`Stacks.Topology.ambientSection` is the component at `U` of the unit of
`TopCat.Sheaf.pullbackPushforwardAdjunction`.

This is what makes the germ computation `Stacks.Topology.germ_ambientSection` available to a
consumer of the abstract adjunction — in particular to the mate
`Stacks.Cohomology.BaseChange.abelianSheafBaseChange`, whose transpose is that unit. -/
theorem ambientSection_eq_unit (F : Y.Sheaf C) (U : Opens Y) :
    ambientSection f F (le_refl ((Opens.map f).obj U)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op U) := by
  have cancel : ∀ {P Q R : C} (a : P ⟶ Q) (h : Q ⟶ R) (h' : R ⟶ Q),
      h ≫ h' = 𝟙 Q → (a ≫ h) ≫ h' = a := by
    intro P Q R a h h' hh
    rw [Category.assoc, hh, Category.comp_id]
  have idl : ∀ {P Q R : C} (a : P ⟶ Q) (b : Q ⟶ R), a ≫ 𝟙 Q ≫ b = a ≫ b := by
    intro P Q R a b
    rw [Category.id_comp]
  have hstar :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op U) ≫
          (sheafPullbackPresheafIso f F).hom.app (op ((Opens.map f).obj U)) =
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) C
            (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app F).hom.app (op U) :=
    NatTrans.congr_app (congrArg (·.hom) (unit_comp_map_pullbackIso_hom f F)) (op U)
  have hback :
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) C
            (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app F).hom.app (op U) ≫
          (sheafPullbackPresheafIso f F).inv.app (op ((Opens.map f).obj U)) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op U) := by
    rw [← hstar]
    exact cancel _ _ _ (Iso.hom_inv_id_app _ _)
  have h1 : ambientSection f F (le_refl ((Opens.map f).obj U)) =
      (((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (inverseImagePresheaf f F)).app (op ((Opens.map f).obj U))) ≫
        (sheafPullbackPresheafIso f F).inv.app (op ((Opens.map f).obj U)) := by
    simp only [ambientSection, Category.assoc]
    rw [show (inverseImagePresheaf f F).map (homOfLE (le_refl ((Opens.map f).obj U))).op = 𝟙 _
        from CategoryTheory.Functor.map_id _ _]
    exact idl _ _
  exact h1.trans
    ((congrArg
      (fun m : F.presheaf.obj (op U) ⟶
          (CategoryTheory.sheafify (Opens.grothendieckTopology X)
            (inverseImagePresheaf f F)).obj (op ((Opens.map f).obj U)) ↦
        m ≫ (sheafPullbackPresheafIso f F).inv.app (op ((Opens.map f).obj U)))
      (pullbackConstruction_unit_app f F U).symm).trans hback)

/-- **The germ of the unit of the adjunction applied to a section.** The germ at `x` of the
section of `f⁻¹ F` that the unit produces out of a section `s` of `F` on `U` is the image, under
the stalk comparison `Stacks.Topology.ambientStalkHom`, of the germ of `s` at `f x`.

This is `Stacks.Topology.germ_ambientSection` stated for the abstract adjunction, which is the
form in which a germwise computation with `TopCat.Sheaf.pullbackPushforwardAdjunction` consumes
it. -/
theorem germ_unit_app (F : Y.Sheaf C) (U : Opens Y) (x : X) (hx : (f : X → Y) x ∈ U)
    (s : ToType (F.presheaf.obj (op U))) :
    ((TopCat.Sheaf.pullback C f).obj F).presheaf.germ ((Opens.map f).obj U) x hx
        (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op U) s) =
      ambientStalkHom f F x (F.presheaf.germ U (f x) hx s) := by
  rw [← ambientSection_eq_unit f F U]
  exact germ_ambientSection f F (le_refl ((Opens.map f).obj U)) x hx s

end

end Stacks.Topology

end

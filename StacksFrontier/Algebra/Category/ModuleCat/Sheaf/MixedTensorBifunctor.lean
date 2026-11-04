module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MixedBaseChangeTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.BaseChangeSecondVariable

/-!
# The mixed tensor product as a bifunctor

Let `f : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site.  For a (pre)sheaf `H`
of `O₂`-modules and a (pre)sheaf `G` of `O₁`-modules, the tensor product `H ⊗_{O₁} G` over the
smaller sheaf of rings is a (pre)sheaf of `O₂`-modules through its first factor
(`Stacks.MixedBaseChange.mixedTensorObj`).  This file makes it a bifunctor

`Mod(O₂) ⥤ Mod(O₁) ⥤ Mod(O₂)`,

additive in each variable, and shows that the `O₂`-linear cancellation of a base change

`H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G`

is natural in both variables.

## Main definitions

* `Stacks.MixedBaseChange.mixedMapRight`: the mixed tensor product with a morphism of second
  factors.
* `Stacks.MixedBaseChange.mixedTensor`: the mixed tensor product of presheaves of modules, as a
  bifunctor.
* `Stacks.MixedBaseChange.mixedSheafTensor`: the mixed tensor product of sheaves of modules, as
  a bifunctor: `(H, G) ↦ (H ⊗_{O₁} G)^#`.

## Main results

* `Stacks.MixedBaseChange.restrictScalars_mixedMapRight`: the restriction of scalars of the
  mixed tensor product with a morphism of second factors is the tensor product over `O₁` with
  it, by definition.
* `Stacks.MixedBaseChange.mixedBaseChange_naturality_snd` and
  `mixedSheafBaseChange_naturality_snd`: the `O₂`-linear cancellation of a base change is
  natural in the second factor, for presheaves and for sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w

namespace Stacks.MixedBaseChange

open Stacks Stacks.FlatChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (f : O₁ ⟶ O₂)

/-- An isomorphism conjugates a commuting square into a commuting square. -/
lemma conj_square {D : Type*} [Category D] {A B A' B' : D} (e : A ≅ B) (e' : A' ≅ B')
    {s : B ⟶ B'} {t : A ⟶ A'} (h : e.hom ≫ s = t ≫ e'.hom) : s ≫ e'.inv = e.inv ≫ t := by
  rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Two commuting squares pasted along a common edge. -/
lemma paste_squares {D : Type*} [Category D] {A B C' A' B' C'' : D}
    {s : A ⟶ A'} {a : A ⟶ B} {a' : A' ⟶ B'} {t : B ⟶ B'} {b : B ⟶ C'} {b' : B' ⟶ C''}
    {m : C' ⟶ C''} (h₁ : s ≫ a' = a ≫ t) (h₂ : t ≫ b' = b ≫ m) :
    s ≫ a' ≫ b' = (a ≫ b) ≫ m := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-! ## The second variable, for presheaves of modules -/

section Presheaf

variable (H : PresheafOfModules.{w} (ringPresheaf O₂.obj))

/-- **The mixed tensor product of `H` with a morphism `γ : G ⟶ G'` of second factors**: on
sections it is `id ⊗ γ`, which is `O₂(X)`-linear because the `O₂(X)`-action is through the first
factor. -/
noncomputable def mixedMapRight {G G' : PresheafOfModules.{w} (ringPresheaf O₁.obj)}
    (γ : G ⟶ G') : mixedTensorObj f H G ⟶ mixedTensorObj f H G' where
  app X := by
    letI : Module ((ringPresheaf O₂.obj).obj X)
        ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X) := sectionModule f H G X
    letI : Module ((ringPresheaf O₂.obj).obj X)
        ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G'.obj X) :=
      sectionModule f H G' X
    refine ModuleCat.ofHom (X := mixedObj f H G X) (Y := mixedObj f H G' X)
      (show ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X)
          →ₗ[(ringPresheaf O₂.obj).obj X]
          ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G'.obj X) from
        { toFun := TensorProduct.map LinearMap.id (γ.app X).hom
          map_add' := map_add _
          map_smul' := ?_ })
    intro s t
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
    | tmul a x => rfl
  naturality := by
    intro X Y g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact hom_apply_congr ((tensorMapRight (restrict f H) γ).naturality g) t

/-- **The restriction of scalars of `mixedMapRight` is the tensor product over `O₁` with the
same morphism**, by definition. -/
theorem restrictScalars_mixedMapRight {G G' : PresheafOfModules.{w} (ringPresheaf O₁.obj)}
    (γ : G ⟶ G') :
    (PresheafOfModules.restrictScalars (ringPresheafMap f)).map (mixedMapRight f H γ) =
      tensorMapRight (restrict f H) γ :=
  rfl

/-- The restriction of scalars of `mixedHom` is the tensor product over `O₁` of the restriction,
by definition. -/
theorem restrictScalars_mixedHom (G : PresheafOfModules.{w} (ringPresheaf O₁.obj))
    {H H' : PresheafOfModules.{w} (ringPresheaf O₂.obj)} (φ : H ⟶ H') :
    (PresheafOfModules.restrictScalars (ringPresheafMap f)).map (mixedHom f G φ) =
      (tensorRight G).map ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ) :=
  rfl

end Presheaf

/-- Tensoring with the identity of the second factor is the identity. -/
lemma tensorMapRight_id {O : Cᵒᵖ ⥤ CommRingCat.{w}} (M N : PresheafOfModules.{w} (ringPresheaf O)) :
    tensorMapRight M (𝟙 N) = 𝟙 (tensorObj M N) := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  exact TensorProduct.map_id

/-- Tensoring over a presheaf of rings is additive in the second variable. -/
lemma tensorMapRight_add {O : Cᵒᵖ ⥤ CommRingCat.{w}} (M : PresheafOfModules.{w} (ringPresheaf O))
    {N N' : PresheafOfModules.{w} (ringPresheaf O)} (α β : N ⟶ N') :
    tensorMapRight M (α + β) = tensorMapRight M α + tensorMapRight M β := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  exact TensorProduct.map_add_right _ _ _

/-- Tensoring over a presheaf of rings is additive in the first variable. -/
lemma tensorRight_map_add {O : Cᵒᵖ ⥤ CommRingCat.{w}} (N : PresheafOfModules.{w} (ringPresheaf O))
    {M M' : PresheafOfModules.{w} (ringPresheaf O)} (α β : M ⟶ M') :
    (tensorRight N).map (α + β) = (tensorRight N).map α + (tensorRight N).map β := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  exact TensorProduct.map_add_left _ _ _

/-! ## The bifunctor, for presheaves of modules -/

section Bifunctor

/-- The mixed tensor product in the first and in the second variable commute. -/
lemma mixedTensor_naturality {H H' : PresheafOfModules.{w} (ringPresheaf O₂.obj)} (φ : H ⟶ H')
    {G G' : PresheafOfModules.{w} (ringPresheaf O₁.obj)} (γ : G ⟶ G') :
    mixedMapRight f H γ ≫ mixedHom f G' φ = mixedHom f G φ ≫ mixedMapRight f H' γ := by
  have h : tensorMapRight (restrict f H) γ ≫
        (tensorRight G').map ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ) =
      (tensorRight G).map ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ) ≫
        tensorMapRight (restrict f H') γ :=
    ((tensorRightNatTrans γ).naturality
      ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ)).symm
  apply (PresheafOfModules.restrictScalars (ringPresheafMap f)).map_injective
  rw [Functor.map_comp, Functor.map_comp, restrictScalars_mixedMapRight,
    restrictScalars_mixedMapRight, restrictScalars_mixedHom, restrictScalars_mixedHom]
  exact h

/-- **The mixed tensor product of presheaves of modules, as a bifunctor**:
`(H, G) ↦ H ⊗_{O₁} G`, a presheaf of `O₂`-modules. -/
noncomputable def mixedTensor :
    PresheafOfModules.{w} (ringPresheaf O₂.obj) ⥤
      PresheafOfModules.{w} (ringPresheaf O₁.obj) ⥤ PresheafOfModules.{w} (ringPresheaf O₂.obj)
    where
  obj H :=
    { obj G := mixedTensorObj f H G
      map γ := mixedMapRight f H γ
      map_id G := by
        apply (PresheafOfModules.restrictScalars (ringPresheafMap f)).map_injective
        rw [(PresheafOfModules.restrictScalars (ringPresheafMap f)).map_id]
        exact tensorMapRight_id (restrict f H) G
      map_comp γ γ' := (PresheafOfModules.restrictScalars (ringPresheafMap f)).map_injective
        ((tensorMapRight_comp (restrict f H) γ γ').symm.trans
          ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map_comp
            (mixedMapRight f H γ) (mixedMapRight f H γ')).symm) }
  map {H H'} φ :=
    { app G := mixedHom f G φ
      naturality G G' γ := mixedTensor_naturality f φ γ }
  map_id H := NatTrans.ext (funext fun G ↦ (mixedTensorRight f G).map_id H)
  map_comp φ ψ := NatTrans.ext (funext fun G ↦ (mixedTensorRight f G).map_comp φ ψ)

/-- The mixed tensor product with a fixed first factor is additive. -/
instance mixedTensor_obj_additive (H : PresheafOfModules.{w} (ringPresheaf O₂.obj)) :
    ((mixedTensor f).obj H).Additive where
  map_add {_G _G'} {α β} := (PresheafOfModules.restrictScalars (ringPresheafMap f)).map_injective
    ((tensorMapRight_add (restrict f H) α β).trans
      ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map_add
        (f := mixedMapRight f H α) (g := mixedMapRight f H β)).symm)

/-- The mixed tensor product with a fixed second factor is additive. -/
instance mixedTensorRight_additive (G : PresheafOfModules.{w} (ringPresheaf O₁.obj)) :
    (mixedTensorRight f G).Additive where
  map_add {_H _H'} {α β} := (PresheafOfModules.restrictScalars (ringPresheafMap f)).map_injective
    ((congrArg (tensorRight G).map
        ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map_add (f := α) (g := β))).trans
      ((tensorRight_map_add G _ _).trans
        ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map_add
          (f := mixedHom f G α) (g := mixedHom f G β)).symm))

/-- The mixed tensor product is additive in its first variable. -/
instance mixedTensor_additive : (mixedTensor f).Additive where
  map_add {_H _H'} {α β} := NatTrans.ext (funext fun G ↦
    (mixedTensorRight_additive f G).map_add (f := α) (g := β))

/-- **The `O₂`-linear cancellation of a base change is natural in the second factor**, for
presheaves of modules.  Both sides are `O₂`-linear and their restrictions of scalars are the two
sides of `Stacks.Cohomology.MixedDerivedTensor.baseChange_naturality_snd`; restriction of scalars
is faithful. -/
lemma mixedBaseChange_naturality_snd (H : PresheafOfModules.{w} (ringPresheaf O₂.obj))
    {G G' : PresheafOfModules.{w} (ringPresheaf O₁.obj)} (γ : G ⟶ G') :
    tensorMapRight H ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).map γ) ≫
        (mixedBaseChange f H G').hom =
      (mixedBaseChange f H G).hom ≫ mixedMapRight f H γ := by
  apply (PresheafOfModules.restrictScalars (ringPresheafMap f)).map_injective
  rw [Functor.map_comp, Functor.map_comp, restrictScalars_mixedBaseChange,
    restrictScalars_mixedBaseChange, restrictScalars_mixedMapRight]
  exact Stacks.Cohomology.MixedDerivedTensor.baseChange_naturality_snd f γ H

end Bifunctor

/-! ## The bifunctor, for sheaves of modules -/

section Sheaf

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Sheafification of presheaves of modules is additive: it is a left adjoint. -/
instance moduleSheafification_additive (O : Sheaf J CommRingCat.{w}) :
    (moduleSheafification O : PresheafOfModules.{w} _ ⥤ SheafOfModules.{w} _).Additive :=
  have adj := PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  have : (moduleSheafification O :
      PresheafOfModules.{w} _ ⥤ SheafOfModules.{w} _).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _ adj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0}
      (moduleSheafification O : PresheafOfModules.{w} _ ⥤ SheafOfModules.{w} _) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts
      (moduleSheafification O : PresheafOfModules.{w} _ ⥤ SheafOfModules.{w} _) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- **The mixed tensor product of sheaves of modules, as a bifunctor**:
`(H, G) ↦ (H ⊗_{O₁} G)^#`, a sheaf of `O₂`-modules.  With `G` fixed it is
`Stacks.MixedBaseChange.mixedSheafTensorRight`. -/
noncomputable def mixedSheafTensor :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⥤
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) where
  obj H :=
    { obj G := (mixedSheafTensorRight f G).obj H
      map γ := (moduleSheafification O₂).map (mixedMapRight f H.val γ.val)
      map_id G := (congrArg (moduleSheafification O₂).map
          (((mixedTensor f).obj H.val).map_id G.val)).trans
        ((moduleSheafification O₂).map_id _)
      map_comp γ γ' := (congrArg (moduleSheafification O₂).map
          (((mixedTensor f).obj H.val).map_comp γ.val γ'.val)).trans
        ((moduleSheafification O₂).map_comp _ _) }
  map {_H _H'} φ :=
    { app G := (mixedSheafTensorRight f G).map φ
      naturality _G _G' γ := ((moduleSheafification O₂).map_comp _ _).symm.trans
        ((congrArg (moduleSheafification O₂).map (mixedTensor_naturality f φ.val γ.val)).trans
          ((moduleSheafification O₂).map_comp _ _)) }
  map_id H := NatTrans.ext (funext fun G ↦ (mixedSheafTensorRight f G).map_id H)
  map_comp φ ψ := NatTrans.ext (funext fun G ↦ (mixedSheafTensorRight f G).map_comp φ ψ)

/-- The mixed tensor product of sheaves with a fixed second factor is additive. -/
instance mixedSheafTensorRight_additive
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) :
    (mixedSheafTensorRight f G).Additive where
  map_add {_H _H'} {α β} :=
    (congrArg (moduleSheafification O₂).map
      ((congrArg (mixedTensorRight f G.val).map
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).map_add
          (f := α) (g := β))).trans
          (mixedTensorRight_additive f G.val).map_add)).trans (moduleSheafification O₂).map_add

/-- The mixed tensor product of sheaves with a fixed first factor is additive. -/
instance mixedSheafTensor_obj_additive
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((mixedSheafTensor f).obj H).Additive where
  map_add {_G _G'} {α β} :=
    (congrArg (moduleSheafification O₂).map
      ((congrArg ((mixedTensor f).obj H.val).map
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₁)).map_add
          (f := α) (g := β))).trans
          (mixedTensor_obj_additive f H.val).map_add)).trans (moduleSheafification O₂).map_add

/-- The mixed tensor product of sheaves is additive in its first variable. -/
instance mixedSheafTensor_additive : (mixedSheafTensor f).Additive where
  map_add {_H _H'} {α β} := NatTrans.ext (funext fun G ↦
    (mixedSheafTensorRight_additive f G).map_add (f := α) (g := β))

/-- **The `O₂`-linear cancellation of a base change is natural in the second factor**, for
sheaves of modules: for `γ : G ⟶ G'` and a sheaf `H` of `O₂`-modules, the isomorphism
`H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G` commutes with the maps induced by `γ`.

Two squares are pasted: the naturality of the unit of sheafification at the sectionwise
extension of scalars, and the presheaf-level `mixedBaseChange_naturality_snd`. -/
lemma mixedSheafBaseChange_naturality_snd
    {G G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)} (γ : G ⟶ G')
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₂).obj H).map
          ((extendScalars f).map γ) ≫
        (mixedSheafBaseChangeNatIso f G').hom.app H =
      (mixedSheafBaseChangeNatIso f G).hom.app H ≫ ((mixedSheafTensor f).obj H).map γ := by
  have hA := map_comp_eq_map_comp (moduleSheafification O₂)
    ((tensorMapRight_comp H.val (toExtendScalarsVal f G) ((extendScalars f).map γ).val).trans
      ((congrArg (fun z ↦ tensorMapRight H.val z)
        ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.naturality
            ((presheafExtendScalars f).map γ.val)).symm).trans
        (tensorMapRight_comp H.val ((presheafExtendScalars f).map γ.val)
          (toExtendScalarsVal f G')).symm))
  have hB : (moduleSheafification O₂).map
          (tensorMapRight H.val ((presheafExtendScalars f).map γ.val)) ≫
        (moduleSheafification O₂).map (mixedBaseChange f H.val G'.val).hom =
      (moduleSheafification O₂).map (mixedBaseChange f H.val G.val).hom ≫
        (moduleSheafification O₂).map (mixedMapRight f H.val γ.val) :=
    map_comp_eq_map_comp _ (mixedBaseChange_naturality_snd f H.val γ.val)
  exact paste_squares (conj_square ((tensorRightExtendScalarsIso f G).app H.val)
    ((tensorRightExtendScalarsIso f G').app H.val) hA) hB

end Sheaf

end Stacks.MixedBaseChange

end

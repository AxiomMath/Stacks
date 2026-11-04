module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.SheafificationAndRestrictionOfScalars

/-!
# The cancellation of a base change, on pure tensors

`Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso` identifies, for a morphism
`α : O₁ ⟶ O₂` of sheaves of commutative rings, a sheaf `G` of `O₁`-modules and a sheaf `H` of
`O₂`-modules,

`H|_{O₁} ⊗_{O₁} G  ≅  (H ⊗_{O₂} (O₂ ⊗_{O₁} G))|_{O₁}`.

It is assembled from three isomorphisms — the sectionwise cancellation of a base change, the
comparison of the two sheafifications and the replacement of the sectionwise extension of scalars
by its sheafification — none of which is described on sections where it is defined. **This file
computes it on the image of a pure tensor**: `h ⊗ x ↦ h ⊗ η(x)`, `η` the unit of the
extension-restriction adjunction `Stacks.FlatChangeOfRings.extendScalarsAdjunction`.

That is the description the underived identity of [Stacks, Tag 08DE] needs in order to be compared
with a morphism that is not linear over the bigger ring, such as a de Rham differential.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.baseChange_inv_app_tmul`: the sectionwise cancellation of
  a base change, inverted, on a pure tensor.
* `Stacks.Cohomology.MixedDerivedTensor.sheafifyRestrictHom_val_app_unit`: the comparison of the
  two sheafifications on the image of a section.
* `Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso_hom_app_unit`: **the
  cancellation of a base change on the image of a pure tensor.**
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Stacks.Cohomology.MixedDerivedTensor

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (α : O₁ ⟶ O₂)

open scoped TensorProduct in
/-- **The sectionwise cancellation of a base change, inverted, on a pure tensor**:
`h ⊗_{O₁} x ↦ h ⊗_{O₂} (1 ⊗_{O₁} x)`. The isomorphism itself is
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which sends `h ⊗ (1 ⊗ x)` to `1 • h ⊗ x`. -/
theorem baseChange_inv_app_tmul (G : PresheafOfModules.{w} (ringPresheaf O₁.obj))
    (H : PresheafOfModules.{w} (ringPresheaf O₂.obj)) (X : Cᵒᵖ) (a : H.obj X) (x : G.obj X) :
    ((Stacks.FlatChangeOfRings.baseChange α G H).inv.app X).hom
        (show (tensorObj ((PresheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringPresheafMap α)).obj H) G).obj X from
          a ⊗ₜ[O₁.obj.obj X] x) =
      (show (tensorObj H ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α.hom).obj
          G)).obj X from
        letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (α.hom.app X).hom.toAlgebra
        a ⊗ₜ[O₂.obj.obj X] ((1 : O₂.obj.obj X) ⊗ₜ[O₁.obj.obj X] x)) :=
  rfl

end

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (α : O₁ ⟶ O₂)

/-- **The sheafification of a morphism of presheaves of modules, on the image of a section**: the
image of `z` is carried to the image of `ψ z`. This is the naturality of the sheafification unit,
read on an element. -/
theorem moduleSheafification_map_val_app_toSheafifyVal {O : Sheaf J CommRingCat.{w}}
    {M N : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj} (ψ : M ⟶ N)
    (U : Cᵒᵖ) (z : M.obj U) :
    (((Stacks.moduleSheafification O).map ψ).val.app U).hom ((toSheafifyVal M).app U z) =
      (toSheafifyVal N).app U (ψ.app U z) :=
  (congrArg (fun φ : M ⟶ ((Stacks.moduleSheafification O).obj N).val => (φ.app U).hom z)
    (toSheafifyVal_naturality ψ)).symm

/-- **The comparison of the two sheafifications on the image of a section**: the image of `z` in
the sheafification over `O₁` of the restriction of scalars of `M` is carried to its image in the
sheafification of `M` over `O₂`. This is the defining property of
`Stacks.Cohomology.MixedDerivedTensor.sheafifyRestrictHom`, its adjoint being the restricted
unit, read on an element. -/
theorem sheafifyRestrictHom_val_app_toSheafifyVal
    (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) (U : Cᵒᵖ)
    (z : M.obj U) :
    ((sheafifyRestrictHom α M).val.app U).hom
        ((toSheafifyVal ((PresheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap α).hom).obj M)).app U z) =
      (toSheafifyVal M).app U z := by
  have h := homEquiv_sheafifyRestrictHom α M
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun φ => (φ.app U).hom z) h

open scoped TensorProduct in
/-- **The unit of the extension-restriction adjunction on a section**: `x ↦ 1 ⊗ x`, followed by
the sheafification unit. The adjunction
`Stacks.FlatChangeOfRings.extendScalarsAdjunction` is the presheaf-level one composed with
sheafification and restricted to sheaves, so its unit is the presheaf-level unit
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply`) followed by the
unit of sheafification. -/
theorem extendScalarsAdjunction_unit_app_val_app
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) (U : Cᵒᵖ)
    (x : G.val.obj U) :
    (((Stacks.FlatChangeOfRings.extendScalarsAdjunction α).unit.app G).val.app U).hom x =
      letI := (α.hom.app U).hom.toAlgebra
      (toSheafifyVal ((Stacks.FlatChangeOfRings.presheafExtendScalars α).obj G.val)).app U
        ((1 : O₂.obj.obj U) ⊗ₜ[O₁.obj.obj U] x) := by
  have h : (SheafOfModules.forget _).map
      ((Stacks.FlatChangeOfRings.extendScalarsAdjunction α).unit.app G) = _ :=
    Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ G
  have h2 := congrArg (fun φ => (φ.app U).hom x) h
  exact h2.trans (congrArg
    (fun y => ((toSheafifyVal ((Stacks.FlatChangeOfRings.presheafExtendScalars α).obj G.val)).app
      U).hom y)
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply α.hom G.val U x))

open scoped TensorProduct in
/-- **The cancellation of a base change, on the image of a pure tensor**: for a section `a` of a
sheaf `H` of `O₂`-modules and a section `x` of a sheaf `G` of `O₁`-modules,

`a ⊗_{O₁} x  ↦  a ⊗_{O₂} η(x)`,

`η : G ⟶ (O₂ ⊗_{O₁} G)|_{O₁}` the unit of
`Stacks.FlatChangeOfRings.extendScalarsAdjunction`. The three isomorphisms
`Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso` is assembled from are crossed one
at a time: the sectionwise cancellation of the base change carries `a ⊗ x` to `a ⊗ (1 ⊗ x)`
(`Stacks.Cohomology.MixedDerivedTensor.baseChange_inv_app_tmul`), the comparison of the two
sheafifications keeps the image of a section
(`Stacks.Cohomology.MixedDerivedTensor.sheafifyRestrictHom_val_app_toSheafifyVal`), and the
replacement of the sectionwise extension of scalars by its sheafification applies the
sheafification unit to `1 ⊗ x`, which is `η(x)`
(`Stacks.Cohomology.MixedDerivedTensor.extendScalarsAdjunction_unit_app_val_app`). -/
theorem tensorBaseChangeLinearIso_hom_app_val_app_toSheafifyVal
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) (U : Cᵒᵖ)
    (a : H.val.obj U) (x : G.val.obj U) :
    (((tensorBaseChangeLinearIso α G).hom.app H).val.app U).hom
        ((toSheafifyVal (tensorObj ((SheafOfModules.restrictScalars.{w}
          (Stacks.FlatChangeOfRings.ringSheafMap α)).obj H).val G.val)).app U
          (a ⊗ₜ[O₁.obj.obj U] x)) =
      (toSheafifyVal (tensorObj H.val ((Stacks.FlatChangeOfRings.extendScalars α).obj G).val)).app
        U (a ⊗ₜ[O₂.obj.obj U]
          (((Stacks.FlatChangeOfRings.extendScalarsAdjunction α).unit.app G).val.app U).hom x) := by
  let := (α.hom.app U).hom.toAlgebra
  have e1 := moduleSheafification_map_val_app_toSheafifyVal (O := O₁)
    ((Stacks.FlatChangeOfRings.baseChangeNatIsoOf α G).inv.app H.val) U (a ⊗ₜ[O₁.obj.obj U] x)
  have e2 := sheafifyRestrictHom_val_app_toSheafifyVal α
    (tensorObj H.val ((Stacks.FlatChangeOfRings.presheafExtendScalars α).obj G.val)) U
    (a ⊗ₜ[O₂.obj.obj U] ((1 : O₂.obj.obj U) ⊗ₜ[O₁.obj.obj U] x))
  have e3 := moduleSheafification_map_val_app_toSheafifyVal (O := O₂)
    ((tensorRightNatTrans (Stacks.FlatChangeOfRings.toExtendScalarsVal α G)).app H.val) U
    (a ⊗ₜ[O₂.obj.obj U] ((1 : O₂.obj.obj U) ⊗ₜ[O₁.obj.obj U] x))
  have e4 := extendScalarsAdjunction_unit_app_val_app α G U x
  refine (congrArg _ (congrArg _ e1)).trans ((congrArg _ e2).trans (e3.trans ?_))
  exact congrArg (fun y => (toSheafifyVal (tensorObj H.val
    ((Stacks.FlatChangeOfRings.extendScalars α).obj G).val)).app U (a ⊗ₜ[O₂.obj.obj U] y)) e4.symm

end Sheafify

/-! ### The underived identity of [Stacks, Tag 08DE] on pure tensors -/

section Tag08I6

open StacksPullbackFactorization

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)

/-- **The comparison `f⁻¹G ⟶ (f^*G)|_{f⁻¹O'}` through which the underived identity of
[Stacks, Tag 08DE] acts on the second factor**: the unit of the extension of scalars along
`f⁻¹O' ⟶ O`, followed by the identification
`Stacks.Cohomology.MixedDerivedTensor.pullbackIsoExtendInverseImage` of that extension with
`f^*G`. -/
def inverseImageToPullbackTopos
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :
    (auxHomG f).pullbackTopos.obj G ⟶ (restrictToInvRing f).obj (f.pullbackTopos.obj G) :=
  (Stacks.FlatChangeOfRings.extendScalarsAdjunction ((auxHomH f).fSharp)).unit.app _ ≫
    (restrictToInvRing f).map (pullbackIsoExtendInverseImage f G).hom

open scoped TensorProduct in
/-- **The underived identity of [Stacks, Tag 08DE] on the image of a pure tensor**: for a section
`a` of a sheaf `F` of `O`-modules and a section `x` of `f⁻¹G`,

`a ⊗_{f⁻¹O'} x  ↦  a ⊗_O c(x)`,

`c : f⁻¹G ⟶ (f^*G)|_{f⁻¹O'}` the comparison
`Stacks.Cohomology.MixedDerivedTensor.inverseImageToPullbackTopos`. The identity is the
cancellation of a base change
(`Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso_hom_app_val_app_toSheafifyVal`)
followed by the identification of the extension of scalars of `f⁻¹G` with `f^*G` in the second
factor, which acts on the image of a pure tensor through the second entry. -/
theorem underivedTensorInverseImageLinearIso_hom_app_val_app_toSheafifyVal
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
    (U : X.Cᵒᵖ) (a : F.val.obj U) (x : ((auxHomG f).pullbackTopos.obj G).val.obj U) :
    (((underivedTensorInverseImageLinearIso f G).hom.app F).val.app U).hom
        ((toSheafifyVal (tensorObj ((restrictToInvRing f).obj F).val
          ((auxHomG f).pullbackTopos.obj G).val)).app U (a ⊗ₜ[(invRing f).obj.obj U] x)) =
      (toSheafifyVal (tensorObj F.val (f.pullbackTopos.obj G).val)).app U
        (a ⊗ₜ[X.O.obj.obj U] ((inverseImageToPullbackTopos f G).val.app U).hom x) := by
  refine Eq.trans (congrArg (fun y =>
      (((restrictToInvRing f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.map
          (pullbackIsoExtendInverseImage f G).hom).app F)).val.app U).hom y)
    (tensorBaseChangeLinearIso_hom_app_val_app_toSheafifyVal ((auxHomH f).fSharp)
      ((auxHomG f).pullbackTopos.obj G) F U a x)) ?_
  exact moduleSheafification_map_val_app_toSheafifyVal (O := X.O)
    (tensorMapRight F.val (pullbackIsoExtendInverseImage f G).hom.val) U _

/-- **The comparison `f⁻¹G ⟶ (f^*G)|_{f⁻¹O'}` is the transpose of the unit of `f^* ⊣ f_*`**
along the geometric half `g^* ⊣ g_*` of the factorization: precomposed with the unit of
`g^* ⊣ g_*` and pushed forward, it is the unit of `f^* ⊣ f_*` read through
`StacksPullbackFactorization.pushforwardFactorIso`.

Both identifications that `Stacks.Cohomology.MixedDerivedTensor.inverseImageToPullbackTopos` is
built from are uniqueness of left adjoints, and the units of adjunctions related by
`CategoryTheory.Adjunction.leftAdjointUniq` correspond
(`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`); the rest is the naturality of
`StacksPullbackFactorization.pushforwardFactorIso`. -/
theorem unit_comp_pushforwardTopos_map_inverseImageToPullbackTopos
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :
    (auxHomG f).pullbackPushforwardAdjunctionTopos.unit.app G ≫
        (auxHomG f).pushforwardTopos.map (inverseImageToPullbackTopos f G) =
      f.pullbackPushforwardAdjunctionTopos.unit.app G ≫
        (pushforwardFactorIso f).inv.app (f.pullbackTopos.obj G) := by
  have h1 := Adjunction.unit_leftAdjointUniq_hom_app
    (Stacks.FlatChangeOfRings.extendScalarsAdjunction ((auxHomH f).fSharp))
    (auxHomH f).pullbackPushforwardAdjunctionTopos ((auxHomG f).pullbackTopos.obj G)
  have h2 := Adjunction.unit_leftAdjointUniq_hom_app
    (((auxHomG f).pullbackPushforwardAdjunctionTopos.comp
      (auxHomH f).pullbackPushforwardAdjunctionTopos).ofNatIsoRight (pushforwardFactorIso f))
    f.pullbackPushforwardAdjunctionTopos G
  have h3 : inverseImageToPullbackTopos f G =
      (auxHomH f).pullbackPushforwardAdjunctionTopos.unit.app ((auxHomG f).pullbackTopos.obj G) ≫
        (auxHomH f).pushforwardTopos.map ((pullbackFactorIso f).hom.app G) := by
    rw [← h1]
    simp only [inverseImageToPullbackTopos, pullbackIsoExtendInverseImage,
      extendScalarsIsoPullbackAuxHomH]
    rfl
  have h4 : (((auxHomG f).pullbackPushforwardAdjunctionTopos.comp
      (auxHomH f).pullbackPushforwardAdjunctionTopos).ofNatIsoRight
        (pushforwardFactorIso f)).unit.app G =
      ((auxHomG f).pullbackPushforwardAdjunctionTopos.comp
        (auxHomH f).pullbackPushforwardAdjunctionTopos).unit.app G ≫
        (pushforwardFactorIso f).hom.app _ := by
    have := Adjunction.homEquiv_ofNatIsoRight_apply ((auxHomG
        f).pullbackPushforwardAdjunctionTopos.comp
      (auxHomH f).pullbackPushforwardAdjunctionTopos) (pushforwardFactorIso f) (X := G)
      (𝟙 (((auxHomG f).pullbackTopos ⋙ (auxHomH f).pullbackTopos).obj G))
    rw [Adjunction.homEquiv_id, Adjunction.homEquiv_id] at this
    exact this
  refine (Iso.eq_comp_inv ((pushforwardFactorIso f).app (f.pullbackTopos.obj G))).2 ?_
  refine Eq.trans ?_ h2
  rw [h4, h3, Adjunction.comp_unit_app]
  simp only [Category.assoc]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg ((auxHomG f).pullbackPushforwardAdjunctionTopos.unit.app G ≫ ·) ?_
  refine Eq.trans (congrArg (· ≫ (pushforwardFactorIso f).hom.app (f.pullbackTopos.obj G))
    ((auxHomG f).pushforwardTopos.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg ((auxHomG f).pushforwardTopos.map
    ((auxHomH f).pullbackPushforwardAdjunctionTopos.unit.app ((auxHomG f).pullbackTopos.obj G)) ≫ ·)
    ?_
  exact (pushforwardFactorIso f).hom.naturality ((pullbackFactorIso f).hom.app G)

/-- **The comparison `f⁻¹G ⟶ (f^*G)|_{f⁻¹O'}` on a pullback-unit section**: the image under the
unit of `g^* ⊣ g_*` of a section `s` of `G` is carried to its image under the unit of
`f^* ⊣ f_*`. This is
`Stacks.Cohomology.MixedDerivedTensor.unit_comp_pushforwardTopos_map_inverseImageToPullbackTopos`
read on `s`; the comparison `StacksPullbackFactorization.pushforwardFactorIso` of the two
pushforwards does not move a section. -/
theorem inverseImageToPullbackTopos_val_app_unit
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
    (V : Y.Cᵒᵖ) (s : G.val.obj V) :
    ((inverseImageToPullbackTopos f G).val.app (Opposite.op (f.u.obj V.unop))).hom
        ((((auxHomG f).pullbackPushforwardAdjunctionTopos.unit.app G).val.app V).hom s) =
      ((f.pullbackPushforwardAdjunctionTopos.unit.app G).val.app V).hom s :=
  congrArg (fun φ : G ⟶ (auxHomG f).pushforwardTopos.obj
      ((restrictToInvRing f).obj (f.pullbackTopos.obj G)) => (φ.val.app V).hom s)
    (unit_comp_pushforwardTopos_map_inverseImageToPullbackTopos f G)

end Tag08I6

end Stacks.Cohomology.MixedDerivedTensor

end

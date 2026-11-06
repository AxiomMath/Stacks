module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectAugmentationFunctorLeft
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleSquare
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphismsTwoSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Descent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalIsSite

/-!
# Fppf hypercoverings of algebraic spaces: the square of ringed topoi

Let `T` be a big fppf site of algebraic spaces over `S`, `U` a simplicial object of it and
`a : U → X` an augmentation. The total site `(Spaces/U)_{fppf,total}` carries the structure sheaf
`𝒪_{big,total}`, `V/U_n ↦ Γ(V, 𝒪_V)`, the restriction of `𝒪_{big}` along `V/U_n ↦ V/X`. With it
the square of topoi of Stacks 0DH5 becomes a commutative square of ringed topoi (Stacks 0DHC).

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfTotalRingedTopos`: the ringed topos
  `(Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total})`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfAugmentationRingedHom`: the ringed
  augmentation `a_{fppf}`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfTotalRingedHom`: the morphism of ringed
  topoi `h`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace Stacks.Sites.CocontinuousExchange

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {A : Type u₅} [Category.{v₅} A]
  {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D}
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
  [∀ F : C'ᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F]
  (w : TwoSquare v' u' u v)

/-- **Structure maps across the exchange of Stacks 0FN1, on presheaves.** A map
`P_{D'} ⟶ Ran_{u'}(v'^p P_C)` adjoint to `ψ` factors through the base change transformation of the
square as soon as `ψ` is the composite of `χ : P_{D'} ⟶ v^p P_D`, the square and
`θ : u^p P_D ⟶ P_C`. -/
theorem ranAdjunction_unit_comp_eq_simplicialSmallEtaleBigFppfRinged
    {PD' : D'ᵒᵖ ⥤ A} {PD : Dᵒᵖ ⥤ A} {PC : Cᵒᵖ ⥤ A}
    (ψ : u'.op ⋙ PD' ⟶ v'.op ⋙ PC) (χ : PD' ⟶ v.op ⋙ PD) (θ : u.op ⋙ PD ⟶ PC)
    (H : ∀ V : C'ᵒᵖ, ψ.app V =
      χ.app (u'.op.obj V) ≫ PD.map (w.app V.unop).op ≫ θ.app (v'.op.obj V)) :
    (u'.op.ranAdjunction A).unit.app PD' ≫ u'.op.ran.map ψ =
      χ ≫ Functor.whiskerLeft v.op ((u.op.ranAdjunction A).unit.app PD ≫ u.op.ran.map θ) ≫
        w.op.ranBaseChange.app PC := by
  refine Functor.hom_ext_of_isRightKanExtension _ (u'.op.ranCounit.app _) _ _ ?_
  ext V
  have fac := Stacks.SheafOfModules.ranBaseChange_fac w.op PC V
  have n₁ := (u.op.ran.map θ).naturality (w.op.natTrans.app V)
  have u₁ := ((u.op.ranAdjunction A).unit.app PD).naturality (w.op.natTrans.app V)
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at u₁
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ran_map_app_ranCounit_app]
  rw [fac, ← reassoc_of% n₁, ← reassoc_of% u₁,
    AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ran_map_app_ranCounit_app u.op θ,
    Functor.ranCounit_app_app_ranAdjunction_unit_app_app_assoc, H V]
  exact (Functor.ranCounit_app_app_ranAdjunction_unit_app_app_assoc (L := u'.op) PD' V _).trans rfl

section Sheaf

variable (J' : GrothendieckTopology C') (J : GrothendieckTopology C) (K' : GrothendieckTopology D')
  (K : GrothendieckTopology D) [u.IsCocontinuous J K] [u'.IsCocontinuous J' K'] [u.IsContinuous J K]
  [u'.IsContinuous J' K'] [v.IsContinuous K' K] [v'.IsContinuous J' J] [w.GuitartExact]

/-- **Structure maps across the exchange of Stacks 0FN1.** For sheaves `O_{D'}`, `O_D`, `O_C` and
maps `ψ : u'^p O_{D'} ⟶ v'^p O_C`, `χ : O_{D'} ⟶ v^p O_D`, `θ : u^p O_D ⟶ O_C` with `ψ` the
composite of `χ`, the square and `θ`, the adjoint `O_{D'} ⟶ u'_* v'^p O_C` of `ψ` is carried by the
exchange isomorphism to `v^p` of the adjoint of `θ`, preceded by `χ`. -/
theorem sheafIso_unit_comp_eq_simplicialSmallEtaleBigFppfRinged
    {OD' : Sheaf K' A} {OD : Sheaf K A} {OC : Sheaf J A}
    (ψ : (u'.sheafPushforwardContinuous A J' K').obj OD' ⟶
      (v'.sheafPushforwardContinuous A J' J).obj OC)
    (χ : OD' ⟶ (v.sheafPushforwardContinuous A K' K).obj OD)
    (θ : (u.sheafPushforwardContinuous A J K).obj OD ⟶ OC)
    (H : ∀ V : C'ᵒᵖ, ψ.hom.app V =
      χ.hom.app (u'.op.obj V) ≫ OD.obj.map (w.app V.unop).op ≫ θ.hom.app (v'.op.obj V)) :
    (u'.sheafAdjunctionCocontinuous A J' K').unit.app OD' ≫
        (u'.sheafPushforwardCocontinuous A J' K').map ψ =
      (χ ≫ (v.sheafPushforwardContinuous A K' K).map
        ((u.sheafAdjunctionCocontinuous A J K).unit.app OD ≫
          (u.sheafPushforwardCocontinuous A J K).map θ)) ≫
        (sheafIsoOfTwoSquareAndMorphismsTwoSquare A J' J K' K w).inv.app OC := by
  refine ObjectProperty.hom_ext _ ?_
  show ((u'.sheafAdjunctionCocontinuous A J' K').unit.app OD').hom ≫ u'.op.ran.map ψ.hom =
    (χ.hom ≫ Functor.whiskerLeft v.op (((u.sheafAdjunctionCocontinuous A J K).unit.app OD).hom ≫
      u.op.ran.map θ.hom)) ≫
      ((sheafIsoOfTwoSquareAndMorphismsTwoSquare A J' J K' K w).inv.app OC).hom
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom,
    Functor.sheafAdjunctionCocontinuous_unit_app_hom,
    sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare]
  exact (ranAdjunction_unit_comp_eq_simplicialSmallEtaleBigFppfRinged w ψ.hom χ.hom θ.hom H).trans
    (Category.assoc _ _ _).symm

/-- The case `O_C = u^p O_D`, `θ = 𝟙` of
`sheafIso_unit_comp_eq_simplicialSmallEtaleBigFppfRinged`. -/
theorem sheafIso_unit_eq_simplicialSmallEtaleBigFppfRinged {OD' : Sheaf K' A} {OD : Sheaf K A}
    (ψ : (u'.sheafPushforwardContinuous A J' K').obj OD' ⟶
      (v'.sheafPushforwardContinuous A J' J).obj ((u.sheafPushforwardContinuous A J K).obj OD))
    (χ : OD' ⟶ (v.sheafPushforwardContinuous A K' K).obj OD)
    (H : ∀ V : C'ᵒᵖ, ψ.hom.app V = χ.hom.app (u'.op.obj V) ≫ OD.obj.map (w.app V.unop).op) :
    (u'.sheafAdjunctionCocontinuous A J' K').unit.app OD' ≫
        (u'.sheafPushforwardCocontinuous A J' K').map ψ =
      (χ ≫ (v.sheafPushforwardContinuous A K' K).map
        ((u.sheafAdjunctionCocontinuous A J K).unit.app OD)) ≫
        (sheafIsoOfTwoSquareAndMorphismsTwoSquare A J' J K' K w).inv.app
          ((u.sheafPushforwardContinuous A J K).obj OD) := by
  have h := sheafIso_unit_comp_eq_simplicialSmallEtaleBigFppfRinged w J' J K' K ψ χ (𝟙 _)
    (fun V ↦ (H V).trans (whisker_eq _ (Category.comp_id _).symm))
  rw [CategoryTheory.Functor.map_id] at h
  exact h.trans (congrArg (fun k ↦ (χ ≫ (v.sheafPushforwardContinuous A K' K).map k) ≫
    (sheafIsoOfTwoSquareAndMorphismsTwoSquare A J' J K' K w).inv.app
      ((u.sheafPushforwardContinuous A J K).obj OD))
    (Category.comp_id _))

end Sheaf

end Stacks.Sites.CocontinuousExchange

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  (a : U ⟶ (SimplicialObject.const T.Spaces).obj X)

/-- The structure sheaf `𝒪_{big,total}` of `(Spaces/U)_{fppf,total}`, `V/U_n ↦ Γ(V, 𝒪_V)`: the
restriction of the big structure sheaf `𝒪_{big}` of `X` along `V/U_n ↦ V/X`. -/
def bigFppfTotalStructureSheaf :
    Sheaf (SimplicialOver.totalTopology T.topology U) CommRingCat.{u + 1} :=
  ((SimplicialOver.augmentationFunctor U a).sheafPushforwardContinuous CommRingCat.{u + 1}
    (SimplicialOver.totalTopology T.topology U) (BigFppfSpaceOver.topology T X)).obj
    (BigFppfSpaceSite.structureSheaf T X)

/-- The ringed topos `(Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total})`. -/
abbrev bigFppfTotalRingedTopos : RingedTopos :=
  (SimplicialOver.situation T.topology U).totalRingedTopos (bigFppfTotalStructureSheaf a)

set_option synthInstance.maxHeartbeats 400000 in
/-- The morphism of topoi `a_{fppf} : Sh((Spaces/U)_{fppf,total}) ⟶ Sh((Spaces/X)_fppf)` of the
continuous and cocontinuous functor `V/U_n ↦ V/X`: its inverse image is restriction. -/
def bigFppfAugmentationToposHom :
    MorphismOfTopoi (Sheaf (SimplicialOver.totalTopology T.topology U) (Type (u + 1)))
      (Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1))) :=
  Functor.morphismOfTopoiOfCocontinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (SimplicialOver.augmentationFunctor U a) _ _

/-- The morphism of topoi `a_{fppf}` above is the augmentation of Stacks 09WL: the two have the
same direct image. -/
theorem bigFppfAugmentationToposHom_pushforward :
    (bigFppfAugmentationToposHom a).pushforward =
      (SimplicialOver.augmentationMorphismOfTopoi T.topology U a).pushforward :=
  (SimplicialOver.augmentationMorphismOfTopoi_pushforward T.topology U a).symm

/-- **The ringed augmentation `a_{fppf} : (Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total}) ⟶
(Sh((Spaces/X)_fppf), 𝒪_{big})`** of Stacks 0D9X: `𝒪_{big,total} = a_{fppf}⁻¹𝒪_{big}`. -/
def bigFppfAugmentationRingedHom :
    RingedToposHom (bigFppfTotalRingedTopos a) (BigFppfSpaceSite.bigFppfRingedTopos T X) :=
  RingedToposHom.ofInverseImageIso (X := bigFppfTotalRingedTopos a)
    (Y := BigFppfSpaceSite.bigFppfRingedTopos T X) (bigFppfAugmentationToposHom a)
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
      (SimplicialOver.totalTopology T.topology U) (BigFppfSpaceOver.topology T X)
      (SimplicialOver.augmentationFunctor U a) (BigFppfSpaceSite.structureSheaf T X))

/-- The functor `V/U_n ↦ V/U_n ↦ V/X` does not change the underlying morphism. -/
theorem augmentationFunctor_map_toBigFppfTotal_left
    {V W : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U} (g : V ⟶ W) :
    ((SimplicialOver.augmentationFunctor U a).map ((toBigFppfTotal U).map g)).left = g.hom :=
  (SimplicialOver.augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft a
      ((toBigFppfTotal U).map g)).trans
    (toBigFppfTotal_map_fiber_left U g)

/-- The structure sheaf `𝒪_U` of `U_{spaces,étale}` is the restriction of `𝒪_{big,total}` along
`u`: both assign to `V/U_n` the ring `Γ(V, 𝒪_V)`. -/
def bigFppfTotalStructureIso :
    structureSheaf U ≅
      ((toBigFppfTotal U).sheafPushforwardContinuous CommRingCat.{u + 1} (topology U)
        (SimplicialOver.totalTopology T.topology U)).obj (bigFppfTotalStructureSheaf a) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {V W} g ↦ by
    change (Space.globalFunctionsPresheaf T.schemeSite S T.scheme_mem).map g.unop.hom.op ≫ 𝟙 _ =
      𝟙 _ ≫ (Space.globalFunctionsPresheaf T.schemeSite S T.scheme_mem).map
        ((SimplicialOver.augmentationFunctor U a).map ((toBigFppfTotal U).map g.unop)).left.op
    rw [Category.comp_id, Category.id_comp, augmentationFunctor_map_toBigFppfTotal_left]
    rfl))

/-- **The morphism of ringed topoi `h : (Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total}) ⟶
(Sh(U_{spaces,étale}), 𝒪_U)`** of Stacks 0DHC: the morphism of topoi of `u`, with the
identification `𝒪_U = h_*𝒪_{big,total}` as structure map. -/
def bigFppfTotalRingedHom : RingedToposHom (bigFppfTotalRingedTopos a) (ringedTopos U) where
  toToposHom := bigFppfTotalToposHom U
  fSharp := (bigFppfTotalStructureIso a ≪≫
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso (topology U)
      (SimplicialOver.totalTopology T.topology U) (toBigFppfTotal U)
      (bigFppfTotalStructureSheaf a)).symm).hom

section TwoIso

open RingedToposHom Stacks.Sheaves.ToposPushforward

/-- The structure map of `a_{fppf}` is the unit of the adjunction `a_{fppf}⁻¹ ⊣ a_{fppf,*}`. -/
theorem forgetFSharp_bigFppfAugmentationRingedHom :
    forgetFSharp (bigFppfAugmentationRingedHom a) =
      (bigFppfAugmentationToposHom a).adj.unit.app
        ((BigFppfSpaceSite.bigFppfRingedTopos T X).forgetRing.obj
          (BigFppfSpaceSite.structureSheaf T X)) := by
  refine (forget_map_commRingImageAdjunction_homEquiv (bigFppfAugmentationToposHom a) _ _ _).trans
    ?_
  exact (congrArg ((bigFppfAugmentationToposHom a).adj.homEquiv _ _)
      (Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget
        (SimplicialOver.totalTopology T.topology U) (BigFppfSpaceOver.topology T X)
        (SimplicialOver.augmentationFunctor U a) (BigFppfSpaceSite.structureSheaf T X))).trans
    (((bigFppfAugmentationToposHom a).adj.homEquiv_unit _ _ _).trans
      ((whisker_eq _ ((bigFppfAugmentationToposHom a).pushforward.map_id _)).trans
        (Category.comp_id _)))

set_option synthInstance.maxHeartbeats 400000 in
/-- At a sheaf `F` on `(Spaces/U)_{fppf,total}`, the inverse of the exchange isomorphism
`bigFppfExchangeIso a` is the base change transformation of the square `bigFppfTwoSquare a`. -/
theorem bigFppfExchangeIso_inv_app_hom (F : Sheaf (SimplicialOver.totalTopology T.topology U)
      (Type (u + 1))) :
    ((bigFppfExchangeIso a).inv.app F).hom = (bigFppfTwoSquare a).op.ranBaseChange.app F.obj :=
  Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare
    _ _ _ _ _ _ F

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0DHC.** Let `U` be a simplicial algebraic space with an augmentation `a : U → X`.
The square of ringed topoi
```
  (Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total}) --h--> (Sh(U_{étale}), 𝒪_U)
           | a_fppf                                          | a
           v                                                 v
  (Sh((Spaces/X)_fppf), 𝒪_{big}) ---------h_{-1}--------> (Sh(X_{étale}), 𝒪_X)
```
commutes: `a ∘ h ≅ h_{-1} ∘ a_{fppf}` as morphisms of ringed topoi. Here `h` is the morphism of
ringed topoi of `u : V/U_n ↦ V/U_n` with `h_*𝒪_{big,total} = 𝒪_U`, `a_{fppf}` the ringed
augmentation with `a_{fppf}⁻¹𝒪_{big} = 𝒪_{big,total}`, `a` the ringed augmentation of Stacks
0DE7 and `h_{-1} = a_X` the morphism of Stacks 0DGM. -/
def bigFppfAugmentationSquareTwoIso :
    TwoIso (A := bigFppfTotalRingedTopos a)
      (B := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
      (RingedToposHom.comp (X := bigFppfTotalRingedTopos a) (Y := ringedTopos U)
        (Z := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (augmentationRingedToposHom a) (bigFppfTotalRingedHom a))
      (RingedToposHom.comp (X := bigFppfTotalRingedTopos a)
        (Y := BigFppfSpaceSite.bigFppfRingedTopos T X)
        (Z := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X) (bigFppfAugmentationRingedHom a)) where
  e := bigFppfExchangeIso a
  commutes := by
    have ha : forgetFSharp (augmentationRingedToposHom a) =
        forgetFSharp (constRingedToposHom X) ≫ (constRingedToposHom X).toToposHom.pushforward.map
          (forgetFSharp (ringedToposHom a)) :=
      forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} _ _
    refine (eq_whisker (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1} (augmentationRingedToposHom a) (bigFppfTotalRingedHom a)) _).trans
      (Eq.trans ?_ (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
        u + 1} (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)
          (bigFppfAugmentationRingedHom a)).symm)
    rw [ha, forgetFSharp_constRingedToposHom, forgetFSharp_bigFppfAugmentationRingedHom]
    refine (Iso.eq_comp_inv ((bigFppfExchangeIso a).app
      ((bigFppfTotalRingedTopos a).forgetRing.obj (bigFppfTotalRingedTopos a).O))).mp ?_
    refine (Category.assoc _ _ _).trans ((whisker_eq _
      ((constRingedToposHom X).toToposHom.pushforward.map_comp _ _).symm).trans ?_)
    have key := Stacks.Sites.CocontinuousExchange.sheafIso_unit_eq_simplicialSmallEtaleBigFppfRinged
      (bigFppfTwoSquare a)
      (topology ((SimplicialObject.const T.Spaces).obj X))
      (SimplicialOver.totalTopology T.topology U)
      (SpacesEtale.topology T.schemeSite S T.scheme_mem X) (BigFppfSpaceOver.topology T X)
      (OD' := (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).forgetRing.obj
        (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X))
      (OD := (BigFppfSpaceSite.bigFppfRingedTopos T X).forgetRing.obj
        (BigFppfSpaceSite.structureSheaf T X))
      ((ringedToposHom a).forgetFSharp ≫ (ringedToposHom a).toToposHom.pushforward.map
        (bigFppfTotalRingedHom a).forgetFSharp)
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X).forgetFSharp (fun V ↦
        (Category.comp_id _).trans (Category.id_comp _).symm)
    exact key

end TwoIso

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end

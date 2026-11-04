module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiRelativeCohomology
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianBaseChange
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteModuleSheafScalarAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image of locally constant module sheaves, and restriction of the action

Stacks Tag 0DV5 part (3) is part (2) with scalar operations: a sheaf of `Λ`-modules is an abelian
sheaf together with an additive functor out of the one-object category of `Λ`, and a finite
`Λ`-module with a continuous `G`-action is a finite discrete `G`-module with such operations. The
equivalence of part (3) is therefore the equivalence of part (2) read on additive functors out of
`CategoryTheory.SingleObj Λ`. This file supplies what is needed to transport a commuting square
along that reading, so that Stacks Tag 0DV6 for sheaves of modules follows from the abelian case.

## Main definitions

* `CategoryTheory.additiveWhiskerRight` — postcomposition with an additive functor, on the
  additive functors out of the one-object category of a ring.
* `Stacks.GroupCohomology.continuousModuleRes` and
  `Stacks.GroupCohomology.finiteTypeContinuousModuleRes` — restriction of an `R`-`G`-module along
  a continuous homomorphism, on all of them and on those of finite type.

## Main results

* `Stacks.Sites.AbelianPullback.moduleSheafPullbackScalarSquare` — **the inverse image of sheaves
  of modules is the inverse image of the underlying abelian sheaves with its scalar
  operations.**
* `Stacks.ConstantSheaf.finiteModuleSheafPullbackScalarSquare` — the same on the finite locally
  constant sheaves.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleToScalarAction_res` — reading a finite
  `Λ`-`G`-module as a finite discrete `G`-module with scalar operations commutes with
  restriction.
* `CategoryTheory.scalarActionTransportSquare` — **a commuting square of additive equivalences
  transports to the additive functors out of the one-object category of a ring.**

## Implementation notes

`moduleSheafPullbackScalarSquare` needs no new mathematics: the *direct* image of sheaves of
modules is the direct image of the underlying abelian sheaves with its scalar operations on the
nose, because both are restriction along the opposite functor computed sectionwise, which is
`moduleSheafPushforwardScalarSquare` and holds by `rfl`. Postcomposition with an additive functor
carries an adjunction to an adjunction (`CategoryTheory.additiveWhiskerRightAdjunction`, which is
`CategoryTheory.Adjunction.whiskerRight` restricted to the additive functors), so the right-hand
side of the square is left adjoint to the direct image of module sheaves, and uniqueness of left
adjoints identifies it with the inverse image. In particular the inverse image of module sheaves
here is the *chosen* left adjoint of the direct image, not a transported substitute.

The remaining two squares are `rfl`: both dictionaries are built from the underlying data, which
neither the inverse image of abelian sheaves nor restriction of an action disturbs.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ uR uG uW

attribute [local instance] discreteForget₂AddCommGrpCat
  Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

/-! ### Postcomposition on additive functors out of the one-object category of a ring -/

namespace CategoryTheory

section Postcomp

variable (Λ : Type r) [Ring Λ] {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {Bc : Type u₂} [Category.{v₂} Bc] [Preadditive Bc]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]

/-- **Postcomposition with an additive functor, on the additive functors out of the one-object
category of a ring.** Composing an additive functor with an additive functor is additive, so
postcomposition restricts to the additive functors. -/
public def additiveWhiskerRight (F : A ⥤ Bc) [F.Additive] :
    (SingleObj Λ ⥤+ A) ⥤ (SingleObj Λ ⥤+ Bc) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringRight (SingleObj Λ) A Bc).obj F)
    fun G ↦ by
      have := G.property
      have h : (G.obj ⋙ F).Additive := inferInstance
      exact h

/-- Postcomposition on the additive functors is postcomposition on all functors. -/
public theorem additiveWhiskerRight_comp_ι (F : A ⥤ Bc) [F.Additive] :
    additiveWhiskerRight Λ F ⋙ ObjectProperty.ι _ =
      (ObjectProperty.ι _ : (SingleObj Λ ⥤+ A) ⥤ (SingleObj Λ ⥤ A)) ⋙
        (Functor.whiskeringRight (SingleObj Λ) A Bc).obj F := rfl

/-- Postcomposition is functorial in the functor postcomposed with. -/
public theorem additiveWhiskerRight_comp (F : A ⥤ Bc) [F.Additive] (G : Bc ⥤ E) [G.Additive] :
    additiveWhiskerRight Λ (F ⋙ G) =
      additiveWhiskerRight Λ F ⋙ additiveWhiskerRight Λ G := rfl

/-- Postcomposition with a fully faithful additive functor is fully faithful. -/
public def additiveWhiskerRightFullyFaithful (F : A ⥤ Bc) [F.Additive]
    (hF : F.FullyFaithful) : (additiveWhiskerRight Λ F).FullyFaithful := by
  refine Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _) ?_
  rw [additiveWhiskerRight_comp_ι]
  exact (ObjectProperty.fullyFaithfulι _).comp (hF.whiskeringRight (SingleObj Λ))

/-- **Postcomposition carries an adjunction of additive functors to an adjunction.** -/
public def additiveWhiskerRightAdjunction {L : A ⥤ Bc} {R : Bc ⥤ A} [L.Additive] [R.Additive]
    (adj : L ⊣ R) : additiveWhiskerRight Λ L ⊣ additiveWhiskerRight Λ R :=
  Adjunction.restrictFullyFaithful (Adjunction.whiskerRight (SingleObj Λ) adj)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (eqToIso (additiveWhiskerRight_comp_ι Λ L)).symm
    (eqToIso (additiveWhiskerRight_comp_ι Λ R)).symm

/-- Postcomposition carries an isomorphism of additive functors to an isomorphism. -/
public def additiveWhiskerRightNatIso {F G : A ⥤ Bc} [F.Additive] [G.Additive] (α : F ≅ G) :
    additiveWhiskerRight Λ F ≅ additiveWhiskerRight Λ G :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      ((Functor.whiskeringRight (SingleObj Λ) A Bc).mapIso α))

/-- **A commuting square of additive functors induces a commuting square of the
postcompositions.** -/
public def additiveWhiskerRightSquare {F : A ⥤ Bc} [F.Additive] {G : Bc ⥤ E} [G.Additive]
    {H : A ⥤ E} [H.Additive] (α : F ⋙ G ≅ H) :
    additiveWhiskerRight Λ F ⋙ additiveWhiskerRight Λ G ≅ additiveWhiskerRight Λ H :=
  eqToIso (additiveWhiskerRight_comp Λ F G).symm ≪≫ additiveWhiskerRightNatIso Λ α

end Postcomp

end CategoryTheory

/-! ### The inverse image of sheaves of modules as the inverse image of abelian sheaves -/

namespace Stacks.Sites.AbelianPullback

section ModulePullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
  (Λ : Type r) [Ring Λ]
  [HasSheafify J AddCommGrpCat.{uW}] [HasSheafify K AddCommGrpCat.{uW}]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{uW} J K).IsRightAdjoint]
  [(F.sheafPushforwardContinuous (ModuleCat.{uW} Λ) J K).IsRightAdjoint]
  [J.HasSheafCompose (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]
  [ReflectsLimitsOfSize.{v₁, max v₁ u₁} (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]
  [ReflectsLimitsOfSize.{v₂, max v₂ u₂} (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]

omit [HasSheafify J AddCommGrpCat.{uW}] [HasSheafify K AddCommGrpCat.{uW}]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{uW} J K).IsRightAdjoint]
  [(F.sheafPushforwardContinuous (ModuleCat.{uW} Λ) J K).IsRightAdjoint] in
/-- **The direct image of sheaves of modules is the direct image of the underlying abelian
sheaves with its scalar operations, on the nose.** Both are restriction along the opposite
functor, computed sectionwise. -/
@[sga "4 IV 11.2.3" "partial"]
public theorem moduleSheafPushforwardScalarSquare :
    F.sheafPushforwardContinuous (ModuleCat.{uW} Λ) J K ⋙
        (moduleSheafScalarActionEquivalence J Λ).functor =
      (moduleSheafScalarActionEquivalence K Λ).functor ⋙
        additiveWhiskerRight Λ (F.sheafPushforwardContinuous AddCommGrpCat.{uW} J K) := rfl

/-- **The inverse image of sheaves of modules is the inverse image of the underlying abelian
sheaves with its scalar operations.** Uniqueness of left adjoints: the right-hand side is left
adjoint to the direct image of module sheaves, because postcomposition carries the adjunction of
abelian sheaves to an adjunction and the direct images agree by
`moduleSheafPushforwardScalarSquare`. -/
public def moduleSheafPullbackScalarSquare :
    F.sheafPullback (ModuleCat.{uW} Λ) J K ⋙
        (moduleSheafScalarActionEquivalence K Λ).functor ≅
      (moduleSheafScalarActionEquivalence J Λ).functor ⋙
        additiveWhiskerRight Λ (F.sheafPullback AddCommGrpCat.{uW} J K) := by
  have hR : ((moduleSheafScalarActionEquivalence K Λ).functor ⋙
        additiveWhiskerRight Λ (F.sheafPushforwardContinuous AddCommGrpCat.{uW} J K)) ⋙
          (moduleSheafScalarActionEquivalence J Λ).inverse ≅
      F.sheafPushforwardContinuous (ModuleCat.{uW} Λ) J K :=
    Functor.isoWhiskerRight (eqToIso (moduleSheafPushforwardScalarSquare F J K Λ)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (moduleSheafScalarActionEquivalence J Λ).unitIso.symm ≪≫
      Functor.rightUnitor _
  have e := (F.sheafAdjunctionContinuous (ModuleCat.{uW} Λ) J K).leftAdjointUniq
    (((moduleSheafScalarActionEquivalence J Λ).toAdjunction.comp
      ((additiveWhiskerRightAdjunction Λ
          (F.sheafAdjunctionContinuous AddCommGrpCat.{uW} J K)).comp
        (moduleSheafScalarActionEquivalence K Λ).symm.toAdjunction)).ofNatIsoRight hR)
  exact Functor.isoWhiskerRight e _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (moduleSheafScalarActionEquivalence K Λ).counitIso ≪≫
      Functor.rightUnitor _)

end ModulePullback

end Stacks.Sites.AbelianPullback

/-! ### The same on the finite locally constant sheaves -/

namespace Stacks.ConstantSheaf

section FiniteModuleDictionary

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (Λ : Type r) [Ring Λ]
  [Finite Λ]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u₁ v₁}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u₁ v₁} Λ) AddCommGrpCat.{max u₁ v₁})]
  [ReflectsLimitsOfSize.{v₁, max v₁ u₁}
    (forget₂ (ModuleCat.{max u₁ v₁} Λ) AddCommGrpCat.{max u₁ v₁})]

/-- The inclusion of the finite locally constant abelian sheaves is additive: addition of
morphisms is inherited from the ambient abelian sheaves. -/
public instance additive_ι_isFiniteLocallyConstantAbelianSheaf :
    (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι.Additive where
  map_add := rfl

omit [Finite Λ] [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u₁ v₁}]
  [ReflectsLimitsOfSize.{v₁, max v₁ u₁}
    (forget₂ (ModuleCat.{max u₁ v₁} Λ) AddCommGrpCat.{max u₁ v₁})] in
/-- **Reading a finite locally constant sheaf of modules as a finite locally constant abelian
sheaf with scalar operations is the ambient reading.** -/
public theorem finiteModuleSheafToScalarAction_comp_ι :
    finiteModuleSheafToScalarAction J Λ ⋙
        additiveWhiskerRight Λ (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι =
      ObjectProperty.ι _ ⋙ moduleSheafToScalarAction J Λ := rfl

end FiniteModuleDictionary

section FiniteModuleSquare

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (Λ : Type r) [Ring Λ]
  [Finite Λ]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u₁ v₁}]
  [∀ U : D, HasWeakSheafify (K.over U) AddCommGrpCat.{max u₁ v₁}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u₁ v₁} Λ) AddCommGrpCat.{max u₁ v₁})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{max u₁ v₁} Λ) AddCommGrpCat.{max u₁ v₁})]
  [ReflectsLimitsOfSize.{v₁, max v₁ u₁}
    (forget₂ (ModuleCat.{max u₁ v₁} Λ) AddCommGrpCat.{max u₁ v₁})]
  (pmod : Sheaf J (ModuleCat.{max u₁ v₁} Λ) ⥤ Sheaf K (ModuleCat.{max u₁ v₁} Λ))
  (pab : Sheaf J AddCommGrpCat.{max u₁ v₁} ⥤ Sheaf K AddCommGrpCat.{max u₁ v₁}) [pab.Additive]

/-- **The square of the module dictionary against the two inverse images, on the finite locally
constant sheaves.** Each of the four functors is a lift to a full subcategory of a functor in the
square `Stacks.Sites.AbelianPullback.moduleSheafPullbackScalarSquare`, which is therefore all the
square says. -/
public def finiteModuleSheafPullbackScalarSquare
    (Pab : (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).FullSubcategory ⥤
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).FullSubcategory) [Pab.Additive]
    (hPab : Pab ⋙ (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι =
      (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι ⋙ pab)
    (Pmod : ObjectProperty.FullSubcategory
        (fun G : Sheaf J (ModuleCat.{max u₁ v₁} Λ) ↦ IsFiniteLocallyConstant J G) ⥤
      ObjectProperty.FullSubcategory
        (fun G : Sheaf K (ModuleCat.{max u₁ v₁} Λ) ↦ IsFiniteLocallyConstant K G))
    (hPmod : Pmod ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙ pmod)
    (hmod : moduleSheafToScalarAction J Λ ⋙ additiveWhiskerRight Λ pab ≅
      pmod ⋙ moduleSheafToScalarAction K Λ) :
    (finiteLocallyConstantModuleSheafScalarActionEquivalence J Λ).functor ⋙
        additiveWhiskerRight Λ Pab ≅
      Pmod ⋙ (finiteLocallyConstantModuleSheafScalarActionEquivalence K Λ).functor :=
  letI := (additiveWhiskerRightFullyFaithful Λ
    (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι
    (ObjectProperty.fullyFaithfulι _)).full
  letI := (additiveWhiskerRightFullyFaithful Λ
    (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι
    (ObjectProperty.fullyFaithfulι _)).faithful
  Functor.squareOfAmbient (ObjectProperty.ι _) (ObjectProperty.ι _)
    (additiveWhiskerRight Λ (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι)
    (additiveWhiskerRight Λ (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι)
    (eqToIso (finiteModuleSheafToScalarAction_comp_ι J Λ))
    (eqToIso (additiveWhiskerRight_comp Λ Pab
        (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} K).ι).symm ≪≫
      additiveWhiskerRightNatIso Λ (eqToIso hPab) ≪≫
      eqToIso (additiveWhiskerRight_comp Λ
        (isFiniteLocallyConstantAbelianSheaf.{v₁, u₁, u₁} J).ι pab))
    (eqToIso hPmod)
    (eqToIso (finiteModuleSheafToScalarAction_comp_ι K Λ))
    hmod

end FiniteModuleSquare

end Stacks.ConstantSheaf

/-! ### Restriction of a finite type continuous module -/

namespace Stacks.GroupCohomology

section Res

variable (Λ : Type uR) [Ring Λ] {G H : Type uG} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] (φ : G →ₜ* H)

/-- **Restriction of an `R`-`H`-module along a continuous homomorphism `φ : G →ₜ* H`.** The
underlying module and its topology are unchanged. -/
public def continuousModuleRes :
    Stacks.Injectives.ContinuousModule.{uR, uG, uW} Λ H ⥤
      Stacks.Injectives.ContinuousModule.{uR, uG, uW} Λ G :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ ContAction.res (ModuleCat.{uW} Λ) φ) fun M ↦ M.property

/-- Restriction of `R`-`H`-modules is restriction of all continuous actions on modules. -/
public theorem continuousModuleRes_comp_ι :
    continuousModuleRes.{uR, uG, uW} Λ φ ⋙ ObjectProperty.ι _ =
      (ObjectProperty.ι _ : Stacks.Injectives.ContinuousModule.{uR, uG, uW} Λ H ⥤
        ContAction (ModuleCat.{uW} Λ) H) ⋙ ContAction.res (ModuleCat.{uW} Λ) φ := rfl

/-- **Restriction on the finite type `R`-`H`-modules.** The underlying module is unchanged, so it
stays finitely generated. -/
public def finiteTypeContinuousModuleRes :
    FiniteTypeContinuousModule.{uR, uG, uW} Λ H ⥤
      FiniteTypeContinuousModule.{uR, uG, uW} Λ G :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ continuousModuleRes.{uR, uG, uW} Λ φ) fun M ↦ M.property

/-- Restriction on the finite type `R`-`H`-modules is restriction on all of them. -/
public theorem finiteTypeContinuousModuleRes_comp_ι :
    finiteTypeContinuousModuleRes.{uR, uG, uW} Λ φ ⋙ ObjectProperty.ι _ =
      (ObjectProperty.ι _ : FiniteTypeContinuousModule.{uR, uG, uW} Λ H ⥤
          Stacks.Injectives.ContinuousModule.{uR, uG, uW} Λ H) ⋙
        continuousModuleRes.{uR, uG, uW} Λ φ := rfl

/-- Restriction of finite discrete modules is additive. -/
public instance additive_continuousGAddCommGrpResIsFinite :
    (ContinuousGAddCommGrp.resIsFinite φ).Additive where
  map_add := rfl

/-- **Reading a finite `Λ`-`H`-module as a finite discrete `H`-module with scalar operations
commutes with restriction along `φ`.** Restriction changes neither the underlying abelian group
nor the scalar operations, so the two composites agree on the nose. -/
public theorem finiteTypeContinuousModuleToScalarAction_res [Finite Λ] :
    finiteTypeContinuousModuleToScalarAction.{uR, uG, uW} Λ H ⋙
        additiveWhiskerRight Λ (ContinuousGAddCommGrp.resIsFinite φ) =
      finiteTypeContinuousModuleRes.{uR, uG, uW} Λ φ ⋙
        finiteTypeContinuousModuleToScalarAction.{uR, uG, uW} Λ G := rfl

end Res

end Stacks.GroupCohomology

/-! ### Transporting a square along the reading of scalar operations -/

namespace CategoryTheory

section Transport

variable (Λ : Type r) [Ring Λ]
  {A₁ : Type u₁} [Category.{v₁} A₁] [Preadditive A₁]
  {B₁ : Type u₃} [Category.{v₃} B₁] [Preadditive B₁]

/-- The functor of `CategoryTheory.scalarActionCongrRight` is postcomposition with the functor of
the equivalence. -/
public theorem scalarActionCongrRight_functor (e : A₁ ≌ B₁) [e.functor.Additive] :
    (scalarActionCongrRight Λ e).functor = additiveWhiskerRight Λ e.functor := rfl

end Transport

section TransportSquare

variable (Λ : Type r) [Ring Λ]
  {A₁ : Type u₁} [Category.{v₁} A₁] [Preadditive A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Preadditive A₂]
  {B₁ : Type u₃} [Category.{v₃} B₁] [Preadditive B₁]
  {B₂ : Type u₄} [Category.{v₄} B₂] [Preadditive B₂]

/-- **Transport a commuting square of additive functors through the dictionaries presenting four
categories as additive functors out of the one-object category of a ring.** The two horizontal
equivalences enter only through `CategoryTheory.additiveWhiskerRight`, so the square they induce
is the given one; the two vertical functors are matched with their counterparts by `h₁` and
`h₂`. -/
public def scalarActionTransportSquare
    {A₁' : Type*} [Category* A₁'] {A₂' : Type*} [Category* A₂']
    {B₁' : Type*} [Category* B₁'] {B₂' : Type*} [Category* B₂']
    (Φ₁ : A₁' ≌ (SingleObj Λ ⥤+ A₁)) (Φ₂ : A₂' ≌ (SingleObj Λ ⥤+ A₂))
    (Ψ₁ : (SingleObj Λ ⥤+ B₁) ≌ B₁') (Ψ₂ : (SingleObj Λ ⥤+ B₂) ≌ B₂')
    {e₁ : A₁ ≌ B₁} [e₁.functor.Additive] {e₂ : A₂ ≌ B₂} [e₂.functor.Additive]
    {P : A₁ ⥤ A₂} [P.Additive] {R : B₁ ⥤ B₂} [R.Additive]
    {Pm : A₁' ⥤ A₂'} {Rm : B₁' ⥤ B₂'}
    (h₁ : Pm ⋙ Φ₂.functor ≅ Φ₁.functor ⋙ additiveWhiskerRight Λ P)
    (h₂ : additiveWhiskerRight Λ R ⋙ Ψ₂.functor ≅ Ψ₁.functor ⋙ Rm)
    (α : e₁.functor ⋙ R ≅ P ⋙ e₂.functor) :
    (Φ₁.functor ⋙ additiveWhiskerRight Λ e₁.functor ⋙ Ψ₁.functor) ⋙ Rm ≅
      Pm ⋙ (Φ₂.functor ⋙ additiveWhiskerRight Λ e₂.functor ⋙ Ψ₂.functor) :=
  Functor.isoWhiskerLeft (Φ₁.functor ⋙ additiveWhiskerRight Λ e₁.functor) h₂.symm ≪≫
    Functor.isoWhiskerLeft Φ₁.functor
      (Functor.isoWhiskerRight
        (eqToIso (additiveWhiskerRight_comp Λ e₁.functor R).symm ≪≫
          additiveWhiskerRightNatIso Λ α ≪≫
          eqToIso (additiveWhiskerRight_comp Λ P e₂.functor)) Ψ₂.functor) ≪≫
    Functor.isoWhiskerRight h₁.symm (additiveWhiskerRight Λ e₂.functor ⋙ Ψ₂.functor)

end TransportSquare

end CategoryTheory

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesId
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCompMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The transport of direct images along a 2-isomorphism is monoidal

Let `F H : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be morphisms of ringed topoi with an isomorphism
`e : F_* ≅ H_*` of geometric direct images carrying the structure map of `F` to that of `H`.
The induced isomorphism `F_* ≅ H_*` of direct images of sheaves of modules,
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso`, is a monoidal natural
transformation for the lax monoidal structures of the direct images (the right adjoints of the
monoidal pullbacks of Stacks 03EL).

## Main definitions

* `AlgebraicGeometry.RingedToposHom.toModulesPushforwardModulesIsoOfNatIso`: the transport, in
  the spelling of the modules development.

## Main results

* `AlgebraicGeometry.RingedToposHom.isMonoidal_toModulesPushforwardModulesIsoOfNatIso_hom`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (tensorPairing hom_ext_tensorPairing
  tensorPairing_comp_tensorHom prodComparison_comp_tensorPairing_comp_μ moduleSheafFunctor_map_ε
  comp_comp_comp_of_eq comp_comp_comp_eq_of_eq hom_ext_moduleSheafFunctor)

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₁}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X.J.HasSheafCompose (forget RingCat.{w₁})] [Y.J.HasSheafCompose (forget RingCat.{w₁})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [HasSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasSheafify Y.J AddCommGrpCat.{w₁}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  (F H : RingedToposHom X Y)
  (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
  (he : F.fSharpRing ≫
    pullbackRingSheafMapOfNatTrans Y.J ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))
      e.hom = H.fSharpRing)

/-- The transport `F_* ≅ H_*` of direct images of sheaves of modules along `e`, in the spelling
of the modules development. -/
def toModulesPushforwardModulesIsoOfNatIso :
    Stacks.Sheaves.RingedToposModules.pushforwardModules F.toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.pushforwardModules H.toModulesHom :=
  F.toModulesPushforwardIso ≪≫ pushforwardModulesIsoOfNatIso F H e he ≪≫
    H.toModulesPushforwardIso.symm

omit [HasSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasSheafify Y.J AddCommGrpCat.{w₁}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}] in
/-- On underlying sheaves of sets the transport is `e`. -/
theorem moduleSheafFunctor_map_toModulesPushforwardModulesIsoOfNatIso_hom_app
    (M : _root_.SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((toModulesPushforwardModulesIsoOfNatIso F H e he).hom.app M) =
      e.hom.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M) := by
  dsimp only [toModulesPushforwardModulesIsoOfNatIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id,
    moduleSheafFunctor_map_toModulesPushforwardIso_inv_app_eq_id]
  exact Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **The transport is compatible with the tensorators.** -/
theorem toModulesPushforwardModulesIsoOfNatIso_μ
    (M N : _root_.SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Functor.LaxMonoidal.μ
          (Stacks.Sheaves.RingedToposModules.pushforwardModules F.toModulesHom) M N ≫
        (toModulesPushforwardModulesIsoOfNatIso F H e he).hom.app (M ⊗ N) =
      ((toModulesPushforwardModulesIsoOfNatIso F H e he).hom.app M ⊗ₘ
          (toModulesPushforwardModulesIsoOfNatIso F H e he).hom.app N) ≫
        Functor.LaxMonoidal.μ
          (Stacks.Sheaves.RingedToposModules.pushforwardModules H.toModulesHom) M N := by
  have := F.toToposHom.adj.rightAdjoint_preservesLimits
  refine hom_ext_tensorPairing ((cancel_epi (prodComparison F.toToposHom.pushforward
    (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M)
    (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) N))).1 ?_)
  refine Eq.trans (b := e.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      M ⨯ Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) N) ≫
    H.toToposHom.pushforward.map (tensorPairing M N)) ?_ (Eq.symm ?_)
  · rw [CategoryTheory.Functor.map_comp,
      moduleSheafFunctor_map_toModulesPushforwardModulesIsoOfNatIso_hom_app]
    exact (comp_comp_comp_of_eq
      (prodComparison_comp_tensorPairing_comp_μ F.toModulesHom M N) _).trans
      (e.hom.naturality (tensorPairing M N))
  · have hn := tensorPairing_comp_tensorHom
      ((toModulesPushforwardModulesIsoOfNatIso F H e he).hom.app M)
      ((toModulesPushforwardModulesIsoOfNatIso F H e he).hom.app N)
    rw [moduleSheafFunctor_map_toModulesPushforwardModulesIsoOfNatIso_hom_app,
      moduleSheafFunctor_map_toModulesPushforwardModulesIsoOfNatIso_hom_app] at hn
    rw [CategoryTheory.Functor.map_comp]
    exact comp_comp_comp_eq_of_eq _ _ _ _ _ _ _ hn
      (prodComparison_natural_of_natTrans e.hom).symm
      (prodComparison_comp_tensorPairing_comp_μ H.toModulesHom M N)

/-- **The transport is compatible with the units.** -/
theorem toModulesPushforwardModulesIsoOfNatIso_ε :
    Functor.LaxMonoidal.ε (Stacks.Sheaves.RingedToposModules.pushforwardModules F.toModulesHom) ≫
        (toModulesPushforwardModulesIsoOfNatIso F H e he).hom.app
          (𝟙_ (_root_.SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) =
      Functor.LaxMonoidal.ε
        (Stacks.Sheaves.RingedToposModules.pushforwardModules H.toModulesHom) := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_ε,
    moduleSheafFunctor_map_toModulesPushforwardModulesIsoOfNatIso_hom_app, moduleSheafFunctor_map_ε]
  exact sheafCompose_map_fSharpRing_comp_hom F H e he

/-- **The transport of direct images of sheaves of modules along a 2-isomorphism is a monoidal
natural transformation.** -/
instance isMonoidal_toModulesPushforwardModulesIsoOfNatIso_hom :
    NatTrans.IsMonoidal (toModulesPushforwardModulesIsoOfNatIso F H e he).hom where
  unit := toModulesPushforwardModulesIsoOfNatIso_ε F H e he
  tensor M N := toModulesPushforwardModulesIsoOfNatIso_μ F H e he M N

/-! ### The transport of pullbacks and Stacks 03EL -/

/-- The transport `F^* ≅ H^*` of pullbacks of sheaves of modules along `e`: the comparison of
left adjoints of the direct images, identified along
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso`. -/
def pullbackModulesIsoOfNatIso :
    F.toModulesHom.pullbackModules ≅ H.toModulesHom.pullbackModules :=
  (pullbackAdjPushforwardModules F).leftAdjointUniq
    ((pullbackAdjPushforwardModules H).ofNatIsoRight (pushforwardModulesIsoOfNatIso F H e he).symm)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X.J.HasSheafCompose (forget RingCat.{w₁})] [Y.J.HasSheafCompose (forget RingCat.{w₁})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [HasSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasSheafify Y.J AddCommGrpCat.{w₁}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}] in
/-- The conjugate of the comparison of left adjoints of two right adjoints identified along `P`,
after both adjunctions have been transported along isomorphisms of their right adjoints. -/
private theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_ofNatIsoRight
    {C₀ C₁ : Type*} [Category C₀] [Category C₁] {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ R₁' R₂' : C₁ ⥤ C₀}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (t₁ : R₁ ≅ R₁') (t₂ : R₂ ≅ R₂') (P : R₁' ≅ R₂') :
    conjugateEquiv a₂ a₁ (Adjunction.leftAdjointUniq (a₁.ofNatIsoRight t₁)
        ((a₂.ofNatIsoRight t₂).ofNatIsoRight P.symm)).hom = t₂.hom ≫ P.inv ≫ t₁.inv := by
  have h := Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (a₁.ofNatIsoRight t₁) (a₂.ofNatIsoRight t₂) P.symm
  rw [Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_left,
    Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_right] at h
  rw [← cancel_epi t₂.inv, ← cancel_mono t₁.hom]
  simpa using h

omit [HasSheafify Y.J AddCommGrpCat.{w₁}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}] in
/-- The conjugate of the transport of pullbacks, under the adjunctions of the modules
development, is the inverse transport of direct images. -/
theorem conjugateEquiv_pullbackModulesIsoOfNatIso_hom :
    conjugateEquiv (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules H.toModulesHom)
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules F.toModulesHom)
        (pullbackModulesIsoOfNatIso F H e he).hom =
      (toModulesPushforwardModulesIsoOfNatIso F H e he).inv :=
  conjugateEquiv_leftAdjointUniq_ofNatIsoRight_ofNatIsoRight
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules F.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules H.toModulesHom)
    F.toModulesPushforwardIso H.toModulesPushforwardIso (pushforwardModulesIsoOfNatIso F H e he)

attribute [local instance] Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal

/-- **Stacks 03EL is compatible with the transport of pullbacks along a 2-isomorphism**, at the
monoidal spelling. -/
theorem pullbackModulesIsoOfNatIso_hom_app_tensor_comp_δ
    (A B : _root_.SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (pullbackModulesIsoOfNatIso F H e he).hom.app (A ⊗ B) ≫
        Functor.OplaxMonoidal.δ
          (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules H.toModulesHom)
          A B =
      Functor.OplaxMonoidal.δ
          (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules F.toModulesHom)
          A B ≫
        ((pullbackModulesIsoOfNatIso F H e he).hom.app A ⊗ₘ
          (pullbackModulesIsoOfNatIso F H e he).hom.app B) := by
  have : NatTrans.IsMonoidal (conjugateEquiv
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules H.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules F.toModulesHom)
      (pullbackModulesIsoOfNatIso F H e he).hom) := by
    rw [conjugateEquiv_pullbackModulesIsoOfNatIso_hom]
    infer_instance
  exact Adjunction.app_tensor_comp_δ_of_isMonoidal_conjugateEquiv
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules H.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules F.toModulesHom)
    (pullbackModulesIsoOfNatIso F H e he).hom A B

/-- **Stacks 03EL is compatible with the transport of pullbacks along a 2-isomorphism**, at the
tensor bifunctor of sheaves of modules. -/
theorem pullbackModulesIsoOfNatIso_hom_app_pullbackTensorIso
    (A B : _root_.SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackModulesIsoOfNatIso F H e he).hom.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w₁, w₁, w₁} Y.O).obj A).obj B) ≫
        (Stacks.SheafOfModules.pullbackTensorIso H.toModulesHom).hom.app (A, B) =
      (Stacks.SheafOfModules.pullbackTensorIso F.toModulesHom).hom.app (A, B) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w₁, w₁, w₁} X.O).map
            ((pullbackModulesIsoOfNatIso F H e he).hom.app A)).app
          ((F.toModulesHom.pullbackModules).obj B) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w₁, w₁, w₁} X.O).obj
          ((H.toModulesHom.pullbackModules).obj A)).map
            ((pullbackModulesIsoOfNatIso F H e he).hom.app B) :=
  (pullbackModulesIsoOfNatIso_hom_app_tensor_comp_δ F H e he A B).trans
    (congrArg (fun t ↦ (Stacks.SheafOfModules.pullbackTensorIso F.toModulesHom).hom.app (A, B) ≫ t)
      (Stacks.SheafOfModules.Strict.tensorHom_eq_tensorSheafBifunctor_map X.O _ _))

end AlgebraicGeometry.RingedToposHom


namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open _root_.Stacks.AlgebraicGeometry Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u c c'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : AlgebraicGeometry.RingedTopos.{u, c, u}}
  {Y : AlgebraicGeometry.RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (F H : AlgebraicGeometry.RingedToposHom X Y)
  (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
  (he : F.fSharpRing ≫
    pullbackRingSheafMapOfNatTrans Y.J ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))
      e.hom = H.fSharpRing)
  (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

/-- **Stacks 07A4 along the transport of pullbacks along a 2-isomorphism** of morphisms of ringed
topoi. -/
theorem derivedPullbackTensorIso_pullbackModulesIsoOfNatIso :
    Functor.whiskerLeft (Functor.uncurry.obj TY.tensor)
          (derivedPullbackIsoOfPullbackModulesIso
            (AlgebraicGeometry.RingedToposHom.pullbackModulesIsoOfNatIso F H e he)).hom ≫
        (derivedPullbackTensorIso H TX TY).hom =
      (derivedPullbackTensorIso F TX TY).hom ≫
        Functor.whiskerRight (NatTrans.prod
          (derivedPullbackIsoOfPullbackModulesIso
            (AlgebraicGeometry.RingedToposHom.pullbackModulesIsoOfNatIso F H e he)).hom
          (derivedPullbackIsoOfPullbackModulesIso
            (AlgebraicGeometry.RingedToposHom.pullbackModulesIsoOfNatIso F H e he)).hom)
          (Functor.uncurry.obj TX.tensor) :=
  derivedPullbackTensorIso_transport _ TX TY
    (AlgebraicGeometry.RingedToposHom.pullbackModulesIsoOfNatIso_hom_app_pullbackTensorIso F H e he)

end Stacks.Cohomology.DerivedPullbackOfToposHom

end

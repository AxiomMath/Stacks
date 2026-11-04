module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DirectImageFiberMapGerm
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison

/-!
# Stacks 05V5 at a matched pair of points, on `1 ⊗ m`

The inverse of the comparison `(f^*G)_Φ ≅ G_Ψ ⊗_{𝒪'_Ψ} 𝒪_Φ` carries `1 ⊗ m` to the stalk at `Φ`
of the canonical map `f⁻¹G ⟶ f^*G` applied to the image of `m` under `G_Ψ ≅ (f⁻¹G)_Φ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.StalkInverseImage Stacks.Sheaves.StalkTransport
open scoped TensorProduct ChangeOfRings

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

noncomputable section

universe w v u v' u'

namespace Stacks.Sheaves.StalkPullback

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅
    f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))

/-- **Stacks 05V5 at a matched pair of points, read backwards on `1 ⊗ m`.** For `m` the class of
a germ `z` of the underlying sheaf of sets of `G` at `Ψ`, the inverse of
`Stacks.Sheaves.StalkPullback.stalkFunctorIso` sends `1 ⊗ m` to the class of the image of
`e(z) ∈ (f⁻¹G)_Φ` under the stalk of the unit `f⁻¹G ⟶ f^*G` of Stacks 03CZ. -/
theorem stalkFunctorIso_inv_app_one_tmul_moduleStalkComparison
    (G : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (z : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)) :
    (stalkFunctorIso f Φ Ψ e).inv.app G
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
          (moduleStalkComparison Ψ ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G z)) =
      moduleStalkComparison Φ ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((RingedToposHom.pullbackModules f).obj G)
        ((Φ.sheafFiber (A := Type w)).map
          ((Sheaf.moduleSheafFunctor (inverseImageStructureRing f)).map
            ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageStructureRing f).property
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property).unit.app
              ((inverseImageFunctor f).obj G)))
          (e.hom.app _ z)) := by
  have h4 : (stalkIsoStepFour f Φ Ψ e).inv.app G
      ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
          (moduleStalkComparison Ψ ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G z)) =
      (1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
        (show (ModuleCat.restrictScalars (toTargetStalkRing Ψ)).obj
            ((ModuleCat.restrictScalars
              (stalkRingEquiv f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) Φ Ψ
                e).toRingHom).obj
                ((inverseImageStalkFunctor f Φ).obj ((inverseImageFunctor f).obj G))) from
          moduleStalkComparison Φ
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)
            (e.hom.app _ z)) := by
    refine (ModuleCat.ExtendScalars.map_tmul _ _ _ _).trans ?_
    exact congrArg (fun t => (1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj,
      stalkRingMap f Φ Ψ e] (show (ModuleCat.restrictScalars (toTargetStalkRing Ψ)).obj
            ((ModuleCat.restrictScalars
              (stalkRingEquiv f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) Φ Ψ
                e).toRingHom).obj
                ((inverseImageStalkFunctor f Φ).obj ((inverseImageFunctor f).obj G))) from t))
      (stalkModuleMap_moduleStalkComparison _ _ Φ Ψ e G z)
  refine (congrArg (fun t => (stalkIsoStepOne f Φ).inv.app G ((stalkIsoStepTwo f Φ Ψ e).inv.app G
    ((stalkIsoStepThree f Φ Ψ e).inv.app G t))) h4).trans ?_
  have h2 := ModuleCat.restrictExtendScalarsCompIso_hom_app_one_tmul (toInverseImageStalkRing f Φ)
    (fSharpStalk f Φ) (commRingStalkEquiv f Φ Ψ e)
    ((inverseImageStalkFunctor f Φ).obj ((inverseImageFunctor f).obj G))
    (moduleStalkComparison Φ
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)
      (e.hom.app _ z))
  refine (congrArg (fun t => (stalkIsoStepOne f Φ).inv.app G t) h2).trans ?_
  refine (unit_square_app Φ (fSharpCommRing f) (inverseImageStructureRing f).property
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property ((inverseImageFunctor f).obj G)
      _).trans ?_
  refine Eq.trans (?_ : _ = (Stacks.sheafModuleFiber Φ (inverseImageStructureRing f)).map
    ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageStructureRing f).property
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property).unit.app
              ((inverseImageFunctor f).obj G))
      (moduleStalkComparison Φ (inverseImageStructureRing f) ((inverseImageFunctor f).obj G)
        (e.hom.app _ z))) ?_
  · rfl
  · refine (moduleStalkComparison_naturality Φ (inverseImageStructureRing f) _ _).symm.trans ?_
    rfl

/-- `Stacks.Sheaves.StalkPullback.stalkFunctorIso_inv_app_one_tmul_moduleStalkComparison` across
an identification `k = k'` of two morphisms of ringed topoi: the comparison is taken at `k'` and
the right-hand side is read through `k`, the comparison of stalk functors being transported along
the equality of the underlying morphisms of topoi. -/
theorem stalkFunctorIso_inv_app_one_tmul_of_eq (k k' : RingedToposHom X Y) (hk : k = k')
    (hT : k.toToposHom = k'.toToposHom)
    (h : RingedToposHom.pullbackModules k ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O =
      RingedToposHom.pullbackModules k' ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O)
    (e : Ψ.sheafFiber (A := Type w) ≅ k'.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))
    (G : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (z : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)) :
    (eqToIso h ≪≫ stalkFunctorIso k' Φ Ψ e).inv.app G
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap k' Φ Ψ e]
          (moduleStalkComparison Ψ ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G z)) =
      moduleStalkComparison Φ ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((RingedToposHom.pullbackModules k).obj G)
        ((Φ.sheafFiber (A := Type w)).map
          ((Sheaf.moduleSheafFunctor (inverseImageStructureRing k)).map
            ((extendRestrictScalarsAdjunction X.J (fSharpCommRing k)
              (inverseImageStructureRing k).property
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property).unit.app
              ((inverseImageFunctor k).obj G)))
          ((Φ.sheafFiber (A := Type w)).map
            (eqToHom (congrArg (fun T : MorphismOfTopoi X.Topos Y.Topos =>
              T.inverseImage.obj
                (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)) hT.symm))
            (e.hom.app _ z))) := by
  subst hk
  have hh : eqToIso h = Iso.refl _ := rfl
  have hT' : eqToHom (congrArg (fun T : MorphismOfTopoi X.Topos Y.Topos =>
      T.inverseImage.obj (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G))
      hT.symm) = 𝟙 _ := rfl
  rw [hh, Iso.refl_trans, hT', CategoryTheory.Functor.map_id]
  exact stalkFunctorIso_inv_app_one_tmul_moduleStalkComparison k Φ Ψ e G z

/-- `Stacks.Sheaves.StalkPullback.stalkFunctorIso_inv_app_one_tmul_of_eq` for a morphism of
ringed topoi `f` in the sense of Stacks 01D3: an isomorphism `σ` which is the comparison at a
four-field form `k'` of `f`, read through the pullback of sheaves of modules of `f`, sends
`1 ⊗ m` to the stalk of the unit of the four-field form `f.toModulesHom`. -/
theorem iso_inv_app_one_tmul_of_eq_stalkFunctorIso
    (f : AlgebraicGeometry.RingedToposHom X Y) (k' : RingedToposHom X Y)
    (hk : f.toModulesHom = k') (hT : f.toToposHom = k'.toToposHom)
    (e : Ψ.sheafFiber (A := Type w) ≅ k'.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))
    (σ : f.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      Stacks.sheafModuleFiberOfCommRing Ψ Y.O ⋙ ModuleCat.extendScalars (stalkRingMap k' Φ Ψ e))
    (h : f.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O =
      RingedToposHom.pullbackModules k' ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O)
    (hσ : σ = eqToIso h ≪≫ stalkFunctorIso k' Φ Ψ e)
    (G : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (z : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)) :
    σ.inv.app G
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap k' Φ Ψ e]
          (moduleStalkComparison Ψ ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G z)) =
      moduleStalkComparison Φ ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (f.toModulesHom.pullbackModules.obj G)
        ((Φ.sheafFiber (A := Type w)).map
          ((Sheaf.moduleSheafFunctor (inverseImageStructureRing f.toModulesHom)).map
            ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f.toModulesHom)
              (inverseImageStructureRing f.toModulesHom).property
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property).unit.app
              ((inverseImageFunctor f.toModulesHom).obj G)))
          ((Φ.sheafFiber (A := Type w)).map
            (eqToHom (congrArg (fun T : MorphismOfTopoi X.Topos Y.Topos =>
              T.inverseImage.obj
                (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)) hT.symm))
            (e.hom.app _ z))) := by
  subst hσ
  exact stalkFunctorIso_inv_app_one_tmul_of_eq Φ Ψ f.toModulesHom k' hk hT h e G z

end Stacks.Sheaves.StalkPullback

end

end

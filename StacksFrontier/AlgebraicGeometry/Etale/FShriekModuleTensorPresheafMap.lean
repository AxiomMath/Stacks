module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensorNaturality

/-!
# The projection-formula map of presheaves of `Λ`-modules

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. The recipe
`(Z, s) ⊗ t ↦ (Z, s ⊗ f^{-1}t)` of [Stacks, Tag 0GKF] is `Λ`-linear in `s` and natural in the
test object; this file proves it `Λ`-linear in `t` as well, and assembles it into the morphism of
presheaves of `Λ`-modules

`f_{p!}F ⊗_Λ G ⟶ f_{p!}(F ⊗_Λ f^{-1}G)`.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom_smul_section` — the recipe is
  `Λ`-linear in the section of `G`.
* `AlgebraicGeometry.SmallEtale.finiteSupportPushforward_obj_map` — the restriction maps of
  `f_{p!}A` are base change of supports, with the colimit generators eliminated.
* `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorHom_naturality` — the `Λ`-linear recipe is
  natural in the test object.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorBilinear` — the recipe as a `Λ`-bilinear
  map on the sections over one test object.
* `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorPresheafMap` — **the projection-formula
  map of presheaves of `Λ`-modules.**

## Implementation notes

The tensor product on presheaves of `Λ`-modules is the pointwise one of
`CategoryTheory.Monoidal.functorCategoryMonoidal`, so a morphism out of it is a family of maps
out of the tensor products of the sections, and naturality is checked on pure tensors by
`TensorProduct.ext`, where it is
`AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom_naturality`.

## References

* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace Stacks

/-- Inserting a composite `e₃ ≫ e₄ = 𝟙 P` between two factors of a composite changes nothing. -/
public theorem comp_cancel_mid {C : Type*} [Category* C] {W P P' Q : C} (e₁ : W ⟶ P)
    (m : P ⟶ P) (e₃ : P ⟶ P') (e₄ : P' ⟶ P) (k : P ⟶ Q) (h : e₃ ≫ e₄ = 𝟙 P) :
    e₁ ≫ m ≫ k = (e₁ ≫ m ≫ e₃) ≫ e₄ ≫ k := by
  rw [Category.assoc, Category.assoc, ← Category.assoc e₃ e₄ k, h, Category.id_comp]

end Stacks

namespace AlgebraicGeometry.SmallEtale

universe u v

section ObjMap

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{v} (FiniteSupport B f V))

/-- **The restriction maps of `f_{p!}A` over one morphism of the test objects** are base change of
supports, transported along the identification of the values of `f_{p!}` with the colimits of
supported sections. -/
public theorem finiteSupportPushforward_obj_map
    (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) :
    ((finiteSupportPushforward.{u, v} B f hsmall).1.obj A).map g.op =
      letI := hsmall V
      letI := hsmall V'
      eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq A V) ≫
        finiteSupportBaseChangeHom B f A g ≫
          eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq A V').symm := by
  let := hsmall V
  let := hsmall V'
  have h :
      eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq A V).symm ≫
          ((finiteSupportPushforward.{u, v} B f hsmall).1.obj A).map g.op ≫
            eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq A V') =
        finiteSupportBaseChangeHom B f A g := by
    refine colimit.hom_ext fun E => ?_
    rw [(finiteSupportPushforward.{u, v} B f hsmall).2.map_restrict A g E,
      finiteSupportBaseChangeHom_ι]
  rw [← h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    eqToHom_trans, Category.comp_id]

end ObjMap

section Section

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The projection-formula recipe is `Λ`-linear in the section of `G`.** -/
public theorem finiteSupportTensorSectionsHom_smul_section
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) (a : Λ) :
    finiteSupportTensorSectionsHom B Λ f F G V (a • t) =
      colim.map (finiteSupportDiagramMap B f
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property) F a).asHom V) ≫
        finiteSupportTensorSectionsHom B Λ f F G V t := by
  have hΘ :
      (tensorOpenSectionMap B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
          (baseChange B f V)
          (modPullbackUnitSection B Λ f G V (a • t))).finiteSupportDiagramHom B f =
        finiteSupportDiagramMap B f
            (Stacks.ModuleCatLift.sheafScalarEnd Λ
              (SmallEtale.topology B X.obj X.property) F a).asHom V ≫
          (tensorOpenSectionMap B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
            (baseChange B f V)
            (modPullbackUnitSection B Λ f G V t)).finiteSupportDiagramHom B f := by
    refine NatTrans.ext (funext fun E => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun s => Subtype.ext ?_))
    show tensorSectionHom B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
        (baseChange B f V) (modPullbackUnitSection B Λ f G V (a • t))
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)) s.val = _
    rw [show (modPullbackUnitSection B Λ f G V (a • t)) =
        a • (modPullbackUnitSection B Λ f G V t) from
      (modPullbackUnitSection B Λ f G V).hom.map_smul a t]
    exact tensorSectionHom_smul B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
      (baseChange B f V) a
      (modPullbackUnitSection B Λ f G V t)
      (supportOpen B X.obj X.property (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E)) s.val
  show colim.map _ = _
  rw [hΘ, CategoryTheory.Functor.map_comp]
  rfl

/-- **The `Λ`-linear projection-formula recipe is additive in the section of `G`.** -/
public theorem modFiniteSupportTensorHom_add_section
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t t' : G.obj.obj (op V))
    (x : ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V)) :
    modFiniteSupportTensorHom B Λ f F G V (t + t') x =
      modFiniteSupportTensorHom B Λ f F G V t x +
        modFiniteSupportTensorHom B Λ f F G V t' x := by
  have hmor : (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        (modFiniteSupportTensorHom B Λ f F G V (t + t')) =
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          (modFiniteSupportTensorHom B Λ f F G V t) +
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          (modFiniteSupportTensorHom B Λ f F G V t') := by
    show eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
        finiteSupportTensorSectionsHom B Λ f F G V (t + t') ≫
      eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm = _
    rw [finiteSupportTensorSectionsHom_add, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  exact ConcreteCategory.congr_hom hmor x

/-- **The `Λ`-linear projection-formula recipe is `Λ`-linear in the section of `G`.** -/
public theorem modFiniteSupportTensorHom_smul_section
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) (a : Λ)
    (x : ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V)) :
    modFiniteSupportTensorHom B Λ f F G V (a • t) x =
      a • modFiniteSupportTensorHom B Λ f F G V t x := by
  have hmor : (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        (modFiniteSupportTensorHom B Λ f F G V (a • t)) =
      ((((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V)).smul a).asHom ≫
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          (modFiniteSupportTensorHom B Λ f F G V t) := by
    show eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
        finiteSupportTensorSectionsHom B Λ f F G V (a • t) ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm =
      ((((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V)).smul a).asHom ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
        finiteSupportTensorSectionsHom B Λ f F G V t ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm
    rw [finiteSupportTensorSectionsHom_smul_section,
      modFiniteSupportPresheaf_obj_smul.{u, v, max (u + 1) v} B Λ f F (op V) a,
      finiteSupportPushforward_map_app.{u, max (u + 1) v} B f (fun _ => inferInstance) _ V]
    exact Stacks.comp_cancel_mid _ _ _ _ _
      (eqToIso ((finiteSupportPushforward.{u, max (u + 1) v} B f
        (fun _ => inferInstance)).2.obj_eq
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V)).inv_hom_id
  exact (ConcreteCategory.congr_hom hmor x).trans
    ((modFiniteSupportTensorHom B Λ f F G V t).hom.map_smul a x)

/-- **The `Λ`-linear projection-formula recipe is natural in the test object.** -/
public theorem modFiniteSupportTensorHom_naturality
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (t : G.obj.obj (op V)) :
    modFiniteSupportTensorHom B Λ f F G V t ≫
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
          (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))).map g.op =
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).map g.op ≫
        modFiniteSupportTensorHom B Λ f F G V' (G.obj.map g.op t) := by
  have hnat := finiteSupportTensorSectionsHom_naturality B Λ f F G g t
  have hnat' : ∀ {Z : AddCommGrpCat.{max (u + 1) v}}
      (k : finiteSupportSections B f
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
          (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))) V' ⟶ Z),
      finiteSupportTensorSectionsHom B Λ f F G V t ≫
          finiteSupportBaseChangeHom B f
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
              (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))) g ≫ k =
        finiteSupportBaseChangeHom B f
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g ≫
          finiteSupportTensorSectionsHom B Λ f F G V' (G.obj.map g.op t) ≫ k := by
    intro Z k
    rw [← Category.assoc, hnat, Category.assoc]
  refine (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  show (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
        finiteSupportTensorSectionsHom B Λ f F G V t ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm) ≫
      ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
          (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)))).map g.op =
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)).map g.op ≫
      (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V') ≫
        finiteSupportTensorSectionsHom B Λ f F G V' (G.obj.map g.op t) ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V').symm)
  rw [finiteSupportPushforward_obj_map.{u, max (u + 1) v} B f (fun _ => inferInstance) _ g,
    finiteSupportPushforward_obj_map.{u, max (u + 1) v} B f (fun _ => inferInstance) _ g]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, hnat']

/-- **The projection-formula recipe as a `Λ`-bilinear map on the sections over a test
object**: `x ⊗ t ↦ x ⊗ f^{-1}t`, extended `Λ`-bilinearly. -/
public def modFiniteSupportTensorBilinear
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property) :
    ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V) ⊗
        G.obj.obj (op V) ⟶
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
        (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))).obj (op V) :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.flip
    { toFun := fun t => (modFiniteSupportTensorHom B Λ f F G V t).hom,
      map_add' := fun t t' => LinearMap.ext fun x =>
        modFiniteSupportTensorHom_add_section B Λ f F G V t t' x,
      map_smul' := fun a t => LinearMap.ext fun x =>
        modFiniteSupportTensorHom_smul_section B Λ f F G V t a x }))

/-- `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorBilinear` on a pure tensor `x ⊗ t` is the
`Λ`-linear projection-formula recipe at `t`, applied to `x`. -/
@[simp]
public lemma modFiniteSupportTensorBilinear_tmul
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (x : ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V))
    (t : G.obj.obj (op V)) :
    modFiniteSupportTensorBilinear B Λ f F G V (x ⊗ₜ[Λ] t) =
      modFiniteSupportTensorHom B Λ f F G V t x :=
  rfl

/-- **The projection-formula map of presheaves of `Λ`-modules**,
`f_{p!}F ⊗_Λ G ⟶ f_{p!}(F ⊗_Λ f^{-1}G)`. On a pure tensor of sections over a test object `V`
it is the recipe `(Z, s) ⊗ t ↦ (Z, s ⊗ f^{-1}t)` of [Stacks, Tag 0GKF]. -/
public def modFiniteSupportTensorPresheafMap
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj ⟶
      (modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
        (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) where
  app V := modFiniteSupportTensorBilinear B Λ f F G V.unop
  naturality V V' m := by
    refine ModuleCat.hom_ext (TensorProduct.ext' fun x t => ?_)
    exact (ConcreteCategory.congr_hom
      (modFiniteSupportTensorHom_naturality B Λ f F G m.unop t) x).symm

end Section

end AlgebraicGeometry.SmallEtale

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMateMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackCongrOfSiteIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorCompositionLaw

/-!
# The module-level comparison of Stacks 03EL along isomorphic morphisms of ringed topoi

Let `φ, ψ : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be morphisms of ringed topoi presented by continuous
functors of sites which are morphisms of sites, and let `e : ψ.u ≅ φ.u` be an isomorphism of the
underlying functors carrying the structure map of `φ` to that of `ψ`. The pullbacks of sheaves of
modules along `φ` and `ψ` are then isomorphic,
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposIsoOfIso : φ^* ≅ ψ^*`. This file proves that
this isomorphism is compatible with the comparisons

`φ^*(A ⊗ B) ⟶ φ^*A ⊗ φ^*B`, `ψ^*(A ⊗ B) ⟶ ψ^*A ⊗ ψ^*B`

of [Stacks, Tag 03EL] (`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap`).

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pushforwardModulesIsoOfIso` — the isomorphism `Ψ_* ≅ Φ_*` of
  the four-field direct images of sheaves of modules of the morphisms `Φ`, `Ψ` attached to `φ`,
  `ψ`, induced by `e`.

## Main results

* `Stacks.Sheaves.DerivedPullback.conjugateEquiv_pullbackToposIsoOfIso` — the isomorphism
  `φ^* ≅ ψ^*`, read on the four-field pullbacks, is the mate of `Ψ_* ≅ Φ_*`.
* `Stacks.Sheaves.DerivedPullback.moduleSheafFunctor_map_pushforwardModulesIsoOfIso_hom_app` —
  on underlying sheaves of sets, `Ψ_* ≅ Φ_*` is the transformation of direct images of sheaves of
  sets induced by `e`.
* `Stacks.Sheaves.DerivedPullback.pullbackToposIsoOfIso_hom_app_comp_pullbackToposTensorMap` —
  **the comparison of Stacks 03EL is compatible with `φ^* ≅ ψ^*`.**

## Implementation notes

The comparison of Stacks 03EL for a site-presented morphism is that of the four-field morphism of
Stacks 03D6 transported along the identification of the two pullbacks
(`Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso`). For four-field morphisms the
compatibility with the mate of a transformation of direct images is
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_mate`, which asks that the transformation
be, on underlying sheaves of sets, a transformation of direct images of sheaves of sets. Here that
transformation is the restriction along `e`, and every other comparison of direct images involved
is the identity on underlying sheaves of sets.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {φ ψ : RingedToposSiteHom X Y} {e : ψ.u ≅ φ.u}
  (he : RingedToposSiteHom.FSharpCompatible φ ψ e)
  (hmosφ : φ.u.IsMorphismOfSites Y.J X.J) (hmosψ : ψ.u.IsMorphismOfSites Y.J X.J)

/-- **The four-field direct images along isomorphic morphisms of ringed topoi are isomorphic**:
`Ψ_* ≅ ψ_* ≅ φ_* ≅ Φ_*`, for `Φ`, `Ψ` the four-field morphisms of Stacks 03D6 attached to `φ`,
`ψ`, the middle isomorphism being induced by `e`. -/
def pushforwardModulesIsoOfIso :
    pushforwardModules (modulesHomOfSiteHom ψ hmosψ) ≅
      pushforwardModules (modulesHomOfSiteHom φ hmosφ) :=
  (RingedSite.Hom.ofRingedToposSiteHom ψ hmosψ).pushforwardModulesToposIso ≪≫
    (RingedToposSiteHom.pushforwardToposIsoOfIso he).symm ≪≫
      (RingedSite.Hom.ofRingedToposSiteHom φ hmosφ).pushforwardModulesToposIso.symm

/-- The conjugate of the inverse of an isomorphism of left adjoints induced by an isomorphism of
right adjoints. -/
private theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv {A B : Type*} [Category A]
    [Category B] {L L' : A ⥤ B} {R R' : B ⥤ A} (adj : L ⊣ R) (e : R ≅ R') (adj' : L' ⊣ R') :
    conjugateEquiv adj adj' (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').inv =
      e.hom := by
  have h : conjugateEquiv adj' adj (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').hom ≫
      conjugateEquiv adj adj' (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').inv = 𝟙 _ :=
    conjugateEquiv_comm adj' adj (Iso.inv_hom_id _)
  rwa [Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom, Iso.inv_comp_eq_id]
    at h

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `pullbackModulesSiteIso` is the comparison of left adjoints induced by the comparison of the
two direct images. -/
private theorem pullbackModulesSiteIso_eq' (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    pullbackModulesSiteIso f hmos =
      Adjunction.leftAdjointUniq
        ((pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmos)).ofNatIsoRight
          (RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardModulesToposIso)
        f.pullbackPushforwardAdjunctionTopos :=
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The isomorphism `φ^* ≅ ψ^*`, read on the four-field pullbacks, is the mate of `Ψ_* ≅ Φ_*`.**
The composite `Φ^* ≅ φ^* ≅ ψ^* ≅ Ψ^*` is conjugate, for the adjunctions of Stacks 03D7 of `Ψ`
and `Φ`, to `pushforwardModulesIsoOfIso`. -/
theorem conjugateEquiv_pullbackToposIsoOfIso :
    conjugateEquiv (pullbackAdjPushforwardModules (modulesHomOfSiteHom ψ hmosψ))
        (pullbackAdjPushforwardModules (modulesHomOfSiteHom φ hmosφ))
        ((pullbackModulesSiteIso φ hmosφ).hom ≫
          (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
            (pullbackModulesSiteIso ψ hmosψ).inv) =
      (pushforwardModulesIsoOfIso he hmosφ hmosψ).hom := by
  rw [← conjugateEquiv_comp (pullbackAdjPushforwardModules (modulesHomOfSiteHom ψ hmosψ))
      φ.pullbackPushforwardAdjunctionTopos,
    ← conjugateEquiv_comp (pullbackAdjPushforwardModules (modulesHomOfSiteHom ψ hmosψ))
      ψ.pullbackPushforwardAdjunctionTopos φ.pullbackPushforwardAdjunctionTopos]
  have h₁ : conjugateEquiv (pullbackAdjPushforwardModules (modulesHomOfSiteHom ψ hmosψ))
      ψ.pullbackPushforwardAdjunctionTopos (pullbackModulesSiteIso ψ hmosψ).inv =
        (RingedSite.Hom.ofRingedToposSiteHom ψ hmosψ).pushforwardModulesToposIso.hom := by
    rw [pullbackModulesSiteIso_eq' ψ hmosψ]
    exact conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv _ _ _
  have h₂ : conjugateEquiv ψ.pullbackPushforwardAdjunctionTopos
      φ.pullbackPushforwardAdjunctionTopos (RingedToposSiteHom.pullbackToposIsoOfIso he).hom =
        (RingedToposSiteHom.pushforwardToposIsoOfIso he).inv :=
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _
  have h₃ : conjugateEquiv φ.pullbackPushforwardAdjunctionTopos
      (pullbackAdjPushforwardModules (modulesHomOfSiteHom φ hmosφ))
        (pullbackModulesSiteIso φ hmosφ).hom =
        (RingedSite.Hom.ofRingedToposSiteHom φ hmosφ).pushforwardModulesToposIso.inv := by
    rw [pullbackModulesSiteIso_eq' φ hmosφ]
    exact Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _
  rw [h₁, h₂, h₃]
  exact Category.assoc _ _ _

/-- On underlying sheaves of sets the comparison of the four-field direct image with Mathlib's,
followed by any morphism, is that morphism: the comparison is the identity there. -/
private theorem map_pushforwardModulesToposIso_hom_app_comp' (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {T : Sheaf Y.J (Type u)}
    (m : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      ((RingedSite.Hom.ofRingedToposSiteHom f hmos).toRingedToposSiteHom.pushforwardTopos.obj N) ⟶
        T) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardModulesToposIso.hom.app N) ≫ m =
      m := by
  have h₁ := GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_pushforwardModulesIso_hom_app
    (RingedSite.Hom.ofRingedToposSiteHom f hmos).ringedToposHom N
  have h₂ : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardToposIso.hom.app N) = 𝟙 _ :=
    moduleSheafFunctor_map_ofSheafHom _ _ _
  show (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((AlgebraicGeometry.RingedToposHom.pushforwardModulesIso
          (RingedSite.Hom.ofRingedToposSiteHom f hmos).ringedToposHom).hom.app N ≫
        (RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardToposIso.hom.app N) ≫ m = m
  rw [Functor.map_comp, h₁, h₂]
  exact (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.id_comp m))

/-- The inverse comparison of the four-field direct image with Mathlib's is the identity on
underlying sheaves of sets, read as a morphism followed by anything. -/
private theorem map_pushforwardModulesToposIso_inv_app_comp' (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {T : Sheaf Y.J (Type u)}
    (m : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      ((pushforwardModules
        (RingedSite.Hom.ofRingedToposSiteHom f hmos).ringedToposHom.toRingedToposModulesHom).obj
          N) ⟶ T) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardModulesToposIso.inv.app N) ≫ m =
      m :=
  (map_pushforwardModulesToposIso_hom_app_comp' f hmos N _).symm.trans
    (by rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp])

/-- **On underlying sheaves of sets, `Ψ_* ≅ Φ_*` is restriction along `e`**: the transformation
`ψ.u_* ⟶ φ.u_*` of direct images of sheaves of sets induced by `e.inv : φ.u ⟶ ψ.u`. -/
theorem moduleSheafFunctor_map_pushforwardModulesIsoOfIso_hom_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pushforwardModulesIsoOfIso he hmosφ hmosψ).hom.app N) =
      (Functor.sheafPushforwardContinuousNatTrans e.inv (Type u) Y.J X.J).app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) := by
  have hQ : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((RingedToposSiteHom.pushforwardToposIsoOfIso he).inv.app N) =
        (Functor.sheafPushforwardContinuousNatTrans e.inv (Type u) Y.J X.J).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) :=
    Sheaf.hom_ext_sections fun _ _ ↦ rfl
  refine (Functor.map_comp _ _ _).trans
    ((map_pushforwardModulesToposIso_hom_app_comp' ψ hmosψ N _).trans
      ((Functor.map_comp _ _ _).trans ((congrArg (· ≫ _) hQ).trans ?_)))
  exact (congrArg (_ ≫ ·) (map_pushforwardModulesToposIso_inv_app_comp' φ hmosφ N (𝟙 _))).trans
    (Category.comp_id _)

/-- **The comparison of Stacks 03EL for the four-field pullbacks is compatible with
`Φ^* ≅ φ^* ≅ ψ^* ≅ Ψ^*`.** This is `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_mate`
for the mate of `Ψ_* ≅ Φ_*` (`conjugateEquiv_pullbackToposIsoOfIso`), whose hypothesis is
`moduleSheafFunctor_map_pushforwardModulesIsoOfIso_hom_app`. -/
theorem pullbackModulesIsoOfIso_hom_app_comp_pullbackTensorIso_hom_app
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((pullbackModulesSiteIso φ hmosφ).hom ≫ (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
          (pullbackModulesSiteIso ψ hmosψ).inv).app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj F).obj G) ≫
      (pullbackTensorIso (modulesHomOfSiteHom ψ hmosψ)).hom.app (F, G) =
    (pullbackTensorIso (modulesHomOfSiteHom φ hmosφ)).hom.app (F, G) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).map
        (((pullbackModulesSiteIso φ hmosφ).hom ≫
              (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
            (pullbackModulesSiteIso ψ hmosψ).inv).app F ×ₘ
          ((pullbackModulesSiteIso φ hmosφ).hom ≫
            (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
              (pullbackModulesSiteIso ψ hmosψ).inv).app G) := by
  have hγ : (pullbackModulesSiteIso φ hmosφ).hom ≫
      (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
      (pullbackModulesSiteIso ψ hmosψ).inv =
        (conjugateEquiv (pullbackAdjPushforwardModules (modulesHomOfSiteHom ψ hmosψ))
          (pullbackAdjPushforwardModules (modulesHomOfSiteHom φ hmosφ))).symm
          (pushforwardModulesIsoOfIso he hmosφ hmosψ).hom := by
    rw [← conjugateEquiv_pullbackToposIsoOfIso he hmosφ hmosψ, Equiv.symm_apply_apply]
  rw [hγ]
  exact pullbackTensorIso_hom_app_comp_mate (modulesHomOfSiteHom ψ hmosψ)
    (modulesHomOfSiteHom φ hmosφ)
    (Functor.sheafPushforwardContinuousNatTrans e.inv (Type u) Y.J X.J)
    (pushforwardModulesIsoOfIso he hmosφ hmosψ).hom F G
    (moduleSheafFunctor_map_pushforwardModulesIsoOfIso_hom_app he hmosφ hmosψ)

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The composite `Φ^* ≅ φ^* ≅ ψ^* ≅ Ψ^*` followed by `Ψ^* ≅ ψ^*` is `Φ^* ≅ φ^* ≅ ψ^*`, in each
tensor factor. -/
private theorem tensorFactor_pullbackModulesSiteIso_comp
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
        (((pullbackModulesSiteIso φ hmosφ).hom ≫
              (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
            (pullbackModulesSiteIso ψ hmosψ).inv).app A ×ₘ
          ((pullbackModulesSiteIso φ hmosφ).hom ≫
            (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
              (pullbackModulesSiteIso ψ hmosψ).inv).app B) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
        ((pullbackModulesSiteIso ψ hmosψ).hom.app A ×ₘ (pullbackModulesSiteIso ψ hmosψ).hom.app B) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
        ((pullbackModulesSiteIso φ hmosφ).hom.app A ×ₘ (pullbackModulesSiteIso φ hmosφ).hom.app B) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
        ((RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app A ×ₘ
          (RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app B) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The isomorphism `φ^* ≅ ψ^*` followed by `ψ^* ≅ Ψ^*` is `φ^* ≅ Φ^*` followed by the composite
`Φ^* ≅ Ψ^*`. -/
private theorem pullbackToposIsoOfIso_hom_app_comp_pullbackModulesSiteIso_inv_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app M ≫
        (pullbackModulesSiteIso ψ hmosψ).inv.app M =
      (pullbackModulesSiteIso φ hmosφ).inv.app M ≫
        ((pullbackModulesSiteIso φ hmosφ).hom ≫ (RingedToposSiteHom.pullbackToposIsoOfIso he).hom ≫
          (pullbackModulesSiteIso ψ hmosψ).inv).app M := by
  simp

/-- **The comparison of Stacks 03EL is compatible with `φ^* ≅ ψ^*`.** For sheaves of
`𝒪_D`-modules `A` and `B`, the isomorphism `φ^* ≅ ψ^*` at `A ⊗ B` followed by the comparison
`ψ^*(A ⊗ B) ⟶ ψ^*A ⊗ ψ^*B` is the comparison for `φ` followed by `φ^* ≅ ψ^*` in each tensor
factor. -/
theorem pullbackToposIsoOfIso_hom_app_comp_pullbackToposTensorMap
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).obj B) ≫
        pullbackToposTensorMap ψ hmosψ A B =
      pullbackToposTensorMap φ hmosφ A B ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map
            ((RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app A)).app (φ.pullbackTopos.obj B) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
            (ψ.pullbackTopos.obj A)).map
              ((RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app B) := by
  rw [show ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map
          ((RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app A)).app (φ.pullbackTopos.obj B) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          (ψ.pullbackTopos.obj A)).map ((RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app B) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
        ((RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app A ×ₘ
          (RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app B) from rfl,
    pullbackToposTensorMap_eq_uncurry ψ hmosψ, pullbackToposTensorMap_eq_uncurry φ hmosφ,
    reassoc_of% pullbackToposIsoOfIso_hom_app_comp_pullbackModulesSiteIso_inv_app he hmosφ hmosψ,
    reassoc_of% pullbackModulesIsoOfIso_hom_app_comp_pullbackTensorIso_hom_app he hmosφ hmosψ A B,
    tensorFactor_pullbackModulesSiteIso_comp he hmosφ hmosψ A B]
  simp only [Category.assoc]

end Stacks.Sheaves.DerivedPullback

end

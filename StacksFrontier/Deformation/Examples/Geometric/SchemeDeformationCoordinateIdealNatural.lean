module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationCoordinateIdeal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolutionBaseChange
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChangeIdealMap
public import StacksFrontier.Deformation.RingedSpaceThickening.FirstOrderIdealMapIso

/-!
# Naturality of the coordinate ideals in the vector space

For a `k`-linear map `g : V ⟶ W` the map `k[g] : k[V] → k[W]` induces `Spec k[W] → Spec k[V]`,
compatible with the closed points. The deformation problems of [Stacks Project, Tag 08U7] over
`k[V]` and `k[W]` are compared by the map of pulled back ideals `f^*t_V^*𝒥_V ⟶ f^*t_W^*𝒥_W`
(`AlgebraicGeometry.RingedSpaceThickening.baseChangeIdealMap`). Under the identifications
`f^*t^*𝒥 ≅ 𝒪_X ⊗_k V` of `coordPulledIdealIso` it is `𝒪_X ⊗_k g`. This is the coefficient
naturality behind the `k`-linear form of the second display of [Stacks Project, Tag 0DY9].

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.homEquiv_baseChangeIdealMapOnBase_comp`: the transpose
  of the map of pulled back base ideals.
* `AlgebraicGeometry.RingedSpaceThickening.baseChangeIdealMapOnBase_comp_eq_of_top`: over a
  one-point base, maps out of the pulled back base ideal are compared on global sections.
* `Deformation.Examples.baseChangeIdealMapOnBase_coordConormalIso`: on `Spec k`, the map of
  pulled back base ideals is `g^~ : V^~ ⟶ W^~`.
* `Deformation.Examples.baseChangeIdealMap_coordPulledIdealIso`: on `X`, it is `𝒪_X ⊗_k g`.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

open RingedSpaceModuleAdjunction

variable {S S₁ S₂ : RingedSpace.{u, u}} {t₁ : S ⟶ S₁} {t₂ : S ⟶ S₂}

/-- Transposing along `t₁` the map of pulled back base ideals followed by `φ` is transposing the
map of base ideals along `h'` and then `φ` along `t₂`. -/
theorem homEquiv_baseChangeIdealMapOnBase_comp (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁)
    (M : SheafOfModules.{u} (structureSheafRing S))
    (φ : (modulePullback t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₂) ⟶ M) :
    (modulePullbackPushforwardAdjunction t₁).homEquiv _ _ (baseChangeIdealMapOnBase h' comm ≫ φ) =
      ((modulePullbackPushforwardAdjunction h').homEquiv _ _ (baseIdealSheafMap h' comm) ≫
        (modulePushforward h').map ((modulePullbackPushforwardAdjunction t₂).homEquiv _ _ φ)) ≫
          (modulePushforwardComp t₂ h').hom.app M ≫
            eqToHom (congrArg (fun g => (modulePushforward g).obj M) comm) := by
  subst comm
  have l2 := homEquiv_compUniq_inv t₂ h' (AlgebraicGeometry.SheafOfModules.idealSheaf (t₂ ≫ h'))
    M ((modulePullbackCompUniq t₂ h').hom.app _ ≫
      (modulePullback t₂).map (baseIdealSheafMap h' rfl) ≫ φ)
  rw [Iso.inv_hom_id_app_assoc, Adjunction.comp_homEquiv] at l2
  simp only [baseChangeIdealMapOnBase, eqToHom_refl, Category.id_comp, Category.assoc,
    modulePushforwardComp_hom_app]
  refine l2.symm.trans ?_
  change (modulePullbackPushforwardAdjunction h').homEquiv _ _
    ((modulePullbackPushforwardAdjunction t₂).homEquiv _ _
      ((modulePullback t₂).map (baseIdealSheafMap h' rfl) ≫ φ)) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

/-- Over a one-point base `S₁`, a map out of `t₁^*𝒥₁` through `baseChangeIdealMapOnBase` is
determined by the transposes on global sections. -/
theorem baseChangeIdealMapOnBase_comp_eq_of_top [Subsingleton S₁] (h' : S₂ ⟶ S₁)
    (comm : t₂ ≫ h' = t₁) {M M' : SheafOfModules.{u} (structureSheafRing S)}
    (φ₂ : (modulePullback t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₂) ⟶ M)
    (ψ₂ : AlgebraicGeometry.SheafOfModules.idealSheaf t₂ ⟶ (modulePushforward t₂).obj M)
    (hφ₂ : (modulePullbackPushforwardAdjunction t₂).homEquiv _ _ φ₂ = ψ₂)
    (φ₁ : (modulePullback t₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₁) ⟶ M')
    (ψ₁ : AlgebraicGeometry.SheafOfModules.idealSheaf t₁ ⟶ (modulePushforward t₁).obj M')
    (hφ₁ : (modulePullbackPushforwardAdjunction t₁).homEquiv _ _ φ₁ = ψ₁)
    (ψ : M' ⟶ M)
    (H : ∀ x, (ψ₂.val.app (op ⊤)).hom
        ((((modulePullbackPushforwardAdjunction h').homEquiv _ _
          (baseIdealSheafMap h' comm)).val.app (op ⊤)).hom x) =
      (ψ.val.app (op ⊤)).hom ((ψ₁.val.app (op ⊤)).hom x)) :
    baseChangeIdealMapOnBase h' comm ≫ φ₂ = φ₁ ≫ ψ := by
  subst comm hφ₁ hφ₂
  apply ((modulePullbackPushforwardAdjunction (t₂ ≫ h')).homEquiv _ _).injective
  rw [homEquiv_baseChangeIdealMapOnBase_comp, Adjunction.homEquiv_naturality_right]
  simp only [modulePushforwardComp_hom_app, eqToHom_refl]
  exact Deformation.Examples.moduleHom_ext_top (ModuleCat.hom_ext (LinearMap.ext H))

end AlgebraicGeometry.RingedSpaceThickening

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

section Coordinate

variable (V : FGModuleCat.{u} k)

/-- The isomorphism `𝒥 ≅ t_*(V^~)` on global sections: the class of `snd` of an element of the
ideal of the closed point. -/
theorem coordIdealSheafIso_hom_app_top
    (x : (Stacks.ClosedImmersion.idealSheaf
      (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom).val.obj (op ⊤)) :
    ((coordIdealSheafIso V).hom.val.app (op ⊤)).hom x =
      (tilde.toOpen (R := CommRingCat.of k) V.obj ⊤).hom (TrivSqZeroExt.snd
        ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom
          (((Stacks.ClosedImmersion.idealSheafι
            (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom).val.app (op ⊤)).hom x))) := by
  simp only [coordIdealSheafIso, idealSheafIsoOfKerIsoTop, moduleIsoOfTop, moduleHomOfTop_apply]
  set f := SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom
      (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom)
  set F := SheafOfModules.evaluation
    (structureSheafRing (baseSpec (coordBase (Λ := Λ) V)).toRingedSpace) (op ⊤)
  have hF : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have h1 := ModuleCat.kernelIsoKer_hom_ker_subtype_apply (F.map f)
    ((kernelComparison f F).hom x)
  have h2 := congrArg (fun m => m.hom x) (kernelComparison_comp_ι f F)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h2
  change (kerTopLinearEquiv V) ((ModuleCat.kernelIsoKer (F.map f)).hom.hom
    ((kernelComparison f F).hom x)) = _
  exact congrArg (fun y => (tilde.toOpen (R := CommRingCat.of k) V.obj ⊤).hom (TrivSqZeroExt.snd
    ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom y))) (h1.trans h2)

/-- The transpose of `t^*𝒥 ≅ V^~` along `t^* ⊣ t_*` is `𝒥 ≅ t_*(V^~)`. -/
theorem homEquiv_coordConormalIso_hom :
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom).homEquiv _ _
        (coordConormalIso V).hom = (coordIdealSheafIso V).hom := by
  simp only [coordConormalIso, conormalIsoOfIdealSheafIso, closedQuotientPullbackPushforwardIso]
  exact ((congrArg _ (Adjunction.homEquiv_counit _ _ _ _).symm).trans
    (Equiv.apply_symm_apply _ _))

end Coordinate

/-- `g^~ : V^~ ⟶ W^~` on `Spec k` for a `k`-linear map `g : V ⟶ W`, in the spelling of sheaves of
modules over the structure sheaf. -/
noncomputable def tildeCoeffMap {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    tildeCoeff V ⟶ tildeCoeff W :=
  (tilde.functor (CommRingCat.of k)).map g.hom

open AlgebraicGeometry.RingedSpaceThickening RingedSpaceModuleAdjunction in
/-- **The map of pulled back base ideals along `Spec k[g]` is `g^~`**, under the identifications
`t^*𝒥 ≅ V^~` of the conormal sheaves of the closed points. -/
theorem baseChangeIdealMapOnBase_coordConormalIso {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    baseChangeIdealMapOnBase _
        (residueSpecMap_toShHom_comp_baseSpecMap
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)) ≫
        (coordConormalIso (Λ := Λ) W).hom =
      (coordConormalIso (Λ := Λ) V).hom ≫ tildeCoeffMap g := by
  refine baseChangeIdealMapOnBase_comp_eq_of_top _
    (residueSpecMap_toShHom_comp_baseSpecMap
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)) _ _
    (homEquiv_coordConormalIso_hom W) _ _ (homEquiv_coordConormalIso_hom V) _ ?_
  intro x
  refine (coordIdealSheafIso_hom_app_top W _).trans (Eq.trans ?_
    (congrArg _ (coordIdealSheafIso_hom_app_top V x)).symm)
  have h2 := congrArg (fun m => (m.val.app (op ⊤)).hom x)
    (homEquiv_baseIdealSheafMap_comp _ (residueSpecMap_toShHom_comp_baseSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply] at h2
  refine (congrArg (fun z => (tilde.toOpen (R := CommRingCat.of k) W.obj ⊤).hom (TrivSqZeroExt.snd
    ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) W))).hom.hom z))) h2).trans ?_
  generalize ((Stacks.ClosedImmersion.idealSheafι
    (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom).val.app (op ⊤)).hom x = y
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) W))).hom.hom
      (((structureSheafModuleHom (baseSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)).toLRSHom.toShHom).val.app
          (op ⊤)).hom y) =
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom y) :=
    congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g).hom.toRingHom))
  refine (congrArg (fun z => (tilde.toOpen (R := CommRingCat.of k) W.obj ⊤).hom
    (TrivSqZeroExt.snd z)) hΓ).trans ?_
  generalize (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom y = z
  have hh := ConcreteCategory.congr_hom (tilde.toOpen_map_app (R := CommRingCat.of k)
    (M := V.obj) (N := W.obj) g.hom ⊤) (TrivSqZeroExt.snd z)
  simp only [ConcreteCategory.comp_apply] at hh
  let _ (M : ModuleCat.{u} k) : Module kᵐᵒᵖ M :=
    Module.compHom M {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  have _ (M : ModuleCat.{u} k) : IsCentralScalar k M := ⟨fun _ _ => rfl⟩
  exact (congrArg (tilde.toOpen (R := CommRingCat.of k) W.obj ⊤).hom
    (TrivSqZeroExt.snd_map _ _)).trans hh.symm

open AlgebraicGeometry.RingedSpaceThickening RingedSpaceModuleAdjunction in
/-- **The map of pulled back ideals along `Spec k[g]` is `𝒪_X ⊗_k g`**, under the identifications
`f^*t^*𝒥 ≅ 𝒪_X ⊗_k V` of `coordPulledIdealIso`. -/
theorem baseChangeIdealMap_coordPulledIdealIso (X : Over (Spec (CommRingCat.of k)))
    {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    baseChangeIdealMap X.hom.toLRSHom.toShHom _
        (residueSpecMap_toShHom_comp_baseSpecMap
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)) ≫
        (coordPulledIdealIso (Λ := Λ) W X).hom =
      (coordPulledIdealIso (Λ := Λ) V X).hom ≫ (coefficientSheafFunctor X.hom).map g := by
  have e2 := (Stacks.ProjectiveBundleQuotients.pullbackIso X.hom).inv.naturality (tildeCoeffMap g)
  change (modulePullback X.hom.toLRSHom.toShHom).map (baseChangeIdealMapOnBase _
      (residueSpecMap_toShHom_comp_baseSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g))) ≫
      (modulePullback X.hom.toLRSHom.toShHom).map (coordConormalIso (Λ := Λ) W).hom ≫
        (Stacks.ProjectiveBundleQuotients.pullbackIso X.hom).inv.app (tildeCoeff W) =
    ((modulePullback X.hom.toLRSHom.toShHom).map (coordConormalIso (Λ := Λ) V).hom ≫
        (Stacks.ProjectiveBundleQuotients.pullbackIso X.hom).inv.app (tildeCoeff V)) ≫
      (Scheme.Modules.pullback X.hom).map (tildeCoeffMap g)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((Functor.map_comp _ _ _).symm.trans
    ((congrArg (modulePullback X.hom.toLRSHom.toShHom).map
      (baseChangeIdealMapOnBase_coordConormalIso (Λ := Λ) g)).trans
      (Functor.map_comp _ _ _)))).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg _ e2).trans (Category.assoc _ _ _).symm)

end Deformation.Examples

end

module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineHomRecovery
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineOpenTensorSections

/-!
# A morphism out of a pullback, recovered from the sections over an affine open

Let `f : T ⟶ S` be a morphism of schemes whose image lies in an affine open `U` of `S`, let `ℳ`
be a quasi-coherent `𝒪_S`-module and `𝒩` an arbitrary `𝒪_T`-module. A morphism `f^*ℳ ⟶ 𝒩` is
then determined by, and may be prescribed through, its effect on the pullbacks of the sections
of `ℳ` over `U`: the morphisms `f^*ℳ ⟶ 𝒩` are the `Γ(S, U)`-semilinear maps
`Γ(ℳ, U) ⟶ Γ(𝒩, ⊤)`, the scalars acting on the target through `f^♯`.

This is `Stacks.AlgebraicGeometry.AffineHomRecovery`, which is the case `U = S`, read on the
affine scheme `U` through the factorization `f = f' ≫ U.ι`: the pullback `f^*ℳ` is
`f'^*(ℳ|_U)` by the composition and congruence isomorphisms of the pullback and the comparison
of the restriction with the pullback along an open immersion, and those carry the pullback of a
section of `ℳ` over `U` to the pullback along `f'` of its restriction to `U` read as a global
section of `ℳ|_U` (`pullbackIso_hom_pullbackSection`).

## Main definitions

* `Stacks.AlgebraicGeometry.AffineOpenHomRecovery.lift`: the factorization `f' : T ⟶ U`.
* `Stacks.AlgebraicGeometry.AffineOpenHomRecovery.pullbackIso`: `f^*ℳ ≅ f'^*(ℳ|_U)`.
* `Stacks.AlgebraicGeometry.AffineOpenHomRecovery.homOfSections`: **the morphism `f^*ℳ ⟶ 𝒩`
  realising a prescribed semilinear map on the sections over `U`.**

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenHomRecovery.homOfSections_pullbackSection`: its value on
  the pullback of a section over `U`.
* `Stacks.AlgebraicGeometry.AffineOpenHomRecovery.hom_ext`: **two morphisms `f^*ℳ ⟶ 𝒩` agreeing
  on the pullbacks of the sections over `U` are equal.**
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenHomRecovery

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U)

/-- **The factorization of `f` through the open `U`** containing its image. -/
def lift : T ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι f (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf (Set.mem_univ t))

/-- The factorization `f'` composed with the inclusion of `U` is `f`. -/
@[reassoc (attr := simp)]
theorem lift_ι : lift f U hf ≫ U.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

variable (M : S.Modules)

/-- **The pullback along `f` is the pullback along `f'` of the restriction to `U`.** -/
def pullbackIso :
    (Scheme.Modules.pullback f).obj M ≅
      (Scheme.Modules.pullback (lift f U hf)).obj (M.restrict U.ι) :=
  (Scheme.Modules.pullbackCongr (lift_ι f U hf).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (lift f U hf) U.ι).app M).symm ≪≫
      (Scheme.Modules.pullback (lift f U hf)).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

/-- A section of `ℳ` over `U`, read as a global section of `ℳ|_U`: its restriction to the image
`U.ι ''ᵁ ⊤` of the whole of `U`, which is `U` itself up to an equality of opens. -/
def restrictTop (x : M.val.obj (op U)) : (M.restrict U.ι).val.obj (op ⊤) :=
  M.val.map (homOfLE (Scheme.Opens.ι_image_le U ⊤)).op x

/-- **The comparison carries the pullback of a section over `U` to the pullback along `f'` of
its restriction.** -/
theorem pullbackIso_hom_pullbackSection (x : M.val.obj (op U)) :
    ((pullbackIso f U hf M).hom.val.app (op ⊤))
        (Scheme.Modules.pullbackSection f M U ⊤ hf x) =
      Scheme.Modules.pullbackSection (lift f U hf) (M.restrict U.ι) ⊤ ⊤ le_top
        (restrictTop U M x) := by
  have h1 := Scheme.Modules.pullbackSection_congr (lift_ι f U hf).symm M U ⊤ hf
    (by rw [lift_ι]; exact hf) x
  have h2 := Scheme.Modules.pullbackSection_comp (lift f U hf) U.ι M U ⊤ ⊤
    (Scheme.Opens.ι_preimage_self U).ge le_top (by rw [lift_ι]; exact hf) x
  have h3 := Scheme.Modules.pullbackSection_naturality (lift f U hf)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M) ⊤ ⊤ le_top
    (Scheme.Modules.pullbackSection U.ι M U ⊤ (Scheme.Opens.ι_preimage_self U).ge x)
  have h4 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection U.ι M U ⊤
    (Scheme.Opens.ι_preimage_self U).ge (Scheme.Opens.ι_image_le U ⊤) x
  change ((Scheme.Modules.pullback (lift f U hf)).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M)).val.app (op ⊤)
      (((Scheme.Modules.pullbackComp (lift f U hf) U.ι).inv.app M).val.app (op ⊤)
        (((Scheme.Modules.pullbackCongr (lift_ι f U hf).symm).hom.app M).val.app (op ⊤)
          (Scheme.Modules.pullbackSection f M U ⊤ hf x))) = _
  rw [h1, ← h2]
  have h5 : ((Scheme.Modules.pullbackComp (lift f U hf) U.ι).inv.app M).val.app (op ⊤)
      (((Scheme.Modules.pullbackComp (lift f U hf) U.ι).hom.app M).val.app (op ⊤)
        (Scheme.Modules.pullbackSection (lift f U hf) ((Scheme.Modules.pullback U.ι).obj M) ⊤ ⊤
          le_top (Scheme.Modules.pullbackSection U.ι M U ⊤
            (Scheme.Opens.ι_preimage_self U).ge x))) =
      Scheme.Modules.pullbackSection (lift f U hf) ((Scheme.Modules.pullback U.ι).obj M) ⊤ ⊤
          le_top (Scheme.Modules.pullbackSection U.ι M U ⊤
            (Scheme.Opens.ι_preimage_self U).ge x) := by
    change (((Scheme.Modules.pullbackComp (lift f U hf) U.ι).hom.app M ≫
      (Scheme.Modules.pullbackComp (lift f U hf) U.ι).inv.app M).val.app (op ⊤)) _ = _
    rw [Iso.hom_inv_id_app]
    rfl
  rw [h5, h3, h4]
  rfl

variable [M.IsQuasicoherent] (hU : IsAffineOpen U) (N : T.Modules)

/-- The restriction of a quasi-coherent module to an open is quasi-coherent. -/
instance isQuasicoherent_restrict : (M.restrict U.ι).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_restrictFunctor U.ι M

/-- For opens `V ≤ W ≤ V`, restricting a function from `V` to `W` and back to `V` is the
identity. -/
theorem presheaf_map_map_of_le_of_le {X : Scheme.{u}} {V W : X.Opens} (h₁ : V ≤ W) (h₂ : W ≤ V)
    (r : Γ(X, V)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op r) = r := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
  have hid : (homOfLE h₁ ≫ homOfLE h₂ : V ⟶ V) = 𝟙 _ := Subsingleton.elim _ _
  rw [hid, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- For `g : T ⟶ U`, the map `(g ≫ U.ι)^♯ : Γ(S, U) ⟶ Γ(T, ⊤)` applied to the restriction of a
global function `r` of `U` back to `U` is `g^♯ r`. -/
theorem comp_ι_appLE {g : T ⟶ U.toScheme} (h : (⊤ : T.Opens) ≤ (g ≫ U.ι) ⁻¹ᵁ U)
    (r : Γ(U.toScheme, ⊤)) :
    (g ≫ U.ι).appLE U ⊤ h (S.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op r) =
      g.appTop r := by
  have key := Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ (Scheme.Opens.ι_preimage_self U).ge le_top
  have h1 : U.ι.appLE U ⊤ (Scheme.Opens.ι_preimage_self U).ge
      (S.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op r) = r := by
    rw [Scheme.Opens.ι_appLE]
    exact presheaf_map_map_of_le_of_le (X := S) _ _ r
  have h2 : (g ≫ U.ι).appLE U ⊤ h
      (S.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op r) =
      g.appLE ⊤ ⊤ le_top (U.ι.appLE U ⊤ (Scheme.Opens.ι_preimage_self U).ge
        (S.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op r)) := by
    rw [← key]
    rfl
  rw [h2, h1]
  exact congrArg (fun φ => φ r) (g.appLE_eq_app (U := ⊤))

/-- Two equal morphisms have the same `appLE`. -/
theorem appLE_congr_hom {g₁ g₂ : T ⟶ S} (e : g₁ = g₂) (h₁ : (⊤ : T.Opens) ≤ g₁ ⁻¹ᵁ U)
    (h₂ : (⊤ : T.Opens) ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U ⊤ h₁ = g₂.appLE U ⊤ h₂ := by
  subst e
  rfl

omit [M.IsQuasicoherent] in
/-- The action of the global functions of `U` on the global sections of `ℳ|_U` is the action of
the functions on `U.ι ''ᵁ ⊤` on the sections of `ℳ` there. -/
theorem restrict_ι_smul (r : Γ(U.toScheme, ⊤)) (y : Γ(M.restrict U.ι, ⊤)) :
    (r • y : Γ(M.restrict U.ι, ⊤)) =
      (show Γ(S, U.ι ''ᵁ ⊤) from r) • (show Γ(M, U.ι ''ᵁ ⊤) from y) := by
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M ⊤ r y
  rw [Scheme.Opens.ι_appIso] at h
  exact h

/-- The restriction from `U.ι ''ᵁ ⊤` back to `U`. -/
abbrev restrictBack (y : (M.restrict U.ι).val.obj (op ⊤)) : M.val.obj (op U) :=
  M.val.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op y

/-- For opens `V ≤ W ≤ V`, restricting a section of a module from `V` to `W` and back to `V` is
the identity. -/
theorem module_map_map_of_le_of_le {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens}
    (h₁ : V ≤ W) (h₂ : W ≤ V) (y : F.val.obj (op V)) :
    F.val.map (homOfLE h₁).op (F.val.map (homOfLE h₂).op y) = y := by
  have hid : (homOfLE h₂).op ≫ (homOfLE h₁).op = 𝟙 (op V) := Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, hid, PresheafOfModules.map_id]
  rfl

omit [M.IsQuasicoherent] in
/-- `restrictBack` is a left inverse of `restrictTop`. -/
theorem restrictBack_restrictTop (x : M.val.obj (op U)) :
    restrictBack U M (restrictTop U M x) = x :=
  module_map_map_of_le_of_le M (V := U) _ _ x

omit [M.IsQuasicoherent] in
/-- `restrictBack` is a right inverse of `restrictTop`. -/
theorem restrictTop_restrictBack (y : (M.restrict U.ι).val.obj (op ⊤)) :
    restrictTop U M (restrictBack U M y) = y :=
  module_map_map_of_le_of_le M (V := U.ι ''ᵁ ⊤) _ _ y

/-- The whole of `T` maps into `U` under `f' ≫ U.ι`. -/
theorem lift_le : (⊤ : T.Opens) ≤ (lift f U hf ≫ U.ι) ⁻¹ᵁ U := by
  rw [lift_ι]
  exact hf

end Stacks.AlgebraicGeometry.AffineOpenHomRecovery

namespace Stacks.AlgebraicGeometry.AffineOpenHomRecovery

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U)
  (M : S.Modules) [M.IsQuasicoherent] (hU : IsAffineOpen U) (N : T.Modules)
  (ℓ : M.val.obj (op U) →+ N.val.obj (op ⊤))
  (hℓ : ∀ (r : Γ(S, U)) (x : M.val.obj (op U)), ℓ (r • x) = f.appLE U ⊤ hf r • ℓ x)

/-- The prescribed map, read as a linear map on the global sections of `ℳ|_U`. -/
def liftLinear :
    Γ(M.restrict U.ι, ⊤) →ₗ[Γ(U.toScheme, ⊤)]
      Γ(AffineHomRecovery.pushforward (lift f U hf) N, ⊤) where
  toFun y := ℓ (restrictBack U M y)
  map_add' y z := by
    change ℓ (restrictBack U M (y + z)) = ℓ (restrictBack U M y) + ℓ (restrictBack U M z)
    rw [show restrictBack U M (y + z) = restrictBack U M y + restrictBack U M z from
      map_add _ _ _, map_add]
  map_smul' r y := by
    change ℓ (restrictBack U M (r • y)) = (lift f U hf).appTop r • ℓ (restrictBack U M y)
    have e1 : restrictBack U M (r • y) =
        (S.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op r) • restrictBack U M y := by
      rw [restrict_ι_smul]
      exact Scheme.Modules.map_smul M _ r y
    rw [e1, hℓ, appLE_congr_hom U (lift_ι f U hf).symm hf (lift_le f U hf),
      comp_ι_appLE U (lift_le f U hf) r]

/-- A morphism out of `g^*F` applied to the pullback of a global section is its effect
`AffineHomRecovery.sectionsMap` on global sections. -/
private theorem app_pullbackSection_top_eq_sectionsMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (N : Y.Modules) (χ : (Scheme.Modules.pullback g).obj F ⟶ N)
    (y : F.val.obj (op ⊤)) :
    χ.val.app (op ⊤) (Scheme.Modules.pullbackSection g F ⊤ ⊤ le_top y) =
      AffineHomRecovery.sectionsMap g F N χ y :=
  (congrArg (fun z => χ.val.app (op ⊤) z)
    (Scheme.Modules.pullbackSection_top g F le_top y)).trans
    (Stacks.RingedSpace.homEquiv_val_app g.toLRSHom.toShHom F N χ (op ⊤) y).symm

include hU in
/-- **The morphism `f^*ℳ ⟶ 𝒩` realising a prescribed semilinear map on the sections over `U`.** -/
def homOfSections : (Scheme.Modules.pullback f).obj M ⟶ N :=
  haveI : IsAffine U.toScheme := hU
  (pullbackIso f U hf M).hom ≫
    (AffineHomRecovery.homEquiv (lift f U hf) (M.restrict U.ι) N).symm (liftLinear f U hf M N ℓ hℓ)

/-- The morphism `homOfSections` sends the pullback of a section `x` of `ℳ` over `U` to `ℓ x`. -/
theorem homOfSections_pullbackSection (x : M.val.obj (op U)) :
    (homOfSections f U hf M hU N ℓ hℓ).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f M U ⊤ hf x) = ℓ x := by
  have : IsAffine U.toScheme := hU
  set φ₀ := (AffineHomRecovery.homEquiv (lift f U hf) (M.restrict U.ι) N).symm
    (liftLinear f U hf M N ℓ hℓ) with hφ₀
  have hh := (AffineHomRecovery.homEquiv (lift f U hf) (M.restrict U.ι) N).apply_symm_apply
    (liftLinear f U hf M N ℓ hℓ)
  change φ₀.val.app (op ⊤) (((pullbackIso f U hf M).hom.val.app (op ⊤))
    (Scheme.Modules.pullbackSection f M U ⊤ hf x)) = ℓ x
  rw [pullbackIso_hom_pullbackSection]
  exact (app_pullbackSection_top_eq_sectionsMap _ _ _ φ₀ _).trans
    ((DFunLike.congr_fun hh (restrictTop U M x)).trans
      (congrArg ℓ (restrictBack_restrictTop U M x)))

omit [M.IsQuasicoherent] in
include hU in
/-- **Two morphisms `f^*ℳ ⟶ 𝒩` agreeing on the pullbacks of the sections over `U` are equal.** -/
theorem hom_ext [M.IsQuasicoherent] {φ ψ : (Scheme.Modules.pullback f).obj M ⟶ N}
    (h : ∀ x : M.val.obj (op U), φ.val.app (op ⊤) (Scheme.Modules.pullbackSection f M U ⊤ hf x) =
      ψ.val.app (op ⊤) (Scheme.Modules.pullbackSection f M U ⊤ hf x)) : φ = ψ := by
  have : IsAffine U.toScheme := hU
  suffices hs : (pullbackIso f U hf M).inv ≫ φ = (pullbackIso f U hf M).inv ≫ ψ by
    simpa using congrArg ((pullbackIso f U hf M).hom ≫ ·) hs
  refine AffineHomRecovery.hom_ext (lift f U hf) (M.restrict U.ι) N fun y => ?_
  have key : ∀ χ : (Scheme.Modules.pullback f).obj M ⟶ N,
      AffineHomRecovery.sectionsMap (lift f U hf) (M.restrict U.ι) N
        ((pullbackIso f U hf M).inv ≫ χ) y =
      χ.val.app (op ⊤) (Scheme.Modules.pullbackSection f M U ⊤ hf (restrictBack U M y)) := by
    intro χ
    have hy := (pullbackIso_hom_pullbackSection f U hf M (restrictBack U M y)).trans
      (congrArg (Scheme.Modules.pullbackSection (lift f U hf) (M.restrict U.ι) ⊤ ⊤ le_top)
        (restrictTop_restrictBack U M y))
    refine (app_pullbackSection_top_eq_sectionsMap (lift f U hf) (M.restrict U.ι) N
      ((pullbackIso f U hf M).inv ≫ χ) y).symm.trans ?_
    rw [← hy]
    change ((pullbackIso f U hf M).hom ≫ (pullbackIso f U hf M).inv ≫ χ).val.app (op ⊤) _ = _
    rw [Iso.hom_inv_id_assoc]
  exact (key φ).trans ((h _).trans (key ψ).symm)

/-- The pullback of a section is additive. -/
theorem pullbackSection_add {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) (V : X.Opens)
    (W : Y.Opens) (h : W ≤ g ⁻¹ᵁ V) (a b : F.val.obj (op V)) :
    Scheme.Modules.pullbackSection g F V W h (a + b) =
      Scheme.Modules.pullbackSection g F V W h a + Scheme.Modules.pullbackSection g F V W h b := by
  unfold Scheme.Modules.pullbackSection
  rw [map_add]
  exact map_add (((Scheme.Modules.pullback g).obj F).val.map (homOfLE h).op).hom _ _

/-- The pullback of a section is semilinear along `f^♯`. -/
theorem pullbackSection_smul {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) (V : X.Opens)
    (W : Y.Opens) (h : W ≤ g ⁻¹ᵁ V) (r : X.ringCatSheaf.obj.obj (op V)) (a : F.val.obj (op V)) :
    Scheme.Modules.pullbackSection g F V W h (r • a) =
      (show Y.ringCatSheaf.obj.obj (op W) from g.appLE V W h r) •
        Scheme.Modules.pullbackSection g F V W h a := by
  unfold Scheme.Modules.pullbackSection
  rw [map_smul]
  exact (((Scheme.Modules.pullback g).obj F).val.map_smul (homOfLE h).op _ _).trans rfl

/-- The module structure on the sections of a sheaf of modules spelled over
`Stacks.RingedSpace.structureRingSheaf`, over the functions of the scheme. -/
local instance sectionsModuleStructureRingSheaf {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) : Module Γ(X, U) (F.val.obj (op U)) :=
  (F.val.obj (op U)).isModule

omit [M.IsQuasicoherent] in
include hU in
/-- **Two morphisms out of `f^*(F ⊗ G)` agreeing on the pullbacks of the pure tensors of sections
over `U` are equal.** -/
theorem hom_ext_tensor (F G : S.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {φ ψ : (Scheme.Modules.pullback f).obj
      (Stacks.AlgebraicGeometry.AffineOpenTensorSections.tensorMod F G) ⟶ N}
    (h : ∀ (a : Γ(F, U)) (b : Γ(G, U)),
      φ.val.app (op ⊤) (Scheme.Modules.pullbackSection f _ U ⊤ hf
        (Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTmul F G U a b)) =
      ψ.val.app (op ⊤) (Scheme.Modules.pullbackSection f _ U ⊤ hf
        (Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTmul F G U a b))) :
    φ = ψ := by
  refine hom_ext f U hf _ hU N fun z => ?_
  obtain ⟨t, rfl⟩ :=
    (Stacks.AlgebraicGeometry.AffineOpenTensorSections.bijective_gammaTensorMap hU F G).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact h a b
  | add x y hx hy =>
    have e := pullbackSection_add f
      (Stacks.AlgebraicGeometry.AffineOpenTensorSections.tensorMod F G) U ⊤ hf
      (Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTensorMap F G U x)
      (Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTensorMap F G U y)
    rw [map_add]
    exact (congrArg (fun w => φ.val.app (op ⊤) w) e).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans ((map_add _ _ _).symm.trans
        (congrArg (fun w => ψ.val.app (op ⊤) w) e.symm))))

end Stacks.AlgebraicGeometry.AffineOpenHomRecovery

end

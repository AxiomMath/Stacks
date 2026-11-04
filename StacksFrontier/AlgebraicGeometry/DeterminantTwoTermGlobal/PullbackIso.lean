module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.PullbackLocal
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections

/-!
# The determinant commutes with pullback

Let `f : X ⟶ Y` be a morphism of schemes and `K` a perfect object of `D(𝒪_Y)` of Tor amplitude in
`[-1, 0]`. The maps of local determinants along `f` glue to a morphism `det(K) → f_* det(Lf^*K)`,
whose adjoint `f^* det(K) → det(Lf^*K)` is an isomorphism: on an affine open `W ⊆ X` mapping into
an affine open `V ⊆ Y` it is the base change `Γ(X, W) ⊗_{Γ(Y, V)} det(M_V) ≅ det(M'_W)`. When `K`
has rank zero it carries the pullback of `δ(K)` to `δ(Lf^*K)`.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.detPushforwardMap`: `det(K) → f_* det(Lf^*K)`.
* `AlgebraicGeometry.DeterminantTwoTerm.pullbackDetIso`: `f^* det(K) ≅ det(Lf^*K)`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite TwoTermDeterminant
open AlgebraicGeometry.StandardModel
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (K : PerfectTwoTermAmplitude Y)

/-- The pieces of an affine open `W ≤ f⁻¹U`: affine opens `W' ≤ W` mapping into an affine open
`V ≤ U`. -/
abbrev PbIdx (U : Y.Opens) (W : X.affineOpens) :=
  Σ V : AffineLineSystem.AffBelow U,
    {W' : X.affineOpens // (W' : X.Opens) ≤ (W : X.Opens) ⊓ f ⁻¹ᵁ V.1}

/-- An affine open `W ≤ f⁻¹U` is covered by the affine opens `W' ≤ W` mapping into affine opens
`V ≤ U`. -/
theorem le_iSup_pbIdx (U : Y.Opens) (W : X.affineOpens) (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) :
    (W : X.Opens) ≤ ⨆ p : PbIdx f U W, (p.2.1 : X.Opens) := by
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (hW hx) U.2
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (W : X.Opens) ⊓ f ⁻¹ᵁ V from ⟨hx, hxV⟩) ((W : X.Opens) ⊓ f ⁻¹ᵁ V).2
  exact Opens.mem_iSup.mpr ⟨⟨⟨⟨V, hV⟩, hVU⟩, ⟨⟨W', hW'⟩, hle⟩⟩, hxW'⟩

/-- The map of local determinants along `f` over `W` followed by restriction to `W' ≤ W` is the map
of local determinants along `f` over `W'`. -/
theorem pullbackDetMap_restrict (V : Y.affineOpens) {W W' : X.affineOpens}
    (h : (W : X.Opens) ≤ f ⁻¹ᵁ V) (hWW : (W' : X.Opens) ≤ W) (x : localDet K V.2.fromSpec) :
    (detSystem (pullbackObj f K)).map hWW (pullbackDetMap f K V W h x) =
      pullbackDetMap f K V W' (hWW.trans h) x := by
  have hg : Spec.map (f.appLE V W h ≫ X.presheaf.map (homOfLE hWW).op) ≫ V.2.fromSpec =
      W'.2.fromSpec ≫ f := by
    rw [Scheme.Hom.appLE_map]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W'.2 _
  rw [pullbackDetMap, detSystem_map_pullbackDetMapAt f K V _ _ hWW hg]
  exact pullbackDetMapAt_congr f K V W' (by rw [Scheme.Hom.appLE_map]) hg
    (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W'.2 _) x

/-- Restricting from `V` to `V' ≤ V` and then mapping along `f` over `W ≤ f⁻¹V'` is the map of
local determinants along `f` from `V` over `W`. -/
theorem pullbackDetMap_detSystem_map {V V' : Y.affineOpens} (W : X.affineOpens)
    (hVV : (V' : Y.Opens) ≤ V) (h : (W : X.Opens) ≤ f ⁻¹ᵁ V') (x : localDet K V.2.fromSpec) :
    pullbackDetMap f K V' W h ((detSystem K).map hVV x) =
      pullbackDetMap f K V W (h.trans (f.preimage_mono hVV)) x := by
  have hg : Spec.map (Y.presheaf.map (homOfLE hVV).op ≫ f.appLE V' W h) ≫ V.2.fromSpec =
      W.2.fromSpec ≫ f := by
    rw [Scheme.Hom.map_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W.2 _
  rw [pullbackDetMap, pullbackDetMapAt_detSystem_map f K W hVV _ _ hg]
  exact pullbackDetMapAt_congr f K V W (by rw [Scheme.Hom.map_appLE]) hg
    (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W.2 _) x

/-- For `V ≤ U` and `W' ≤ W` with `W' ≤ f⁻¹V` and `W ≤ f⁻¹U`, the image of `r ∈ Γ(Y, U)` under
restriction to `V` followed by `f.appLE` equals its image under `f.app U` followed by the
restrictions to `W` and then `W'`. -/
theorem appLE_presheaf_map {U V : Y.Opens} (hVU : V ≤ U) {W W' : X.Opens} (h : W' ≤ f ⁻¹ᵁ V)
    (hW'W : W' ≤ W) (hW : W ≤ f ⁻¹ᵁ U) (r : Γ(Y, U)) :
    f.appLE V W' h (Y.presheaf.map (homOfLE hVU).op r) =
      X.presheaf.map (homOfLE hW'W).op (X.presheaf.map (homOfLE hW).op (f.app U r)) := by
  simp only [← ConcreteCategory.comp_apply]
  congr 1
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

/-- Two sections over an affine open `W ≤ f⁻¹U` agree if their restrictions to every piece of
`PbIdx f U W` agree. -/
private theorem ext_of_pbIdx (f : X ⟶ Y) (K : PerfectTwoTermAmplitude Y) {U : Y.Opens}
    {W : X.affineOpens} (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) {x y : (detSystem (pullbackObj f K)).obj W}
    (h : ∀ p : PbIdx f U W, (detSystem (pullbackObj f K)).map (p.2.2.trans inf_le_left) x =
      (detSystem (pullbackObj f K)).map (p.2.2.trans inf_le_left) y) : x = y :=
  (detSystem (pullbackObj f K)).ext_of_cover W (fun p : PbIdx f U W => p.2.1)
    (fun p => p.2.2.trans inf_le_left) (le_iSup_pbIdx f U W hW) h

variable {f K}

/-- **The local pulled-back determinants of a section agree.** For a compatible family `s` over `U`
and affine opens `V₁, V₂ ≤ U` with `W ≤ f⁻¹V₁ ⊓ f⁻¹V₂`, the two maps along `f` agree on `W`. -/
theorem pullbackDetMap_eq_of_sections {U : Y.Opens} (s : (detSystem K).Sections U)
    (V₁ V₂ : AffineLineSystem.AffBelow U) (W : X.affineOpens) (h₁ : (W : X.Opens) ≤ f ⁻¹ᵁ V₁.1)
    (h₂ : (W : X.Opens) ≤ f ⁻¹ᵁ V₂.1) :
    pullbackDetMap f K V₁.1 W h₁ (s.1 V₁) = pullbackDetMap f K V₂.1 W h₂ (s.1 V₂) := by
  let U₃ : Y.Opens := (V₁.1 : Y.Opens) ⊓ V₂.1
  refine ext_of_pbIdx f K (U := U₃) (le_inf h₁ h₂) fun p => ?_
  have hV1 : (p.1.1 : Y.Opens) ≤ V₁.1 := p.1.2.trans inf_le_left
  have hV2 : (p.1.1 : Y.Opens) ≤ V₂.1 := p.1.2.trans inf_le_right
  have hW3 : (p.2.1 : X.Opens) ≤ f ⁻¹ᵁ p.1.1 := p.2.2.trans inf_le_right
  refine (pullbackDetMap_restrict f K V₁.1 h₁ (p.2.2.trans inf_le_left) _).trans ?_
  refine Eq.trans ?_ (pullbackDetMap_restrict f K V₂.1 h₂ (p.2.2.trans inf_le_left) _).symm
  have e1 := (pullbackDetMap_detSystem_map f K p.2.1 hV1 hW3 (s.1 V₁)).symm.trans
    (congrArg (pullbackDetMap f K p.1.1 p.2.1 hW3) (s.2 V₁ ⟨p.1.1, hV1.trans V₁.2⟩ hV1))
  have e2 := (pullbackDetMap_detSystem_map f K p.2.1 hV2 hW3 (s.1 V₂)).symm.trans
    (congrArg (pullbackDetMap f K p.1.1 p.2.1 hW3) (s.2 V₂ ⟨p.1.1, hV2.trans V₂.2⟩ hV2))
  exact e1.trans e2.symm

variable (f K)

/-- The local pulled-back determinants of a compatible family, glued over an affine open
`W ≤ f⁻¹U`. -/
theorem existsUnique_pbValue {U : Y.Opens} (s : (detSystem K).Sections U) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) :
    ∃! x : (detSystem (pullbackObj f K)).obj W, ∀ p : PbIdx f U W,
      (detSystem (pullbackObj f K)).map (p.2.2.trans inf_le_left) x =
        pullbackDetMap f K p.1.1 p.2.1 (p.2.2.trans inf_le_right) (s.1 p.1) := by
  refine (detSystem (pullbackObj f K)).existsUnique_glue W (W := fun p : PbIdx f U W => p.2.1)
    (fun p => p.2.2.trans inf_le_left) (le_iSup_pbIdx f U W hW) _ fun p q W'' h₁ h₂ => ?_
  refine (pullbackDetMap_restrict f K _ _ h₁ _).trans (Eq.trans ?_
    (pullbackDetMap_restrict f K _ _ h₂ _).symm)
  exact pullbackDetMap_eq_of_sections s p.1 q.1 W'' _ _

/-- The value over `W` of the pulled-back section. -/
def pbValue {U : Y.Opens} (s : (detSystem K).Sections U) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) : (detSystem (pullbackObj f K)).obj W :=
  (existsUnique_pbValue f K s W hW).exists.choose

/-- The restriction of `pbValue f K s W hW` to each piece `W'` of `PbIdx f U W` is the map of local
determinants along `f` applied to the value of `s` on the corresponding `V`. -/
theorem pbValue_spec {U : Y.Opens} (s : (detSystem K).Sections U) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) (p : PbIdx f U W) :
    (detSystem (pullbackObj f K)).map (p.2.2.trans inf_le_left) (pbValue f K s W hW) =
      pullbackDetMap f K p.1.1 p.2.1 (p.2.2.trans inf_le_right) (s.1 p.1) :=
  (existsUnique_pbValue f K s W hW).exists.choose_spec p

/-- Over an affine open mapping into an affine open `V ≤ U`, the pulled-back section is the map of
local determinants along `f` applied to the value of the section on `V`. -/
theorem pbValue_eq {U : Y.Opens} (s : (detSystem K).Sections U) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) (V : AffineLineSystem.AffBelow U)
    (h : (W : X.Opens) ≤ f ⁻¹ᵁ V.1) :
    pbValue f K s W hW = pullbackDetMap f K V.1 W h (s.1 V) := by
  refine ext_of_pbIdx f K hW fun p => ?_
  rw [pbValue_spec]
  exact (pullbackDetMap_eq_of_sections s p.1 V p.2.1 _ _).trans
    (pullbackDetMap_restrict f K V.1 h _ _).symm

/-- The restriction of the pulled-back section over `W` to `W' ≤ W` is the pulled-back section over
`W'`. -/
theorem pbValue_restrict {U : Y.Opens} (s : (detSystem K).Sections U) {W W' : X.affineOpens}
    (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) (hWW : (W' : X.Opens) ≤ W) :
    (detSystem (pullbackObj f K)).map hWW (pbValue f K s W hW) =
      pbValue f K s W' (hWW.trans hW) := by
  refine ext_of_pbIdx f K (hWW.trans hW) fun p => ?_
  rw [AffineLineSystem.map_map, pbValue_spec]
  exact pbValue_spec f K s W hW ⟨p.1, ⟨p.2.1, le_inf ((p.2.2.trans inf_le_left).trans hWW)
    (p.2.2.trans inf_le_right)⟩⟩

/-- The pulled-back section of a sum is the sum of the pulled-back sections. -/
theorem pbValue_add {U : Y.Opens} (s t : (detSystem K).Sections U) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) :
    pbValue f K (s + t) W hW = pbValue f K s W hW + pbValue f K t W hW := by
  refine ext_of_pbIdx f K hW fun p => ?_
  rw [map_add, pbValue_spec, pbValue_spec, pbValue_spec]
  exact map_add _ _ _

/-- The pulled-back section of `r • s` is `s`'s pulled-back section multiplied by the image of `r`
under `f^♯` restricted to `W`. -/
theorem pbValue_smul {U : Y.Opens} (r : Γ(Y, U)) (s : (detSystem K).Sections U)
    (W : X.affineOpens) (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U) :
    pbValue f K (r • s) W hW = X.presheaf.map (homOfLE hW).op (f.app U r) • pbValue f K s W hW := by
  refine ext_of_pbIdx f K hW fun p => ?_
  rw [pbValue_spec, LinearMap.map_smulₛₗ, pbValue_spec]
  refine ((pullbackDetMap f K p.1.1 p.2.1 (p.2.2.trans inf_le_right)).map_smulₛₗ
    (Y.presheaf.map (homOfLE p.1.2).op r) (s.1 p.1)).trans ?_
  exact congrArg (· • _) (appLE_presheaf_map f p.1.2 _ (p.2.2.trans inf_le_left) hW r)

/-- The pulled-back section of a compatible family over `U`, a compatible family over `f⁻¹U`. -/
def pbSections {U : Y.Opens} (s : (detSystem K).Sections U) :
    (detSystem (pullbackObj f K)).Sections (f ⁻¹ᵁ U) :=
  ⟨fun W => pbValue f K s W.1 W.2, fun W _ h => pbValue_restrict f K s W.2 h⟩

/-- Pulling back the restriction of `s` to `U' ≤ U` gives, over `W ≤ f⁻¹U'`, the pulled-back
section of `s`. -/
theorem pbValue_restrictFun {U U' : Y.Opens} (hUU : U' ≤ U) (s : (detSystem K).Sections U)
    (W : X.affineOpens) (hW : (W : X.Opens) ≤ f ⁻¹ᵁ U') :
    pbValue f K ((detSystem K).restrictFun hUU s) W hW =
      pbValue f K s W (hW.trans (f.preimage_mono hUU)) := by
  refine (existsUnique_pbValue f K _ W hW).unique (pbValue_spec f K _ W hW) fun p => ?_
  refine (pbValue_restrict f K s _ (p.2.2.trans inf_le_left)).trans ?_
  exact pbValue_eq f K s p.2.1 _ ⟨p.1.1, p.1.2.trans hUU⟩ (p.2.2.trans inf_le_right)

/-- Pulling back compatible families along `f`, a map semilinear over `f^♯`. -/
def pbSectionsₛₗ (U : Y.Opens) :
    (detSystem K).Sections U →ₛₗ[(f.app U).hom] (detSystem (pullbackObj f K)).Sections (f ⁻¹ᵁ U)
    where
  toFun := pbSections f K
  map_add' s t := Subtype.ext (funext fun W => pbValue_add f K s t W.1 W.2)
  map_smul' r s := Subtype.ext (funext fun W => pbValue_smul f K r s W.1 W.2)

/-- `pbSections` commutes with restriction along `U' ≤ U` and `f⁻¹U' ≤ f⁻¹U`. -/
theorem pbSections_restrict {U U' : Y.Opens} (hUU : U' ≤ U) (s : (detSystem K).Sections U) :
    pbSections f K ((detSystem K).restrict hUU s) =
      (detSystem (pullbackObj f K)).restrict (f.preimage_mono hUU) (pbSections f K s) :=
  Subtype.ext (funext fun W => pbValue_restrictFun f K hUU s W.1 W.2)

/-- The pulled-back sections, as a map of presheaves of abelian groups. -/
def detPushforwardPresheaf : (detModule K).presheaf ⟶
    ((Scheme.Modules.pushforward f).obj (detModule (pullbackObj f K))).presheaf where
  app U := AddCommGrpCat.ofHom (pbSectionsₛₗ f K U.unop).toAddMonoidHom
  naturality {U U'} i := by
    ext s
    exact pbSections_restrict f K i.unop.le s

/-- **The pulled-back local determinants glue to `det(K) → f_* det(Lf^*K)`.** -/
def detPushforwardMap :
    detModule K ⟶ (Scheme.Modules.pushforward f).obj (detModule (pullbackObj f K)) :=
  ⟨PresheafOfModules.homMk (detPushforwardPresheaf f K) fun U r s =>
    (pbSectionsₛₗ f K U.unop).map_smulₛₗ r s⟩

/-- On sections over `U`, `detPushforwardMap f K` is `pbSections f K`. -/
theorem detPushforwardMap_app (U : Y.Opens) (s : Γ(detModule K, U)) :
    (detPushforwardMap f K).app U s = pbSections f K s := rfl

/-- **The comparison `f^* det(K) → det(Lf^*K)`**, adjoint to the glued pulled-back local
determinants. -/
def pullbackDetHom :
    (Scheme.Modules.pullback f).obj (detModule K) ⟶ detModule (pullbackObj f K) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (detPushforwardMap f K)

/-- `pullbackDetHom f K` over `f⁻¹U`, applied to the image of a section `a` under the unit of the
pullback–pushforward adjunction, is `detPushforwardMap f K` applied to `a`. -/
theorem pullbackDetHom_unit (U : Y.Opens) (a : Γ(detModule K, U)) :
    (pullbackDetHom f K).val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (detModule K)).val.app
          (op U) a) = (detPushforwardMap f K).app U a := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit (detModule K)
    (detModule (pullbackObj f K)) (pullbackDetHom f K)
  rw [pullbackDetHom, Equiv.apply_symm_apply] at h
  exact (congrArg (fun q : detModule K ⟶ (Scheme.Modules.pushforward f).obj
    (detModule (pullbackObj f K)) => q.val.app (op U) a) h).symm

/-- `pullbackDetHom f K` sends the pullback to `W ≤ f⁻¹U` of a section `a` of `det(K)` over `U` to
the restriction to `W` of `detPushforwardMap f K` applied to `a`. -/
theorem pullbackDetHom_pullbackSection (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (a : Γ(detModule K, U)) :
    (pullbackDetHom f K).val.app (op W) (Scheme.Modules.pullbackSection f (detModule K) U W h a) =
      (detModule (pullbackObj f K)).presheaf.map (homOfLE h).op
        ((detPushforwardMap f K).app U a) := by
  refine (PresheafOfModules.naturality_apply (pullbackDetHom f K).val (homOfLE h).op _).trans ?_
  exact congrArg _ (pullbackDetHom_unit f K U a)

/-- The semilinear map `m ↦ 1 ⊗ m` into an extension of scalars. -/
def extendScalarsUnitₛₗ {R S : CommRingCat.{u}} (σ : R ⟶ S) (A : ModuleCat.{u} R) :
    A →ₛₗ[σ.hom] (ModuleCat.extendScalars σ.hom).obj A where
  toFun a := (1 : S) ⊗ₜ[R, σ.hom] a
  map_add' _ _ := TensorProduct.tmul_add _ _ _
  map_smul' r a := (extendScalarsUnit σ.hom A).map_smul r a

/-- `extendScalarsUnitₛₗ σ A` sends `a` to `1 ⊗ a`. -/
theorem extendScalarsUnitₛₗ_apply {R S : CommRingCat.{u}} (σ : R ⟶ S) (A : ModuleCat.{u} R)
    (a : A) : extendScalarsUnitₛₗ σ A a = (1 : S) ⊗ₜ[R, σ.hom] a := rfl

/-- A linear map out of an extension of scalars to a base change, compatible with the two maps out
of the module, is bijective. -/
theorem bijective_of_extendScalars {R S : CommRingCat.{u}} (σ : R ⟶ S) (A : ModuleCat.{u} R)
    {N : Type u} [AddCommGroup N] [Module S N] {φ : A →ₛₗ[σ.hom] N}
    (hφ : IsBaseChangeAlong σ.hom φ) (k : (ModuleCat.extendScalars σ.hom).obj A →ₗ[S] N)
    (hk : ∀ a, k ((1 : S) ⊗ₜ[R,σ.hom] a) = φ a) : Function.Bijective k :=
  IsBaseChangeAlong.bijective_lift
    (isBaseChangeAlong_of_extendScalarsIso _ (Iso.refl _) (extendScalarsUnitₛₗ σ A) fun _ => rfl)
    hφ k (LinearMap.ext hk)

/-- `pullbackDetHom f K` is bijective on sections over an affine open `W` mapping into an affine
open `V`. -/
theorem bijective_pullbackDetHom_app (V : Y.affineOpens) (W : X.affineOpens)
    (h : (W : X.Opens) ≤ f ⁻¹ᵁ V) :
    Function.Bijective ((pullbackDetHom f K).val.app (op (W : X.Opens))) := by
  let e := affinePullbackSectionsBaseChangeIso f (detModule K) V.2 W.2 h
  let k : (ModuleCat.extendScalars (f.appLE V W h).hom).obj
      (ModuleCat.of Γ(Y, V) Γ(detModule K, V)) →ₗ[Γ(X, W)]
      localDet (pullbackObj f K) W.2.fromSpec :=
    (detSectionsEquiv (pullbackObj f K) W).toLinearMap ∘ₗ
      Scheme.Modules.sectionsLinearMap (pullbackDetHom f K) W ∘ₗ e.hom.hom
  have hk : Function.Bijective k := by
    refine bijective_of_extendScalars (f.appLE V W h) (ModuleCat.of Γ(Y, V) Γ(detModule K, V))
      ((isBaseChangeAlong_pullbackDetMap f K V W h).comp_linearEquiv_right
        (detSectionsEquiv K V)) k fun a => ?_
    have h1 := affinePullbackSectionsBaseChangeIso_one_tmul f (detModule K) V.2 W.2 h a
    have h2 : detSectionsEquiv (pullbackObj f K) W ((pullbackDetHom f K).val.app (op W)
        (Scheme.Modules.pullbackSection f (detModule K) V W h a)) =
          pullbackDetMap f K V W h (detSectionsEquiv K V a) :=
      (congrArg _ (pullbackDetHom_pullbackSection f K V W h a)).trans
        (pbValue_eq f K a W h ⟨V, le_rfl⟩ h)
    have h3 : k ((1 : Γ(X, W)) ⊗ₜ[Γ(Y, V), (f.appLE V W h).hom] a) =
        detSectionsEquiv (pullbackObj f K) W ((pullbackDetHom f K).val.app (op (W : X.Opens))
          (e.hom ((1 : Γ(X, W)) ⊗ₜ[Γ(Y, V), (f.appLE V W h).hom] a))) := rfl
    exact h3.trans ((congrArg (fun z => detSectionsEquiv (pullbackObj f K) W
      ((pullbackDetHom f K).val.app (op (W : X.Opens)) z)) h1).trans h2)
  exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso e.hom)).1
    ((Function.Bijective.of_comp_iff' (detSectionsEquiv (pullbackObj f K) W).bijective _).1 hk)

/-- The comparison `f^* det(K) → det(Lf^*K)` is an isomorphism. -/
instance isIso_pullbackDetHom : IsIso (pullbackDetHom f K) := by
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f (detModule K)
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover _
    (fun p : Σ V : Y.affineOpens, {W : X.affineOpens // (W : X.Opens) ≤ f ⁻¹ᵁ V} =>
      (p.2.1 : X.Opens)) ?_ (fun p => p.2.1.2) fun p => bijective_pullbackDetHom_app f K _ _ p.2.2
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) (⊤ : Y.Opens).2
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).2
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨⟨W, hW⟩, hle⟩⟩, hxW⟩

/-- For a morphism of schemes `f : X ⟶ Y` and a perfect object `K` of `D(𝒪_Y)` of Tor amplitude in
`[-1, 0]`, the canonical identification `f^* det(K) ≅ det(Lf^*K)`, adjoint to the glued maps of
local determinants (`detSectionsEquiv_pullbackDetIso_hom`). -/
@[stacks 0FJY "(b) the canonical identification f^*det(K) → det(Lf^*K)"]
def pullbackDetIso :
    (Scheme.Modules.pullback f).obj (detModule K) ≅ detModule (pullbackObj f K) :=
  asIso (pullbackDetHom f K)

/-- For affine opens `V ⊆ Y` and `W ⊆ f⁻¹V`, the identification `f^* det(K) ≅ det(Lf^*K)` sends the
pullback of a section `a` of `det(K)` over `V` to the image of `a` under the base change
`det(M_V) → Γ(X, W) ⊗_{Γ(Y, V)} det(M_V) = det(M'_W)` of the determinants of More on Algebra,
Section 0FJI of the local avatars `M_V` of `K` and `M'_W` of `Lf^*K`. -/
@[stacks 0FJY "(b) the identification f^*det(K) → det(Lf^*K) is, over affine opens W ⊆ f⁻¹V, the
base change of the determinant of the local avatar of K over V"]
theorem detSectionsEquiv_pullbackDetIso_hom (V : Y.affineOpens) (W : X.affineOpens)
    (h : (W : X.Opens) ≤ f ⁻¹ᵁ V) (a : Γ(detModule K, V)) :
    detSectionsEquiv (pullbackObj f K) W ((pullbackDetIso f K).hom.val.app (op W)
        (Scheme.Modules.pullbackSection f (detModule K) V W h a)) =
      pullbackDetMap f K V W h (detSectionsEquiv K V a) :=
  (congrArg _ (pullbackDetHom_pullbackSection f K V W h a)).trans
    (pbValue_eq f K a W h ⟨V, le_rfl⟩ h)

/-- If `K` has rank zero, the pulled-back section of `δ(K)` over an affine open `W` is the
determinant section `δ` of the local complex of `Lf^*K` over `W`. -/
theorem pbValue_deltaSection (hK : IsRankZero K) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    pbValue f K ((detSystem K).sec ⊤ (deltaSection K hK)) W hW =
      delta (localComplex (pullbackObj f K) W.2.fromSpec) (isRankZero_pullbackObj f K hK _ _) := by
  refine (existsUnique_pbValue f K _ W hW).unique (pbValue_spec f K _ W hW) fun p => ?_
  refine (((detSystem (pullbackObj f K)).sec ⊤
    (deltaSection (pullbackObj f K) (isRankZero_pullbackObj f K hK))).2 ⟨W, le_top⟩
    ⟨p.2.1, le_top⟩ (p.2.2.trans inf_le_left)).trans ?_
  exact (pullbackDetMapAt_delta f K p.1.1 p.2.1 _ _ hK).symm

/-- If `K` has rank zero, the identification `f^* det(K) ≅ det(Lf^*K)` carries the pullback of the
canonical global section `δ(K)` to `δ(Lf^*K)`. -/
@[stacks 0FJY "(c) if K has rank 0, δ(K) pulls back to δ(Lf^*K) via f^*det(K) → det(Lf^*K)"]
theorem pullbackDetIso_hom_deltaSection (hK : IsRankZero K) :
    (pullbackDetIso f K).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection f (detModule K) ⊤ ⊤ le_top (deltaSection K hK)) =
      deltaSection (pullbackObj f K) (isRankZero_pullbackObj f K hK) := by
  refine (pullbackDetHom_pullbackSection f K ⊤ ⊤ le_top (deltaSection K hK)).trans ?_
  apply ((detSystem (pullbackObj f K)).sec ⊤).injective
  exact Subtype.ext (funext fun W => pbValue_deltaSection f K hK W.1 (W.2.trans le_top))

end AlgebraicGeometry.DeterminantTwoTerm

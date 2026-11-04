module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleStalkLargeFiber
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits

/-!
# The stalk of `ε^*M̃` on an affine represented algebraic space

Let `U` be an object of the big fppf site over `S` whose scheme `T` is affine, `i : T ≅ Spec A`,
and let `x̄` be a geometric point of the algebraic space `h_U = yoneda.obj U`.  For an `A`-module
`M`, restrict `M̃` to `T` along `i` and apply the associated-module functor
`ε^* = AlgebraicGeometry.Space.representedAssociatedModule` of Stacks 03DU (4).  This file
computes the module stalk of the result at `x̄`: it is `M ⊗_A 𝒪_{h_U, x̄}`, naturally in `M`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineStalkRingHom`: the ring map `A → 𝒪_{h_U, x̄}`
  sending `a` to the germ at `x̄`, on the identity chart of `h_U`, of the global function
  `i^*(a)` of `T`.
* `AlgebraicGeometry.Space.representedAffineAssociatedModuleStalkIso`: the natural isomorphism
  `(ε^*(M̃|_T))_{x̄} ≅ 𝒪_{h_U, x̄} ⊗_A M` of functors of the `A`-module `M`.

## Main results

* `AlgebraicGeometry.Space.pointStalkRingEquiv_representedAffineStalkRingHom`: read in the étale
  local ring, the ring map sends `a` to the germ of `i^*(a)` on the canonical neighbourhood.
* `AlgebraicGeometry.Space.isIso_app_of_isIso_app_self`: a natural transformation between
  colimit-preserving functors out of `A`-modules is an isomorphism once it is one at `A`.

## Implementation notes

The comparison `𝒪_{x̄} ⊗_A M ⟶ (ε^*(M̃|_T))_{x̄}` is built for any additive functor
`F : Mod_A ⥤ Mod_R` from an element `e ∈ F(A)` on which `A` acts through a ring map `γ : A → R`
(`AlgebraicGeometry.Space.wattsTrans`, after Eilenberg and Watts): `m ∈ M` is the image of `1`
under `a ↦ a • m`, and is sent to the image of `e`.  Here `e` is the germ of `1`, and that `A`
acts on it through `γ` is a computation of multiplication by `a` along each factor of the
functor: `Ã = 𝒪_{Spec A}` by definition, restriction along `i` (`Scheme.Modules.restrictUnitIso`),
the associated-module functor, through the transpose of `SheafOfModules.pullbackObjUnitToUnit`
(`AlgebraicGeometry.Space.pullbackObjUnitToUnit_conj_val_app_one`), and the stalk.  The
comparison is an isomorphism at `A` because the stalk of the structure sheaf is free of rank one
on the germ of `1`, and so everywhere, both functors preserving colimits.

The module stalk is only known to preserve colimits of shapes in `Type 0`
(`Stacks.preservesColimits_sheafModuleFiber`); the argument is repeated here at the size of the
universe of the modules, which the free presentation of an arbitrary module needs.

Several composites of morphisms are written with `CategoryStruct.comp` at a named category, or
assembled from their components by `Eq.trans` rather than rewritten: the categories of modules
of the small étale site of `h_U` carry two syntactically different instances, through
`AlgebraicGeometry.Space.Modules` and through `SheafOfModules`, which agree only up to
unfolding.  The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched
off for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModuleEtalePullback.lean`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian


section Watts

variable {A R : Type u} [CommRing A] [CommRing R] (F : ModuleCat.{u} A ⥤ ModuleCat.{u} R)
  [F.Additive] (γ : A →+* R) (e : F.obj (ModuleCat.of A A))

/-- The `γ`-semilinear map `M → F(M)` attached to an element `e` of `F(A)`: an element `m` of
`M` is the image of `1` under the `A`-linear map `A → M`, `a ↦ a • m`, and is sent to the image
of `e` under that map. -/
def wattsMap (he : ∀ a : A, F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a)) e = γ a • e)
    (M : ModuleCat.{u} A) : M ⟶ (ModuleCat.restrictScalars γ).obj (F.obj M) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars γ).obj (F.obj M))
    (show M →ₗ[A] (ModuleCat.restrictScalars γ).obj (F.obj M) from
    { toFun := fun m => F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)) e
      map_add' := fun m m' => by
        simp only [LinearMap.toSpanSingleton_add]
        rw [ModuleCat.ofHom_add, F.map_add]
        rfl
      map_smul' := fun a m => by
        have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A M (a • m)) =
            ModuleCat.ofHom (LinearMap.toSpanSingleton A A a) ≫
              ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) := by
          ext
          simp
        rw [h, F.map_comp, ModuleCat.comp_apply, he, map_smul]
        rfl })

omit [F.Additive] in
/-- The maps `wattsMap` are natural in the module. -/
theorem map_wattsMap_apply {M N : ModuleCat.{u} A} (f : M ⟶ N) (m : M) :
    F.map f (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)) e) =
      F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A N (f m))) e := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) ≫ f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A N (f m)) := by
    ext
    simp
  rw [← ModuleCat.comp_apply, ← F.map_comp, h]

variable (he : ∀ a : A, F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a)) e = γ a • e)

/-- The natural transformation `R ⊗_A M ⟶ F(M)`, `r ⊗ m ↦ r • F(a ↦ a • m)(e)`, attached to an
element `e` of `F(A)` on which `A` acts through `γ`. -/
def wattsTrans : ModuleCat.extendScalars.{u, u, u} γ ⟶ F where
  app M := ((ModuleCat.extendRestrictScalarsAdj γ).homEquiv _ _).symm (wattsMap F γ e he M)
  naturality M N f := by
    apply ((ModuleCat.extendRestrictScalarsAdj γ).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext m
    exact (map_wattsMap_apply F e f m).symm

/-- `wattsTrans` is, at each module, the transpose of `wattsMap` across the adjunction between
extension and restriction of scalars. -/
theorem wattsTrans_app (M : ModuleCat.{u} A) :
    (wattsTrans F γ e he).app M =
      ((ModuleCat.extendRestrictScalarsAdj γ).homEquiv _ _).symm (wattsMap F γ e he M) :=
  rfl

/-- `wattsTrans` is an isomorphism at `A` as soon as `r ↦ r • e` is bijective. -/
theorem isIso_wattsTrans_app_self (hb : Function.Bijective (fun r : R => r • e)) :
    IsIso ((wattsTrans F γ e he).app (ModuleCat.of A A)) := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} γ
  let u0 : (ModuleCat.extendScalars.{u, u, u} γ).obj (ModuleCat.of A A) :=
    adj.unit.app (ModuleCat.of A A) (1 : A)
  let ρ : R ≃ₗ[R] F.obj (ModuleCat.of A A) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ e) hb
  have hρ : ρ.symm e = 1 := (LinearEquiv.symm_apply_eq _).2 (one_smul R e).symm
  let τ : F.obj (ModuleCat.of A A) ⟶ (ModuleCat.extendScalars.{u, u, u} γ).obj (ModuleCat.of A A) :=
    ρ.symm.toModuleIso.hom ≫ ModuleCat.ofHom (X := R)
      (Y := ((ModuleCat.extendScalars.{u, u, u} γ).obj (ModuleCat.of A A)))
      (LinearMap.toSpanSingleton R _ u0)
  have he1 : wattsMap F γ e he (ModuleCat.of A A) (1 : A) = e := by
    have h1 : ModuleCat.ofHom (LinearMap.toSpanSingleton A A 1) = 𝟙 (ModuleCat.of A A) := by
      ext
      simp
    change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A 1)) e = e
    rw [h1, F.map_id]
    rfl
  have hu : (wattsTrans F γ e he).app (ModuleCat.of A A) u0 = e := by
    refine Eq.trans ?_ he1
    rw [wattsTrans_app]
    change (adj.homEquiv _ _ (((adj.homEquiv _ _).symm
      (wattsMap F γ e he (ModuleCat.of A A))))) (1 : A) = _
    rw [Equiv.apply_symm_apply]
  refine ⟨τ, ?_, ?_⟩
  · apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, wattsTrans_app, Equiv.apply_symm_apply,
      Adjunction.homEquiv_id]
    ext
    change τ (wattsMap F γ e he (ModuleCat.of A A) (1 : A)) = u0
    rw [he1]
    change (ρ.symm e) • u0 = u0
    rw [hρ, one_smul]
  · ext y
    obtain ⟨r, rfl⟩ := hb.2 y
    have hτ : τ (r • e) = r • u0 := by
      change (ρ.symm (r • e)) • u0 = r • u0
      rw [map_smul, hρ, smul_eq_mul, mul_one]
    change (wattsTrans F γ e he).app (ModuleCat.of A A) (τ (r • e)) = r • e
    rw [hτ, map_smul, hu]

end Watts

section Dense

variable {A : Type u} [CommRing A] {C : Type*} [Category* C] {L L' : ModuleCat.{u} A ⥤ C}
  [PreservesColimitsOfSize.{u, u} L] [PreservesColimitsOfSize.{u, u} L'] (α : L ⟶ L')
  (hα : IsIso (α.app (ModuleCat.of A A)))
include hα

/-- A natural transformation between colimit-preserving functors out of `A`-modules which is an
isomorphism at `A` is an isomorphism at every free module `A^{(ι)}`: the free module is the
coproduct of copies of `A`, and both functors carry that coproduct to a coproduct. -/
theorem isIso_app_finsupp_of_isIso_app_self (ι : Type u) :
    IsIso (α.app (ModuleCat.of A (ι →₀ A))) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft (Discrete.functor fun _ : ι => ModuleCat.of A A) α).app
      j) :=
    fun _ => hα
  have : IsIso (Functor.whiskerLeft (Discrete.functor fun _ : ι => ModuleCat.of A A) α) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit _ α _ (ModuleCat.finsuppCoconeIsColimit A A ι)

/-- **A natural transformation between colimit-preserving functors out of `A`-modules is an
isomorphism as soon as it is one at `A`.**  Every module `M` is the cokernel of a map of free
modules `A^{(ker π)} → A^{(M)}`, the presentation through `π : A^{(M)} → M`, and both functors
carry that cokernel to a cokernel. -/
theorem isIso_app_of_isIso_app_self (M : ModuleCat.{u} A) : IsIso (α.app M) := by
  have : PreservesColimitsOfSize.{0, 0} L := preservesColimitsOfSize_shrink.{0, u, 0, u} L
  have : PreservesColimitsOfSize.{0, 0} L' := preservesColimitsOfSize_shrink.{0, u, 0, u} L'
  let π : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A id
  have hπ : Function.Surjective π := fun m => ⟨Finsupp.single m 1, by simp [π]⟩
  let κ : (LinearMap.ker π →₀ A) →ₗ[A] (M →₀ A) :=
    Finsupp.linearCombination A (LinearMap.ker π).subtype
  have hrange : LinearMap.range κ = LinearMap.ker π := by
    rw [Finsupp.range_linearCombination, Submodule.coe_subtype, Subtype.range_coe,
        Submodule.span_eq]
  let f : ModuleCat.of A (LinearMap.ker π →₀ A) ⟶ ModuleCat.of A (M →₀ A) := ModuleCat.ofHom κ
  let e : cokernel f ≅ M := ModuleCat.cokernelIsoRangeQuotient f ≪≫
    LinearEquiv.toModuleIso ((Submodule.quotEquivOfEq _ _ hrange).trans
      (π.quotKerEquivOfSurjective hπ))
  have : ∀ j, IsIso ((Functor.whiskerLeft (parallelPair f 0) α).app j) := by
    rintro (_ | _) <;> exact isIso_app_finsupp_of_isIso_app_self α hα _
  have : IsIso (Functor.whiskerLeft (parallelPair f 0) α) := NatIso.isIso_of_isIso_app _
  have : IsIso (α.app (cokernel f)) :=
    isIso_app_coconePt_of_preservesColimit _ α (colimit.cocone _) (colimit.isColimit _)
  have h : α.app M = inv (L.map e.hom) ≫ α.app (cokernel f) ≫ L'.map e.hom := by
    rw [← α.naturality e.hom, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

end Dense

section PullbackUnit

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {Φ : C ⥤ D}
  {Sr : Sheaf J RingCat.{u}} {Rr : Sheaf K RingCat.{u}} [Φ.IsContinuous J K]
  (φ : Sr ⟶ (Φ.sheafPushforwardContinuous RingCat.{u} J K).obj Rr)
  [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  [IsIso (SheafOfModules.pullbackObjUnitToUnit φ)]

/-- An endomorphism of the unit module pulled back along a morphism of ringed sites, and read on
the unit module of the target through `SheafOfModules.pullbackObjUnitToUnit`, takes the value
`φ(h(1))` at `1` over the image of an object of the source site. -/
theorem pullbackObjUnitToUnit_conj_val_app_one (h : SheafOfModules.unit Sr ⟶ SheafOfModules.unit Sr)
    (X : Cᵒᵖ) :
    (inv (SheafOfModules.pullbackObjUnitToUnit φ) ≫ (SheafOfModules.pullback φ).map h ≫
        SheafOfModules.pullbackObjUnitToUnit φ).val.app (Opposite.op (Φ.obj X.unop))
        (1 : Rr.obj.obj (Opposite.op (Φ.obj X.unop))) =
      φ.hom.app X (h.val.app X (1 : Sr.obj.obj X)) := by
  have key : SheafOfModules.unitToPushforwardObjUnit φ ≫ (SheafOfModules.pushforward.{u} φ).map
      (inv (SheafOfModules.pullbackObjUnitToUnit φ) ≫ (SheafOfModules.pullback φ).map h ≫
        SheafOfModules.pullbackObjUnitToUnit φ) =
      h ≫ SheafOfModules.unitToPushforwardObjUnit φ := by
    rw [← SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
      ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
      IsIso.hom_inv_id_assoc]
  refine Eq.trans ?_ (congrArg (fun f => f.val.app X (1 : Sr.obj.obj X)) key)
  exact (congrArg (fun y : Rr.obj.obj (Opposite.op (Φ.obj X.unop)) =>
    (inv (SheafOfModules.pullbackObjUnitToUnit φ) ≫ (SheafOfModules.pullback φ).map h ≫
        SheafOfModules.pullbackObjUnitToUnit φ).val.app (Opposite.op (Φ.obj X.unop)) y)
    (map_one (φ.hom.app X).hom)).symm

end PullbackUnit

/-- The endomorphism of `𝒪_{Spec A} = Ã` induced by multiplication by `a` on `A` takes the
global section `1` to the global function `a`. -/
theorem tilde_map_toSpanSingleton_val_app_top_one (A : CommRingCat.{u}) (a : A) :
    ((tilde.functor A).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a))).val.app
      (Opposite.op ⊤) (1 : Γ(Spec A, ⊤)) = (Scheme.ΓSpecIso A).inv a := by
  have h := congrArg (fun f => f (1 : A)) (congrArg ModuleCat.Hom.hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a)) ⊤))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine (congrArg (fun y : Γ(Spec A, ⊤) =>
    ((tilde.functor A).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a))).val.app
      (Opposite.op ⊤) y) (map_one (Scheme.ΓSpecIso A).inv.hom)).symm.trans (h.trans ?_)
  rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  rfl

/-- An endomorphism `t` of `𝒪_Y`, restricted along an open immersion `f : X ⟶ Y` and read on
`𝒪_X` through `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, takes the global section `1`
to the pullback along `f` of the global section `t(1)`. -/
theorem restrictUnitIso_conj_val_app_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    ((Scheme.Modules.restrictUnitIso f).inv ≫ (Scheme.Modules.restrictFunctor f).map t ≫
      (Scheme.Modules.restrictUnitIso f).hom).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) =
      f.appTop (t.val.app (Opposite.op ⊤) (1 : Γ(Y, ⊤))) := by
  change (f.appIso ⊤).hom (t.val.app (Opposite.op (f ''ᵁ ⊤)) ((f.appIso ⊤).inv 1)) = _
  rw [map_one]
  have hnat := congrArg (fun g => g (1 : Γ(Y, ⊤))) (congrArg ModuleCat.Hom.hom
    (t.val.naturality (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op))
  have h1 : (SheafOfModules.unit Y.ringCatSheaf).val.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op
      (1 : Γ(Y, ⊤)) = (1 : Γ(Y, f ''ᵁ ⊤)) :=
    map_one (Y.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op).hom
  have key : Y.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op ≫ (f.appIso ⊤).hom = f.appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  simp only [ModuleCat.hom_comp] at hnat
  conv_lhs => rw [← h1]
  refine (congrArg (fun z => (f.appIso ⊤).hom z) hnat).trans ?_
  exact ConcreteCategory.congr_hom key _

/-- The comparison of structure sheaves of the small étale site of the scheme `T` underlying
`U`, at the open `⊤`, followed by restriction to the object corresponding to the identity chart
of `yoneda.obj U`, is the identity of `Γ(T, ⊤)`: that object is `T` itself, over `T` by the
identity. -/
theorem structureSheaf_map_structureMap_app_top (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS :
    B.Contains S) (U : BigFppfOver B S hS)
    (g : (representedSmallEtaleEquivalence B S hS U).functor.obj (selfChart B S hS U) ⟶
      _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤)
    (z : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map g.op
      ((_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (Opposite.op ⊤) z) = z := by
  simp only [_root_.AlgebraicGeometry.SmallEtale.structureSheaf_obj,
    _root_.AlgebraicGeometry.SmallEtale.structureMap_hom_app]
  have hw : ((_root_.AlgebraicGeometry.SmallEtale.inclusion (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
        Over.post (associatedBigEtaleSite B).inclusion).map g).left ≫
      (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι = 𝟙 _ :=
    Over.w ((_root_.AlgebraicGeometry.SmallEtale.inclusion (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
        Over.post (associatedBigEtaleSite B).inclusion).map g)
  change (((_root_.AlgebraicGeometry.SmallEtale.inclusion (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
        Over.post (associatedBigEtaleSite B).inclusion).map g).left.appTop)
      ((⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι.appTop z) = z
  have key := (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop hw)
  exact (ConcreteCategory.congr_hom key z).trans rfl

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  (x : GeometricPoint B S hS (yoneda.obj U))
  (A : CommRingCat.{u}) (i : (BigFppfOver.toScheme B S hS).obj U ≅ Spec A)

/-- The associated module on `yoneda.obj U` of the restriction to `T` of `Ã = 𝒪_{Spec A}`
is the structure sheaf: restriction along the isomorphism `i` carries `𝒪_{Spec A}` to `𝒪_T`, and
`ε^*` carries `𝒪_T` to `𝒪`. -/
def representedAffineUnitIso :
    (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj
      ((Scheme.Modules.restrictFunctor i.hom).obj ((tilde.functor A).obj (ModuleCat.of A A))) ≅
    SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U)) :=
  (representedModulePushforward B S hS U).mapIso
    ((SheafOfModules.pullback (_root_.AlgebraicGeometry.SmallEtale.structureMap
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).mapIso
      (Scheme.Modules.restrictUnitIso i.hom) ≪≫
    @asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property))

/-- **Multiplication by `a ∈ A`, carried to the structure sheaf of `yoneda.obj U`, is
multiplication by the global function of `T` corresponding to `a`.**  Read through
`AlgebraicGeometry.Space.representedAffineUnitIso`, the image of the endomorphism `b ↦ b • a`
of `A` takes the section `1` over the identity chart to `i^*(a)`. -/
theorem representedAffineUnitIso_conj_val_app_one (a : A) :
    (representedAffineUnitIso B S hS U A i).hom.val.app (Opposite.op (selfChart B S hS U))
      (((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        ((Scheme.Modules.restrictFunctor i.hom).map
          ((tilde.functor A).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a))))).val.app
            (Opposite.op (selfChart B S hS U))
        ((representedAffineUnitIso B S hS U A i).inv.val.app (Opposite.op (selfChart B S hS U))
          (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))) =
      i.hom.appTop ((Scheme.ΓSpecIso A).inv a) := by
  let φ := _root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  let t := (tilde.functor A).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a))
  let h : SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⟶
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf :=
    CategoryStruct.comp
      (obj := SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
      (Scheme.Modules.restrictUnitIso i.hom).inv
      (CategoryStruct.comp
        (obj := SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
        ((Scheme.Modules.restrictFunctor i.hom).map t) (Scheme.Modules.restrictUnitIso i.hom).hom)
  let Y := (representedSmallEtaleEquivalence B S hS U).functor.obj (selfChart B S hS U)
  have hc : ∀ z, (inv (SheafOfModules.pullbackObjUnitToUnit φ) ≫ (SheafOfModules.pullback φ).map h ≫
      SheafOfModules.pullbackObjUnitToUnit φ).val.app (Opposite.op Y) z =
      (SheafOfModules.pullbackObjUnitToUnit φ).val.app (Opposite.op Y)
        (((SheafOfModules.pullback φ).map (Scheme.Modules.restrictUnitIso i.hom).hom).val.app
          (Opposite.op Y)
        (((SheafOfModules.pullback φ).map ((Scheme.Modules.restrictFunctor i.hom).map t)).val.app
          (Opposite.op Y)
        (((SheafOfModules.pullback φ).map (Scheme.Modules.restrictUnitIso i.hom).inv).val.app
          (Opposite.op Y)
        ((inv (SheafOfModules.pullbackObjUnitToUnit φ)).val.app (Opposite.op Y) z)))) := by
    intro z
    have e' : (SheafOfModules.pullback φ).map h =
        (SheafOfModules.pullback φ).map (Scheme.Modules.restrictUnitIso i.hom).inv ≫
          (SheafOfModules.pullback φ).map ((Scheme.Modules.restrictFunctor i.hom).map t) ≫
            (SheafOfModules.pullback φ).map (Scheme.Modules.restrictUnitIso i.hom).hom :=
      ((SheafOfModules.pullback φ).map_comp _ _).trans
        (congrArg (fun k => (SheafOfModules.pullback φ).map
          (Scheme.Modules.restrictUnitIso i.hom).inv ≫ k)
          ((SheafOfModules.pullback φ).map_comp _ _))
    rw [e']
    rfl
  refine (hc (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).symm.trans ?_
  let g : Y ⟶ _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤ :=
    _root_.AlgebraicGeometry.SmallEtale.homOfRangeLe _ _ _ ⊤ (by simp)
  let c := inv (SheafOfModules.pullbackObjUnitToUnit φ) ≫ (SheafOfModules.pullback φ).map h ≫
      SheafOfModules.pullbackObjUnitToUnit φ
  have hnat := congrArg (fun f => f (1 : (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.obj
        (Opposite.op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤))))
    (congrArg ModuleCat.Hom.hom (c.val.naturality g.op))
  simp only [ModuleCat.hom_comp] at hnat
  have h1 := map_one ((_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map g.op).hom
  have s3 := pullbackObjUnitToUnit_conj_val_app_one φ h (Opposite.op ⊤)
  have k2 := restrictUnitIso_conj_val_app_top i.hom t
  have k1 := tilde_map_toSpanSingleton_val_app_top_one A a
  have hz := structureSheaf_map_structureMap_app_top B S hS U g (i.hom.appTop ((Scheme.ΓSpecIso
      A).inv a))
  refine (congrArg (fun y => c.val.app (Opposite.op Y) y) h1).symm.trans ?_
  refine hnat.trans ?_
  refine Eq.trans ?_ hz
  exact congrArg (fun y => ((_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
        g.op) y)
    (s3.trans (congrArg (fun y => φ.hom.app (Opposite.op ⊤) y)
      (k2.trans (congrArg (fun y => i.hom.appTop y) k1))))

/-- Every étale chart of `yoneda.obj U` maps to the identity chart, by the morphism of the
big fppf site that the chart is. -/
def toSelfChart (V : SmallEtale B S hS (yoneda.obj U)) : V ⟶ selfChart B S hS U :=
  ObjectProperty.homMk (CostructuredArrow.homMk (Yoneda.fullyFaithful.preimage V.obj.hom)
    (by simp [selfChart]))

/-- A geometric point of `yoneda.obj U` has exactly one lift to the identity chart. -/
theorem selfChart_fiber_ext
    (a b : (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).fiber.obj
      (selfChart B S hS U)) : a = b :=
  Subtype.ext (a.2.trans b.2.symm)

/-- The canonical lift of a geometric point of `yoneda.obj U` to the identity chart, as an
element of the fibre functor of the point of the small étale site. -/
def selfChartLift :
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).fiber.obj
      (selfChart B S hS U) :=
  ⟨(selfNeighborhood B S hS U x).point, (selfNeighborhood B S hS U x).point_comp⟩

/-- The germ of a section `s • m` is the germ of `s`, read in the `CommRingCat`-valued stalk of
the structure sheaf, acting on the germ of `m`. -/
theorem toPresheafFiber_smul_germ
    (N : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)))
    (V : SmallEtale B S hS (yoneda.obj U))
    (v : (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).fiber.obj V)
    (s : (ringStructureSheaf B S hS (yoneda.obj U)).obj.obj (Opposite.op V))
    (m : N.val.obj (Opposite.op V)) :
    ((etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber V v
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj s) •
      (show (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).obj N
            from
        Stacks.toPresheafModuleFiber
          (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)) N.val V v m) =
      Stacks.toPresheafModuleFiber
          (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)) N.val V v (s
              • m) :=
  (congrArg (fun r : ((etaleSitePoint B S hS (yoneda.obj U) x
      (isAlgebraicSpace_yoneda B S hS U)).presheafFiber (A := RingCat.{u})).obj
        (ringStructureSheaf B S hS (yoneda.obj U)).obj =>
      r • Stacks.toPresheafModuleFiber
        (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)) N.val V v m)
    (Stacks.commRingSheafFiberIso_inv_toPresheafFiber
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O V v
          s)).trans
    (Stacks.toPresheafModuleFiber_smul _ N.val V v s m).symm

/-- The germ of the section `1` of the structure sheaf of `yoneda.obj U` at a geometric point,
as an element of the module stalk of the structure sheaf. -/
def representedUnitGerm : (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).obj
        (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))) :=
  Stacks.toPresheafModuleFiber
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))).val (selfChart B S hS U)
    (selfChartLift B S hS U x) (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))

/-- `AlgebraicGeometry.Space.representedUnitGerm` is the germ of `1` over any étale neighbourhood
of the
geometric point. -/
theorem representedUnitGerm_eq (V : SmallEtale B S hS (yoneda.obj U))
    (v : (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).fiber.obj V) :
    representedUnitGerm B S hS U x = Stacks.toPresheafModuleFiber
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))).val V v
      (1 : (ringStructureSheaf B S hS (yoneda.obj U)).obj.obj (Opposite.op V)) := by
  have hv : (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).fiber.map
      (toSelfChart B S hS U V) v = selfChartLift B S hS U x := selfChart_fiber_ext B S hS U x _ _
  rw [representedUnitGerm, ← hv]
  exact (Stacks.toPresheafModuleFiber_w _ _ (toSelfChart B S hS U V) v _).trans
    (congrArg _ (map_one ((ringStructureSheaf B S hS (yoneda.obj U)).obj.map
      (toSelfChart B S hS U V).op).hom))

/-- The germ of a section `s` of the structure sheaf is `s` acting on the germ of `1`. -/
private theorem toPresheafFiber_smul_representedUnitGerm
    (V : SmallEtale B S hS (yoneda.obj U))
    (v : (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).fiber.obj V)
    (s : (ringStructureSheaf B S hS (yoneda.obj U)).obj.obj (Opposite.op V)) :
    ((etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber V v
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj s) •
      representedUnitGerm B S hS U x =
    Stacks.toPresheafModuleFiber
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))).val V v s := by
  rw [representedUnitGerm_eq B S hS U x V v]
  exact (toPresheafFiber_smul_germ B S hS U x
      (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))) V v s
      (1 : (ringStructureSheaf B S hS (yoneda.obj U)).obj.obj (Opposite.op V))).trans
    (congrArg _ (mul_one s))

/-- The module stalk of the structure sheaf of `yoneda.obj U` at a geometric point is free of
rank one over the stalk ring, on the germ of `1`. -/
theorem bijective_smul_representedUnitGerm :
    Function.Bijective (fun r : ((etaleSitePoint B S hS (yoneda.obj U) x
        (isAlgebraicSpace_yoneda B S hS U)).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj =>
      r • representedUnitGerm B S hS U x) := by
  constructor
  · intro r r' hrr
    obtain ⟨V, v, s, s', rfl, rfl⟩ :=
      (etaleSitePoint B S hS (yoneda.obj U) x
          (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber_jointly_surjective₂
        (P := (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj) r r'
    beta_reduce at hrr
    have h3 := (toPresheafFiber_smul_representedUnitGerm B S hS U x V v s).symm.trans
      (hrr.trans (toPresheafFiber_smul_representedUnitGerm B S hS U x V v s'))
    obtain ⟨W, f, w, hw, hfs⟩ := (Stacks.toPresheafModuleFiber_eq_iff _ _ V v _ _).1 h3
    rw [← hw]
    exact ((etaleSitePoint B S hS (yoneda.obj U) x
      (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber_w_apply f w _ s).symm.trans
      ((congrArg ((etaleSitePoint B S hS (yoneda.obj U) x
        (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber W w
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj)
              hfs).trans
        ((etaleSitePoint B S hS (yoneda.obj U) x
          (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber_w_apply f w _ s'))
  · intro y
    obtain ⟨V, v, s, rfl⟩ := Stacks.toPresheafModuleFiber_jointly_surjective
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))).val y
    refine ⟨(etaleSitePoint B S hS (yoneda.obj U) x
        (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber V v
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj s, ?_⟩
    exact toPresheafFiber_smul_representedUnitGerm B S hS U x V v s

/-- **The ring map `A → 𝒪_{h_U, x̄}`.**  An element `a` of `A` is sent to the germ at the
geometric point `x̄`, through its canonical lift to the identity chart of `yoneda.obj U`, of the
global regular function `i^*(a)` on the scheme `T` underlying `U`. -/
def representedAffineStalkRingHom :
    A →+* geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x :=
  ((etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber
      (selfChart B S hS U) (selfChartLift B S hS U x)
      (smallEtaleRingedTopos B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj).hom.comp
    (i.hom.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom)

/-- Read in the étale local ring `𝒪_{h_U, x̄}`, the image of `a ∈ A` under
`AlgebraicGeometry.Space.representedAffineStalkRingHom` is the germ of `i^*(a)` on the canonical
neighbourhood of `x̄`. -/
theorem pointStalkRingEquiv_representedAffineStalkRingHom (a : A) :
    pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x
        (representedAffineStalkRingHom B S hS U x A i a) =
      etaleLocalRingGerm B S hS (yoneda.obj U) x (Opposite.op (selfNeighborhood B S hS U x))
        (i.hom.appTop ((Scheme.ΓSpecIso A).inv a)) :=
  pointStalkRingEquiv_germ_neighborhood B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x
    (selfNeighborhood B S hS U x) _

/-- The functor `M ↦ (ε^*(M̃|_T))_{x̄}` from `A`-modules to modules over the stalk ring at the
geometric point `x̄`, for `T ≅ Spec A`. -/
abbrev representedAffineStalkFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u}
    (geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x) :=
  tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom ⋙
    representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U) ⋙
    Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- The module stalk of a morphism of `𝒪_{h_U}`-modules sends the germ of a section to the germ
of its image. -/
theorem sheafModuleFiberOfCommRing_map_germ
    {N N' : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U))} (φ : N ⟶ N')
    (V : SmallEtale B S hS (yoneda.obj U))
    (v : (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).fiber.obj V)
    (m : N.val.obj (Opposite.op V)) :
    (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).map φ
        (Stacks.toPresheafModuleFiber
          (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)) N.val V v m) =
      Stacks.toPresheafModuleFiber
          (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)) N'.val V v
        (φ.val.app (Opposite.op V) m) :=
  Stacks.toPresheafModuleFiber_naturality _ φ.val V v m

/-- The generator of `(ε^*(Ã|_T))_{x̄}`: the germ of `1`, carried along
`AlgebraicGeometry.Space.representedAffineUnitIso`. -/
def representedAffineStalkGenerator :
    (representedAffineStalkFunctor B S hS U x A i).obj (ModuleCat.of A A) :=
  (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).map
    (representedAffineUnitIso B S hS U A i).inv (representedUnitGerm B S hS U x)

/-- `A` acts on the generator of `(ε^*(Ã|_T))_{x̄}` through
`AlgebraicGeometry.Space.representedAffineStalkRingHom`. -/
theorem representedAffineStalkFunctor_map_generator (a : A) :
    (representedAffineStalkFunctor B S hS U x A i).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a))
        (representedAffineStalkGenerator B S hS U x A i) =
      representedAffineStalkRingHom B S hS U x A i a • representedAffineStalkGenerator B S hS U x A
          i := by
  let Fib := Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
  let Θ := (Fib.mapIso (representedAffineUnitIso B S hS U A i)).toLinearEquiv
  apply Θ.injective
  refine Eq.trans ?_ (Θ.map_smul (representedAffineStalkRingHom B S hS U x A i a)
    (representedAffineStalkGenerator B S hS U x A i)).symm
  refine Eq.trans ?_ (congrArg (fun z => (show ((etaleSitePoint B S hS (yoneda.obj U) x
      (isAlgebraicSpace_yoneda B S hS U)).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj from
      representedAffineStalkRingHom B S hS U x A i a) • z)
    (Θ.apply_symm_apply (representedUnitGerm B S hS U x))).symm
  have hK := representedAffineUnitIso_conj_val_app_one B S hS U A i a
  have hR := toPresheafFiber_smul_representedUnitGerm B S hS U x (selfChart B S hS U)
    (selfChartLift B S hS U x) (i.hom.appTop ((Scheme.ΓSpecIso A).inv a))
  refine Eq.trans ?_ hR.symm
  have m1 := sheafModuleFiberOfCommRing_map_germ B S hS U x (representedAffineUnitIso B S hS U A
      i).inv
    (selfChart B S hS U) (selfChartLift B S hS U x)
    (1 : (ringStructureSheaf B S hS (yoneda.obj U)).obj.obj (Opposite.op (selfChart B S hS U)))
  have m2 := sheafModuleFiberOfCommRing_map_germ B S hS U x
    ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        ((Scheme.Modules.restrictFunctor i.hom).map
          ((tilde.functor A).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a)))))
    (selfChart B S hS U) (selfChartLift B S hS U x)
    ((representedAffineUnitIso B S hS U A i).inv.val.app (Opposite.op (selfChart B S hS U))
      (1 : (ringStructureSheaf B S hS (yoneda.obj U)).obj.obj (Opposite.op (selfChart B S hS U))))
  have m3 := sheafModuleFiberOfCommRing_map_germ B S hS U x (representedAffineUnitIso B S hS U A
      i).hom
    (selfChart B S hS U) (selfChartLift B S hS U x)
    (((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        ((Scheme.Modules.restrictFunctor i.hom).map
          ((tilde.functor A).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a))))).val.app
            (Opposite.op (selfChart B S hS U))
      ((representedAffineUnitIso B S hS U A i).inv.val.app (Opposite.op (selfChart B S hS U))
        (1 : (ringStructureSheaf B S hS (yoneda.obj U)).obj.obj
          (Opposite.op (selfChart B S hS U)))))
  exact (congrArg Θ ((congrArg (Fib.map
      ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        ((Scheme.Modules.restrictFunctor i.hom).map
          ((tilde.functor A).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A a)))))) m1).trans
              m2)).trans
    (m3.trans (congrArg (Stacks.toPresheafModuleFiber
        (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
        (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))).val (selfChart B S hS U)
        (selfChartLift B S hS U x)) hK))

/-- The functor `M ↦ (ε^*(M̃|_T))_{x̄}` is additive, each of its factors being additive. -/
instance additive_representedAffineStalkFunctor :
    (representedAffineStalkFunctor B S hS U x A i).Additive where
  map_add {_ _ f g} :=
    (congrArg (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).map
      ((congrArg (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        ((congrArg (Scheme.Modules.restrictFunctor i.hom).map ((tilde.functor A).map_add (f := f)
            (g := g))).trans
          (Scheme.Modules.restrictFunctor i.hom).map_add)).trans
        (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map_add)).trans
      (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).map_add

/-- `(ε^*(Ã|_T))_{x̄}` is free of rank one over the stalk ring on its generator. -/
theorem bijective_smul_representedAffineStalkGenerator :
    Function.Bijective (fun r : geometricStalkRing B S hS
        (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x =>
      r • representedAffineStalkGenerator B S hS U x A i) := by
  let Θ := ((Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).mapIso
        (representedAffineUnitIso B S hS U A i)).toLinearEquiv
  have hfun : (Θ.symm ∘ fun r : ((etaleSitePoint B S hS (yoneda.obj U) x
        (isAlgebraicSpace_yoneda B S hS U)).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj =>
        r • representedUnitGerm B S hS U x) =
      (fun r : geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x
          =>
        r • representedAffineStalkGenerator B S hS U x A i) :=
    funext fun r => Θ.symm.map_smul r (representedUnitGerm B S hS U x)
  exact Eq.mp (congrArg Function.Bijective hfun)
    (Θ.symm.bijective.comp (bijective_smul_representedUnitGerm B S hS U x))

/-- The comparison `𝒪_{x̄} ⊗_A M ⟶ (ε^*(M̃|_T))_{x̄}`, `r ⊗ m ↦ r • m_{x̄}`, natural in the
`A`-module `M`. -/
def representedAffineStalkTrans :
    ModuleCat.extendScalars.{u, u, u} (representedAffineStalkRingHom B S hS U x A i) ⟶
      representedAffineStalkFunctor B S hS U x A i :=
  wattsTrans (representedAffineStalkFunctor B S hS U x A i) (representedAffineStalkRingHom B S hS U
      x A i)
    (representedAffineStalkGenerator B S hS U x A i)
    (representedAffineStalkFunctor_map_generator B S hS U x A i)

/-- The comparison `𝒪_{x̄} ⊗_A M ⟶ (ε^*(M̃|_T))_{x̄}` is an isomorphism at `M = A`. -/
theorem isIso_representedAffineStalkTrans_app_self :
    IsIso ((representedAffineStalkTrans B S hS U x A i).app (ModuleCat.of A A)) :=
  isIso_wattsTrans_app_self _ _ _ _ (bijective_smul_representedAffineStalkGenerator B S hS U x A i)

/-- The module stalk at a geometric point of `yoneda.obj U` preserves small colimits: on
underlying abelian groups it is the stalk of the underlying abelian sheaf, a left adjoint. -/
instance preservesColimitsOfSize_representedStalk :
    PreservesColimitsOfSize.{u, u} (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) := by
  let Φ := etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)
  let R := ringStructureSheaf B S hS (yoneda.obj U)
  have h0 : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    have hsize : PreservesColimitsOfSize.{u + 1, u} (SheafOfModules.toSheaf.{u} R) := inferInstance
    preservesColimitsOfSize_shrink.{u, u, u, u + 1} _
  have hcomp : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.toSheaf.{u} R ⋙ Φ.sheafFiber (A := AddCommGrpCat.{u})) := inferInstance
  have hforget : PreservesColimitsOfSize.{u, u} (Stacks.sheafModuleFiber Φ R ⋙
      forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj)) AddCommGrpCat.{u}) :=
    preservesColimits_of_natIso (Stacks.sheafModuleFiberCompForget₂ Φ R).symm
  have hreflects : ReflectsColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj)) AddCommGrpCat.{u})
          :=
    reflectsColimits_of_reflectsIsomorphisms
  have hfib : PreservesColimitsOfSize.{u, u} (Stacks.sheafModuleFiber Φ R) :=
    preservesColimits_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj)) AddCommGrpCat.{u})
  have hres : PreservesColimitsOfSize.{u, u} (ModuleCat.restrictScalars.{u}
      (Stacks.commRingSheafFiberIso Φ
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).inv.hom)
            :=
    (ModuleCat.restrictCoextendScalarsAdj _).leftAdjoint_preservesColimits
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ hfib hres

/-- The functor `M ↦ (ε^*(M̃|_T))_{x̄}` preserves small colimits, each of its factors being a
left adjoint or the module stalk. -/
instance preservesColimitsOfSize_representedAffineStalkFunctor :
    PreservesColimitsOfSize.{u, u} (representedAffineStalkFunctor B S hS U x A i) := by
  have h1 : PreservesColimitsOfSize.{u, u} (representedModulePushforward B S hS U) :=
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction.leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfSize.{u, u}
      (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)) :=
    @comp_preservesColimits _ _ _ _ _ _ _ _ inferInstance h1
  have h3 : PreservesColimitsOfSize.{u, u}
      (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U) ⋙
        Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) :=
    @comp_preservesColimits _ _ _ _ _ _ _ _ h2 (preservesColimitsOfSize_representedStalk B S hS U x)
  have h4 : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor i.hom ⋙
      representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U) ⋙
        Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) :=
    @comp_preservesColimits _ _ _ _ _ _ _ _ inferInstance h3
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ inferInstance h4

/-- **The stalk of `ε^*(M̃|_T)` at a geometric point is `M ⊗_A 𝒪_{x̄}`.**  For the scheme `T`
underlying `U` with an isomorphism `i : T ≅ Spec A` and a geometric point `x̄` of `yoneda.obj U`,
the functor `M ↦ (ε^*(M̃|_T))_{x̄}` is extension of scalars along
`AlgebraicGeometry.Space.representedAffineStalkRingHom`, naturally in the `A`-module `M`. -/
def representedAffineAssociatedModuleStalkIso :
    tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom ⋙
        representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U) ⋙
        Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O ≅
      ModuleCat.extendScalars.{u, u, u} (representedAffineStalkRingHom B S hS U x A i) :=
  haveI : ∀ M, IsIso ((representedAffineStalkTrans B S hS U x A i).app M) :=
    isIso_app_of_isIso_app_self _ (isIso_representedAffineStalkTrans_app_self B S hS U x A i)
  haveI : IsIso (representedAffineStalkTrans B S hS U x A i) := NatIso.isIso_of_isIso_app _
  (asIso (representedAffineStalkTrans B S hS U x A i)).symm

end Represented

end AlgebraicGeometry.Space

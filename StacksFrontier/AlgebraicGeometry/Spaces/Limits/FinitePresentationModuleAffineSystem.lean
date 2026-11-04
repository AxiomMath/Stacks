module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NaturalEndScalar
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleHomRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductModuleObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealAnnihilatorSubsheaf
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic

/-!
# Finitely presented modules over a limit of affine schemes, on the small étale sites

Let `E` be a cofiltered diagram of objects of the big fppf site of `S` with affine underlying
schemes, and let `c` be a cone on it whose underlying schemes form a limit.  This file proves the
colimit assertion of Stacks 01ZR for the `𝒪`-modules of the small étale sites of the represented
algebraic spaces `h_{E j}`, by reading them as Zariski modules on the underlying schemes.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiToEtale`: the comparison `𝓕 ↦ 𝓕^a` from Zariski
  modules on the scheme underlying `U` to `𝒪`-modules on `h_U`.
* `AlgebraicGeometry.Space.representedZariskiToEtalePullbackIso`: its compatibility with inverse
  images, as a natural isomorphism.

## Main results

* `AlgebraicGeometry.Space.eventualModuleMapEqOverAffineSystem`: the affine case of the
  faithfulness clause of Stacks 07V7,
  `AlgebraicGeometry.Space.EventualModuleMapEqOverAffineSystem`, with no hypothesis.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.CompareIso

variable {𝒵 𝒵' 𝒵'' ℳ ℳ' ℳ'' : Type*} {_ : Category 𝒵} {_ : Category 𝒵'} {_ : Category 𝒵''}
  {_ : Category ℳ} {_ : Category ℳ'} {_ : Category ℳ''}
  {A : 𝒵 ⥤ ℳ} {A' : 𝒵' ⥤ ℳ'} {A'' : 𝒵'' ⥤ ℳ''}
  {Pe : ℳ ⥤ ℳ'} {Pk : ℳ' ⥤ ℳ''} {Pj : ℳ ⥤ ℳ''}
  {Ze : 𝒵 ⥤ 𝒵'} {Zk : 𝒵' ⥤ 𝒵''} {Zj : 𝒵 ⥤ 𝒵''}

/-- The identification of two iterated pullbacks obtained from three comparisons with another
category and an identification there. -/
def thetaIso (Λe : A ⋙ Pe ≅ Ze ⋙ A') (Λk : A' ⋙ Pk ≅ Zk ⋙ A'') (Λj : A ⋙ Pj ≅ Zj ⋙ A'')
    (zc : Ze ⋙ Zk ≅ Zj) : (A ⋙ Pe) ⋙ Pk ≅ A ⋙ Pj :=
  Functor.isoWhiskerRight Λe Pk ≪≫ Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Ze Λk ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight zc A'' ≪≫ Λj.symm

/-- The component of `thetaIso` at an object, as a composite of the components of the given
isomorphisms. -/
theorem thetaIso_hom_app (Λe : A ⋙ Pe ≅ Ze ⋙ A') (Λk : A' ⋙ Pk ≅ Zk ⋙ A'')
    (Λj : A ⋙ Pj ≅ Zj ⋙ A'') (zc : Ze ⋙ Zk ≅ Zj) (X : 𝒵) :
    (thetaIso Λe Λk Λj zc).hom.app X = Pk.map (Λe.hom.app X) ≫ Λk.hom.app (Ze.obj X) ≫
      A''.map (zc.hom.app X) ≫ Λj.inv.app X := by
  simp [thetaIso]

/-- **A morphism descended through the comparison is compatible with the identification
`thetaIso`.** -/
theorem map_comp_thetaIso_hom (Λe : A ⋙ Pe ≅ Ze ⋙ A') (Λk : A' ⋙ Pk ≅ Zk ⋙ A'')
    (Λj : A ⋙ Pj ≅ Zj ⋙ A'') (zc : Ze ⋙ Zk ≅ Zj) {X Y : 𝒵}
    (ψ₀ : Ze.obj X ⟶ Ze.obj Y) (φ₀ : Zj.obj X ⟶ Zj.obj Y)
    (h₀ : Zk.map ψ₀ ≫ zc.hom.app Y = zc.hom.app X ≫ φ₀) :
    Pk.map (Λe.hom.app X ≫ A'.map ψ₀ ≫ Λe.inv.app Y) ≫ (thetaIso Λe Λk Λj zc).hom.app Y =
      (thetaIso Λe Λk Λj zc).hom.app X ≫ (Λj.hom.app X ≫ A''.map φ₀ ≫ Λj.inv.app Y) := by
  rw [thetaIso_hom_app, thetaIso_hom_app]
  have hk := Λk.hom.naturality ψ₀
  simp only [Functor.comp_map] at hk
  have e1 : Pk.map (Λe.inv.app Y) ≫ Pk.map (Λe.hom.app Y) = 𝟙 _ := by
    rw [← Pk.map_comp, Iso.inv_hom_id_app, Pk.map_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% e1, reassoc_of% hk, ← A''.map_comp_assoc, h₀, A''.map_comp_assoc,
    Iso.inv_hom_id_app_assoc]

/-- **Two identifications differing by a natural endomorphism which commutes with a given
morphism give the same compatibility.** -/
theorem comp_hom_eq_of_comm {K₁ K₂ : 𝒵 ⥤ ℳ} (α β : K₁ ≅ K₂) {X Y : 𝒵}
    (ψ : K₁.obj X ⟶ K₁.obj Y) (φ : K₂.obj X ⟶ K₂.obj Y)
    (hψ : ψ ≫ α.hom.app Y = α.hom.app X ≫ φ)
    (hc : (α.inv ≫ β.hom).app X ≫ φ = φ ≫ (α.inv ≫ β.hom).app Y) :
    ψ ≫ β.hom.app Y = β.hom.app X ≫ φ := by
  have e : ∀ Z, β.hom.app Z = α.hom.app Z ≫ (α.inv ≫ β.hom).app Z := fun Z => by simp
  rw [e, e, reassoc_of% hψ, ← hc, Category.assoc]

/-- **Transfer of a compatibility along a comparison with another category.**  A morphism `ψ₀`
compatible with `φ₀` through the identification `zc` there gives a morphism compatible with
`φ'` through the identification `cc`, provided every natural endomorphism of `A ⋙ Pj` commutes
with `φ'`. -/
theorem compat_of_compat (Λe : A ⋙ Pe ≅ Ze ⋙ A') (Λk : A' ⋙ Pk ≅ Zk ⋙ A'')
    (Λj : A ⋙ Pj ≅ Zj ⋙ A'') (zc : Ze ⋙ Zk ≅ Zj) (cc : Pe ⋙ Pk ≅ Pj) {X Y : 𝒵}
    (ψ₀ : Ze.obj X ⟶ Ze.obj Y) (φ₀ : Zj.obj X ⟶ Zj.obj Y)
    (h₀ : Zk.map ψ₀ ≫ zc.hom.app Y = zc.hom.app X ≫ φ₀) (φ' : Pj.obj (A.obj X) ⟶ Pj.obj (A.obj Y))
    (hφ' : φ' = Λj.hom.app X ≫ A''.map φ₀ ≫ Λj.inv.app Y)
    (hc : ∀ δ : A ⋙ Pj ⟶ A ⋙ Pj, δ.app X ≫ φ' = φ' ≫ δ.app Y) :
    cc.inv.app (A.obj X) ≫ Pk.map (Λe.hom.app X ≫ A'.map ψ₀ ≫ Λe.inv.app Y) ≫
      cc.hom.app (A.obj Y) = φ' := by
  have h1 := map_comp_thetaIso_hom Λe Λk Λj zc ψ₀ φ₀ h₀
  rw [← hφ'] at h1
  let β : (A ⋙ Pe) ⋙ Pk ≅ A ⋙ Pj := Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft A cc
  have h2 := comp_hom_eq_of_comm (thetaIso Λe Λk Λj zc) β _ φ' h1 (hc _)
  have hβ : ∀ Z, β.hom.app Z = cc.hom.app (A.obj Z) := fun Z => by simp [β]
  rw [hβ, hβ] at h2
  rw [h2, Iso.inv_hom_id_app_assoc]

/-- `compat_of_compat`, conjugated by isomorphisms of the two modules with values of `A`. -/
theorem compat_of_compat' (Λe : A ⋙ Pe ≅ Ze ⋙ A') (Λk : A' ⋙ Pk ≅ Zk ⋙ A'')
    (Λj : A ⋙ Pj ≅ Zj ⋙ A'') (zc : Ze ⋙ Zk ≅ Zj) (cc : Pe ⋙ Pk ≅ Pj) {X Y : 𝒵} {M N : ℳ}
    (eF : A.obj X ≅ M) (eG : A.obj Y ≅ N) (φ : Pj.obj M ⟶ Pj.obj N)
    (ψ₀ : Ze.obj X ⟶ Ze.obj Y) (φ₀ : Zj.obj X ⟶ Zj.obj Y)
    (h₀ : Zk.map ψ₀ ≫ zc.hom.app Y = zc.hom.app X ≫ φ₀)
    (hφ₀ : A''.map φ₀ = Λj.inv.app X ≫ (Pj.map eF.hom ≫ φ ≫ Pj.map eG.inv) ≫ Λj.hom.app Y)
    (hc : ∀ (δ : A ⋙ Pj ⟶ A ⋙ Pj) (φ'' : Pj.obj (A.obj X) ⟶ Pj.obj (A.obj Y)),
      δ.app X ≫ φ'' = φ'' ≫ δ.app Y) :
    cc.inv.app M ≫ Pk.map (Pe.map eF.inv ≫ (Λe.hom.app X ≫ A'.map ψ₀ ≫ Λe.inv.app Y) ≫
      Pe.map eG.hom) ≫ cc.hom.app N = φ := by
  have key := compat_of_compat Λe Λk Λj zc cc ψ₀ φ₀ h₀ (Pj.map eF.hom ≫ φ ≫ Pj.map eG.inv)
    (by rw [hφ₀]; simp) (fun δ => hc δ _)
  have nF := cc.inv.naturality eF.inv
  have nG := cc.hom.naturality eG.hom
  simp only [Functor.comp_map] at nF nG
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% nF, nG]
  have e : Pj.map eF.inv ≫ cc.inv.app (A.obj X) ≫ Pk.map (Λe.hom.app X) ≫ Pk.map (A'.map ψ₀) ≫
      Pk.map (Λe.inv.app Y) ≫ cc.hom.app (A.obj Y) ≫ Pj.map eG.hom =
      Pj.map eF.inv ≫ (cc.inv.app (A.obj X) ≫ Pk.map (Λe.hom.app X ≫ A'.map ψ₀ ≫
        Λe.inv.app Y) ≫ cc.hom.app (A.obj Y)) ≫ Pj.map eG.hom := by
    simp only [Functor.map_comp, Category.assoc]
  rw [e, key]
  simp only [Category.assoc, ← Pj.map_comp, Iso.inv_hom_id, Pj.map_id, Category.comp_id]
  rw [← Pj.map_comp_assoc, Iso.inv_hom_id, Pj.map_id, Category.id_comp]

end CategoryTheory.CompareIso

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of Zariski modules with étale modules on a represented space -/

/-- The comparison `𝓕 ↦ 𝓕^a` from sheaves of modules on the Zariski site of the scheme
underlying `U` to `𝒪`-modules on the small étale site of the algebraic space `h_U`. -/
noncomputable def representedZariskiToEtale (U : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules ⥤
      Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2 :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS U).functor

/-- The inverse image along a represented morphism, read through the identification of the two
small étale sites: `E_T ⋙ h_g^* ≅ σ_g^* ⋙ E_{T'}`. -/
noncomputable def representedSmallEtalePullbackIso {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    (representedSmallEtaleModuleEquivalence B S hS T).functor ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) ≅
      SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').functor := by
  let E := representedSmallEtaleModuleEquivalence B S hS T
  let E' := representedSmallEtaleModuleEquivalence B S hS T'
  let F := modulePullback B S hS (representedSpaceMap B S hS g)
  let σ := SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)
  let P : F ⋙ E'.inverse ≅ E.inverse ⋙ σ :=
    representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
  let i1 : E.functor ⋙ F ≅ ((E.functor ⋙ F) ⋙ E'.inverse) ⋙ E'.functor :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft (E.functor ⋙ F) E'.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm
  let i2 : ((E.functor ⋙ F) ⋙ E'.inverse) ⋙ E'.functor ≅
      ((E.functor ⋙ E.inverse) ⋙ σ) ⋙ E'.functor :=
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.functor P ≪≫
        (Functor.associator _ _ _).symm) E'.functor
  let i3 : ((E.functor ⋙ E.inverse) ⋙ σ) ⋙ E'.functor ≅ σ ⋙ E'.functor :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight E.unitIso.symm σ ≪≫ Functor.leftUnitor σ)
      E'.functor
  exact i1 ≪≫ i2 ≪≫ i3

/-- **The comparison commutes with inverse images**, naturally in the Zariski module: for a
morphism `g : T' ⟶ T` of the site, `h_g^* (𝓕^a) ≅ (g^* 𝓕)^a`. -/
noncomputable def representedZariskiToEtalePullbackIso {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) :
    representedZariskiToEtale B S hS T ⋙ modulePullback B S hS (representedSpaceMap B S hS g) ≅
      Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g) ⋙
        representedZariskiToEtale B S hS T' := by
  let A := _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let A' := _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
  let E' := representedSmallEtaleModuleEquivalence B S hS T'
  let j1 := Functor.isoWhiskerLeft A (representedSmallEtalePullbackIso B S hS g)
  let j2 : (A ⋙ SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)) ⋙
      E'.functor ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g) ⋙ A') ⋙ E'.functor :=
    Functor.isoWhiskerRight
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
        (associatedBigEtaleSite B) g.left).symm E'.functor
  exact Functor.associator _ _ _ ≪≫ j1 ≪≫ (Functor.associator _ _ _).symm ≪≫ j2 ≪≫
    Functor.associator _ _ _

/-- The compatibility of the comparison with inverse images, along the morphism of represented
algebraic spaces written as `AlgebraicGeometry.schemeSpaceMap`. -/
noncomputable def representedZariskiToEtalePullbackIso' {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) :
    representedZariskiToEtale B S hS T ⋙ modulePullback B S hS (schemeSpaceMap g) ≅
      Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g) ⋙
        representedZariskiToEtale B S hS T' :=
  representedZariskiToEtalePullbackIso B S hS g

/-- The comparison carries the structure sheaf to the structure sheaf. -/
noncomputable def representedZariskiToEtaleObjUnitIso (U : BigFppfOver B S hS) :
    (representedZariskiToEtale B S hS U).obj
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O) :=
  representedAssociatedModuleObjUnitIso B S hS U (schemeSpace U).2

section Transfer

variable (U : BigFppfOver B S hS)

/-- On quasi-coherent modules the comparison is faithful. -/
theorem representedZariskiToEtale_map_injective
    {F G : ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (hF : SheafOfModules.IsQuasicoherent F) (hG : SheafOfModules.IsQuasicoherent G)
    {a b : F ⟶ G}
    (h : (representedZariskiToEtale B S hS U).map a = (representedZariskiToEtale B S hS U).map b) :
    a = b := by
  exact congrArg (fun f => InducedCategory.Hom.hom f)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map_injective
      (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) (a₁ := ObjectProperty.homMk a) (a₂ := ObjectProperty.homMk b)
      (InducedCategory.hom_ext (by exact h)))

/-- On quasi-coherent modules the comparison is full. -/
theorem representedZariskiToEtale_map_surjective
    {F G : ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (hF : SheafOfModules.IsQuasicoherent F) (hG : SheafOfModules.IsQuasicoherent G)
    (φ : (representedZariskiToEtale B S hS U).obj F ⟶ (representedZariskiToEtale B S hS U).obj G) :
    ∃ a : F ⟶ G, (representedZariskiToEtale B S hS U).map a = φ := by
  let e := representedQuasicoherentSchemeEquivalence B S hS U
  obtain ⟨a, ha⟩ := e.functor.map_surjective (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩)
    (ObjectProperty.homMk (X := e.functor.obj ⟨F, hF⟩) (Y := e.functor.obj ⟨G, hG⟩) φ)
  exact ⟨a.hom, congrArg (fun f : e.functor.obj ⟨F, hF⟩ ⟶ e.functor.obj ⟨G, hG⟩ => f.hom) ha⟩

/-- Every quasi-coherent `𝒪`-module on `h_U` is the comparison of a quasi-coherent Zariski
module. -/
theorem exists_representedZariskiToEtale_iso
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hM : M.IsQuasicoherentOnSite) :
    ∃ F : ((BigFppfOver.toScheme B S hS).obj U).Modules, SheafOfModules.IsQuasicoherent F ∧
      Nonempty ((representedZariskiToEtale B S hS U).obj F ≅ M) := by
  let e := representedQuasicoherentSchemeEquivalence B S hS U
  let X : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS U)).FullSubcategory := ⟨M, hM⟩
  exact ⟨(e.inverse.obj X).obj, (e.inverse.obj X).property,
    ⟨(ObjectProperty.ι _).mapIso (e.counitIso.app X)⟩⟩

/-- The comparison of a quasi-coherent Zariski module is quasi-coherent. -/
theorem isQuasicoherentOnSite_representedZariskiToEtale
    {F : ((BigFppfOver.toScheme B S hS).obj U).Modules} (hF : SheafOfModules.IsQuasicoherent F) :
    ((representedZariskiToEtale B S hS U).obj F).IsQuasicoherentOnSite :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).property

/-- Finite presentation on the site and finite presentation agree for `𝒪`-modules on `h_U`. -/
private theorem isFinitePresentationOnSite_iff_isFinitePresentation
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2) :
    M.IsFinitePresentationOnSite ↔ M.IsFinitePresentation := by
  let (V : SmallEtale B S hS (yoneda.obj U)) :
      HasSheafify ((SmallEtale.topology B S hS (yoneda.obj U)).over V) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let (V : SmallEtale B S hS (yoneda.obj U))
      (N : SheafOfModules.{u} ((representedStructureRingSheaf B S hS U).over V)) :
      Small.{u} N.sections :=
    SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  let (V : (smallEtaleRingedSite B S hS (schemeSpace U).obj (schemeSpace U).2).C)
      (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace U).obj (schemeSpace U).2).O).over V)) :
      Small.{u} N.sections :=
    SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  let (V : (smallEtaleRingedSite B S hS (schemeSpace U).obj (schemeSpace U).2).C) :
      HasSheafify ((smallEtaleRingedSite B S hS (schemeSpace U).obj (schemeSpace U).2).J.over V)
        AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact ⟨fun _ =>
    Stacks.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite_of_small _,
    fun _ => SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation M⟩

/-- A Zariski module whose comparison is of finite presentation on the site is of finite
presentation. -/
theorem isFinitePresentation_of_representedZariskiToEtale
    {F : ((BigFppfOver.toScheme B S hS).obj U).Modules} (hF : SheafOfModules.IsQuasicoherent F)
    (hM : ((representedZariskiToEtale B S hS U).obj F).IsFinitePresentationOnSite) :
    F.IsFinitePresentation :=
  (_root_.AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property F hF).2
    ((isFinitePresentation_representedSmallEtaleModule_iff B S hS U _).2
      ((isFinitePresentationOnSite_iff_isFinitePresentation B S hS U _).1 hM))

/-- **The comparison of a finitely presented Zariski module is finitely presented on the site.** -/
theorem isFinitePresentationOnSite_representedZariskiToEtale
    {F : ((BigFppfOver.toScheme B S hS).obj U).Modules} (hF : F.IsFinitePresentation) :
    ((representedZariskiToEtale B S hS U).obj F).IsFinitePresentationOnSite :=
  (isFinitePresentationOnSite_iff_isFinitePresentation B S hS U _).2
    ((isFinitePresentation_representedSmallEtaleModule_iff B S hS U _).1
      (AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_of_isFinitePresentation
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property F hF))

/-- A finitely presented `𝒪`-module on `h_U` is the comparison of a finitely presented Zariski
module. -/
theorem exists_representedZariskiToEtale_iso_of_isFinitePresentationOnSite
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hM : M.IsFinitePresentationOnSite) :
    ∃ F : ((BigFppfOver.toScheme B S hS).obj U).Modules, SheafOfModules.IsQuasicoherent F ∧
      F.IsFinitePresentation ∧ Nonempty ((representedZariskiToEtale B S hS U).obj F ≅ M) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_representedZariskiToEtale_iso B S hS U M
    (SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite M)
  exact ⟨F, hF, isFinitePresentation_of_representedZariskiToEtale B S hS U hF
    (SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm hM), ⟨e⟩⟩

end Transfer

/-! ### The faithfulness clause for a system of affine schemes -/

/-- **Stacks 01ZR (3) on the small étale ringed sites of a system of affine schemes**: the
hypothesis `AlgebraicGeometry.Space.EventualModuleMapEqOverAffineSystem` of the faithfulness
clause of Stacks 07V7 holds.

Both modules are comparisons `𝓕^a` of finitely presented Zariski modules and both morphisms are
comparisons of Zariski morphisms; the comparison commutes with inverse images and is faithful on
quasi-coherent modules, so this is Stacks 01ZR (3) for the underlying affine schemes,
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine'`. -/
theorem eventualModuleMapEqOverAffineSystem : EventualModuleMapEqOverAffineSystem B S hS := by
  intro J _ _ E hE c hc j M N hM hN φ ψ h
  obtain ⟨F, hF, hFfp, ⟨eF⟩⟩ :=
    exists_representedZariskiToEtale_iso_of_isFinitePresentationOnSite B S hS _ M hM
  obtain ⟨G, hG, hGfp, ⟨eG⟩⟩ :=
    exists_representedZariskiToEtale_iso_of_isFinitePresentationOnSite B S hS _ N hN
  obtain ⟨a, ha⟩ := representedZariskiToEtale_map_surjective B S hS _ hF hG
    (eF.hom ≫ φ ≫ eG.inv)
  obtain ⟨b, hb⟩ := representedZariskiToEtale_map_surjective B S hS _ hF hG
    (eF.hom ≫ ψ ≫ eG.inv)
  -- transport the hypothesis
  have hW : ∀ {k : J} (t : BigFppfOver B S hS) (g : t ⟶ E.obj k)
      {X Y : ((BigFppfOver.toScheme B S hS).obj (E.obj k)).Modules}
      (x y : X ⟶ Y), SheafOfModules.IsQuasicoherent X → SheafOfModules.IsQuasicoherent Y →
      ((modulePullback B S hS (schemeSpaceMap g)).map
          ((representedZariskiToEtale B S hS _).map x) =
        (modulePullback B S hS (schemeSpaceMap g)).map
          ((representedZariskiToEtale B S hS _).map y) ↔
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map x =
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map y) := by
    intro k t g X Y x y hX hY
    constructor
    · intro hxy
      have h' := Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
        (representedZariskiToEtalePullbackIso' B S hS g)
        (f := x) (g := y) (by simpa only [Functor.comp_map] using hxy)
      exact representedZariskiToEtale_map_injective B S hS t
        (Stacks.Modules.isQuasicoherent_pullback _ X hX)
        (Stacks.Modules.isQuasicoherent_pullback _ Y hY) h'
    · intro hxy
      exact Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
        (representedZariskiToEtalePullbackIso' B S hS g).symm
        (f := x) (g := y) (congrArg (representedZariskiToEtale B S hS t).map hxy)
  let D := E ⋙ BigFppfOver.toScheme B S hS
  have : ∀ k, IsAffine (D.obj k) := hE
  have key : ∀ {t : BigFppfOver B S hS} (g : t ⟶ E.obj j),
      (modulePullback B S hS (schemeSpaceMap g)).map φ =
          (modulePullback B S hS (schemeSpaceMap g)).map ψ ↔
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map a =
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map b := by
    intro t g
    rw [← hW t g a b hF hG, ha, hb, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, ← Functor.mapIso_hom, ← Functor.mapIso_inv, Iso.cancel_iso_hom_left,
      Iso.cancel_iso_inv_right]
  have : F.IsFinitePresentation := hFfp
  have : G.IsFinitePresentation := hGfp
  obtain ⟨k, e, hk⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine'
    D ((BigFppfOver.toScheme B S hS).mapCone c) hc j F G a b ((key (c.π.app j)).1 h)
  exact ⟨k, e, (key (E.map e)).2 hk⟩

/-! ### Natural endomorphisms of the comparison followed by an inverse image -/

/-- The sections of the structure sheaf of the small étale site of an algebraic space commute. -/
local instance isMulCommutative_smallEtaleRingSheaf (X : AlgebraicSpaces B S hS) :
    ∀ V, IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj V) :=
  fun V => ⟨⟨fun a b => RingedSite.mul_comm_ringSheaf _ V a b⟩⟩

/-- The comparison followed by an inverse image is a left adjoint. -/
theorem isLeftAdjoint_representedZariskiToEtale_comp {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    (representedZariskiToEtale B S hS U ⋙ modulePullback B S hS (schemeSpaceMap g)).IsLeftAdjoint :=
  ((((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).comp
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction).comp
    (modulePullbackAdjunction B S hS (schemeSpaceMap g)))).isLeftAdjoint

/-- **A natural endomorphism of `𝓕 ↦ g^*(𝓕^a)` commutes with every morphism between the values
at two quasi-coherent modules on an affine scheme**: at such modules it is multiplication by a
single global section. -/
theorem natEnd_app_comp_of_isAffine {V U : BigFppfOver B S hS} (g : V ⟶ U)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (δ : representedZariskiToEtale B S hS U ⋙ modulePullback B S hS (schemeSpaceMap g) ⟶
      representedZariskiToEtale B S hS U ⋙ modulePullback B S hS (schemeSpaceMap g))
    {F G : ((BigFppfOver.toScheme B S hS).obj U).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : (modulePullback B S hS (schemeSpaceMap g)).obj
        ((representedZariskiToEtale B S hS U).obj F) ⟶
      (modulePullback B S hS (schemeSpaceMap g)).obj ((representedZariskiToEtale B S hS U).obj G)) :
    δ.app F ≫ φ = φ ≫ δ.app G := by
  let K := representedZariskiToEtale B S hS U ⋙ modulePullback B S hS (schemeSpaceMap g)
  let κ : K.obj (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace V).1 (schemeSpace V).2).O) :=
    (modulePullback B S hS (schemeSpaceMap g)).mapIso
        (representedZariskiToEtaleObjUnitIso B S hS U) ≪≫
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
        (smallEtaleRingedToposModulesHom B S hS (schemeSpaceMap g))).symm
  obtain ⟨f, hf⟩ := Stacks.SheafOfModules.exists_eq_globalSectionToEnd_app_of_iso κ
    (δ.app (SheafOfModules.unit _))
  have key : ∀ (X : ((BigFppfOver.toScheme B S hS).obj U).Modules) [X.IsQuasicoherent],
      δ.app X = (Stacks.SheafOfModules.globalSectionToEnd _ f).app (K.obj X) := by
    intro X _
    let σ := generatingSectionsOfIsAffine X
    exact Stacks.SheafOfModules.app_eq_globalSectionToEnd_app_of_jointlyEpi K δ f hf
      (fun i => X.unitHomEquiv.symm (σ.s i))
      (fun a b h => Stacks.SheafOfModules.jointlyEpi_map_of_generatingSections K
        (isLeftAdjoint_representedZariskiToEtale_comp B S hS g) σ a b h)
  rw [key F, key G]
  exact Stacks.SheafOfModules.globalSectionToEnd_app_comp f φ

/-! ### The fullness clause for a system of affine schemes -/

section Fullness

variable {J : Type u} [Category.{u} J] (E : J ⥤ BigFppfOver B S hS) (c : Cone E)

/-- The leg of a cone at an index, typed with the vertex of the cone as its source. -/
def coneLeg (j : J) : c.pt ⟶ E.obj j := c.π.app j

/-- The legs of a cone commute with the transition morphisms of the diagram: the leg at `k`
followed by the image of `e : k ⟶ j` is the leg at `j`. -/
theorem coneLeg_w {j k : J} (e : k ⟶ j) :
    coneLeg B S hS E c k ≫ E.map e = coneLeg B S hS E c j :=
  c.w e

/-- The cone of underlying schemes, with its legs written as the images of the legs. -/
abbrev schemeCone : Cone (E ⋙ BigFppfOver.toScheme B S hS) where
  pt := (BigFppfOver.toScheme B S hS).obj c.pt
  π := { app := fun j => (BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c j)
         naturality := fun j k e => by
           change 𝟙 _ ≫ _ = _ ≫ (BigFppfOver.toScheme B S hS).map (E.map e)
           rw [Category.id_comp, ← Functor.map_comp, coneLeg_w] }

/-- The cone of underlying schemes is a limit cone when the image of the cone is. -/
def isLimitSchemeCone (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) :
    IsLimit (schemeCone B S hS E c) :=
  hc.ofIsoLimit (Cone.ext (Iso.refl _) (fun _ => (Category.id_comp _).symm))

/-- The projections of a cone, read on represented algebraic spaces, commute with the transition
morphisms. -/
theorem schemeSpaceMap_π_comp {j k : J} (e : k ⟶ j) :
    schemeSpaceMap (coneLeg B S hS E c k) ≫ schemeSpaceMap (E.map e) =
      schemeSpaceMap (coneLeg B S hS E c j) := by
  rw [← schemeSpaceMap_comp, coneLeg_w]

/-- The canonical identification of iterated Zariski inverse images along a cone. -/
noncomputable def zariskiConeCompIso {j k : J} (e : k ⟶ j) :
    Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (E.map e)) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c k)) ≅
      Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c j)) :=
  Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (by rw [← Functor.map_comp, coneLeg_w])

/-- The identification of iterated inverse images along a cone obtained by reading the Zariski
one through the comparison with étale modules. -/
noncomputable def coneCompareIso {j k : J} (e : k ⟶ j) :
    (representedZariskiToEtale B S hS (E.obj j) ⋙
        modulePullback B S hS (schemeSpaceMap (E.map e))) ⋙
        modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c k)) ≅
      representedZariskiToEtale B S hS (E.obj j) ⋙
        modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c j)) :=
  Functor.isoWhiskerRight (representedZariskiToEtalePullbackIso' B S hS (E.map e)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c k)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (zariskiConeCompIso B S hS E c e) _ ≪≫
    (representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c j)).symm

/-- The canonical identification of iterated Zariski inverse images along a cone, at a module. -/
theorem zariskiConeCompIso_hom_app {j k : J} (e : k ⟶ j)
    (X : ((BigFppfOver.toScheme B S hS).obj (E.obj j)).Modules) :
    (zariskiConeCompIso B S hS E c e).hom.app X =
      Stacks.AlgebraicGeometry.ModuleLimits.canHom
        ((schemeCone B S hS E c).π.app k)
        ((E ⋙ BigFppfOver.toScheme B S hS).map e)
        ((schemeCone B S hS E c).π.app j)
        ((schemeCone B S hS E c).w e) X := rfl

/-- Stacks 01ZR (2) for the underlying affine schemes, with the canonical identification written
through `AlgebraicGeometry.Space.zariskiConeCompIso`. -/
theorem exists_zariski_compat [IsCofiltered J]
    (hE : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj j)))
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (b : J)
    (F G : ((BigFppfOver.toScheme B S hS).obj (E.obj b)).Modules)
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ₀ : (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c b))).obj F ⟶
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c b))).obj G) :
    ∃ (l : J) (e : l ⟶ b) (ψ₀ : (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map (E.map e))).obj F ⟶
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (E.map e))).obj G),
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c l))).map ψ₀ ≫
          (zariskiConeCompIso B S hS E c e).hom.app G =
        (zariskiConeCompIso B S hS E c e).hom.app F ≫ φ₀ := by
  let D := E ⋙ BigFppfOver.toScheme B S hS
  have : ∀ k, IsAffine (D.obj k) := hE
  obtain ⟨l, e, ψ₀, h₀⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine'
      D (schemeCone B S hS E c) (isLimitSchemeCone B S hS E c hc) b F G φ₀
  refine ⟨l, e, ψ₀, ?_⟩
  rwa [zariskiConeCompIso_hom_app, zariskiConeCompIso_hom_app]

/-- The assembly of the fullness clause for a system of affine schemes from its Zariski form. -/
theorem moduleHomRestrict_eq_of_zariski_compat {l b : J} (e : l ⟶ b)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj b))]
    {M N : Modules.{u, u} B S hS (schemeSpace (E.obj b)).1 (schemeSpace (E.obj b)).2}
    {F G : ((BigFppfOver.toScheme B S hS).obj (E.obj b)).Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (eF : (representedZariskiToEtale B S hS (E.obj b)).obj F ≅ M)
    (eG : (representedZariskiToEtale B S hS (E.obj b)).obj G ≅ N)
    (φ : (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).obj M ⟶
      (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).obj N)
    (φ₀ : (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c b))).obj F ⟶
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c b))).obj G)
    (hφ₀ : (representedZariskiToEtale B S hS c.pt).map φ₀ =
      (representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c b)).inv.app F ≫
        ((modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).map eF.hom ≫ φ ≫
          (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).map eG.inv) ≫
        (representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c b)).hom.app G)
    (ψ₀ : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (E.map e))).obj F ⟶
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (E.map e))).obj G)
    (h₀ : (Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c l))).map ψ₀ ≫
          (zariskiConeCompIso B S hS E c e).hom.app G =
        (zariskiConeCompIso B S hS E c e).hom.app F ≫ φ₀) :
    moduleHomRestrict M N (schemeSpaceMap (coneLeg B S hS E c l)) (schemeSpaceMap (E.map e))
        (schemeSpaceMap (coneLeg B S hS E c b)) (schemeSpaceMap_π_comp B S hS E c e)
      ((modulePullback B S hS (schemeSpaceMap (E.map e))).map eF.inv ≫
        ((representedZariskiToEtalePullbackIso' B S hS (E.map e)).hom.app F ≫
          (representedZariskiToEtale B S hS (E.obj l)).map ψ₀ ≫
          (representedZariskiToEtalePullbackIso' B S hS (E.map e)).inv.app G) ≫
        (modulePullback B S hS (schemeSpaceMap (E.map e))).map eG.hom) = φ := by
  rw [moduleHomRestrict_eq_compIso]
  exact CompareIso.compat_of_compat' (A := representedZariskiToEtale B S hS (E.obj b))
    (A' := representedZariskiToEtale B S hS (E.obj l))
    (A'' := representedZariskiToEtale B S hS c.pt)
    (Pe := modulePullback B S hS (schemeSpaceMap (E.map e)))
    (Pk := modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c l)))
    (Pj := modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b)))
    (Ze := Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (E.map e)))
    (Zk := Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c l)))
    (Zj := Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (coneLeg B S hS E c b)))
    (representedZariskiToEtalePullbackIso' B S hS (E.map e))
    (representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c l))
    (representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c b))
    (zariskiConeCompIso B S hS E c e)
    (modulePullbackCompIso B S hS _ _ ≪≫
      eqToIso (congrArg (modulePullback B S hS) (schemeSpaceMap_π_comp B S hS E c e)))
    (X := F) (Y := G) (M := M) (N := N) eF eG φ ψ₀ φ₀ h₀ hφ₀
    (fun δ φ'' => natEnd_app_comp_of_isAffine B S hS (coneLeg B S hS E c b) δ φ'')

/-- **Stacks 01ZR (2) on the small étale ringed sites of a system of affine schemes**, with the
canonical identification of Stacks 03LU: a morphism between the inverse images to the limit of
two finitely presented modules on a stage is, at a later stage, the restriction of a morphism
between their inverse images there. -/
theorem exists_homRestrict_eq_of_isAffine [IsCofiltered J]
    (hE : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj j)))
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (b : J)
    (M N : Modules.{u, u} B S hS (schemeSpace (E.obj b)).1 (schemeSpace (E.obj b)).2)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).obj M ⟶
      (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).obj N) :
    ∃ (l : J) (e : l ⟶ b) (ψ : (modulePullback B S hS (schemeSpaceMap (E.map e))).obj M ⟶
        (modulePullback B S hS (schemeSpaceMap (E.map e))).obj N),
      moduleHomRestrict M N (schemeSpaceMap (coneLeg B S hS E c l)) (schemeSpaceMap (E.map e))
        (schemeSpaceMap (coneLeg B S hS E c b)) (schemeSpaceMap_π_comp B S hS E c e) ψ = φ := by
  obtain ⟨F, hF, hFfp, ⟨eF⟩⟩ :=
    exists_representedZariskiToEtale_iso_of_isFinitePresentationOnSite B S hS _ M hM
  obtain ⟨G, hG, hGfp, ⟨eG⟩⟩ :=
    exists_representedZariskiToEtale_iso_of_isFinitePresentationOnSite B S hS _ N hN
  have : F.IsQuasicoherent := hF
  have : G.IsQuasicoherent := hG
  have : F.IsFinitePresentation := hFfp
  have : G.IsFinitePresentation := hGfp
  have := hE b
  obtain ⟨φ₀, hφ₀⟩ := representedZariskiToEtale_map_surjective B S hS c.pt
    (Stacks.Modules.isQuasicoherent_pullback _ F hF)
    (Stacks.Modules.isQuasicoherent_pullback _ G hG)
    ((representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c b)).inv.app F ≫
      ((modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).map eF.hom ≫ φ ≫
        (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c b))).map eG.inv) ≫
      (representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c b)).hom.app G)
  obtain ⟨l, e, ψ₀, h₀⟩ := exists_zariski_compat B S hS E c hE hc b F G φ₀
  exact ⟨l, e, _, moduleHomRestrict_eq_of_zariski_compat B S hS E c e eF eG φ φ₀ hφ₀ ψ₀ h₀⟩

/-- **Stacks 01ZR (1) on the small étale ringed sites of a system of affine schemes**: a
finitely presented `𝒪`-module on the limit is the inverse image of a finitely presented
`𝒪`-module on a stage. -/
theorem exists_iso_modulePullback_of_isAffine [IsCofiltered J]
    (hE : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj j)))
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (P : Modules.{u, u} B S hS (schemeSpace c.pt).1 (schemeSpace c.pt).2)
    (hP : P.IsFinitePresentationOnSite) :
    ∃ (l : J) (Q : Modules.{u, u} B S hS (schemeSpace (E.obj l)).1 (schemeSpace (E.obj l)).2),
      Q.IsFinitePresentationOnSite ∧
        Nonempty (P ≅ (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS E c l))).obj Q) := by
  obtain ⟨F₀, hF₀, hF₀fp, ⟨eP⟩⟩ :=
    exists_representedZariskiToEtale_iso_of_isFinitePresentationOnSite B S hS _ P hP
  have : F₀.IsFinitePresentation := hF₀fp
  let D := E ⋙ BigFppfOver.toScheme B S hS
  have : ∀ k, IsAffine (D.obj k) := hE
  have : ∀ {i j : J} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (D.map f) := fun f =>
    isAffineHom_of_isAffine _
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  open Stacks.AlgebraicGeometry.ModuleLimits in
  obtain ⟨l, G₀, hG₀, ⟨eG⟩⟩ :=
    exists_isFinitePresentation_pullback_iso_of_isLimit_of_isAffine_stage
      D (schemeCone B S hS E c) (isLimitSchemeCone B S hS E c hc) j₀ F₀
  exact ⟨l, (representedZariskiToEtale B S hS (E.obj l)).obj G₀,
    isFinitePresentationOnSite_representedZariskiToEtale B S hS _ hG₀,
    ⟨eP.symm ≪≫ (representedZariskiToEtale B S hS c.pt).mapIso eG ≪≫
      ((representedZariskiToEtalePullbackIso' B S hS (coneLeg B S hS E c l)).app G₀).symm⟩⟩

end Fullness

end AlgebraicGeometry.Space

end

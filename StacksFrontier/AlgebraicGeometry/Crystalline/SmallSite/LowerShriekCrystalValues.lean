module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimit
public import StacksFrontier.AlgebraicGeometry.AffineChartLocalization.BaseChangePresheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekColimitLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf

/-!
# The sections of `i_!` of a crystal over an object mapping to `Cris(X/S)`

Let `ℱ` be a locally quasi-coherent crystal on the small crystalline site `Cris(X/S)`, lifted to
the module universe `u + 1`, and let `i_! ℱ` be its module-level lower shriek on `CRIS(X/S)`
([Stacks, Tag 07IJ], `...SmallSite.moduleLowerShriek`).  For an object `B` of `CRIS(X/S)` with
affine ambient scheme `T` and a morphism `τ : B ⟶ i A` to an object `A` of `Cris(X/S)` with affine
ambient scheme, this file proves that

`Γ(B, 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ (i_! ℱ)(B)`,  `t ⊗ s ↦ t · τ^* s`,

is bijective (`bijective_lowerShriekBaseChange`).  This is the fact that `i_! ℱ` is a crystal in
quasi-coherent modules near the objects that map to the small site, read on sections, which the
source uses without comment in [Stacks, Tag 07Q9] when it writes `ℱ'_{T'} = h^* ℱ_T` for
`ℱ' = f_cris^* ℱ`.

## The argument

On the Zariski site of `T`, the presheaf `W ↦ Γ(W, 𝒪_T) ⊗_{Γ(A, 𝒪)} ℱ(A)`
(`Stacks.AlgebraicGeometry.BaseChangePresheaf.basePresheaf`) maps to the restriction to `T` of the
colimit model of `i_! ℱ` (`tauToModel`), and that map is locally injective and locally surjective
(`...SmallSite.exists_restrictOpenLE_tauRestrict_eq_zero`,
`...SmallSite.exists_restrictOpenLE_eq_ι_tauIdx`).  The restriction to `T` of the
sheafification unit is locally bijective too, so the composite is a locally bijective map into a
Zariski sheaf.  Over the affine `T` the sheafification unit of `basePresheaf` is bijective on
global sections
(`Stacks.AlgebraicGeometry.BaseChangePresheaf.bijective_toSheafify_basePresheaf_app`),
and two locally bijective maps out of one presheaf into two sheaves are bijective on the same
sections (`...SmallSite.bijective_app_of_isLocallyBijective`).

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Stacks.PullbackColimitUnivLE

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  {B : Thickening S} {A : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A)

/-! ### The base-change presheaf on the ambient scheme of `B` -/

/-- The map `Γ(A, 𝒪) ⟶ Γ(B, 𝒪)` of `τ`, with target the global sections of the ambient scheme. -/
abbrev tauRing :
    (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj A)) ⟶
      Γ(B.thickening.target.scheme, ⊤) :=
  (crisCommRing S).map τ.op

/-- The sections of `ℱ` over `A`, as a module over the commutative ring `Γ(A, 𝒪)`. -/
abbrev sectionsOver (A : CrystallineThickening S) :
    ModuleCat.{u} ((crisCommRing S).obj (op ((CrystallineThickening.ι S).obj A))) :=
  F.val.obj (op A)

/-- **The presheaf `W ↦ Γ(W, 𝒪_T) ⊗_{Γ(A, 𝒪)} ℱ(A)` on the ambient scheme `T` of `B`.** -/
abbrev tauPresheaf : PresheafOfModules.{u} B.thickening.target.scheme.ringCatSheaf.obj :=
  Stacks.AlgebraicGeometry.BaseChangePresheaf.basePresheaf (tauRing τ) (sectionsOver F A)

/-- The identification of the sections of `𝒪_T` over `W` with the sections of `𝒪_{X/S}` over the
restriction `B|_W`. -/
abbrev ambientRingIso (W : B.thickening.target.scheme.Opens) :
    Γ(B.thickening.target.scheme, W) ≅ (crisCommRing S).obj (op (B.restrictOpen W)) :=
  ((Thickening.restrictionStructureIso B).app (op W)).symm

/-- The ring identification carries the ring map of the base-change presheaf to `τ_W^♯`. -/
lemma ambientRingIso_sectionsRingHom (W : B.thickening.target.scheme.Opens)
    (a : (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj A))) :
    (ambientRingIso W).hom.hom
        ((Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) W).hom a) =
      ((crisCommRing S).map (tauIdx τ W)).hom a := by
  have h := Thickening.structureSheaf_map_restrictOpenHom B W
  have h' : (crisCommRing S).map (B.restrictOpenHom W).op =
      B.thickening.target.scheme.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (ambientRingIso W).hom :=
    (Iso.eq_comp_inv ((Thickening.restrictionStructureIso B).app (op W))).2 h
  change _ = ((crisCommRing S).map τ.op ≫ (crisCommRing S).map (B.restrictOpenHom W).op).hom a
  rw [h']
  rfl

/-- The ring identification is natural in the open. -/
lemma ambientRingIso_naturality {W W' : B.thickening.target.scheme.Opens} (h : W' ≤ W)
    (t : Γ(B.thickening.target.scheme, W)) :
    (ambientRingIso W').hom.hom
        ((B.thickening.target.scheme.presheaf.map (homOfLE h).op).hom t) =
      ((crisCommRing S).map (B.restrictOpenLE h).op).hom ((ambientRingIso W).hom.hom t) := by
  have := (Thickening.restrictionStructureIso B).inv.naturality (homOfLE h).op
  exact congrArg (fun φ ↦ φ.hom t) this

/-- The inverse ring identification carries `τ_W^♯` to the ring map of the presheaf. -/
lemma ambientRingIso_inv_tauIdx (W : B.thickening.target.scheme.Opens)
    (a : (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj A))) :
    (ambientRingIso W).inv.hom (((crisCommRing S).map (tauIdx τ W)).hom a) =
      (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) W).hom a := by
  rw [← ambientRingIso_sectionsRingHom τ W a]
  exact Iso.hom_inv_id_apply (ambientRingIso W) _

/-! ### The comparison of the base-change presheaf with the terms of the colimit -/

/-- The bilinear datum of `tauKappa`. -/
def tauKappaBil (W : B.thickening.target.scheme.Opens) :
    Γ(B.thickening.target.scheme, W) →+ (sectionsOver F A →+
      diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk (tauIdx τ W))) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun n ↦ tmul ((crisCommRing S).map (tauIdx τ W)).hom ((ambientRingIso W).hom.hom t)
        (upSection F n))
      (fun n n' ↦ tmul_add _ _ (upSection F n) (upSection F n')))
    (fun t t' ↦ AddMonoidHom.ext fun n ↦ by
      change tmul _ ((ambientRingIso W).hom.hom (t + t')) _ =
        tmul _ ((ambientRingIso W).hom.hom t) _ + tmul _ ((ambientRingIso W).hom.hom t') _
      rw [map_add, tmul_eq_smul _ (_ + _), add_smul, ← tmul_eq_smul, ← tmul_eq_smul])

/-- **The sections of the base-change presheaf over `W` are the term of the colimit at
`(A, τ_W)`**, `t ⊗ s ↦ t ⊗ s`, the scalars being moved along `Γ(W, 𝒪_T) ≅ Γ(B|_W, 𝒪)` and the
module sections along the universe lift. -/
def tauKappa (W : B.thickening.target.scheme.Opens) :
    (tauPresheaf F τ).obj (op W) →+
      diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk (tauIdx τ W)) :=
  TensorProduct.liftAddHom (tauKappaBil F τ W) (fun a t n ↦ by
    change tmul _ ((ambientRingIso W).hom.hom
        ((Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) W).hom a *
          (show Γ(B.thickening.target.scheme, W) from t)))
        (upSection F n) =
      tmul _ ((ambientRingIso W).hom.hom t) (upSection F (show sectionsOver F A from a • n))
    rw [map_mul, ambientRingIso_sectionsRingHom]
    change _ = tmul _ _ (a • upSection F n)
    rw [tmul_smul_right, mul_comm])

/-- `tauKappa` on a pure tensor. -/
lemma tauKappa_tmul (W : B.thickening.target.scheme.Opens) (t : Γ(B.thickening.target.scheme, W))
    (n : sectionsOver F A) :
    tauKappa F τ W (Stacks.PullbackModel.tmul
        (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) W).hom t n) =
      tmul ((crisCommRing S).map (tauIdx τ W)).hom ((ambientRingIso W).hom.hom t)
        (upSection F n) :=
  rfl

/-- The bilinear datum of `tauKappaInv`. -/
def tauKappaInvBil (W : B.thickening.target.scheme.Opens) :
    (crisCommRing S).obj (op (B.restrictOpen W)) →+ ((ulModel F).obj (op A) →+
      (tauPresheaf F τ).obj (op W)) :=
  AddMonoidHom.mk'
    (fun r ↦ AddMonoidHom.mk'
      (fun m ↦ Stacks.PullbackModel.tmul
        (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) W).hom
        ((ambientRingIso W).inv.hom r) (show sectionsOver F A from m.down))
      (fun m m' ↦ Stacks.PullbackColimit.tmul_add _ _ _ _))
    (fun r r' ↦ AddMonoidHom.ext fun m ↦ by
      change Stacks.PullbackModel.tmul _ ((ambientRingIso W).inv.hom (r + r')) _ =
        Stacks.PullbackModel.tmul _ ((ambientRingIso W).inv.hom r) _ +
          Stacks.PullbackModel.tmul _ ((ambientRingIso W).inv.hom r') _
      rw [map_add, Stacks.PullbackColimit.tmul_eq_smul _ (_ + _), add_smul,
        ← Stacks.PullbackColimit.tmul_eq_smul, ← Stacks.PullbackColimit.tmul_eq_smul])

/-- The inverse of `tauKappa`. -/
def tauKappaInv (W : B.thickening.target.scheme.Opens) :
    diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk (tauIdx τ W)) →+ (tauPresheaf F τ).obj (op W) :=
  TensorProduct.liftAddHom (tauKappaInvBil F τ W) (fun a r m ↦ by
    change Stacks.PullbackModel.tmul _ ((ambientRingIso W).inv.hom
        (((crisCommRing S).map (tauIdx τ W)).hom a *
          (show (crisCommRing S).obj (op (B.restrictOpen W)) from r)))
        (show sectionsOver F A from m.down) =
      Stacks.PullbackModel.tmul _ ((ambientRingIso W).inv.hom r)
        ((show (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj A)) from a) •
          (show sectionsOver F A from m.down))
    rw [map_mul, ambientRingIso_inv_tauIdx, Stacks.PullbackColimit.tmul_smul_right, mul_comm])

/-- `tauKappaInv` is a left inverse of `tauKappa`. -/
lemma tauKappaInv_tauKappa (W : B.thickening.target.scheme.Opens)
    (q : (tauPresheaf F τ).obj (op W)) : tauKappaInv F τ W (tauKappa F τ W q) = q := by
  induction q using TensorProduct.induction_on with
  | zero => exact map_zero ((tauKappaInv F τ W).comp (tauKappa F τ W))
  | tmul t n =>
      exact congrArg (fun z ↦ Stacks.PullbackModel.tmul
          (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) W).hom z n)
        (Iso.hom_inv_id_apply (ambientRingIso W) (show Γ(B.thickening.target.scheme, W) from t))
  | add q q' hq hq' =>
      exact (map_add ((tauKappaInv F τ W).comp (tauKappa F τ W)) q q').trans
        (congrArg₂ (· + ·) hq hq')

/-- `tauKappaInv` is a right inverse of `tauKappa`. -/
lemma tauKappa_tauKappaInv (W : B.thickening.target.scheme.Opens)
    (y : diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (CostructuredArrow.mk (tauIdx τ W))) : tauKappa F τ W (tauKappaInv F τ W y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact map_zero ((tauKappa F τ W).comp (tauKappaInv F τ W))
  | tmul r m =>
      exact congrArg (fun z ↦ tmul ((crisCommRing S).map (tauIdx τ W)).hom z
          (upSection F m.down))
        (Iso.inv_hom_id_apply (ambientRingIso W)
          (show (crisCommRing S).obj (op (B.restrictOpen W)) from r))
  | add y y' hy hy' =>
      exact (map_add ((tauKappa F τ W).comp (tauKappaInv F τ W)) y y').trans
        (congrArg₂ (· + ·) hy hy')

/-- `tauKappa` is bijective. -/
lemma bijective_tauKappa (W : B.thickening.target.scheme.Opens) :
    Function.Bijective (tauKappa F τ W) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨tauKappaInv F τ W, tauKappaInv_tauKappa F τ W, tauKappa_tauKappaInv F τ W⟩

/-- `tauKappa` is compatible with the restriction maps. -/
lemma tauKappa_map {W W' : B.thickening.target.scheme.Opens} (h : W' ≤ W)
    (q : (tauPresheaf F τ).obj (op W)) :
    tauKappa F τ W' ((tauPresheaf F τ).map (homOfLE h).op q) =
      tauRestrict F τ h (tauKappa F τ W q) := by
  let K₁ : (tauPresheaf F τ).obj (op W) →+ diagramObj (CrystallineThickening.ι S)
      (crisCommRing S) (ulModel F) (CostructuredArrow.mk (tauIdx τ W')) :=
    (tauKappa F τ W').comp ((tauPresheaf F τ).map (homOfLE h).op).hom.toAddMonoidHom
  let K₂ : (tauPresheaf F τ).obj (op W) →+ diagramObj (CrystallineThickening.ι S)
      (crisCommRing S) (ulModel F) (CostructuredArrow.mk (tauIdx τ W')) :=
    (tauRestrict F τ h).hom.toAddMonoidHom.comp (tauKappa F τ W)
  change K₁ q = K₂ q
  induction q using TensorProduct.induction_on with
  | zero => exact (map_zero K₁).trans (map_zero K₂).symm
  | tmul t n =>
      exact congrArg (fun z ↦ tmul ((crisCommRing S).map (tauIdx τ W')).hom z (upSection F n))
        (ambientRingIso_naturality h (show Γ(B.thickening.target.scheme, W) from t))
  | add q q' hq hq' =>
      exact (map_add K₁ q q').trans ((congrArg₂ (· + ·) hq hq').trans (map_add K₂ q q').symm)

/-! ### The comparison on the Zariski site of the ambient scheme of `B` -/

/-- The component over `W` of `tauToModel`. -/
def tauToModelApp (W : B.thickening.target.scheme.Opens) :
    ULift.{u + 1} ((tauPresheaf F τ).obj (op W)) →+
      (lowerShriekModel ((moduleULift S).obj F)).obj (op (B.restrictOpen W)) :=
  ((colimit.ι (diagram (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (op (B.restrictOpen W))) (CostructuredArrow.mk (tauIdx τ W))).hom.toAddMonoidHom.comp
    (tauKappa F τ W)).comp AddEquiv.ulift.toAddMonoidHom

/-- `tauToModelApp` written out on elements. -/
lemma tauToModelApp_apply (W : B.thickening.target.scheme.Opens)
    (x : ULift.{u + 1} ((tauPresheaf F τ).obj (op W))) :
    tauToModelApp F τ W x = colimit.ι (diagram (CrystallineThickening.ι S) (crisCommRing S)
      (ulModel F) (op (B.restrictOpen W))) (CostructuredArrow.mk (tauIdx τ W))
        (tauKappa F τ W x.down) := rfl

/-- **The comparison of the base-change presheaf `W ↦ Γ(W, 𝒪_T) ⊗_{Γ(A, 𝒪)} ℱ(A)` with the
restriction to `T` of the colimit model of `i_!ℱ`**: the germ of `t ⊗ s` at the index
`(A, τ_W)`.  The sections of the source are lifted to the module universe `u + 1`. -/
def tauToModel : (tauPresheaf F τ).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ⟶
    B.restrictOpenFunctor.op ⋙ (lowerShriekModel ((moduleULift S).obj F)).presheaf where
  app W := AddCommGrpCat.ofHom (tauToModelApp F τ W.unop)
  naturality {W W'} i := by
    ext x
    change tauToModelApp F τ W'.unop
        (ULift.up ((tauPresheaf F τ).map (homOfLE (leOfHom i.unop)).op x.down)) =
      (lowerShriekModel ((moduleULift S).obj F)).map (B.restrictOpenLE (leOfHom i.unop)).op
        (tauToModelApp F τ W.unop x)
    exact (congrArg (ConcreteCategory.hom (colimit.ι (diagram (CrystallineThickening.ι S)
        (crisCommRing S) (ulModel F) (op (B.restrictOpen W'.unop)))
          (CostructuredArrow.mk (tauIdx τ W'.unop))))
        (tauKappa_map F τ (leOfHom i.unop) x.down)).trans
      (map_restrictOpenLE_ι_tauIdx F τ (leOfHom i.unop) _).symm

/-- `tauToModel_app` written out on elements. -/
lemma tauToModel_app_apply (W : (B.thickening.target.scheme.Opens)ᵒᵖ)
    (x : ULift.{u + 1} ((tauPresheaf F τ).obj W)) :
    (tauToModel F τ).app W x = tauToModelApp F τ W.unop x := rfl

variable [IsAffine A.obj.thickening.target.scheme]
  (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F)

include hF hcrys in
/-- **The comparison `tauToModel` is locally injective** for the Zariski topology. -/
theorem isLocallyInjective_tauToModel :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (tauToModel F τ) where
  equalizerSieve_mem {W} x y hxy := by
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    have h0 : tauToModelApp F τ W.unop (x - y) = 0 :=
      (map_sub (tauToModelApp F τ W.unop) x y).trans (sub_eq_zero.2 hxy)
    obtain ⟨W', h, hpW', hz⟩ :=
      exists_restrictOpenLE_tauRestrict_eq_zero F τ hF hcrys W.unop _ h0 p hp
    refine ⟨W', homOfLE h, ?_, hpW'⟩
    change ULift.up ((tauPresheaf F τ).map (homOfLE h).op x.down) =
      ULift.up ((tauPresheaf F τ).map (homOfLE h).op y.down)
    congr 1
    let K : (tauPresheaf F τ).obj W →+ diagramObj (CrystallineThickening.ι S) (crisCommRing S)
        (ulModel F) (CostructuredArrow.mk (tauIdx τ W')) :=
      (tauKappa F τ W').comp ((tauPresheaf F τ).map (homOfLE h).op).hom.toAddMonoidHom
    exact (bijective_tauKappa F τ W').1 (sub_eq_zero.1 ((map_sub K x.down y.down).symm.trans
      ((tauKappa_map F τ h (x.down - y.down)).trans hz)))

include hF hcrys in
/-- **The comparison `tauToModel` is locally surjective** for the Zariski topology. -/
theorem isLocallySurjective_tauToModel :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (tauToModel F τ) where
  imageSieve_mem {W} s := by
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    obtain ⟨W', h, hpW', w, hw⟩ := exists_restrictOpenLE_eq_ι_tauIdx F τ hF hcrys W s p hp
    obtain ⟨q, rfl⟩ := (bijective_tauKappa F τ W').2 w
    exact ⟨W', homOfLE h, ⟨ULift.up q, hw.symm⟩, hpW'⟩

/-- The presheaf pullback whose sheafification is `i_!ℱ`. -/
abbrev lowerShriekPresheafOf :
    PresheafOfModules.{u + 1} (crisCommRing S ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pullback.{u + 1}
    (𝟙 ((CrystallineThickening.ι S).op ⋙ (crisCommRing S ⋙ forget₂ CommRingCat RingCat)))).obj
      ((moduleULift S).obj F).val

/-- The identification of the colimit model with the presheaf pullback, restricted to the
ambient scheme of `B`. -/
def modelToPullbackRestrict (B : Thickening S) :
    B.restrictOpenFunctor.op ⋙ (lowerShriekModel ((moduleULift S).obj F)).presheaf ≅
      B.restrictOpenFunctor.op ⋙ (lowerShriekPresheafOf F).presheaf :=
  Functor.isoWhiskerLeft B.restrictOpenFunctor.op ((PresheafOfModules.toPresheaf _).mapIso
    ((Stacks.PullbackColimitUnivLE.pullbackIdIso (CrystallineThickening.ι S)
      (crisCommRing S)).app ((moduleULift S).obj F).val).symm)

/-- The sheafification unit of the presheaf pullback, restricted to the ambient scheme of `B`. -/
abbrev sheafifyRestrict (B : Thickening S) :
    B.restrictOpenFunctor.op ⋙ (lowerShriekPresheafOf F).presheaf ⟶
      B.restrictOpenFunctor.op ⋙
        ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.presheaf :=
  Functor.whiskerLeft B.restrictOpenFunctor.op
    (toSheafify (topology S) (lowerShriekPresheafOf F).presheaf)

/-- **The comparison of the base-change presheaf with the restriction to `T` of `i_!ℱ`**:
`tauToModel`, followed by the identification of the colimit model with the presheaf pullback and
by the restriction of the sheafification unit. -/
def tauToSheaf : (tauPresheaf F τ).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ⟶
    B.restrictOpenFunctor.op ⋙ ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.presheaf :=
  (tauToModel F τ ≫ (modelToPullbackRestrict F B).hom) ≫ sheafifyRestrict F B

include hF hcrys in
/-- **`tauToSheaf` is locally injective** for the Zariski topology. -/
theorem isLocallyInjective_tauToSheaf :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (tauToSheaf F τ) := by
  have := isLocallyInjective_tauToModel F τ hF hcrys
  have := isLocallyInjective_toSheafifyBig (lowerShriekPresheafOf F).presheaf
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (sheafifyRestrict F B) :=
    isLocallyInjective_whiskerLeft_restrictOpenFunctorBig B
      (toSheafify (topology S) (lowerShriekPresheafOf F).presheaf)
  exact Presheaf.isLocallyInjective_comp _ _ _

include hF hcrys in
/-- **`tauToSheaf` is locally surjective** for the Zariski topology. -/
theorem isLocallySurjective_tauToSheaf :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (tauToSheaf F τ) := by
  have := isLocallySurjective_tauToModel F τ hF hcrys
  have := isLocallySurjective_toSheafifyBig (lowerShriekPresheafOf F).presheaf
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (sheafifyRestrict F B) :=
    isLocallySurjective_whiskerLeft_restrictOpenFunctorBig B
      (toSheafify (topology S) (lowerShriekPresheafOf F).presheaf)
  exact Presheaf.isLocallySurjective_comp _ _ _

include hF hcrys in
/-- **Over an affine `T` the comparison `tauToSheaf` is bijective on global sections**: it and the
universe lift of the sheafification unit of the base-change presheaf are two locally bijective
morphisms out of one presheaf into two Zariski sheaves, and the latter is bijective over the
affine `T`. -/
theorem bijective_tauToSheaf_app_top [IsAffine B.thickening.target.scheme] :
    Function.Bijective (ConcreteCategory.hom ((tauToSheaf F τ).app
      (op (⊤ : B.thickening.target.scheme.Opens)))) := by
  have := isLocallyInjective_tauToSheaf F τ hF hcrys
  have := isLocallySurjective_tauToSheaf F τ hF hcrys
  have hZ₁ : Presheaf.IsSheaf (Opens.grothendieckTopology B.thickening.target.scheme)
      (sheafify (Opens.grothendieckTopology B.thickening.target.scheme)
        (tauPresheaf F τ).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _
      ((presheafToSheaf (Opens.grothendieckTopology B.thickening.target.scheme) _).obj
        (tauPresheaf F τ).presheaf).property
  have hZ₂ := isSheaf_restrictOpenFunctorBig B
    ((moduleLowerShriek S).obj ((moduleULift S).obj F)).isSheaf
  have hb := Stacks.AlgebraicGeometry.BaseChangePresheaf.bijective_toSheafify_basePresheaf_app
    (tauRing τ) (sectionsOver F A) (isAffineOpen_top B.thickening.target.scheme)
  refine bijective_app_of_isLocallyBijective hZ₁ hZ₂
    (Functor.whiskerRight (toSheafify (Opens.grothendieckTopology B.thickening.target.scheme)
      (tauPresheaf F τ).presheaf) AddCommGrpCat.uliftFunctor.{u + 1, u}) (tauToSheaf F τ) _ ?_
  refine ⟨fun x y hxy ↦ ULift.ext _ _ (hb.1 (congrArg ULift.down hxy)), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hb.2 y.down
  exact ⟨ULift.up x, ULift.ext _ _ hx⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

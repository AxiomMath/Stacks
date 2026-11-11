module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionCrisDeRham

/-!
# The twisted de Rham differential and the connection on a smooth lifting

In the situation of Remark [Stacks, Tag 07MW], let `F` be a crystal in quasi-coherent
`𝒪_{X/S}`-modules (in this library: `F.IsQuasicoherentOnSite`) and `F_Y` its restriction to the
object `(X, Y, γ)`.  The de Rham complex `F ⊗ Ω^•_{X/S}` of [Stacks, Tag 07LM]
(`...SmallSite.crystalDeRhamDifferential`) restricts to `Y`, and [Stacks, Tag 07IZ] identifies its
terms there with `F_Y ⊗ Ω^q_{Y/S}` (`twistedFormsRestrictionIso`, the identification
`...SmallSite.tensorFormsAmbientIso` at the comparison `formsComparison` of
`SmallSite/SmoothLiftingForms.lean`).  This file reads the restricted differentials on
`F_Y ⊗ Ω^•_{Y/S}` and proves that they are a twisted de Rham differential:

* `twistedDifferentialApp` — the differential `F_Y ⊗ Ω^q_{Y/S} ⟶ F_Y ⊗ Ω^{q+1}_{Y/S}` on sections;
  `twistedDifferentialApp_comp` — consecutive ones compose to zero.
* `twistedDifferentialApp_tmul_affine` — over an affine open lying over an affine open of `S` it is
  `x ⊗ ω ↦ ∇(x) ∧ ω + x ⊗ d ω` with `∇` the ring-level canonical connection of
  [Stacks, Tag 07J6] (`...SmallSite.AffineConnection.ringConnection`) of the corresponding object.
* `connectionApp` — the connection `∇ : F_Y ⟶ F_Y ⊗ Ω_{Y/S}`: the degree-zero differential on
  `s ⊗ 1`; `connectionApp_affine` identifies it with the ring-level connection of 07J6, and
  `connectionApp_smul` is its Leibniz rule.
* `twistedDifferentialApp_twistedTmul` — **the Leibniz rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`** on
  every open, proved from the affine formula by locality.
* `twistedDifferentialApp_baseScalar_smul` — **the differential is `f^{-1}𝒪_S`-linear**, from the
  Leibniz rule, `d` killing `f^{-1}𝒪_S`, and the local generation of `F_Y ⊗ Ω^q` by pure tensors.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Hom
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

attribute [local instance] commRingRingCatSheafSections moduleCrysFormRingSections

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

variable (F) in
/-- The restriction `F_Y` of `F` to the object `(X, Y, γ)`. -/
abbrev liftingModule : T.Y.Modules := crysAmbientSchemeModules F T.crystallineThickening

variable (F) in
/-- **[Stacks, Tag 07IZ] for `F ⊗ Ω^q_{X/S}` on the smooth lifting**:
`(F ⊗ Ω^q_{X/S})_Y ≅ F_Y ⊗ Ω^q_{Y/S}` at the coefficient universe `u + 1`. -/
def twistedFormsRestrictionIso (q : ℕ) :=
  tensorFormsAmbientIso F (T.formsComparison q)

/-- The restriction to `Y` of the differential of the de Rham complex of [Stacks, Tag 07LM], read
on `F_Y ⊗ Ω^q_{Y/S} ⟶ F_Y ⊗ Ω^{q+1}_{Y/S}` through `twistedFormsRestrictionIso`. -/
def twistedDifferentialULift (q : ℕ) :
    ambientTensorSheafULift (A := T.crystallineThickening) F
        (relativeDifferentialForms T.toBase (q : ℤ)) ⟶
      ambientTensorSheafULift (A := T.crystallineThickening) F
        (relativeDifferentialForms T.toBase ((q + 1 : ℕ) : ℤ)) :=
  (T.twistedFormsRestrictionIso F q).inv ≫
    Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor T.crystallineThickening).op
      (crystalDeRhamDifferential hF q).hom ≫
    (T.twistedFormsRestrictionIso F (q + 1)).hom

/-- The twisted differential on the sections over an open. -/
def twistedDifferentialApp (q : ℕ) (U : (T.Y.Opens)ᵒᵖ) :
    (twistedForms T.toBase (T.liftingModule F) q).val.obj U →+
      (twistedForms T.toBase (T.liftingModule F) (q + 1)).val.obj U :=
  AddEquiv.ulift.toAddMonoidHom.comp
    (((T.twistedDifferentialULift hF q).app U).hom.comp AddEquiv.ulift.symm.toAddMonoidHom)

/-- `twistedDifferentialApp` on a section, through the universe lift. -/
theorem twistedDifferentialApp_apply (q : ℕ) (U : (T.Y.Opens)ᵒᵖ)
    (x : (twistedForms T.toBase (T.liftingModule F) q).val.obj U) :
    T.twistedDifferentialApp hF q U x = ((T.twistedDifferentialULift hF q).app U (ULift.up x)).down
        :=
  rfl

/-- The twisted differential commutes with restriction. -/
theorem twistedDifferentialApp_restrict (q : ℕ) {U V : (T.Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (x : (twistedForms T.toBase (T.liftingModule F) q).val.obj U) :
    (twistedForms T.toBase (T.liftingModule F) (q + 1)).val.map k
        (T.twistedDifferentialApp hF q U x) =
      T.twistedDifferentialApp hF q V ((twistedForms T.toBase (T.liftingModule F) q).val.map k x) :=
  congrArg ULift.down
    (ConcreteCategory.congr_hom ((T.twistedDifferentialULift hF q).naturality k) (ULift.up x)).symm

/-- Consecutive twisted differentials compose to zero, those of [Stacks, Tag 07LM] doing so. -/
theorem twistedDifferentialULift_comp (q : ℕ) :
    T.twistedDifferentialULift hF q ≫ T.twistedDifferentialULift hF (q + 1) = 0 := by
  have h0 : (crystalDeRhamDifferential hF q).hom ≫ (crystalDeRhamDifferential hF (q + 1)).hom =
      0 := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, crystalDeRhamDifferential_comp]
    rfl
  unfold twistedDifferentialULift
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.whiskerLeft_comp_assoc, h0]
  have hz : Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor
      T.crystallineThickening).op
      (0 : (tensorDifferentialFormsSheaf F q).obj ⟶ (tensorDifferentialFormsSheaf F (q + 1 +
          1)).obj) =
        0 := by
    ext X x
    rfl
  rw [hz]
  simp

/-- Consecutive twisted differentials compose to zero on sections. -/
theorem twistedDifferentialApp_comp (q : ℕ) (U : (T.Y.Opens)ᵒᵖ)
    (x : (twistedForms T.toBase (T.liftingModule F) q).val.obj U) :
    T.twistedDifferentialApp hF (q + 1) U (T.twistedDifferentialApp hF q U x) = 0 :=
  congrArg ULift.down
    ((ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (NatTrans.congr_app (T.twistedDifferentialULift_comp hF q) U)
        (ULift.up x)).trans rfl))

variable (F) in
/-- A pure tensor in the sections of the presheaf `F ⊗ Ω^q_{X/S}` over `A|_W`. -/
abbrev liftingTmul (q : ℕ) (W : T.Y.Opens) (x : F.val.obj (op (T.crystallineThickening.restrictOpen
    W)))
    (ω : (crysDifferentialForms S q).obj (op (T.crystallineThickening.restrictOpen W))) :
    ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) q).obj
        (op (T.crystallineThickening.restrictOpen W))) :=
  x ⊗ₜ ω

/-- **The twisted differential on a pure tensor over an affine-over-affine open**: it is the
extension `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of [Stacks, Tag 07LM] over the corresponding
affine-over-affine object of `Cris(X/S)`, read in `F_Y ⊗ Ω^{q+1}_{Y/S}`. -/
theorem twistedDifferentialApp_tmul_formsCompRel (q : ℕ) {W : T.Y.Opens} (hW : IsAffineOpen W)
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V)
    (h : W ≤ T.crystallineThickening.obj.toBase.hom ⁻¹ᵁ V)
    (x : F.val.obj (op (T.crystallineThickening.restrictOpen W)))
    (ω : (crysDifferentialForms S q).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.twistedDifferentialApp hF q (op W)
        (Stacks.PullbackTensorCoherence.tmul T.Y.toRingedSpace (T.liftingModule F)
          (relativeDifferentialForms T.toBase (q : ℤ)) (op W) x (T.formsCompRel q W ω)) =
      (tensorFormsAmbientUnit F (T.formsComparison (q + 1))).app (op W)
        (affineDeRhamDifferential hF q
          (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV h)
          (T.liftingTmul F q W x ω)) := by
  have h1 := tensorFormsAmbientIso_inv_tmul F (T.formsComparison q) W x ω
  have h2 := crystalDeRhamDifferential_app_toSheafify hF q
    (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV h)
    (T.liftingTmul F q W x ω)
  have h3 := tensorFormsAmbientIso_hom_app_toSheafify' F (T.formsComparison (q + 1)) W
    (ULift.up (affineDeRhamDifferential hF q
      (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV h)
      (T.liftingTmul F q W x ω)))
  refine congrArg ULift.down (Eq.trans ?_ h3)
  refine congrArg ((T.twistedFormsRestrictionIso F (q + 1)).hom.app (op W)) (Eq.trans ?_ h2)
  exact congrArg ((crystalDeRhamDifferential hF q).hom.app
    (op (T.crystallineThickening.restrictOpen W))) h1

/-! ### Reading ring-level tensors over `A|_W` on `Y` -/

variable (F) in
/-- `F(A|_W) ⊗ ⋀^p Ω_{X/S}(A|_W) ⟶ (F_Y ⊗ Ω^p_{Y/S})(W)`, `m ⊗ ω ↦ m ⊗ ω`. -/
def formsTensorComparison (p : ℕ) (W : T.Y.Opens) :
    F.val.obj (op (T.crystallineThickening.restrictOpen W)) ⊗[crysFormRing S
        (T.crystallineThickening.restrictOpen W)]
      ⋀[crysFormRing S (T.crystallineThickening.restrictOpen W)]^p
        ((crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) →+
      (twistedForms T.toBase (T.liftingModule F) p).val.obj (op W) :=
  ((tensorFormsAmbientUnit F (T.formsComparison p)).app (op W)).hom.comp
    (tensorFormsSectionsEquiv F p (T.crystallineThickening.restrictOpen W)).symm.toAddMonoidHom

/-- `formsTensorComparison` on a pure tensor. -/
theorem formsTensorComparison_tmul (p : ℕ) (W : T.Y.Opens)
    (m : F.val.obj (op (T.crystallineThickening.restrictOpen W)))
    (η : ⋀[crysFormRing S (T.crystallineThickening.restrictOpen W)]^p
        ((crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)))) :
    T.formsTensorComparison F p W (m ⊗ₜ η) =
      twistedTmul T.toBase (T.liftingModule F) p (op W) m
        (T.formsCompRel p W ((crysFormSections S p (T.crystallineThickening.restrictOpen W)).symm
          η)) :=
  rfl

variable (F) in
/-- `F(A|_W) ⊗ Ω_{X/S}(A|_W) ⟶ (F_Y ⊗ Ω_{Y/S})(W)`, `m ⊗ α ↦ m ⊗ α`. -/
def connectionComparison (W : T.Y.Opens) :
    F.val.obj (op (T.crystallineThickening.restrictOpen W)) ⊗[crysFormRing S
        (T.crystallineThickening.restrictOpen W)]
      (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)) →+
      (moduleConnectionTarget T.toBase (T.liftingModule F)).val.obj (op W) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ AddMonoidHom.mk'
        (fun α ↦ connectionTmul T.toBase (T.liftingModule F) (op W) m (T.formsCompOneRel W α))
        (fun α α' ↦ (congrArg (connectionTmul T.toBase (T.liftingModule F) (op W) m)
          (map_add (T.formsCompOneRel W) α α')).trans (connectionTmul_add_right _ _ _ _ _ _)))
      (fun m m' ↦ AddMonoidHom.ext fun α ↦ connectionTmul_add_left _ _ _ _ _ _))
    (fun r m α ↦ by
      change connectionTmul T.toBase (T.liftingModule F) (op W) (r • m) (T.formsCompOneRel W α) =
        connectionTmul T.toBase (T.liftingModule F) (op W) m (T.formsCompOneRel W (r • α))
      rw [T.formsCompOneRel_smul]
      exact (congrArg (fun z ↦ connectionTmul T.toBase (T.liftingModule F) (op W) z
        (T.formsCompOneRel W α)) (crysAmbient_smul F T.crystallineThickening W r m)).trans
        ((connectionTmul_smul_left _ _ _ (T.sectionRingIso W r) _ _).trans
          (connectionTmul_smul_right _ _ _ (T.sectionRingIso W r) _ _).symm))

/-- `connectionComparison` on a pure tensor. -/
theorem connectionComparison_tmul (W : T.Y.Opens)
    (m : F.val.obj (op (T.crystallineThickening.restrictOpen W)))
    (α : (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.connectionComparison F W (m ⊗ₜ α) =
      connectionTmul T.toBase (T.liftingModule F) (op W) m (T.formsCompOneRel W α) :=
  rfl

/-- **Reading `∇(m) ∧ ω` on `Y`**: the comparison carries the ring-level wedge of a section of
`F(A|_W) ⊗ Ω_{X/S}(A|_W)` with a form to the twisted wedge pairing. -/
theorem formsTensorComparison_map_leftWedge (q : ℕ) (W : T.Y.Opens)
    (η : ⋀[crysFormRing S (T.crystallineThickening.restrictOpen W)]^q
        ((crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))))
    (z : F.val.obj (op (T.crystallineThickening.restrictOpen W)) ⊗[crysFormRing S
        (T.crystallineThickening.restrictOpen W)]
      (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsTensorComparison F (q + 1) W
        (TensorProduct.map LinearMap.id ((Crystalline.leftWedge q).flip η) z) =
      twistedFormsWedgeSection T.toBase (T.liftingModule F) q (op W)
        (T.connectionComparison F W z)
        (T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
          η)) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    have h := twistedFormsWedgeSection_add T.toBase (T.liftingModule F) q (op W) 0 0
      (T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm η))
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm).symm
  | tmul m α =>
    rw [TensorProduct.map_tmul, formsTensorComparison_tmul, connectionComparison_tmul]
    exact (congrArg (twistedTmul T.toBase (T.liftingModule F) (q + 1) (op W) m)
      (T.formsCompRel_leftWedge q W α η)).trans
      (twistedFormsWedgeSection_tmul T.toBase (T.liftingModule F) q (op W) m _ _).symm
  | add z z' hz hz' =>
    rw [map_add, map_add, hz, hz', map_add, twistedFormsWedgeSection_add]

/-- **The twisted differential on a pure tensor over an affine-over-affine open, expanded**:
`d(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω`, with `∇` the ring-level canonical connection of
[Stacks, Tag 07J6] over the corresponding object of `Cris(X/S)`. -/
theorem twistedDifferentialApp_tmul_affine (q : ℕ) {W : T.Y.Opens} (hW : IsAffineOpen W)
    [IsAffine (T.crystallineThickening.restrictOpen W).obj.thickening.target.scheme]
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V)
    (h : W ≤ T.crystallineThickening.obj.toBase.hom ⁻¹ᵁ V)
    (x : F.val.obj (op (T.crystallineThickening.restrictOpen W)))
    (ω : (crysDifferentialForms S q).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.twistedDifferentialApp hF q (op W)
        (twistedTmul T.toBase (T.liftingModule F) q (op W) x (T.formsCompRel q W ω)) =
      twistedFormsWedgeSection T.toBase (T.liftingModule F) q (op W)
          (T.connectionComparison F W (AffineConnection.ringConnection
            (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV
              h).top_le_preimage_baseOpen
            (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV
              h).isAffineOpen_baseOpen
            (bijective_crysExtensionSectionsMap_affine hF
              (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV h))
            x))
          (T.formsCompRel q W ω) +
        twistedTmul T.toBase (T.liftingModule F) (q + 1) (op W) x
          (relativeDeRhamDifferentialSection T.toBase q (op W) (T.formsCompRel q W ω)) := by
  refine (T.twistedDifferentialApp_tmul_formsCompRel hF q hW hV h x ω).trans ?_
  change T.formsTensorComparison F (q + 1) W (AffineConnection.extDiff _ _ _ q
    (x ⊗ₜ crysFormSections S q (T.crystallineThickening.restrictOpen W) ω)) = _
  refine (congrArg (T.formsTensorComparison F (q + 1) W)
    (AffineConnection.extDiff_tmul _ _ _ q x
      (crysFormSections S q (T.crystallineThickening.restrictOpen W) ω))).trans ?_
  refine (map_add _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · refine (T.formsTensorComparison_map_leftWedge q W _ _).trans ?_
    exact congrArg (twistedFormsWedgeSection T.toBase (T.liftingModule F) q (op W) _)
      (congrArg (T.formsCompRel q W) (LinearEquiv.symm_apply_apply _ ω))
  · refine (T.formsTensorComparison_tmul (q + 1) W x _).trans ?_
    refine congrArg (twistedTmul T.toBase (T.liftingModule F) (q + 1) (op W) x) ?_
    refine (T.formsCompRel_deRham q W _).trans ?_
    exact congrArg (relativeDeRhamDifferentialSection T.toBase q (op W))
      (congrArg (T.formsCompRel q W) (LinearEquiv.symm_apply_apply _ ω))

/-! ### Locality -/

/-- Two sections of a sheaf of modules on `Y` agreeing on every affine-over-affine open below
their open of definition agree. -/
theorem eq_of_forall_isAffineOverAffineOpen (M : T.Y.Modules) {U : T.Y.Opens}
    (a b : M.val.obj (op U))
    (h : ∀ (W : T.Y.Opens), IsAffineOverAffineOpen T.crystallineThickening.obj W →
      ∀ hWU : W ≤ U, M.val.map (homOfLE hWU).op a = M.val.map (homOfLE hWU).op b) :
    a = b :=
  M.isSheaf.section_ext (U := op U) fun p hp ↦ by
    obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOverAffineOpen T.crystallineThickening.obj U p hp
    exact ⟨W, hWU, hpW, h W hW hWU⟩

/-! ### The connection -/

/-- The unit section `1` of `Ω^0_{Y/S}`. -/
abbrev formsOne (U : (T.Y.Opens)ᵒᵖ) : (relativeDifferentialForms T.toBase ((0 : ℕ) : ℤ)).val.obj U
    :=
  (relativeDifferentialFormsAlgebra T.toBase).one.eval U

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory in
/-- `F_Y ⊗ Ω^1_{Y/S} ≅ F_Y ⊗ Ω_{Y/S}`, the inverse of the degree-one generator on the second
factor. -/
def twistedFormsOneIso :
    twistedForms T.toBase (T.liftingModule F) (0 + 1) ≅
      moduleConnectionTarget T.toBase (T.liftingModule F) :=
  whiskerLeftIso (modulesOnRing (T.liftingModule F))
    (asIso (exteriorGeneratorOnRing T.toBase)).symm

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory in
theorem twistedFormsOneIso_hom_tmul (U : (T.Y.Opens)ᵒᵖ) (m : (T.liftingModule F).val.obj U)
    (a : (relativeDifferentials T.toBase).val.obj U) :
    (T.twistedFormsOneIso (F := F)).hom.val.app U (twistedTmul T.toBase (T.liftingModule F) (0 + 1)
        U m
      ((Scheme.Modules.exteriorGenerator (relativeDifferentials T.toBase)).val.app U a)) =
      connectionTmul T.toBase (T.liftingModule F) U m a := by
  refine (Stacks.PullbackTensorCoherence.whiskerLeft_tmul _ U m _).trans ?_
  exact congrArg (connectionTmul T.toBase (T.liftingModule F) U m)
    (Stacks.PullbackTensorCoherence.inv_val_app_apply (exteriorGeneratorOnRing T.toBase) U a)

/-- **The canonical connection on `F_Y`**, on local sections: the degree-zero differential of the
de Rham complex of [Stacks, Tag 07LM], restricted to `Y`, on `s = s ⊗ 1`, read in
`F_Y ⊗ Ω_{Y/S}`. -/
def connectionApp (U : (T.Y.Opens)ᵒᵖ) (s : (T.liftingModule F).val.obj U) :
    (moduleConnectionTarget T.toBase (T.liftingModule F)).val.obj U :=
  (T.twistedFormsOneIso (F := F)).hom.val.app U
    (T.twistedDifferentialApp hF 0 U (twistedTmul T.toBase (T.liftingModule F) 0 U s (T.formsOne
        U)))

/-- The unit crystalline `0`-form over `A|_W` is carried to the unit `0`-form of `Y/S`. -/
theorem formsCompRel_formsZeroOne (W : T.Y.Opens) :
    T.formsCompRel 0 W ((crysFormsZeroIso S).hom.app (op (T.crystallineThickening.restrictOpen W))
      (1 : crysFormRing S (T.crystallineThickening.restrictOpen W))) = T.formsOne (op W) := by
  have e : (crysFormsZeroIso S).hom.app (op (T.crystallineThickening.restrictOpen W))
      (1 : crysFormRing S (T.crystallineThickening.restrictOpen W)) =
      (crysFormSections S 0 (T.crystallineThickening.restrictOpen W)).symm
        (exteriorPower.ιMulti _ 0 Fin.elim0) := by
    refine (crysFormSections S 0 (T.crystallineThickening.restrictOpen W)).injective ?_
    rw [LinearEquiv.apply_symm_apply]
    refine Subtype.ext ((formsZeroOne_coe (T.crystallineThickening.restrictOpen W)).trans ?_)
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
    rfl
  rw [e, formsCompRel_ιMulti]
  rfl

/-- On the image of `F(A|_W) ⊗ Ω_{X/S}(A|_W)`, wedging with the unit form and reading the result
back in `F_Y ⊗ Ω_{Y/S}` does nothing. -/
theorem twistedFormsOneIso_wedge_formsOne (W : T.Y.Opens)
    (z : F.val.obj (op (T.crystallineThickening.restrictOpen W)) ⊗[crysFormRing S
        (T.crystallineThickening.restrictOpen W)]
      (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    (T.twistedFormsOneIso (F := F)).hom.val.app (op W)
        (twistedFormsWedgeSection T.toBase (T.liftingModule F) 0 (op W)
          (T.connectionComparison F W z) (T.formsOne (op W))) =
      T.connectionComparison F W z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    have h := twistedFormsWedgeSection_add T.toBase (T.liftingModule F) 0 (op W) 0 0
      (T.formsOne (op W))
    rw [add_zero] at h
    rw [show twistedFormsWedgeSection T.toBase (T.liftingModule F) 0 (op W) 0 (T.formsOne (op W)) =
      0 from add_eq_left.mp h.symm]
    exact map_zero _
  | tmul m α =>
    rw [connectionComparison_tmul]
    exact (congrArg ((T.twistedFormsOneIso (F := F)).hom.val.app (op W))
      ((twistedFormsWedgeSection_tmul T.toBase (T.liftingModule F) 0 (op W) m _ _).trans
        (congrArg (twistedTmul T.toBase (T.liftingModule F) (0 + 1) (op W) m)
          (relativeExteriorProduct_one T.toBase (op W) _)))).trans
      (T.twistedFormsOneIso_hom_tmul (op W) m _)
  | add z z' hz hz' =>
    rw [map_add, twistedFormsWedgeSection_add, map_add, hz, hz']

/-- **Over an affine-over-affine open the connection is the ring-level canonical connection of
[Stacks, Tag 07J6]** of the corresponding object of `Cris(X/S)`. -/
theorem connectionApp_affine {W : T.Y.Opens} (hW : IsAffineOpen W)
    [IsAffine (T.crystallineThickening.restrictOpen W).obj.thickening.target.scheme]
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V)
    (h : W ≤ T.crystallineThickening.obj.toBase.hom ⁻¹ᵁ V)
    (x : F.val.obj (op (T.crystallineThickening.restrictOpen W))) :
    T.connectionApp hF (op W) x =
      T.connectionComparison F W (AffineConnection.ringConnection
        (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV
          h).top_le_preimage_baseOpen
        (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV
          h).isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF
          (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV h))
        x) := by
  have h0 := T.twistedDifferentialApp_tmul_affine hF 0 hW hV h x
    ((crysFormsZeroIso S).hom.app (op (T.crystallineThickening.restrictOpen W))
      (1 : crysFormRing S (T.crystallineThickening.restrictOpen W)))
  rw [formsCompRel_formsZeroOne] at h0
  have hd : relativeDeRhamDifferentialSection T.toBase 0 (op W) (T.formsOne (op W)) = 0 := by
    rw [← formsCompRel_formsZeroOne, ← LinearEquiv.symm_apply_apply
      (crysFormSections S 0 (T.crystallineThickening.restrictOpen W))
      ((crysFormsZeroIso S).hom.app (op (T.crystallineThickening.restrictOpen W))
        (1 : crysFormRing S (T.crystallineThickening.restrictOpen W))),
      ← formsCompRel_deRham]
    refine Eq.trans (congrArg (fun z ↦ T.formsCompRel (0 + 1) W
      ((crysFormSections S (0 + 1) (T.crystallineThickening.restrictOpen W)).symm z))
      (differential_formsZeroOne (T.crystallineThickening.restrictOpen W))) ?_
    exact (congrArg (T.formsCompRel (0 + 1) W) (map_zero _)).trans (map_zero _)
  rw [hd] at h0
  have h1 := h0.trans ((congrArg (fun t ↦ twistedFormsWedgeSection T.toBase (T.liftingModule F) 0
      (op W) _ (T.formsOne (op W)) + t) (twistedTmul_zero T.toBase (0 + 1) (op W) (T.liftingModule
          F) x)).trans (add_zero _))
  exact (congrArg ((T.twistedFormsOneIso (F := F)).hom.val.app (op W)) h1).trans
    (T.twistedFormsOneIso_wedge_formsOne W _)

/-- The connection is additive. -/
theorem connectionApp_add (U : (T.Y.Opens)ᵒᵖ) (s s' : (T.liftingModule F).val.obj U) :
    T.connectionApp hF U (s + s') = T.connectionApp hF U s + T.connectionApp hF U s' := by
  unfold connectionApp
  rw [twistedTmul_add_left, map_add, map_add]

/-- The connection commutes with restriction. -/
theorem connectionApp_restrict {U V : (T.Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (s : (T.liftingModule F).val.obj U) :
    (moduleConnectionTarget T.toBase (T.liftingModule F)).val.map k (T.connectionApp hF U s) =
      T.connectionApp hF V ((T.liftingModule F).val.map k s) := by
  unfold connectionApp
  refine (PresheafOfModules.naturality_apply (T.twistedFormsOneIso (F := F)).hom.val k
      _).symm.trans ?_
  refine congrArg _ ((T.twistedDifferentialApp_restrict hF 0 k _).trans ?_)
  refine congrArg _ ((twistedTmul_restrict T.toBase (T.liftingModule F) 0 k s _).trans ?_)
  exact congrArg (twistedTmul T.toBase (T.liftingModule F) 0 V ((T.liftingModule F).val.map k s))
    ((relativeDifferentialFormsAlgebra T.toBase).one.2 k)

/-- `connectionComparison` is semilinear. -/
theorem connectionComparison_smul (W : T.Y.Opens)
    (r : crysFormRing S (T.crystallineThickening.restrictOpen W))
    (z : F.val.obj (op (T.crystallineThickening.restrictOpen W)) ⊗[crysFormRing S
        (T.crystallineThickening.restrictOpen W)]
      (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.connectionComparison F W (r • z) = T.sectionRingIso W r • T.connectionComparison F W z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m α =>
    rw [TensorProduct.smul_tmul', connectionComparison_tmul, connectionComparison_tmul]
    exact (congrArg (fun z ↦ connectionTmul T.toBase (T.liftingModule F) (op W) z
        (T.formsCompOneRel W α)) (crysAmbient_smul F T.crystallineThickening W r m)).trans
      (connectionTmul_smul_left _ _ _ (T.sectionRingIso W r) _ _)
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The Leibniz rule for the connection over an affine-over-affine open, from the Leibniz rule of
the ring-level connection of [Stacks, Tag 07J6]. -/
theorem connectionApp_smul_affine {W : T.Y.Opens}
    (hW : IsAffineOverAffineOpen T.crystallineThickening.obj W)
    (b : T.Y.ringCatSheaf.obj.obj (op W)) (x : (T.liftingModule F).val.obj (op W)) :
    T.connectionApp hF (op W) (b • x) =
      b • T.connectionApp hF (op W) x +
        connectionTmul T.toBase (T.liftingModule F) (op W) x
          ((universalRelativeDerivation T.toBase).d (X := op W) b) := by
  obtain ⟨hW1, V, hV, h⟩ := hW
  have : IsAffine (T.crystallineThickening.restrictOpen W).obj.thickening.target.scheme := hW1
  obtain ⟨b', rfl⟩ := (T.sectionRingIso W).surjective b
  let x' : F.val.obj (op (T.crystallineThickening.restrictOpen W)) := x
  have e : T.connectionApp hF (op W) (T.sectionRingIso W b' • x) =
      T.connectionApp hF (op W) (show (T.liftingModule F).val.obj (op W) from b' • x') :=
    congrArg (T.connectionApp hF (op W)) (crysAmbient_smul F T.crystallineThickening W b' x').symm
  refine e.trans ((T.connectionApp_affine hF hW1 hV h _).trans ?_)
  refine (congrArg (T.connectionComparison F W)
    ((AffineConnection.ringConnection
        (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW1 hV
          h).top_le_preimage_baseOpen
        (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW1 hV
          h).isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF
          (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW1 hV
              h))).leibniz
      b' x')).trans ?_
  refine (map_add _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · refine (T.connectionComparison_smul W b' _).trans ?_
    exact congrArg (T.sectionRingIso W b' • ·) (T.connectionApp_affine hF hW1 hV h x').symm
  · exact (T.connectionComparison_tmul W x' _).trans
      (congrArg (connectionTmul T.toBase (T.liftingModule F) (op W) x)
        (T.formsCompOneRel_crysD W b'))

/-- **The Leibniz rule `∇(b · s) = b · ∇(s) + s ⊗ d b` for the connection on `F_Y`.** -/
theorem connectionApp_smul (U : (T.Y.Opens)ᵒᵖ) (b : T.Y.ringCatSheaf.obj.obj U)
    (s : (T.liftingModule F).val.obj U) :
    T.connectionApp hF U (b • s) =
      b • T.connectionApp hF U s +
        connectionTmul T.toBase (T.liftingModule F) U s
          ((universalRelativeDerivation T.toBase).d (X := U) b) := by
  obtain ⟨U⟩ := U
  refine T.eq_of_forall_isAffineOverAffineOpen (moduleConnectionTarget T.toBase (T.liftingModule F))
    _ _ fun W hW hWU ↦ ?_
  let k : op U ⟶ op W := (homOfLE hWU).op
  refine (T.connectionApp_restrict hF k (b • s)).trans ?_
  refine (congrArg (T.connectionApp hF (op W))
    (PresheafOfModules.map_smul (T.liftingModule F).val k b s)).trans ?_
  refine (T.connectionApp_smul_affine hF hW _ _).trans ?_
  refine Eq.trans ?_ (map_add _ _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans ?_ (PresheafOfModules.map_smul
      (moduleConnectionTarget T.toBase (T.liftingModule F)).val k b _).symm
    exact congrArg (_ • ·) (T.connectionApp_restrict hF k s).symm
  · refine Eq.trans ?_ (connectionTmul_restrict T.toBase (T.liftingModule F) k s _).symm
    exact congrArg (connectionTmul T.toBase (T.liftingModule F) (op W) _)
      ((universalRelativeDerivation T.toBase).d_map k b)

/-- **The Leibniz rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` for the twisted differential.** -/
theorem twistedDifferentialApp_twistedTmul (q : ℕ) (U : (T.Y.Opens)ᵒᵖ)
    (s : (T.liftingModule F).val.obj U) (ω : (relativeDifferentialForms T.toBase (q : ℤ)).val.obj
        U) :
    T.twistedDifferentialApp hF q U (twistedTmul T.toBase (T.liftingModule F) q U s ω) =
      twistedFormsWedgeSection T.toBase (T.liftingModule F) q U (T.connectionApp hF U s) ω +
        twistedTmul T.toBase (T.liftingModule F) (q + 1) U s
          (relativeDeRhamDifferentialSection T.toBase q U ω) := by
  obtain ⟨U⟩ := U
  refine T.eq_of_forall_isAffineOverAffineOpen (twistedForms T.toBase (T.liftingModule F) (q + 1))
    _ _ fun W hW hWU ↦ ?_
  let k : op U ⟶ op W := (homOfLE hWU).op
  obtain ⟨ω', hω'⟩ := (T.bijective_formsCompRel q hW).2
    ((relativeDifferentialForms T.toBase (q : ℤ)).val.map k ω)
  obtain ⟨hW1, V, hV, h⟩ := hW
  have : IsAffine (T.crystallineThickening.restrictOpen W).obj.thickening.target.scheme := hW1
  refine (T.twistedDifferentialApp_restrict hF q k _).trans ?_
  refine (congrArg (T.twistedDifferentialApp hF q (op W))
    (twistedTmul_restrict T.toBase (T.liftingModule F) q k s ω)).trans ?_
  rw [← hω']
  refine (T.twistedDifferentialApp_tmul_affine hF q hW1 hV h _ ω').trans ?_
  refine Eq.trans ?_ (map_add _ _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans ?_ (twistedFormsWedgeSection_restrict T.toBase (T.liftingModule F) q k _ ω).symm
    rw [T.connectionApp_restrict hF k s]
    exact congrArg₂ (twistedFormsWedgeSection T.toBase (T.liftingModule F) q (op W))
      (T.connectionApp_affine hF hW1 hV h _).symm hω'
  · refine Eq.trans ?_ (twistedTmul_restrict T.toBase (T.liftingModule F) (q + 1) k s _).symm
    exact congrArg (twistedTmul T.toBase (T.liftingModule F) (q + 1) (op W) _)
      ((congrArg (relativeDeRhamDifferentialSection T.toBase q (op W)) hω').trans
        (relativeDeRhamDifferentialSection_restrict T.toBase q k ω).symm)

/-- The image of a local section of `f^{-1}𝒪_S` in `𝒪_Y`. -/
abbrev baseScalar (U : (T.Y.Opens)ᵒᵖ)
    (r : ((TopCat.Sheaf.pullback CommRingCat.{u} T.toBase.base).obj S.S.scheme.sheaf).obj.obj U) :
    T.Y.ringCatSheaf.obj.obj U :=
  ((inverseImageStructureMap T.toBase).hom.app U).hom r

/-- The twisted differential is linear over `f^{-1}𝒪_S` on a local pure tensor. -/
theorem twistedDifferentialApp_baseScalar_smul_twistedTmul (q : ℕ) (U : (T.Y.Opens)ᵒᵖ)
    (r : ((TopCat.Sheaf.pullback CommRingCat.{u} T.toBase.base).obj S.S.scheme.sheaf).obj.obj U)
    (s : (T.liftingModule F).val.obj U) (ω : (relativeDifferentialForms T.toBase (q : ℤ)).val.obj
        U) :
    T.twistedDifferentialApp hF q U (T.baseScalar U r • twistedTmul T.toBase (T.liftingModule F) q
        U s ω) =
      T.baseScalar U r • T.twistedDifferentialApp hF q U
        (twistedTmul T.toBase (T.liftingModule F) q U s ω) := by
  have e : T.baseScalar U r • twistedTmul T.toBase (T.liftingModule F) q U s ω =
      twistedTmul T.toBase (T.liftingModule F) q U (T.baseScalar U r • s) ω :=
    (toTensorSheafSection_smul_tmul T.Y.toRingedSpace (T.liftingModule F)
      (relativeDifferentialForms T.toBase (q : ℤ)) U _ s ω).symm
  have hd : (universalRelativeDerivation T.toBase).d (X := U) (T.baseScalar U r) = 0 :=
    (universalRelativeDerivation T.toBase).d_app r
  refine (congrArg (T.twistedDifferentialApp hF q U) e).trans ?_
  refine (T.twistedDifferentialApp_twistedTmul hF q U _ ω).trans ?_
  refine Eq.trans ?_ (congrArg (T.baseScalar U r • ·)
    (T.twistedDifferentialApp_twistedTmul hF q U s ω)).symm
  refine Eq.trans ?_ (smul_add _ _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [connectionApp_smul, hd, connectionTmul_zero, add_zero]
    exact twistedFormsWedgeSection_smul_left T.toBase (T.liftingModule F) q U _ _ ω
  · exact toTensorSheafSection_smul_tmul T.Y.toRingedSpace (T.liftingModule F)
      (relativeDifferentialForms T.toBase ((q + 1 : ℕ) : ℤ)) U _ s _

/-- `baseScalar` commutes with restriction. -/
theorem baseScalar_restrict {U V : (T.Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (r : ((TopCat.Sheaf.pullback CommRingCat.{u} T.toBase.base).obj S.S.scheme.sheaf).obj.obj U) :
    T.baseScalar V (((TopCat.Sheaf.pullback CommRingCat.{u} T.toBase.base).obj
        S.S.scheme.sheaf).obj.map k r) = (T.Y.ringCatSheaf.obj.map k).hom (T.baseScalar U r) :=
  ConcreteCategory.congr_hom ((inverseImageStructureMap T.toBase).hom.naturality k) r

/-- **The twisted differential is `f^{-1}𝒪_S`-linear.** -/
theorem twistedDifferentialApp_baseScalar_smul (q : ℕ) (U : (T.Y.Opens)ᵒᵖ)
    (r : ((TopCat.Sheaf.pullback CommRingCat.{u} T.toBase.base).obj S.S.scheme.sheaf).obj.obj U)
    (x : (twistedForms T.toBase (T.liftingModule F) q).val.obj U) :
    T.twistedDifferentialApp hF q U (T.baseScalar U r • x) =
      T.baseScalar U r • T.twistedDifferentialApp hF q U x := by
  obtain ⟨U⟩ := U
  refine @Crystalline.zariski_eq_of_generators T.Y _ _ _ _
    (isLocallySurjective_tensorSheafUnit F (A := T.crystallineThickening)
      (N := relativeDifferentialForms T.toBase (q : ℤ)))
    ((SheafOfModules.toSheaf _).obj (twistedForms T.toBase (T.liftingModule F) (q + 1))).property
    (fun V ↦ ((TopCat.Sheaf.pullback CommRingCat.{u} T.toBase.base).obj
      S.S.scheme.sheaf).obj.obj (op V))
    (fun h r ↦ (((TopCat.Sheaf.pullback CommRingCat.{u} T.toBase.base).obj
      S.S.scheme.sheaf).obj.map (homOfLE h).op).hom r)
    (fun V r (z : (twistedForms T.toBase (T.liftingModule F) q).val.obj (op V)) ↦
      T.twistedDifferentialApp hF q (op V) (T.baseScalar (op V) r • z))
    (fun V r (z : (twistedForms T.toBase (T.liftingModule F) q).val.obj (op V)) ↦
      T.baseScalar (op V) r • T.twistedDifferentialApp hF q (op V) z)
    ?_ ?_ ?_ U r x
  · intro V V' h r z
    refine (T.twistedDifferentialApp_restrict hF q (homOfLE h).op _).trans ?_
    refine congrArg (T.twistedDifferentialApp hF q (op V')) ?_
    refine (PresheafOfModules.map_smul (twistedForms T.toBase (T.liftingModule F) q).val
      (homOfLE h).op _ z).trans ?_
    exact congrArg (· • _) (T.baseScalar_restrict (homOfLE h).op r).symm
  · intro V V' h r z
    refine (PresheafOfModules.map_smul (twistedForms T.toBase (T.liftingModule F) (q + 1)).val
      (homOfLE h).op _ _).trans ?_
    exact congrArg₂ (· • ·) (T.baseScalar_restrict (homOfLE h).op r).symm
      (T.twistedDifferentialApp_restrict hF q (homOfLE h).op z)
  · intro V r p
    induction p using TensorProduct.induction_on with
    | zero =>
      refine (congrArg (fun z ↦ T.twistedDifferentialApp hF q (op V) (T.baseScalar (op V) r • z))
        (AddMonoidHom.map_zero _)).trans ?_
      refine Eq.trans ?_ (congrArg (fun z ↦ T.baseScalar (op V) r • T.twistedDifferentialApp hF q
        (op V) z) (AddMonoidHom.map_zero _)).symm
      simp only [smul_zero, map_zero]
    | tmul m ω => exact T.twistedDifferentialApp_baseScalar_smul_twistedTmul hF q (op V) r m ω
    | add p p' hp hp' =>
      refine (congrArg (fun z ↦ T.twistedDifferentialApp hF q (op V) (T.baseScalar (op V) r • z))
        (AddMonoidHom.map_add _ p p')).trans ?_
      refine Eq.trans ?_ (congrArg (fun z ↦ T.baseScalar (op V) r • T.twistedDifferentialApp hF q
        (op V) z) (AddMonoidHom.map_add _ p p')).symm
      exact ((congrArg (T.twistedDifferentialApp hF q (op V)) (smul_add _ _ _)).trans
        (map_add _ _ _)).trans ((congrArg₂ (· + ·) hp hp').trans ((smul_add _ _ _).symm.trans
          (congrArg (T.baseScalar (op V) r • ·) (map_add _ _ _).symm)))

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

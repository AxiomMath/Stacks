module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekCrystalValues

/-!
# `i_!` of a crystal is, over an affine object mapping to `Cris(X/S)`, the base change of sections

Let `ℱ` be a locally quasi-coherent crystal on the small crystalline site `Cris(X/S)`, lifted to
the module universe `u + 1` by `...SmallSite.moduleULift`, and write `i_! ℱ` for its module-level
lower shriek ([Stacks, Tag 07IJ], `...SmallSite.moduleLowerShriek`).  For an object `B` of
`CRIS(X/S)` and a morphism `τ : B ⟶ i A` to an object `A` of `Cris(X/S)`, the **restriction
along `τ`**

`lowerShriekRestrict : ℱ(A) ⟶ (i_! ℱ)(B)`

is the unit `ℱ(A) ⟶ (i_! ℱ)(i A)` of `i_! ⊣ i^{-1}` followed by the restriction map of `i_! ℱ`
along `τ`; it is semilinear over `τ^♯ : Γ(A, 𝒪) ⟶ Γ(B, 𝒪)`.  The main result,
`bijective_lowerShriekBaseChange`, says that when the ambient schemes of `A` and `B` are affine,
the induced map

`Γ(B, 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ (i_! ℱ)(B)`,  `t ⊗ s ↦ t · τ^* s`,

is bijective: `i_! ℱ` is computed near `B` by the crystal `ℱ`, as [Stacks, Tag 07Q9] uses when it
writes `ℱ'_{T'} = h^* ℱ_T` for `ℱ' = f_cris^* ℱ`.

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

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The restriction along a morphism to the small site -/

/-- **The unit `M(A) ⟶ (i_! M)(i A)` of `i_! ⊣ i^{-1}`**, on sections, with its target read as the
sections of `i_! M` over the image of `A`. -/
def lowerShriekUnitAt (M : ModuleSheaf S) (A : CrystallineThickening S) (a : M.val.obj (op A)) :
    ((moduleLowerShriek S).obj M).val.obj (op ((CrystallineThickening.ι S).obj A)) :=
  ((moduleLowerShriekAdjunction S).unit.app M).val.app (op A) a

/-- `lowerShriekUnitAt` is additive. -/
lemma lowerShriekUnitAt_add (M : ModuleSheaf S) (A : CrystallineThickening S)
    (a a' : M.val.obj (op A)) :
    lowerShriekUnitAt M A (a + a') = lowerShriekUnitAt M A a + lowerShriekUnitAt M A a' :=
  map_add _ a a'

/-- `lowerShriekUnitAt` is compatible with the scalar actions. -/
lemma lowerShriekUnitAt_smul (M : ModuleSheaf S) (A : CrystallineThickening S)
    (c : (structureSheaf S).obj.obj (op A)) (a : M.val.obj (op A)) :
    lowerShriekUnitAt M A (c • a) =
      (show crysSheafRing S ((CrystallineThickening.ι S).obj A) from c) •
        lowerShriekUnitAt M A a :=
  map_smul (((moduleLowerShriekAdjunction S).unit.app M).val.app (op A)).hom c a

/-- **The unit is natural**: for `k : A₁ ⟶ A₂` in `Cris(X/S)`, the unit at `k^* a` is the
restriction along `i k` of the unit at `a`. -/
lemma lowerShriekUnitAt_restrict (M : ModuleSheaf S) {A₁ A₂ : CrystallineThickening S}
    (k : A₁ ⟶ A₂) (a : M.val.obj (op A₂)) :
    lowerShriekUnitAt M A₁ (M.val.restrictₛₗ k.op a) =
      ((moduleLowerShriek S).obj M).val.restrictₛₗ ((CrystallineThickening.ι S).map k).op
        (lowerShriekUnitAt M A₂ a) :=
  PresheafOfModules.naturality_apply ((moduleLowerShriekAdjunction S).unit.app M).val k.op a

/-- **The restriction of `i_! M` along a morphism `τ : B ⟶ i A` to the small site**: the unit
`M(A) ⟶ (i_! M)(i A)` of `i_! ⊣ i^{-1}` followed by the restriction map of `i_! M` along `τ`. -/
def lowerShriekRestrict (M : ModuleSheaf S) {B : Thickening S} {A : CrystallineThickening S}
    (τ : B ⟶ (CrystallineThickening.ι S).obj A) (a : M.val.obj (op A)) :
    ((moduleLowerShriek S).obj M).val.obj (op B) :=
  ((moduleLowerShriek S).obj M).val.restrictₛₗ τ.op (lowerShriekUnitAt M A a)

/-- `lowerShriekRestrict` is additive. -/
lemma lowerShriekRestrict_add (M : ModuleSheaf S) {B : Thickening S}
    {A : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A)
    (a a' : M.val.obj (op A)) :
    lowerShriekRestrict M τ (a + a') = lowerShriekRestrict M τ a + lowerShriekRestrict M τ a' := by
  rw [lowerShriekRestrict, lowerShriekRestrict, lowerShriekRestrict, lowerShriekUnitAt_add,
    map_add]

/-- **The restriction along `τ` is semilinear** over `τ^♯ : Γ(A, 𝒪) ⟶ Γ(B, 𝒪)`. -/
lemma lowerShriekRestrict_smul (M : ModuleSheaf S) {B : Thickening S}
    {A : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A)
    (c : (structureSheaf S).obj.obj (op A)) (a : M.val.obj (op A)) :
    lowerShriekRestrict M τ (c • a) = crysSheafRingMap τ c • lowerShriekRestrict M τ a := by
  rw [lowerShriekRestrict, lowerShriekRestrict, lowerShriekUnitAt_smul]
  exact map_smulₛₗ (((moduleLowerShriek S).obj M).val.restrictₛₗ τ.op) c _

/-- The restriction along a composite is the restriction along the second factor, followed by the
restriction map of `i_! M` along the first. -/
lemma lowerShriekRestrict_comp (M : ModuleSheaf S) {B B' : Thickening S}
    {A : CrystallineThickening S} (g : B' ⟶ B) (τ : B ⟶ (CrystallineThickening.ι S).obj A)
    (a : M.val.obj (op A)) :
    lowerShriekRestrict M (g ≫ τ) a =
      ((moduleLowerShriek S).obj M).val.restrictₛₗ g.op (lowerShriekRestrict M τ a) := by
  rw [lowerShriekRestrict, lowerShriekRestrict, op_comp,
    PresheafOfModules.restrictₛₗ_comp_apply]

/-- **The restriction along `τ` is natural in the object of the small site**: for `k : A₁ ⟶ A₂`
in `Cris(X/S)`, restricting along `τ ≫ i k` is restricting along `τ` after `k^*`. -/
lemma lowerShriekRestrict_comp_ι (M : ModuleSheaf S) {B : Thickening S}
    {A₁ A₂ : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A₁)
    (k : A₁ ⟶ A₂) (a : M.val.obj (op A₂)) :
    lowerShriekRestrict M (τ ≫ (CrystallineThickening.ι S).map k) a =
      lowerShriekRestrict M τ (M.val.restrictₛₗ k.op a) := by
  rw [lowerShriekRestrict, lowerShriekRestrict, lowerShriekUnitAt_restrict, op_comp,
    PresheafOfModules.restrictₛₗ_comp_apply]

/-! ### The comparison on the Zariski site, on pure tensors -/

section Formula

variable (F : SheafOfModules.{u} (structureSheaf S)) {B : Thickening S}
  {A : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A)

/-- The unit of the presheaf pullback, on sections. -/
abbrev pullbackUnitAt (V : CrystallineThickening S) (a : (ulModel F).obj (op V)) :
    (lowerShriekPresheafOf F).obj (op ((CrystallineThickening.ι S).obj V)) :=
  PresheafOfModules.Hom.app ((PresheafOfModules.pullbackPushforwardAdjunction.{u + 1}
    (𝟙 ((CrystallineThickening.ι S).op ⋙ (crisCommRing S ⋙ forget₂ CommRingCat RingCat)))).unit.app
      ((moduleULift S).obj F).val) (op V) a

/-- The sheafification unit at the unit of the presheaf pullback is the unit of `i_!`. -/
lemma toSheafify_pullbackUnitAt (V : CrystallineThickening S) (a : (ulModel F).obj (op V)) :
    (toSheafify (topology S) (lowerShriekPresheafOf F).presheaf).app
        (op ((CrystallineThickening.ι S).obj V)) (pullbackUnitAt F V a) =
      lowerShriekUnitAt ((moduleULift S).obj F) V a := rfl

/-- The sheafification unit of the presheaf pullback, on sections, with its target read as the
sections of `i_!ℱ`. -/
def sheafifyAt (U : (Thickening S)ᵒᵖ) (y : (lowerShriekPresheafOf F).obj U) :
    ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.obj U :=
  (toSheafify (topology S) (lowerShriekPresheafOf F).presheaf).app U y

/-- The sheafification unit of the presheaf pullback is linear. -/
lemma sheafifyAt_smul (U : (Thickening S)ᵒᵖ) (r : crysSheafRing S U.unop)
    (y : (lowerShriekPresheafOf F).obj U) :
    sheafifyAt F U ((show (crisCommRing S ⋙ forget₂ CommRingCat RingCat).obj U from r) • y) =
      r • sheafifyAt F U y :=
  (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
    (R₀ := (crystallineStructureSheaf S).obj) (R := crystallineStructureSheaf S)
    (𝟙 (crystallineStructureSheaf S).obj)).unit.app (lowerShriekPresheafOf F)) U).hom.map_smul
      r y

/-- The sheafification unit of the presheaf pullback is natural. -/
lemma sheafifyAt_restrict {U U' : (Thickening S)ᵒᵖ} (g : U ⟶ U')
    (y : (lowerShriekPresheafOf F).obj U) :
    sheafifyAt F U' ((lowerShriekPresheafOf F).restrictₛₗ g y) =
      ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.restrictₛₗ g (sheafifyAt F U y) :=
  ConcreteCategory.congr_hom
    ((toSheafify (topology S) (lowerShriekPresheafOf F).presheaf).naturality g) y

/-- The identification of the colimit model with the presheaf pullback, on sections. -/
def modelToPullbackAt (U : (Thickening S)ᵒᵖ)
    (z : (lowerShriekModel ((moduleULift S).obj F)).obj U) : (lowerShriekPresheafOf F).obj U :=
  PresheafOfModules.Hom.app ((Stacks.PullbackColimitUnivLE.pullbackIdIso
    (CrystallineThickening.ι S) (crisCommRing S)).inv.app ((moduleULift S).obj F).val) U z

/-- `modelToPullbackAt` is compatible with the scalar actions. -/
lemma modelToPullbackAt_smul (U : (Thickening S)ᵒᵖ)
    (r : (crisCommRing S ⋙ forget₂ CommRingCat RingCat).obj U)
    (z : (lowerShriekModel ((moduleULift S).obj F)).obj U) :
    modelToPullbackAt F U (r • z) = r • modelToPullbackAt F U z :=
  LinearMap.map_smul (PresheafOfModules.Hom.app ((Stacks.PullbackColimitUnivLE.pullbackIdIso
    (CrystallineThickening.ι S) (crisCommRing S)).inv.app ((moduleULift S).obj F).val) U).hom r z

/-- `modelToPullbackAt` is compatible with restriction. -/
lemma modelToPullbackAt_restrict {U U' : (Thickening S)ᵒᵖ} (g : U ⟶ U')
    (z : (lowerShriekModel ((moduleULift S).obj F)).obj U) :
    modelToPullbackAt F U' ((lowerShriekModel ((moduleULift S).obj F)).restrictₛₗ g z) =
      (lowerShriekPresheafOf F).restrictₛₗ g (modelToPullbackAt F U z) :=
  PresheafOfModules.naturality_apply _ g z

/-- `modelToPullbackAt` on the unit. -/
lemma modelToPullbackAt_unit (V : CrystallineThickening S) (a : (ulModel F).obj (op V)) :
    modelToPullbackAt F (op ((CrystallineThickening.ι S).obj V))
        (unit (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) (op V) a) =
      pullbackUnitAt F V a :=
  pullbackIdIso_inv_unit (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) (op V) a

/-- **The comparison `tauToSheaf` on a pure tensor**: `t ⊗ s` goes to `t` times the restriction
of `s` along `τ_W`. -/
lemma tauToSheaf_app_tmul (W : B.thickening.target.scheme.Opens)
    (t : Γ(B.thickening.target.scheme, W)) (s : sectionsOver F A) :
    (tauToSheaf F τ).app (op W) (ULift.up (Stacks.PullbackModel.tmul
        (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) W).hom t s)) =
      (show crysSheafRing S (B.restrictOpen W) from (ambientRingIso W).hom.hom t) •
        lowerShriekRestrict ((moduleULift S).obj F) (B.restrictOpenHom W ≫ τ)
          (upSection F s) := by
  have h2 : germ (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk (tauIdx τ W)) ((ambientRingIso W).hom.hom t) (upSection F s) =
      (show (crisCommRing S ⋙ forget₂ CommRingCat RingCat).obj (op (B.restrictOpen W)) from
        (ambientRingIso W).hom.hom t) •
        (lowerShriekModel ((moduleULift S).obj F)).restrictₛₗ (tauIdx τ W)
          (unit (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) (op A)
            (upSection F s)) :=
    (germ_eq_smul_germ_one _ _ _ _ _).trans (congrArg (_ • ·)
      (germ_one_eq_map_unit (CrystallineThickening.ι S) (crisCommRing S)
        (tauIdx τ W) (upSection F s)))
  change sheafifyAt F _ (modelToPullbackAt F _ (germ (CrystallineThickening.ι S) (crisCommRing S)
    (ulModel F) (CostructuredArrow.mk (tauIdx τ W)) ((ambientRingIso W).hom.hom t)
      (upSection F s))) = _
  refine (congrArg (fun z ↦ sheafifyAt F _ (modelToPullbackAt F _ z)) h2).trans ?_
  refine (congrArg (sheafifyAt F _) (modelToPullbackAt_smul F _ _ _)).trans ?_
  refine (congrArg (fun z ↦ sheafifyAt F (op (B.restrictOpen W))
    ((show (crisCommRing S ⋙ forget₂ CommRingCat RingCat).obj (op (B.restrictOpen W)) from
      (ambientRingIso W).hom.hom t) • z))
    ((modelToPullbackAt_restrict F (tauIdx τ W) _).trans
      (congrArg ((lowerShriekPresheafOf F).restrictₛₗ (tauIdx τ W))
        (modelToPullbackAt_unit F A (upSection F s))))).trans ?_
  refine (sheafifyAt_smul F _ _ _).trans ?_
  exact congrArg ((show crysSheafRing S (B.restrictOpen W) from (ambientRingIso W).hom.hom t) • ·)
    (sheafifyAt_restrict F (tauIdx τ W) _)

end Formula

/-! ### The base change of sections -/

section BaseChange

variable (F : SheafOfModules.{u} (structureSheaf S)) {B : Thickening S}
  {A : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A)

/-- Over the whole ambient scheme the ring map of the base-change presheaf is `τ^♯`. -/
lemma sectionsRingHom_top (a : (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj A))) :
    (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) ⊤).hom a =
      (tauRing τ).hom a := by
  change (B.thickening.target.scheme.presheaf.map (homOfLE le_top).op).hom ((tauRing τ).hom a) = _
  rw [show (homOfLE le_top : (⊤ : B.thickening.target.scheme.Opens) ⟶ ⊤) = 𝟙 ⊤ from
    Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Over the whole ambient scheme the ring identification is the restriction map of `𝒪`. -/
lemma ambientRingIso_top (t : Γ(B.thickening.target.scheme, ⊤)) :
    (ambientRingIso (⊤ : B.thickening.target.scheme.Opens)).hom.hom t =
      crysSheafRingMap (B.restrictOpenHom ⊤) t := by
  have h := Thickening.structureSheaf_map_restrictOpenHom B ⊤
  rw [show (homOfLE le_top : (⊤ : B.thickening.target.scheme.Opens) ⟶ ⊤) = 𝟙 ⊤ from
    Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id] at h
  have h' : (crisCommRing S).map (B.restrictOpenHom ⊤).op =
      (ambientRingIso (⊤ : B.thickening.target.scheme.Opens)).hom :=
    (Iso.eq_comp_inv ((Thickening.restrictionStructureIso B).app (op ⊤))).2 h |>.trans
      (Category.id_comp _)
  exact (congrArg (fun φ ↦ φ.hom t) h').symm

/-- The bilinear datum of `lowerShriekBaseChange`. -/
def lowerShriekBaseChangeBil :
    Γ(B.thickening.target.scheme, ⊤) →+ (sectionsOver F A →+
      ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.obj (op B)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ (show crysSheafRing S B from t) •
        lowerShriekRestrict ((moduleULift S).obj F) τ (upSection F s))
      (fun s s' ↦ by
        rw [show upSection F (s + s') = upSection F s + upSection F s' from rfl,
          lowerShriekRestrict_add, smul_add]))
    (fun t t' ↦ AddMonoidHom.ext fun s ↦ add_smul (show crysSheafRing S B from t) t' _)

/-- **The base change of sections of `i_!ℱ` along `τ : B ⟶ i A`**,

`Γ(B, 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ (i_! ℱ)(B)`,  `t ⊗ s ↦ t · τ^* s`,

the tensor product being taken along `τ^♯`, as the carrier of `ModuleCat.extendScalars`. -/
def lowerShriekBaseChange :
    (ModuleCat.extendScalars (tauRing τ).hom).obj (sectionsOver F A) →+
      ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.obj (op B) :=
  TensorProduct.liftAddHom (lowerShriekBaseChangeBil F τ) (fun a t s ↦ by
    change ((show crysSheafRing S B from
        (tauRing τ).hom a * (show Γ(B.thickening.target.scheme, ⊤) from t))) •
        lowerShriekRestrict ((moduleULift S).obj F) τ (upSection F s) =
      (show crysSheafRing S B from t) •
        lowerShriekRestrict ((moduleULift S).obj F) τ
          ((show (structureSheaf S).obj.obj (op A) from a) •
            (show ((moduleULift S).obj F).val.obj (op A) from upSection F s))
    rw [lowerShriekRestrict_smul, smul_smul, mul_comm]
    rfl)

/-- `lowerShriekBaseChange` on a pure tensor. -/
lemma lowerShriekBaseChange_tmul (t : Γ(B.thickening.target.scheme, ⊤)) (s : sectionsOver F A) :
    lowerShriekBaseChange F τ (Stacks.PullbackModel.tmul (tauRing τ).hom t s) =
      (show crysSheafRing S B from t) •
        lowerShriekRestrict ((moduleULift S).obj F) τ (upSection F s) := rfl

/-- The bilinear datum of `baseChangeToPresheafTop`. -/
def baseChangeToPresheafTopBil :
    Γ(B.thickening.target.scheme, ⊤) →+ (sectionsOver F A →+ (tauPresheaf F τ).obj (op ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ Stacks.PullbackModel.tmul
        (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) ⊤).hom t s)
      (fun s s' ↦ Stacks.PullbackColimit.tmul_add _ _ _ _))
    (fun t t' ↦ AddMonoidHom.ext fun s ↦ by
      change Stacks.PullbackModel.tmul _ (t + t') s =
        Stacks.PullbackModel.tmul _ t s + Stacks.PullbackModel.tmul _ t' s
      rw [Stacks.PullbackColimit.tmul_eq_smul _ (_ + _), add_smul,
        ← Stacks.PullbackColimit.tmul_eq_smul, ← Stacks.PullbackColimit.tmul_eq_smul])

/-- The identification of the source of `lowerShriekBaseChange` with the sections of the
base-change presheaf over the whole of `T`. -/
def baseChangeToPresheafTop :
    (ModuleCat.extendScalars (tauRing τ).hom).obj (sectionsOver F A) →+
      (tauPresheaf F τ).obj (op ⊤) :=
  TensorProduct.liftAddHom (baseChangeToPresheafTopBil F τ)
    (fun a t s ↦ by
      change Stacks.PullbackModel.tmul _
          ((tauRing τ).hom a * (show Γ(B.thickening.target.scheme, ⊤) from t)) s =
        Stacks.PullbackModel.tmul _ (show Γ(B.thickening.target.scheme, ⊤) from t) (a • s)
      rw [Stacks.PullbackColimit.tmul_smul_right, sectionsRingHom_top, mul_comm])

/-- The bilinear datum of `presheafTopToBaseChange`. -/
def presheafTopToBaseChangeBil :
    Γ(B.thickening.target.scheme, ⊤) →+ (sectionsOver F A →+
      (ModuleCat.extendScalars (tauRing τ).hom).obj (sectionsOver F A)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ Stacks.PullbackModel.tmul (tauRing τ).hom t s)
      (fun s s' ↦ Stacks.PullbackColimit.tmul_add _ _ _ _))
    (fun t t' ↦ AddMonoidHom.ext fun s ↦ by
      change Stacks.PullbackModel.tmul _ (t + t') s =
        Stacks.PullbackModel.tmul _ t s + Stacks.PullbackModel.tmul _ t' s
      rw [Stacks.PullbackColimit.tmul_eq_smul _ (_ + _), add_smul,
        ← Stacks.PullbackColimit.tmul_eq_smul, ← Stacks.PullbackColimit.tmul_eq_smul])

/-- The inverse of `baseChangeToPresheafTop`. -/
def presheafTopToBaseChange :
    (tauPresheaf F τ).obj (op ⊤) →+
      (ModuleCat.extendScalars (tauRing τ).hom).obj (sectionsOver F A) :=
  TensorProduct.liftAddHom (presheafTopToBaseChangeBil F τ)
    (fun a t s ↦ by
      change Stacks.PullbackModel.tmul _
          ((Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) ⊤).hom a *
            (show Γ(B.thickening.target.scheme, ⊤) from t)) s =
        Stacks.PullbackModel.tmul _ (show Γ(B.thickening.target.scheme, ⊤) from t) (a • s)
      rw [Stacks.PullbackColimit.tmul_smul_right, sectionsRingHom_top, mul_comm])

/-- Additive maps out of a base change agree if they agree on pure tensors. -/
private theorem addMonoidHom_ext_tmul {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : ModuleCat.{u} A} {P : Type*} [AddCommMonoid P]
    {g h : (ModuleCat.extendScalars f).obj M →+ P}
    (H : ∀ (b : B) (m : M), g (Stacks.PullbackModel.tmul f b m) =
      h (Stacks.PullbackModel.tmul f b m)) : g = h := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul t s => exact H t s
  | add z z' hz hz' => exact (map_add g z z').trans ((congrArg₂ (· + ·) hz hz').trans
      (map_add h z z').symm)

/-- `baseChangeToPresheafTop` is bijective. -/
lemma bijective_baseChangeToPresheafTop : Function.Bijective (baseChangeToPresheafTop F τ) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨presheafTopToBaseChange F τ, fun z ↦ ?_, fun z ↦ ?_⟩
  · exact DFunLike.congr_fun (addMonoidHom_ext_tmul (g := (presheafTopToBaseChange F τ).comp
      (baseChangeToPresheafTop F τ)) (h := AddMonoidHom.id _) (tauRing τ).hom fun t s ↦ rfl) z
  · exact DFunLike.congr_fun (addMonoidHom_ext_tmul
      (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) ⊤).hom
      (g := (baseChangeToPresheafTop F τ).comp (presheafTopToBaseChange F τ))
      (h := AddMonoidHom.id _) fun t s ↦ rfl) z

/-- **The base change of sections, restricted to the whole of `T`, is the comparison
`tauToSheaf` on global sections.** -/
lemma restrict_lowerShriekBaseChange
    (z : (ModuleCat.extendScalars (tauRing τ).hom).obj (sectionsOver F A)) :
    ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.restrictₛₗ
        (B.restrictOpenHom ⊤).op (lowerShriekBaseChange F τ z) =
      (tauToSheaf F τ).app (op ⊤) (ULift.up (baseChangeToPresheafTop F τ z)) := by
  let K₁ := (((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.restrictₛₗ
    (B.restrictOpenHom ⊤).op).toAddMonoidHom.comp (lowerShriekBaseChange F τ)
  let K₂ := ((tauToSheaf F τ).app (op ⊤)).hom.comp
    (AddEquiv.ulift.symm.toAddMonoidHom.comp (baseChangeToPresheafTop F τ))
  refine DFunLike.congr_fun (addMonoidHom_ext_tmul (tauRing τ).hom (g := K₁) (h := K₂)
    fun t s ↦ ?_) z
  change ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.restrictₛₗ
      (B.restrictOpenHom ⊤).op ((show crysSheafRing S B from t) •
        lowerShriekRestrict ((moduleULift S).obj F) τ (upSection F s)) =
    (tauToSheaf F τ).app (op ⊤) (ULift.up (Stacks.PullbackModel.tmul
      (Stacks.AlgebraicGeometry.BaseChangePresheaf.sectionsRingHom (tauRing τ) ⊤).hom t s))
  refine ((((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.restrictₛₗ
    (B.restrictOpenHom ⊤).op).map_smulₛₗ _ _).trans ?_
  refine Eq.trans ?_ (tauToSheaf_app_tmul F τ ⊤ t s).symm
  exact congrArg₂ (fun (a : crysSheafRing S (B.restrictOpen ⊤))
      (y : ((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.obj
        (op (B.restrictOpen ⊤))) ↦ a • y)
    (ambientRingIso_top t).symm (lowerShriekRestrict_comp _ _ τ _).symm

variable [IsAffine A.obj.thickening.target.scheme] [IsAffine B.thickening.target.scheme]
  (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F)

include hF hcrys in
/-- **The sections of `i_!` of a locally quasi-coherent crystal over an affine object mapping to
an affine object of `Cris(X/S)` are the base change of the sections of the crystal**: for
`τ : B ⟶ i A` with the ambient schemes of `A` and `B` affine, the map

`Γ(B, 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ (i_! ℱ)(B)`,  `t ⊗ s ↦ t · τ^* s`,

is bijective. -/
theorem bijective_lowerShriekBaseChange : Function.Bijective (lowerShriekBaseChange F τ) := by
  have := Thickening.isIso_restrictOpenHom_top B
  have hρ : Function.Bijective (((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.restrictₛₗ
      (B.restrictOpenHom ⊤).op) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨((moduleLowerShriek S).obj
      ((moduleULift S).obj F)).val.restrictₛₗ (inv (B.restrictOpenHom ⊤)).op, fun y ↦ ?_,
        fun y ↦ ?_⟩
    · rw [← PresheafOfModules.restrictₛₗ_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
        PresheafOfModules.restrictₛₗ_id_apply]
    · rw [← PresheafOfModules.restrictₛₗ_comp_apply, ← op_comp, IsIso.hom_inv_id, op_id,
        PresheafOfModules.restrictₛₗ_id_apply]
  have hcomp : Function.Bijective ((ConcreteCategory.hom ((tauToSheaf F τ).app (op ⊤))) ∘
      ULift.up ∘ baseChangeToPresheafTop F τ) :=
    (bijective_tauToSheaf_app_top F τ hF hcrys).comp
      (ULift.up_bijective.comp (bijective_baseChangeToPresheafTop F τ))
  refine (hρ.of_comp_iff' _).1 ?_
  have he : (((moduleLowerShriek S).obj ((moduleULift S).obj F)).val.restrictₛₗ
      (B.restrictOpenHom ⊤).op) ∘ (lowerShriekBaseChange F τ) =
      (ConcreteCategory.hom ((tauToSheaf F τ).app (op ⊤))) ∘ ULift.up ∘
        baseChangeToPresheafTop F τ :=
    funext fun z ↦ restrict_lowerShriekBaseChange F τ z
  rw [he]
  exact hcomp

end BaseChange

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

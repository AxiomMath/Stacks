module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalIntegrableConnectionCris
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnectionComparison

/-!
# The de Rham complex of [Stacks, Tag 07LM] is built from the connection of [Stacks, Tag 07J6]

Fix a global crystalline situation of [Stacks, Tag 07MF] and a crystal `F` in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`.  Two constructions of the library produce morphisms of abelian
sheaves out of `F ⊗ Ω^i_{X/S}`:

* the canonical connection `∇ = ...SmallSite.crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}` of
  [Stacks, Lemma 60.15.1, Tag 07J6], defined for every crystal on each object `T` as
  `s ↦ p₁^* s - p₀^* s` on the first-order thickening `T'`, together with its extension
  `...SmallSite.crystalExtensionCris : F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}` by the rule of
  [Stacks, Tag 07I0];
* the differentials `...SmallSite.crystalDeRhamDifferential hF i` of the de Rham complex of
  [Stacks, Proposition 60.23.1, Tag 07LM], assembled from the ring-level connection
  `...SmallSite.AffineConnection.ringConnection` over the affine-over-affine objects and its
  extensions.

This module proves that they agree: the degree-zero differential of the de Rham complex is the
canonical connection, read through `F ⊗ Ω^0_{X/S} = F`, and the degree-one differential is its
extension.

## Main results

* `crystalDeRhamDifferential_zero_eq` — `d⁰ = ∇` after `F ⊗ Ω^0_{X/S} = F`.
* `crystalConnectionCris_eq_crystalDeRhamDifferential_zero` — the same, read the other way.
* `crystalDeRhamDifferential_one_eq` — `d¹` is the extension `crystalExtensionCris` of `∇`.
* `crystalConnectionCrisApp_eq_ringConnection` — over an object with affine ambient scheme the
  canonical connection is the ring-level connection of the sections: both are read back in
  `F(T')` to `p₁^* s - p₀^* s`, and the reading-back map is injective.

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Proposition 60.23.1, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] moduleCrysFormRingSections

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}

/-- Two additive maps out of a tensor product agreeing on pure tensors are equal. -/
private theorem tensor_addMonoidHom_apply_eq {R M N P : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] (f g : M ⊗[R] N →+ P)
    (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) (w : M ⊗[R] N) : f w = g w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul m n => exact h m n

/-! ### Over an object with affine ambient scheme -/

/-- The ring maps of `𝒪_{X/S}` along a morphism `g`, read on the ambient schemes. -/
theorem sectionRingEquiv_crysSheafRingMap {A C : CrystallineThickening S} (g : C ⟶ A)
    (b : crysSheafRing S A.obj) :
    sectionRingEquiv C (g.hom.targetHom.hom ⁻¹ᵁ ⊤)
        (crysSheafRingMap (C.restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ ⊤)).hom
          (crysSheafRingMap g.hom b)) =
      (g.hom.targetHom.hom.app ⊤).hom
        (sectionRingEquiv A ⊤ (crysSheafRingMap (A.restrictOpenHom ⊤).hom b)) := by
  have e : crysSheafRingMap (C.restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ ⊤)).hom
        (crysSheafRingMap g.hom b) =
      crysSheafRingMap (CrystallineThickening.restrictOpenMap g ⊤).hom
        (crysSheafRingMap (A.restrictOpenHom ⊤).hom b) := by
    rw [crysSheafRingMap_comp, crysSheafRingMap_comp]
    exact congrArg (fun k : C.restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ ⊤) ⟶ A ↦
      crysSheafRingMap k.hom b) (CrystallineThickening.restrictOpenMap_restrictOpenHom g ⊤).symm
  rw [e]
  exact openTopResInv_appTop_restrictOpenMap g ⊤ _

/-- The sections of `F ⊗ Ω_{X/S}` over an object `B`, read on the whole of the ambient scheme in
`F_T ⊗ Ω_{T/S,δ}` and then in `F_{T'}` through the canonical morphism of [Stacks, Tag 07J6]. -/
def tensorFormsReadTop (B : CrystallineThickening S) :
    F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentialForms S 1).obj (op B) →+
      FirstOrderSec F B ⊤ :=
  ((firstOrderTensorInclusion F B).val.app (op ⊤)).hom.toAddMonoidHom.comp
    (AddEquiv.ulift.toAddMonoidHom.comp
      (((tensorFormsAmbientIsoOne (F := F) B).hom.app (op ⊤)).hom.comp
        (((tensorDifferentialFormsSheaf F 1).obj.map (B.restrictOpenHom ⊤).op).hom.comp
          (((CategoryTheory.toSheafify (smallTopology S)
            (tensorDifferentialFormsPresheaf F 1)).app (op B)).hom.comp
            AddEquiv.ulift.symm.toAddMonoidHom))))

/-- `tensorFormsReadTop` on a section. -/
theorem tensorFormsReadTop_apply (B : CrystallineThickening S)
    (y : F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentialForms S 1).obj (op B)) :
    tensorFormsReadTop B y = firstOrderTensorSec F B ⊤
      ((tensorFormsAmbientIsoOne B).hom.app (op ⊤)
        ((tensorDifferentialFormsSheaf F 1).obj.map (B.restrictOpenHom ⊤).op
          ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
            (op B) (ULift.up y)))).down := rfl

/-- `F(B) ⊗ Ω_{X/S}(B) ⟶ F(B) ⊗ Ω^1_{X/S}(B)`, `m ⊗ η ↦ m ⊗ η`. -/
def formsOneTensor (B : CrystallineThickening S) :
    F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentials S).obj (op B) →+
      F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentialForms S 1).obj (op B) :=
  (TensorProduct.map LinearMap.id ((crysFormsOneGen S).app (op B)).hom).toAddMonoidHom

/-- `formsOneTensor` on a pure tensor. -/
theorem formsOneTensor_tmul (B : CrystallineThickening S) (m : F.val.obj (op B))
    (η : (crysDifferentials S).obj (op B)) :
    formsOneTensor B (m ⊗ₜ η) = formsTmul F m ((crysFormsOneGen S).app (op B) η) := rfl

section Affine

variable {B : CrystallineThickening S} [IsAffine B.obj.thickening.target.scheme]
  {V : S.S.scheme.Opens} (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V)
  (hV : IsAffineOpen V)

omit [IsAffine B.obj.thickening.target.scheme] in
/-- Through `F_T ⊗ Ω_{T/S,δ}`, the section `m ⊗ d b` is read in `F(T')` as
`(p₁(b) - p₀(b)) · p₀^* m`. -/
theorem tensorFormsReadTop_tmul_crysD_eq_smul (m : F.val.obj (op B)) (b : crysFormRing S B) :
    tensorFormsReadTop B (formsOneTensor B (m ⊗ₜ crysD S B b)) =
      (firstOrderP₁Scalar B ⊤ (sectionRingEquiv B ⊤
          ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map (B.restrictOpenHom ⊤).op b)) -
        firstOrderP₀Scalar B ⊤ (sectionRingEquiv B ⊤
          ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map (B.restrictOpenHom ⊤).op b))) •
        firstOrderP₀Sec F B ⊤ (F.val.map (B.restrictOpenHom ⊤).op m) := by
  let ι := B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)
  let R := structurePresheaf S ⋙ forget₂ CommRingCat RingCat
  let β := sectionRingEquiv B ⊤ (R.map ι.op b)
  let y : FirstOrderSec F B ⊤ := firstOrderP₀Sec F B ⊤ (F.val.map ι.op m)
  rw [tensorFormsReadTop_apply, formsOneTensor_tmul,
    tensorFormsAmbientIsoOne_hom_restrict_toSheafify]
  have e1 : (crysDifferentialForms S 1).map ι.op ((crysFormsOneGen S).app (op B) (crysD S B b)) =
      formsD (B.restrictOpen ⊤) (R.map ι.op b) := formsD_map ι b
  rw [e1, formsCompOne_formsD]
  refine (firstOrderTensorSec_tmul F B ⊤
    (F.val.map ι.op m : (crysAmbientSchemeModules F B).val.obj (op ⊤)) _).trans ?_
  exact congrArg (· • y) (eq_sub_of_add_eq' (firstOrderP₁Scalar_eq B ⊤ β).symm)

/-- **The two readings of `F(B) ⊗ Ω_{X/S}(B)` in `F(T')` agree on `m ⊗ d b`**: through
`F_T ⊗ Ω_{T/S,δ}` it is `(p₁(b) - p₀(b)) · p₀^* m`, and so it is through the canonical map
`...SmallSite.AffineConnection.readBack` of the ring-level connection. -/
theorem tensorFormsReadTop_tmul_crysD (m : F.val.obj (op B)) (b : crysFormRing S B) :
    tensorFormsReadTop B (formsOneTensor B (m ⊗ₜ crysD S B b)) =
      crysSiteRestrict F ((firstOrderThickeningCrysObject S B).restrictOpenHom ⊤)
        (AffineConnection.readBack F hVB hV (m ⊗ₜ crysD S B b)) := by
  let ι := B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)
  let T' := firstOrderThickeningCrysObject S B
  let R := structurePresheaf S ⋙ forget₂ CommRingCat RingCat
  let β := sectionRingEquiv B ⊤ (R.map ι.op b)
  let y : FirstOrderSec F B ⊤ := firstOrderP₀Sec F B ⊤ (F.val.map ι.op m)
  refine (tensorFormsReadTop_tmul_crysD_eq_smul m b).trans ?_
  have h1 := AffineConnection.readBack_tmul_smul_crysD hVB hV m 1 b
  rw [one_smul] at h1
  let r := crysSheafRingMap (firstOrderThickeningSiteP₁ S B.obj) b -
    crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) b
  have h2 := crysSiteRestrict_smul F (T'.restrictOpenHom ⊤) r
    (crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) m)
  have h3 : crysSiteRestrict F (T'.restrictOpenHom ⊤)
      (crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) m) = y :=
    (AffineConnection.crysSiteRestrict_restrictOpenMap_top _ m).symm
  rw [h3] at h2
  have h1' : AffineConnection.readBack F hVB hV (m ⊗ₜ crysD S B b) =
      r • crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) m :=
    h1.trans (congrArg (· • crysSiteRestrict F (firstOrderThickeningCrysP₀ S B) m)
      ((congrArg (· * r) (map_one _)).trans (one_mul r)))
  refine Eq.trans ?_ (congrArg (crysSiteRestrict F (T'.restrictOpenHom ⊤)) h1').symm
  refine Eq.trans ?_ h2.symm
  refine Eq.trans ?_ (crysAmbient_smul F T' ⊤ _ y).symm
  refine congrArg (· • y) ?_
  have hP₁ : firstOrderP₁Scalar B ⊤ β = sectionRingEquiv T' ⊤
      (crysSheafRingMap (T'.restrictOpenHom ⊤).hom
        (crysSheafRingMap (firstOrderThickeningSiteP₁ S B.obj) b)) :=
    (sectionRingEquiv_crysSheafRingMap (firstOrderThickeningCrysP₁ S B) b).symm
  have hP₀ : firstOrderP₀Scalar B ⊤ β = sectionRingEquiv T' ⊤
      (crysSheafRingMap (T'.restrictOpenHom ⊤).hom
        (crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) b)) :=
    (sectionRingEquiv_crysSheafRingMap (firstOrderThickeningCrysP₀ S B) b).symm
  have hr : crysSheafRingMap (T'.restrictOpenHom ⊤).hom r =
      crysSheafRingMap (T'.restrictOpenHom ⊤).hom
          (crysSheafRingMap (firstOrderThickeningSiteP₁ S B.obj) b) -
        crysSheafRingMap (T'.restrictOpenHom ⊤).hom
          (crysSheafRingMap (firstOrderThickeningSiteP₀ S B.obj) b) :=
    map_sub _ _ _
  rw [hr]
  refine Eq.trans ?_ (map_sub (sectionRingEquiv T' ⊤) _ _).symm
  exact congrArg₂ (fun a c : FirstOrderRing B ⊤ ↦ a - c) hP₁ hP₀

/-- **The two readings of `F(B) ⊗ Ω_{X/S}(B)` in `F(T')` agree**, the sections `d b` spanning
`Ω_{X/S}(B)`. -/
theorem tensorFormsReadTop_formsOneTensor
    (w : F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentials S).obj (op B)) :
    tensorFormsReadTop B (formsOneTensor B w) =
      crysSiteRestrict F ((firstOrderThickeningCrysObject S B).restrictOpenHom ⊤)
        (AffineConnection.readBack F hVB hV w) := by
  let ρ : F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentials S).obj (op B) →+
      FirstOrderSec F B ⊤ :=
    (F.val.map ((firstOrderThickeningCrysObject S B).restrictOpenHom ⊤).op).hom.toAddMonoidHom.comp
      (AffineConnection.readBack F hVB hV)
  show ((tensorFormsReadTop B).comp (formsOneTensor B)) w = ρ w
  refine tensor_addMonoidHom_apply_eq _ _ (fun m η ↦ ?_) w
  revert m
  refine Submodule.span_induction (p := fun (η : (GlobalCrystallineSituation.crysDifferentials
      S).obj (op B.obj)) _ ↦ ∀ m : F.val.obj (op B),
        ((tensorFormsReadTop B).comp (formsOneTensor B))
          (m ⊗ₜ @id ((crysDifferentials S).obj (op B)) η) =
        ρ (m ⊗ₜ @id ((crysDifferentials S).obj (op B)) η))
    ?_ ?_ ?_ ?_ (Submodule.eq_top_iff'.mp (crysD_span S B.obj) η)
  · rintro _ ⟨b, rfl⟩ m
    exact tensorFormsReadTop_tmul_crysD hVB hV m b
  · intro m
    have e : m ⊗ₜ[crysFormRing S B] (0 : (crysDifferentials S).obj (op B)) = 0 :=
      TensorProduct.tmul_zero _ m
    exact (congrArg ((tensorFormsReadTop B).comp (formsOneTensor B)) e).trans
      (((map_zero _).trans (map_zero _).symm).trans (congrArg ρ e).symm)
  · intro x y _ _ hx hy m
    have e : m ⊗ₜ[crysFormRing S B] @id ((crysDifferentials S).obj (op B)) (x + y) =
        m ⊗ₜ @id ((crysDifferentials S).obj (op B)) x +
          m ⊗ₜ @id ((crysDifferentials S).obj (op B)) y :=
      TensorProduct.tmul_add m (@id ((crysDifferentials S).obj (op B)) x) (id y)
    exact (congrArg ((tensorFormsReadTop B).comp (formsOneTensor B)) e).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) (hx m) (hy m)).trans
        ((map_add _ _ _).symm.trans (congrArg ρ e).symm)))
  · intro c x _ hx m
    have e : m ⊗ₜ[crysFormRing S B] @id ((crysDifferentials S).obj (op B)) (c • x) =
        (c • m) ⊗ₜ @id ((crysDifferentials S).obj (op B)) x :=
      (TensorProduct.smul_tmul (show crysFormRing S B from c) m
        (@id ((crysDifferentials S).obj (op B)) x)).symm
    exact (congrArg ((tensorFormsReadTop B).comp (formsOneTensor B)) e).trans
      ((hx (c • m)).trans (congrArg ρ e).symm)

/-- **Over an object with affine ambient scheme, the canonical connection on `Cris(X/S)` is the
ring-level connection** `...SmallSite.AffineConnection.ringConnection` of the sections. -/
theorem crystalConnectionCrisApp_eq_ringConnection (hC : IsSheafCrystal F)
    (he : Function.Bijective (crysExtensionSectionsMap F B)) (s : F.val.obj (op B)) :
    crystalConnectionCrisApp hC B (ULift.up s) =
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app (op B)
        (ULift.up (formsOneTensor B (AffineConnection.ringConnection hVB hV he s))) := by
  let ι := B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)
  let Ψ := tensorFormsAmbientIsoOne (F := F) B
  let G := (tensorDifferentialFormsSheaf F 1).obj
  let Y := formsOneTensor B (AffineConnection.ringConnection hVB hV he s)
  let η := CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)
  have hL : firstOrderTensorSec F B ⊤ (Ψ.hom.app (op ⊤)
      (G.map ι.op (crystalConnectionCrisApp hC B (ULift.up s)))).down =
      crysSiteRestrict F ((firstOrderThickeningCrysObject S B).restrictOpenHom ⊤)
        (AffineConnection.connectionDifference F B s) := by
    have a1 := congrArg (fun q ↦ firstOrderTensorSec F B ⊤ q.down)
      (tensorFormsAmbientIsoOne_hom_restrict_crystalConnectionCrisApp hC B (ULift.up s))
    exact a1.trans ((AffineConnection.firstOrderTensorInclusion_crystalConnection_top hC he
      s).trans (congrArg _ (AffineConnection.diffAction_connection he s)))
  have hR : firstOrderTensorSec F B ⊤
      (Ψ.hom.app (op ⊤) (G.map ι.op (η.app (op B) (ULift.up Y)))).down =
      crysSiteRestrict F ((firstOrderThickeningCrysObject S B).restrictOpenHom ⊤)
        (AffineConnection.connectionDifference F B s) := by
    have b1 := tensorFormsReadTop_formsOneTensor hVB hV
      (AffineConnection.ringConnection hVB hV he s)
    rwa [AffineConnection.readBack_ringConnection hVB hV he s] at b1
  have h2 : (Ψ.hom.app (op ⊤) (G.map ι.op (crystalConnectionCrisApp hC B (ULift.up s)))).down =
      (Ψ.hom.app (op ⊤) (G.map ι.op (η.app (op B) (ULift.up Y)))).down :=
    injective_firstOrderTensorInclusion F B hC ⊤ (hL.trans hR.symm)
  have hΨ : ∀ z, Ψ.inv.app (op ⊤) (Ψ.hom.app (op ⊤) z) = z := fun z ↦
    ConcreteCategory.congr_hom (NatTrans.congr_app Ψ.hom_inv_id (op ⊤)) z
  have h4 : G.map ι.op (crystalConnectionCrisApp hC B (ULift.up s)) =
      G.map ι.op (η.app (op B) (ULift.up Y)) :=
    (hΨ _).symm.trans ((congrArg (Ψ.inv.app (op ⊤)) (ULift.ext h2)).trans (hΨ _))
  exact injective_restrictTop G B h4

end Affine

/-! ### The degree-zero and degree-one forms -/

/-- The unit section `1 ∈ Ω^0_{X/S}(B) = 𝒪_{X/S}(B)`, read in the zeroth exterior power. -/
abbrev formsZeroOne (B : CrystallineThickening S) :
    ⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^0
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :=
  crysFormSections S 0 B ((crysFormsZeroIso S).hom.app (op B) (1 : crysFormRing S B))

/-- The unit section is `1` of the exterior algebra. -/
theorem formsZeroOne_coe (B : CrystallineThickening S) :
    (formsZeroOne B : ExteriorAlgebra (GlobalCrystallineSituation.crysFormRing S B.obj)
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))) = 1 :=
  map_one (algebraMap (GlobalCrystallineSituation.crysFormRing S B.obj)
    (ExteriorAlgebra (GlobalCrystallineSituation.crysFormRing S B.obj)
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))))

/-- The section `s` of `F` is `s ⊗ 1` in `F ⊗ Ω^0_{X/S}`. -/
theorem tensorFormsSectionsEquiv_zeroIso_inv (B : CrystallineThickening S) (s : F.val.obj (op B)) :
    tensorFormsSectionsEquiv F 0 B ((tensorDifferentialFormsZeroIso (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))).inv.app (op B) s) =
      s ⊗ₜ formsZeroOne B := rfl

/-- `d 1 = 0`. -/
theorem differential_formsZeroOne (B : CrystallineThickening S) :
    (GlobalCrystallineSituation.crysDeRhamComplex S).differential 0 B.obj (formsZeroOne B) = 0 := by
  have e : (![1] : Fin 1 → crysFormRing S B) 0 • exteriorPower.ιMulti (crysFormRing S B) 0
      (fun j ↦ crysD S B ((![1] : Fin 1 → crysFormRing S B) j.succ)) =
      @id (⋀[crysFormRing S B]^0 ((crysDifferentials S).obj (op B))) (formsZeroOne B) := by
    apply Subtype.ext
    refine Eq.trans ?_ (formsZeroOne_coe B).symm
    show (1 : crysFormRing S B) • ((exteriorPower.ιMulti (crysFormRing S B) 0 _ :
      ⋀[crysFormRing S B]^0 ((crysDifferentials S).obj (op B))) :
        ExteriorAlgebra (crysFormRing S B) ((crysDifferentials S).obj (op B))) = 1
    rw [one_smul, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_zero,
      List.prod_nil]
  refine (congrArg (crysDeRhamDifferential S 0 B) e.symm).trans
    ((crysDeRhamDifferential_generator S 0 B ![1]).trans ?_)
  refine AlternatingMap.map_coord_zero _ 0 ?_
  have h0 := (crysDifferentialsD S B.obj).d_map 1
  rwa [map_one] at h0

/-- `η ∧ 1 = η`. -/
theorem crysFormSections_symm_leftWedge_formsZeroOne (B : CrystallineThickening S)
    (η : (GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :
    (crysFormSections S 1 B).symm (@id (⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^1
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)))
        (leftWedge 0 η (formsZeroOne B))) =
      (crysFormsOneGen S).app (op B) η := by
  apply crysFormVal_injective
  refine (leftWedge_coe 0 η (formsZeroOne B)).trans ?_
  rw [formsZeroOne_coe, mul_one]
  rfl

/-- A degree-one form, read in the exterior algebra, is its degree-one identification. -/
theorem crysFormVal_formsOne (B : CrystallineThickening S)
    (ω : (crysDifferentialForms S 1).obj (op B)) :
    crysFormVal S ω = ExteriorAlgebra.ι (crysFormRing S B) (formsOneEquiv B ω) := by
  obtain ⟨y, rfl⟩ : ∃ y, (crysFormsOneGen S).app (op B) y = ω :=
    ⟨formsOneEquiv B ω, (crysFormsOneApp_symm_eq_oneGen S B.obj _).symm.trans
      ((formsOneEquiv B).symm_apply_apply ω)⟩
  exact congrArg (ExteriorAlgebra.ι (crysFormRing S B)) (crysFormsOneApp_oneGen S B.obj y).symm

/-- The exterior product `η ∧ ω` of the ring-level extension is `formsWedgeOne`. -/
theorem crysFormSections_symm_leftWedge_one (B : CrystallineThickening S)
    (η : (GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj))
    (ω : (crysDifferentialForms S 1).obj (op B)) :
    (crysFormSections S 2 B).symm (@id (⋀[GlobalCrystallineSituation.crysFormRing S B.obj]^(1 + 1)
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)))
        (leftWedge 1 η (crysFormSections S 1 B ω))) =
      formsWedgeOne ((crysFormsOneGen S).app (op B) η) ω := by
  apply crysFormVal_injective
  show ExteriorAlgebra.ι (crysFormRing S B) (@id ((crysDifferentials S).obj (op B)) η) *
      crysFormVal S ω =
    ExteriorAlgebra.ι (crysFormRing S B) (formsOneEquiv B ((crysFormsOneGen S).app (op B) η)) *
      ExteriorAlgebra.ι (crysFormRing S B) (formsOneEquiv B ω)
  rw [crysFormVal_formsOne B ω]
  exact congrArg (fun z ↦ ExteriorAlgebra.ι (crysFormRing S B) z *
    ExteriorAlgebra.ι (crysFormRing S B) (formsOneEquiv B ω))
    (crysFormsOneApp_oneGen S B.obj η).symm

/-- The map from the sections of the presheaf `F ⊗ Ω^i_{X/S}` to those of its sheafification. -/
private def toSheafifyAddHom (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
    (B : CrystallineThickening S) :
    ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op B)) →+
        (tensorDifferentialFormsSheaf F i).obj.obj (op B) :=
  ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
    (op B)).hom.comp AddEquiv.ulift.symm.toAddMonoidHom

/-- The exterior product with a one-form on the image of `formsOneTensor`. -/
theorem crystalWedgeCrisApp_formsOneTensor (B : CrystallineThickening S)
    (ω : (crysDifferentialForms S 1).obj (op B))
    (w : F.val.obj (op B) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj]
      (GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)) :
    crystalWedgeCrisApp F B ω ((CategoryTheory.toSheafify (smallTopology S)
        (tensorDifferentialFormsPresheaf F 1)).app (op B) (ULift.up (formsOneTensor B w))) =
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
        (op B) (ULift.up ((tensorFormsSectionsEquiv F 2 B).symm
          (TensorProduct.map LinearMap.id ((leftWedge (B := GlobalCrystallineSituation.crysFormRing
            S B.obj) (Omega := ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)))
              1).flip (crysFormSections S 1 B ω)) w))) := by
  refine tensor_addMonoidHom_apply_eq
    ((crystalWedgeCrisApp F B ω).hom.comp ((toSheafifyAddHom F 1 B).comp (formsOneTensor B)))
    ((toSheafifyAddHom F 2 B).comp ((tensorFormsSectionsEquiv F 2 B).symm.toAddMonoidHom.comp
      (TensorProduct.map LinearMap.id ((leftWedge (B := GlobalCrystallineSituation.crysFormRing
        S B.obj) (Omega := ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj)))
          1).flip (crysFormSections S 1 B ω))).toAddMonoidHom))
    (fun m η ↦ ?_) w
  refine (crystalWedgeCrisApp_toSheafify B ω m _).trans ?_
  exact congrArg (fun z ↦ toSheafifyAddHom F 2 B (formsTmul F m z))
    (crysFormSections_symm_leftWedge_one B η ω).symm

section QC

open AffineOverAffineCrystallineThickening

variable (hF : F.IsQuasicoherentOnSite)

/-- **The degree-zero differential over an affine-over-affine object is the ring-level
connection**: `d(s ⊗ 1) = ∇(s) ∧ 1 + s ⊗ d 1 = ∇(s)`. -/
theorem affineDeRhamDifferential_zero (B : AffineOverAffineCrystallineThickening S)
    (s : F.val.obj (op B.obj)) :
    affineDeRhamDifferential hF 0 B ((tensorDifferentialFormsZeroIso
        (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))).inv.app
          (op B.obj) s) =
      formsOneTensor B.obj (AffineConnection.ringConnection B.top_le_preimage_baseOpen
        B.isAffineOpen_baseOpen (bijective_crysExtensionSectionsMap_affine hF B) s) := by
  apply (tensorFormsSectionsEquiv F 1 B.obj).injective
  refine (tensorFormsSectionsEquiv_affineDeRhamDifferential hF 0 B _).trans ?_
  rw [tensorFormsSectionsEquiv_zeroIso_inv, AffineConnection.extDiff_tmul,
    differential_formsZeroOne, TensorProduct.tmul_zero, add_zero]
  generalize AffineConnection.ringConnection B.top_le_preimage_baseOpen
    B.isAffineOpen_baseOpen (bijective_crysExtensionSectionsMap_affine hF B) s = w
  refine tensor_addMonoidHom_apply_eq
    (TensorProduct.map LinearMap.id ((leftWedge 0).flip (formsZeroOne B.obj))).toAddMonoidHom
    ((tensorFormsSectionsEquiv F 1 B.obj).toAddMonoidHom.comp (formsOneTensor B.obj))
    (fun m η ↦ ?_) w
  refine congrArg (m ⊗ₜ ·) ?_
  exact ((crysFormSections S 1 B.obj).apply_symm_apply _).symm.trans
    (congrArg (crysFormSections S 1 B.obj)
      (crysFormSections_symm_leftWedge_formsZeroOne B.obj η))

omit hF in
variable (F) in
/-- The identification `F ⊗ Ω^0_{X/S} = F` on the image of a presheaf section. -/
theorem toSheafify_tensorDifferentialFormsSheafZeroIso_hom :
    CategoryTheory.toSheafify (smallTopology S) (tensorFormsULift F 0) ≫
        (tensorDifferentialFormsSheafZeroIso S F).hom.hom =
      Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (tensorDifferentialFormsZeroIso
        (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))).hom)
        AddCommGrpCat.uliftFunctor.{u + 1, u} := by
  have h1 : (tensorDifferentialFormsSheafZeroIso S F).hom.hom =
      sheafifyMap (smallTopology S) (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map
        (tensorDifferentialFormsZeroIso (F.val : PresheafOfModules.{u}
          (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))).hom)
        AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
      (isoSheafify (smallTopology S) (abelianSheaf F).property).inv := by
    show _ ≫ (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).map
      ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).preimage _) = _
    rw [Functor.map_preimage]
    rfl
  have h2 : CategoryTheory.toSheafify (smallTopology S) (abelianSheaf F).obj ≫
      (isoSheafify (smallTopology S) (abelianSheaf F).property).inv = 𝟙 _ :=
    (isoSheafify (smallTopology S) (abelianSheaf F).property).hom_inv_id
  refine (congrArg (CategoryTheory.toSheafify (smallTopology S) (tensorFormsULift F 0) ≫ ·)
    h1).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ (isoSheafify (smallTopology S) (abelianSheaf F).property).inv)
    (toSheafify_naturality (smallTopology S) (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map (tensorDifferentialFormsZeroIso
        (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))).hom)
      AddCommGrpCat.uliftFunctor.{u + 1, u})).symm).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.comp_id _))

/-- **The degree-zero differential of the de Rham complex of [Stacks, Tag 07LM] is the canonical
connection of [Stacks, Tag 07J6].** -/
theorem crystalDeRhamDifferential_zero_eq (hC : IsSheafCrystal F) :
    crystalDeRhamDifferential hF 0 =
      (tensorDifferentialFormsSheafZeroIso S F).hom ≫ crystalConnectionCris hC := by
  refine Sheaf.hom_ext (sheafify_hom_ext (smallTopology S) _ _
    (tensorDifferentialFormsSheaf F 1).property ?_)
  refine (toSheafify_crystalDeRhamDifferential hF 0).trans ?_
  refine hom_ext_of_app S (fun B ↦ ?_)
  ext ⟨x⟩
  let Z := (PresheafOfModules.toPresheaf _).mapIso (tensorDifferentialFormsZeroIso
    (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)))
  have hx : Z.inv.app (op B.obj) (Z.hom.app (op B.obj) x) = x :=
    ConcreteCategory.congr_hom (Z.hom_inv_id_app (op B.obj)) x
  have hR := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_tensorDifferentialFormsSheafZeroIso_hom F) (op B.obj))
    (ULift.up x)
  refine (congrArg (fun y ↦ (presheafDeRhamDifferential hF 0).app (op B.obj) (ULift.up y))
    hx.symm).trans ?_
  refine (presheafDeRhamDifferential_app hF 0 B _).trans ?_
  refine (congrArg (fun y ↦ (CategoryTheory.toSheafify (smallTopology S)
    (tensorFormsULift F 1)).app (op B.obj) (ULift.up y))
    (affineDeRhamDifferential_zero hF B (Z.hom.app (op B.obj) x))).trans ?_
  refine (crystalConnectionCrisApp_eq_ringConnection B.top_le_preimage_baseOpen
    B.isAffineOpen_baseOpen hC (bijective_crysExtensionSectionsMap_affine hF B)
    (Z.hom.app (op B.obj) x)).symm.trans ?_
  exact (congrArg ((crystalConnectionCris hC).hom.app (op B.obj)) hR).symm

/-- **The canonical connection of [Stacks, Tag 07J6] is the degree-zero differential of the de Rham
complex of [Stacks, Tag 07LM]**, read through `F = F ⊗ Ω^0_{X/S}`. -/
theorem crystalConnectionCris_eq_crystalDeRhamDifferential_zero (hC : IsSheafCrystal F) :
    crystalConnectionCris hC =
      (tensorDifferentialFormsSheafZeroIso S F).inv ≫ crystalDeRhamDifferential hF 0 := by
  rw [crystalDeRhamDifferential_zero_eq hF hC, Iso.inv_hom_id_assoc]

/-- The degree-one differential over an affine-over-affine object, on a pure tensor. -/
theorem affineDeRhamDifferential_one_tmul (B : AffineOverAffineCrystallineThickening S)
    (m : F.val.obj (op B.obj)) (ω : (crysDifferentialForms S 1).obj (op B.obj)) :
    affineDeRhamDifferential hF 1 B (formsTmul F m ω) =
      (tensorFormsSectionsEquiv F 2 B.obj).symm
        (TensorProduct.map LinearMap.id ((leftWedge (B := GlobalCrystallineSituation.crysFormRing
            S B.obj.obj) (Omega := ↥((GlobalCrystallineSituation.crysDifferentials S).obj
              (op B.obj.obj))) 1).flip (crysFormSections S 1 B.obj ω))
          (AffineConnection.ringConnection B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
            (bijective_crysExtensionSectionsMap_affine hF B) m)) +
        @id ↑((tensorDifferentialForms (F.val : PresheafOfModules.{u}
          (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) 2).obj (op B.obj))
          (formsTmul F m (formsDeRham B.obj ω)) := by
  apply (tensorFormsSectionsEquiv F 2 B.obj).injective
  refine (tensorFormsSectionsEquiv_affineDeRhamDifferential hF 1 B _).trans ?_
  refine (AffineConnection.extDiff_tmul _ _ _ 1 m _).trans ?_
  refine Eq.trans ?_ (map_add _ _ _).symm
  exact congrArg₂ (· + ·) (AddEquiv.apply_symm_apply _ _).symm rfl

/-- **The degree-one differential of the de Rham complex of [Stacks, Tag 07LM] is the extension
of the canonical connection of [Stacks, Tag 07J6]** by the rule of [Stacks, Tag 07I0]. -/
theorem crystalDeRhamDifferential_one_eq (hC : IsSheafCrystal F) :
    crystalDeRhamDifferential hF 1 = crystalExtensionCris hC := by
  refine Sheaf.hom_ext (sheafify_hom_ext (smallTopology S) _ _
    (tensorDifferentialFormsSheaf F 2).property ?_)
  refine (toSheafify_crystalDeRhamDifferential hF 1).trans ?_
  refine hom_ext_of_app S (fun B ↦ ?_)
  ext ⟨x⟩
  let η₁ := CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)
  let η₂ := CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)
  show (presheafDeRhamDifferential hF 1).app (op B.obj) (ULift.up x) =
    crystalExtensionCrisApp hC B.obj (η₁.app (op B.obj) (ULift.up x))
  refine (presheafDeRhamDifferential_app hF 1 B x).trans ?_
  refine tensor_addMonoidHom_apply_eq
    ((toSheafifyAddHom F 2 B.obj).comp (affineDeRhamDifferential hF 1 B))
    ((crystalExtensionCrisApp hC B.obj).hom.comp (toSheafifyAddHom F 1 B.obj))
    (fun m ω ↦ ?_) x
  refine (congrArg (fun z ↦ η₂.app (op B.obj) (ULift.up z))
    (affineDeRhamDifferential_one_tmul hF B m ω)).trans ?_
  refine (map_add _ (ULift.up _) (ULift.up _)).trans ?_
  refine Eq.trans ?_ (crystalExtensionCrisApp_toSheafify hC B.obj m ω).symm
  refine congrArg₂ (· + ·) ?_ rfl
  refine (crystalWedgeCrisApp_formsOneTensor B.obj ω _).symm.trans ?_
  exact congrArg (crystalWedgeCrisApp F B.obj ω)
    (crystalConnectionCrisApp_eq_ringConnection B.top_le_preimage_baseOpen
      B.isAffineOpen_baseOpen hC (bijective_crysExtensionSectionsMap_affine hF B) m).symm

end QC

end Crystalline.GlobalCrystallineSituation.SmallSite

end

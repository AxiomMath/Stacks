module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionCris
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsSheaf

/-!
# The Leibniz rule for the canonical connection on `Cris(X/S)`

Fix a global crystalline situation of [Stacks, Tag 07MF] and a crystal `F` in `𝒪_{X/S}`-modules
on `Cris(X/S)`.  The sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of `...SmallSite.tensorDifferentialFormsSheaf`
is the abelian sheaf underlying a sheaf of `𝒪_{X/S}`-modules, the sheafification
`tensorDifferentialFormsModuleSheaf` of the presheaf of modules `A ↦ F(A) ⊗ Ω^i_{X/S}(A)`.  With
these scalars the canonical connection `∇ = ...SmallSite.crystalConnectionCris` satisfies the
Leibniz rule of [Stacks, Section 60.15, Tag 07J5]: for every object `A`, every section `f` of
`𝒪_{X/S}` and every section `s` of `F` over `A`,

`∇(f s) = f ∇(s) + s ⊗ d f`.

## Main definitions

* `tensorDifferentialFormsModuleSheaf` — `F ⊗ Ω^i_{X/S}` as a sheaf of `𝒪_{X/S}`-modules.

## Main results

* `toSheaf_tensorDifferentialFormsModuleSheaf` — its underlying abelian sheaf is
  `...SmallSite.tensorDifferentialFormsSheaf`.
* `crystalConnectionCris_smul` — **the Leibniz rule**.

## References

* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] monoidalCategorySchemeModules moduleCrysFormRingSections
  commRingRingCatSheafSections

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))

/-! ### `F ⊗ Ω^i_{X/S}` as a sheaf of modules -/

/-- **`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` as a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`**, at the module
universe `u + 1`: the sheafification of the presheaf of modules `A ↦ F(A) ⊗ Ω^i_{X/S}(A)`. -/
def tensorDifferentialFormsModuleSheaf (i : ℕ) : ModuleSheaf S :=
  (PresheafOfModules.sheafification (𝟙 (structureSheaf S).obj)).obj
    ((Stacks.SheafOfModules.presheafULift.{u + 1} (structureSheaf S).obj).obj
      (tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i))

/-- **The abelian sheaf underlying `tensorDifferentialFormsModuleSheaf` is
`...SmallSite.tensorDifferentialFormsSheaf`.** -/
theorem toSheaf_tensorDifferentialFormsModuleSheaf (i : ℕ) :
    (SheafOfModules.toSheaf _).obj (tensorDifferentialFormsModuleSheaf F i) =
      tensorDifferentialFormsSheaf F i := rfl

/-- The sections of `F ⊗ Ω^i_{X/S}` over an object, as a module over the sections of `𝒪_{X/S}`. -/
abbrev tensorFormsModSec (i : ℕ) (B : CrystallineThickening S) : Type (u + 1) :=
  ↑((tensorDifferentialFormsModuleSheaf F i).val.obj (op B))

/-- The sections of `F ⊗ Ω^i_{X/S}` over an object, as a module over the section ring in the
small-site spelling. -/
@[instance_reducible]
def moduleTensorFormsModSec (i : ℕ) (B : CrystallineThickening S) :
    Module (crysFormRing S B) (tensorFormsModSec F i B) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op B))
    ((tensorDifferentialFormsModuleSheaf F i).val.obj (op B)))

attribute [local instance] moduleTensorFormsModSec

/-- **The unit of the sheafification is linear.** -/
theorem toSheafify_tensorDifferentialFormsPresheaf_smul (i : ℕ) (B : CrystallineThickening S)
    (b : crysFormRing S B)
    (p : F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentialForms S i).obj (op B)) :
    (show tensorFormsModSec F i B from
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
        (op B) (ULift.up (b • p))) =
      b • (show tensorFormsModSec F i B from
        (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
          (op B) (ULift.up p)) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf S).obj)).unit.app
    ((Stacks.SheafOfModules.presheafULift.{u + 1} (structureSheaf S).obj).obj
      (tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i))).app (op B)).hom.map_smul b
    (ULift.up p)


/-- Restriction of a section of `F ⊗ Ω^i_{X/S}` is semilinear for the module structure of
`tensorDifferentialFormsModuleSheaf`. -/
theorem tensorFormsModSec_map_smul (i : ℕ) {B B' : CrystallineThickening S} (k : B' ⟶ B)
    (b : crysFormRing S B) (t : tensorFormsModSec F i B) :
    (show tensorFormsModSec F i B' from (tensorDifferentialFormsSheaf F i).obj.map k.op (b • t)) =
      ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map k.op b) •
        (show tensorFormsModSec F i B' from (tensorDifferentialFormsSheaf F i).obj.map k.op t) :=
  (tensorDifferentialFormsModuleSheaf F i).val.map_smul k.op b t

/-! ### Semilinearity of the identification -/

section General

variable {A : CrystallineThickening S} {i : ℕ} {N : A.obj.thickening.target.scheme.Modules}
  (c : FormsComparison A i N)

/-- `openTopRes` inverts `sectionRingEquiv`. -/
private theorem openTopRes_sectionRingEquiv (V : A.obj.thickening.target.scheme.Opens)
    (r : crysFormRing S (A.restrictOpen V)) :
    (openTopRes V).hom (sectionRingEquiv A V r) = r :=
  (openTopResEquiv A V).apply_symm_apply r

/-- **`sectionRingEquiv` is compatible with restriction.** -/
theorem sectionRingEquiv_restrict {V V' : A.obj.thickening.target.scheme.Opens} (h : V' ≤ V)
    (r : crysFormRing S (A.restrictOpen V)) :
    sectionRingEquiv A V' ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
        (CrystallineThickening.restrictOpenLE A h).op r) =
      A.obj.thickening.target.scheme.presheaf.map (homOfLE h).op (sectionRingEquiv A V r) := by
  have e := restrictedCommRing_map_openTopRes A h (sectionRingEquiv A V r)
  rw [openTopRes_sectionRingEquiv] at e
  exact (congrArg (sectionRingEquiv A V') e).trans ((openTopResEquiv A V').symm_apply_apply _)

/-- **The comparison morphism is semilinear.** -/
theorem tensorFormsAmbientUnit_smul (V : A.obj.thickening.target.scheme.Opens)
    (b : crysFormRing S (A.restrictOpen V))
    (p : F.val.obj (op (A.restrictOpen V)) ⊗[crysFormRing S (A.restrictOpen V)]
      (crysDifferentialForms S i).obj (op (A.restrictOpen V))) :
    (show (ambientTensor F N).val.obj (op V) from
      (tensorFormsAmbientUnit F c).app (op V) (b • p)) =
      sectionRingEquiv A V b • (show (ambientTensor F N).val.obj (op V) from
        (tensorFormsAmbientUnit F c).app (op V) p) := by
  have h1 := tensorMapSemilinear_smul (M₁ := F.val.obj (op (A.restrictOpen V)))
    (M₂ := (crysAmbientSchemeModules F A).val.obj (op V))
    (sectionRingEquiv A V).toRingHom (AddMonoidHom.id _) (c.toFun V)
    (crysAmbient_smul F A V) (c.map_smul V) b p
  refine (congrArg _ h1).trans ?_
  exact (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf A.obj.thickening.target.scheme.toRingedSpace)
      (𝟙 (Stacks.RingedSpace.structureRingSheaf
        A.obj.thickening.target.scheme.toRingedSpace).obj)).unit.app
      (PresheafOfModules.tensorObj (O := A.obj.thickening.target.scheme.toRingedSpace.presheaf)
        (crysAmbientSchemeModules F A).val N.val)).app (op V)).hom.map_smul _ _

/-- Restriction of a section of `𝒪_{X/S}` along two restrictions of an object of `Cris(X/S)`. -/
theorem structurePresheaf_map_restrictOpenLE_comp {V₁ V₂ V₃ : A.obj.thickening.target.scheme.Opens}
    (h₂ : V₃ ≤ V₂) (h₁ : V₂ ≤ V₁) (r : crysFormRing S (A.restrictOpen V₁)) :
    (structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
        (CrystallineThickening.restrictOpenLE A h₂).op
        ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
          (CrystallineThickening.restrictOpenLE A h₁).op r) =
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
        (CrystallineThickening.restrictOpenLE A (h₂.trans h₁)).op r := by
  have e : CrystallineThickening.restrictOpenLE A h₂ ≫ CrystallineThickening.restrictOpenLE A h₁ =
      CrystallineThickening.restrictOpenLE A (h₂.trans h₁) :=
    ((CrystallineThickening.restrictOpenFunctor A).map_comp (homOfLE h₂) (homOfLE h₁)).symm
  rw [← e, op_comp, Functor.map_comp]
  rfl

/-- **The inverse identification is semilinear**, over every open inside a fixed one, for the
restrictions of a fixed section of `𝒪_{X/S}`. -/
theorem tensorFormsAmbientIso_inv_smul_restrict {V : A.obj.thickening.target.scheme.Opens}
    (b : crysFormRing S (A.restrictOpen V)) (V' : A.obj.thickening.target.scheme.Opens)
    (hV' : V' ≤ V) (z : (ambientTensor F N).val.obj (op V')) :
    (show tensorFormsModSec F i (A.restrictOpen V') from
      (tensorFormsAmbientIso F c).inv.app (op V') (ULift.up (sectionRingEquiv A V'
        ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
          (CrystallineThickening.restrictOpenLE A hV').op b) • z))) =
      ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
          (CrystallineThickening.restrictOpenLE A hV').op b) •
        (show tensorFormsModSec F i (A.restrictOpen V') from
          (tensorFormsAmbientIso F c).inv.app (op V') (ULift.up z)) := by
  let R := structurePresheaf S ⋙ forget₂ CommRingCat RingCat
  let br : ∀ V'' : A.obj.thickening.target.scheme.Opens, V'' ≤ V' →
      crysFormRing S (A.restrictOpen V'') := fun V'' h ↦
    R.map (CrystallineThickening.restrictOpenLE A (h.trans hV')).op b
  let φ : ∀ V'' : A.obj.thickening.target.scheme.Opens, V'' ≤ V' →
      (ambientTensorSheafULift F N).obj (op V'') →+
        ((CrystallineThickening.restrictOpenFunctor A).op ⋙
          (tensorDifferentialFormsSheaf F i).obj).obj (op V'') := fun V'' h ↦
    ((tensorFormsAmbientIso F c).inv.app (op V'')).hom.comp
      (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((AddMonoidHom.mk' (fun y : (ambientTensor F N).val.obj (op V'') ↦
          sectionRingEquiv A V'' (br V'' h) • y) (smul_add _)).comp
          AddEquiv.ulift.toAddMonoidHom))
  let ψ : ∀ V'' : A.obj.thickening.target.scheme.Opens, V'' ≤ V' →
      (ambientTensorSheafULift F N).obj (op V'') →+
        ((CrystallineThickening.restrictOpenFunctor A).op ⋙
          (tensorDifferentialFormsSheaf F i).obj).obj (op V'') := fun V'' h ↦
    (AddMonoidHom.mk' (fun y : tensorFormsModSec F i (A.restrictOpen V'') ↦ br V'' h • y)
      (smul_add _)).comp ((tensorFormsAmbientIso F c).inv.app (op V'')).hom
  refine zariski_addMonoidHom_eq.{u + 1, u + 1, u} (tensorFormsAmbientUnitULift F c)
    (CrystallineThickening.isSheaf_restriction A _ (tensorDifferentialFormsSheaf F i).property)
    φ ψ ?_ ?_ ?_ (ULift.up z)
  · intro V₁ V₂ h₁ h₂ h z
    have hb : sectionRingEquiv A V₂ (br V₂ h₂) =
        A.obj.thickening.target.scheme.presheaf.map (homOfLE h).op
          (sectionRingEquiv A V₁ (br V₁ h₁)) :=
      (congrArg (sectionRingEquiv A V₂)
        (structurePresheaf_map_restrictOpenLE_comp h (h₁.trans hV') b).symm).trans
        (sectionRingEquiv_restrict h (br V₁ h₁))
    let z' : (ambientTensor F N).val.obj (op V₁) := z.down
    have hm : (ambientTensor F N).val.map (homOfLE h).op
        (sectionRingEquiv A V₁ (br V₁ h₁) • z') =
        sectionRingEquiv A V₂ (br V₂ h₂) • (ambientTensor F N).val.map (homOfLE h).op z' :=
      ((ambientTensor F N).val.map_smul (homOfLE h).op _ z').trans
        (congrArg (· • (ambientTensor F N).val.map (homOfLE h).op z') hb.symm)
    exact (tensorFormsAmbientIso_inv_naturality F c h _).symm.trans
      (congrArg (fun y ↦ (tensorFormsAmbientIso F c).inv.app (op V₂) (ULift.up y)) hm)
  · intro V₁ V₂ h₁ h₂ h z
    have hb : R.map (CrystallineThickening.restrictOpenLE A h).op (br V₁ h₁) = br V₂ h₂ :=
      structurePresheaf_map_restrictOpenLE_comp h (h₁.trans hV') b
    exact (tensorFormsModSec_map_smul F i (CrystallineThickening.restrictOpenLE A h) _ _).trans
      ((congrArg (· • (show tensorFormsModSec F i (A.restrictOpen V₂) from
        (tensorDifferentialFormsSheaf F i).obj.map (CrystallineThickening.restrictOpenLE A h).op
          ((tensorFormsAmbientIso F c).inv.app (op V₁) z))) hb).trans
        (congrArg (fun y : tensorFormsModSec F i (A.restrictOpen V₂) ↦ br V₂ h₂ • y)
          (tensorFormsAmbientIso_inv_naturality F c h z).symm))
  · intro V₁ h₁ p
    obtain ⟨p⟩ := p
    change F.val.obj (op (A.restrictOpen V₁)) ⊗[crysFormRing S (A.restrictOpen V₁)]
      (crysDifferentialForms S i).obj (op (A.restrictOpen V₁)) at p
    show (tensorFormsAmbientIso F c).inv.app (op V₁) (ULift.up (sectionRingEquiv A V₁ (br V₁ h₁) •
        (show (ambientTensor F N).val.obj (op V₁) from
          (tensorFormsAmbientUnit F c).app (op V₁) p))) =
      (show tensorFormsModSec F i (A.restrictOpen V₁) from br V₁ h₁ •
        (show tensorFormsModSec F i (A.restrictOpen V₁) from
          (tensorFormsAmbientIso F c).inv.app (op V₁)
            (ULift.up ((tensorFormsAmbientUnit F c).app (op V₁) p))))
    refine (congrArg (fun y ↦ (tensorFormsAmbientIso F c).inv.app (op V₁) (ULift.up y))
      (tensorFormsAmbientUnit_smul F c V₁ (br V₁ h₁) p).symm).trans ?_
    refine (tensorFormsAmbientIso_inv_unit F c V₁ (ULift.up (br V₁ h₁ • p))).trans ?_
    refine (toSheafify_tensorDifferentialFormsPresheaf_smul F i _ (br V₁ h₁) p).trans ?_
    exact congrArg (fun y : tensorFormsModSec F i (A.restrictOpen V₁) ↦ br V₁ h₁ • y)
      (tensorFormsAmbientIso_inv_unit F c V₁ (ULift.up p)).symm

/-- **The inverse identification is semilinear.** -/
theorem tensorFormsAmbientIso_inv_smul (V : A.obj.thickening.target.scheme.Opens)
    (b : crysFormRing S (A.restrictOpen V)) (z : (ambientTensor F N).val.obj (op V)) :
    (show tensorFormsModSec F i (A.restrictOpen V) from
      (tensorFormsAmbientIso F c).inv.app (op V) (ULift.up (sectionRingEquiv A V b • z))) =
      b • (show tensorFormsModSec F i (A.restrictOpen V) from
        (tensorFormsAmbientIso F c).inv.app (op V) (ULift.up z)) := by
  have hb : (structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
      (CrystallineThickening.restrictOpenLE A (le_refl V)).op b = b := by
    have e : CrystallineThickening.restrictOpenLE A (le_refl V) = 𝟙 _ :=
      (congrArg (CrystallineThickening.restrictOpenFunctor A).map
        (Subsingleton.elim (homOfLE (le_refl V)) (𝟙 V))).trans
        ((CrystallineThickening.restrictOpenFunctor A).map_id V)
    rw [e, op_id]
    exact ConcreteCategory.congr_hom ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map_id
      (op (A.restrictOpen V))) b
  have h := tensorFormsAmbientIso_inv_smul_restrict F c b V (le_refl V) z
  rw [hb] at h
  exact h

end General

/-! ### The Leibniz rule -/

/-- A pure tensor in the sections over an object of the presheaf `F ⊗ Ω^i_{X/S}`. -/
abbrev formsTmul {i : ℕ} {B : CrystallineThickening S} (x : F.val.obj (op B))
    (ω : (crysDifferentialForms S i).obj (op B)) :
    F.val.obj (op B) ⊗[crysFormRing S B] (crysDifferentialForms S i).obj (op B) :=
  x ⊗ₜ ω

/-- **The differential `d f ∈ Ω^1_{X/S}(B)` of a section of `𝒪_{X/S}`.** -/
abbrev formsD (B : CrystallineThickening S) (b : crysFormRing S B) :
    (crysDifferentialForms S 1).obj (op B) :=
  (crysFormsOneGen S).app (op B) (crysD S B b)

/-- The differential of a section is natural in the object. -/
theorem formsD_map {B B' : CrystallineThickening S} (k : B ⟶ B') (b : crysFormRing S B') :
    (crysDifferentialForms S 1).map k.op (formsD B' b) =
      formsD B ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map k.op b) :=
  (PresheafOfModules.naturality_apply (crysFormsOneGen S) k.op _).symm.trans
    (congrArg ((crysFormsOneGen S).app (op B)) (GlobalCrystallineSituation.crysD_map S k.hom b))

/-- **The comparison of [Stacks, Tag 07IZ] carries `d f` to `d_{T/S,δ} f`.** -/
theorem formsCompOne_formsD (A : CrystallineThickening S) (V : A.obj.thickening.target.scheme.Opens)
    (b : crysFormRing S (A.restrictOpen V)) :
    formsCompOne A V (formsD (A.restrictOpen V) b) =
      sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom V (sectionRingEquiv A V b) := by
  have e1 : formsOneEquiv (A.restrictOpen V) (formsD (A.restrictOpen V) b) =
      crysD S (A.restrictOpen V) b :=
    crysFormsOneApp_oneGen S (A.restrictOpen V).obj _
  refine (congrArg ((restrictedToSheaf A.obj).app (op V)).hom e1).trans ?_
  have h := restrictedToSheaf_app_d A.obj V (sectionRingEquiv A V b)
  rw [openTopRes_sectionRingEquiv] at h
  exact h

variable {F} (hF : IsSheafCrystal F)

/-- **The Leibniz rule for the canonical connection of a crystal on `Cris(X/S)`**
([Stacks, Section 60.15, Tag 07J5]): for every object `A`, every section `f` of `𝒪_{X/S}` and
every section `s` of `F` over `A`, `∇(f s) = f ∇(s) + s ⊗ d f`, the scalars on `F ⊗ Ω_{X/S}`
being those of `tensorDifferentialFormsModuleSheaf`. -/
theorem crystalConnectionCris_smul (A : CrystallineThickening S) (f : crysFormRing S A)
    (s : F.val.obj (op A)) :
    (show tensorFormsModSec F 1 A from
      crystalConnectionCrisApp hF A (ULift.up (f • s))) =
      f • (show tensorFormsModSec F 1 A from
        crystalConnectionCrisApp hF A (ULift.up s)) +
      (show tensorFormsModSec F 1 A from
        (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
          (op A) (ULift.up (formsTmul F s (formsD A f)))) := by
  let R := structurePresheaf S ⋙ forget₂ CommRingCat RingCat
  let rA := A.restrictOpenHom (⊤ : A.obj.thickening.target.scheme.Opens)
  let b : crysFormRing S (A.restrictOpen ⊤) := R.map rA.op f
  let x : F.val.obj (op (A.restrictOpen ⊤)) := F.val.map rA.op s
  apply injective_restrictTop (tensorDifferentialFormsSheaf F 1).obj A
  refine (crystalConnectionCrisApp_restrict hF A (ULift.up (f • s))).trans ?_
  have e1 : (show (crysAmbientSchemeModules F A).val.obj (op ⊤) from
      F.val.map rA.op (f • s)) = sectionRingEquiv A ⊤ b •
        (show (crysAmbientSchemeModules F A).val.obj (op ⊤) from x) :=
    (F.val.map_smul rA.op f s).trans (crysAmbient_smul F A ⊤ b x)
  let Ψ := tensorFormsAmbientIsoOne (F := F) A
  let η := CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)
  let G := (tensorDifferentialFormsSheaf F 1).obj
  have hL : Ψ.inv.app (op ⊤) (ULift.up (crystalConnectionApp A hF ⊤ (F.val.map rA.op (f • s)))) =
      (show tensorFormsModSec F 1 (A.restrictOpen ⊤) from
        b • (show tensorFormsModSec F 1 (A.restrictOpen ⊤) from
          Ψ.inv.app (op ⊤) (ULift.up (crystalConnectionApp A hF ⊤ x)))) +
      (show tensorFormsModSec F 1 (A.restrictOpen ⊤) from
        η.app (op (A.restrictOpen ⊤)) (ULift.up (formsTmul F x (formsD (A.restrictOpen ⊤) b)))) :=
      by
    refine (congrArg (fun y ↦ Ψ.inv.app (op ⊤) (ULift.up (crystalConnectionApp A hF ⊤ y)))
      e1).trans ?_
    refine (congrArg (fun y ↦ Ψ.inv.app (op ⊤) (ULift.up y))
      (crystalConnectionApp_smul A hF ⊤ (sectionRingEquiv A ⊤ b) x)).trans ?_
    refine (map_add (Ψ.inv.app (op ⊤)).hom (ULift.up _) (ULift.up _)).trans ?_
    refine congrArg₂ (· + ·) (tensorFormsAmbientIso_inv_smul F (formsComparisonOne A) ⊤ b _) ?_
    refine Eq.trans ?_ (tensorFormsAmbientIso_inv_tmul F (formsComparisonOne A) ⊤ x
      (formsD (A.restrictOpen ⊤) b))
    exact congrArg (fun ω ↦ Ψ.inv.app (op ⊤) (ULift.up (firstOrderTensorTmul F A ⊤ x ω)))
      (formsCompOne_formsD A ⊤ b).symm
  refine hL.trans ?_
  refine Eq.trans ?_ (map_add (G.map rA.op).hom _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans ?_ (tensorFormsModSec_map_smul F 1 rA f _).symm
    exact congrArg (fun y : tensorFormsModSec F 1 (A.restrictOpen ⊤) ↦ b • y)
      (crystalConnectionCrisApp_restrict hF A (ULift.up s)).symm
  · refine Eq.trans ?_ (ConcreteCategory.congr_hom (η.naturality rA.op) _)
    exact congrArg (fun ω ↦ η.app (op (A.restrictOpen ⊤)) (ULift.up (formsTmul F x ω)))
      (formsD_map rA f).symm

end Crystalline.GlobalCrystallineSituation.SmallSite

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTensorFormsNaturality

/-!
# The canonical connection of a crystal as a morphism of sheaves on `Cris(X/S)`

Fix a global crystalline situation of [Stacks, Tag 07MF] and a crystal `F` in `𝒪_{X/S}`-modules
on `Cris(X/S)`.  `...SmallSite.crystalConnection` is the canonical connection of the proof of
[Stacks, Lemma 60.15.1, Tag 07J6] on the ambient scheme `T` of each object `(U, T, δ)`,
`∇ : F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}`.  This module assembles these into a morphism of abelian
sheaves on `Cris(X/S)`

`∇ : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}`,

through the identification `(F ⊗ Ω_{X/S})_T = F_T ⊗ Ω_{T/S,δ}` of
`...SmallSite.tensorFormsAmbientIso`.  The transition maps of the target along a morphism
`g : B ⟶ A` of `Cris(X/S)` are, on `T`, the maps `x ⊗ ω ↦ g^* x ⊗ g^* ω`, which is the content of
`tensorFormsAmbientIsoOne_map`; this is how the functoriality of the canonical connection in the
object proved in `SmallSite/CrystalConnectionFunctoriality.lean` becomes naturality of a morphism
of sheaves.

## Main definitions

* `crystalConnectionCris` — the canonical connection `∇ : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}` of a crystal,
  as a morphism of abelian sheaves on `Cris(X/S)`.

## Main results

* `tensorFormsAmbientIsoOne_map` — the identification `(F ⊗ Ω_{X/S})_T = F_T ⊗ Ω_{T/S,δ}` carries
  the transition maps of `F ⊗ Ω_{X/S}` to the transition maps `x ⊗ ω ↦ g^* x ⊗ g^* ω`.

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] monoidalCategorySchemeModules

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))

/-! ### The identifications, generally -/

section General

variable {A : CrystallineThickening S} {i : ℕ} {N : A.obj.thickening.target.scheme.Modules}
  (c : FormsComparison A i N)

/-- The identification `(F ⊗ Ω^i_{X/S})_T ≅ F_T ⊗ N` is natural in the open of `T`. -/
theorem tensorFormsAmbientIso_hom_naturality {V V' : A.obj.thickening.target.scheme.Opens}
    (h : V' ≤ V) (q : (tensorDifferentialFormsSheaf F i).obj.obj (op (A.restrictOpen V))) :
    (tensorFormsAmbientIso F c).hom.app (op V')
        ((tensorDifferentialFormsSheaf F i).obj.map
          (CrystallineThickening.restrictOpenLE A h).op q) =
      (ambientTensorSheafULift F N).map (homOfLE h).op
        ((tensorFormsAmbientIso F c).hom.app (op V) q) :=
  ConcreteCategory.congr_hom ((tensorFormsAmbientIso F c).hom.naturality (homOfLE h).op) q

/-- The identification on the image of an arbitrary section of the presheaf tensor product. -/
theorem tensorFormsAmbientIso_hom_app_toSheafify' (V : A.obj.thickening.target.scheme.Opens)
    (p : (tensorDifferentialFormsPresheaf F i).obj (op (A.restrictOpen V))) :
    (tensorFormsAmbientIso F c).hom.app (op V)
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
          (op (A.restrictOpen V)) p) =
      ULift.up ((tensorFormsAmbientUnit F c).app (op V) p.down) := by
  have := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have h := CrystallineThickening.whiskerLeft_comp_restrictOpenSheafifyIso_hom A
    (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))
    (isSheaf_ambientTensorSheafULift F N) (tensorDifferentialFormsSheaf F i).property
    (tensorFormsAmbientUnitULift F c)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) p

/-- The inverse identification undoes the identification. -/
private theorem tensorFormsAmbientIso_inv_hom_app (V : A.obj.thickening.target.scheme.Opens)
    (q : (tensorDifferentialFormsSheaf F i).obj.obj (op (A.restrictOpen V))) :
    (tensorFormsAmbientIso F c).inv.app (op V) ((tensorFormsAmbientIso F c).hom.app (op V) q) =
      q :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (tensorFormsAmbientIso F c).hom_inv_id (op V)) q

/-- **The inverse identification on a local pure tensor of the comparison.** -/
theorem tensorFormsAmbientIso_inv_tmul (V : A.obj.thickening.target.scheme.Opens)
    (x : F.val.obj (op (A.restrictOpen V)))
    (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen V))) :
    (tensorFormsAmbientIso F c).inv.app (op V)
        (ULift.up (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
          (crysAmbientSchemeModules F A) N (op V) x (c.toFun V ω))) =
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
        (op (A.restrictOpen V)) (ULift.up (restrTmul V x ω)) := by
  exact (congrArg ((tensorFormsAmbientIso F c).inv.app (op V))
    (tensorFormsAmbientIso_hom_app_toSheafify F c V x ω).symm).trans
    (tensorFormsAmbientIso_inv_hom_app F c V _)

/-- The inverse identification on the image of the comparison morphism. -/
theorem tensorFormsAmbientIso_inv_unit (V : A.obj.thickening.target.scheme.Opens)
    (p : (tensorDifferentialFormsPresheaf F i).obj (op (A.restrictOpen V))) :
    (tensorFormsAmbientIso F c).inv.app (op V)
        (ULift.up ((tensorFormsAmbientUnit F c).app (op V) p.down)) =
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
        (op (A.restrictOpen V)) p := by
  exact (congrArg ((tensorFormsAmbientIso F c).inv.app (op V))
    (tensorFormsAmbientIso_hom_app_toSheafify' F c V p).symm).trans
    (tensorFormsAmbientIso_inv_hom_app F c V _)

/-- The inverse identification is natural in the open of `T`. -/
theorem tensorFormsAmbientIso_inv_naturality {V V' : A.obj.thickening.target.scheme.Opens}
    (h : V' ≤ V) (z : (ambientTensorSheafULift F N).obj (op V)) :
    (tensorFormsAmbientIso F c).inv.app (op V')
        ((ambientTensorSheafULift F N).map (homOfLE h).op z) =
      (tensorDifferentialFormsSheaf F i).obj.map (CrystallineThickening.restrictOpenLE A h).op
        ((tensorFormsAmbientIso F c).inv.app (op V) z) :=
  ConcreteCategory.congr_hom ((tensorFormsAmbientIso F c).inv.naturality (homOfLE h).op) z

end General

/-- Restriction of an abelian presheaf along a composite. -/
theorem presheaf_map_comp_apply {C : Type*} [Category C] (G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (x : G.obj (op Z)) :
    G.map (a ≫ b).op x = G.map a.op (G.map b.op x) := by
  rw [op_comp, Functor.map_comp]
  rfl

/-! ### The comparison of degree-one forms is natural -/

/-- **The comparison of degree-one forms is natural in the object**: along `g : B ⟶ A` it carries
the transition map of `Ω^1_{X/S}` to `dg`. -/
theorem formsCompOne_map {A B : CrystallineThickening S} (g : B ⟶ A)
    (V : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen V))) :
    formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ V)
        ((crysDifferentialForms S 1).map (CrystallineThickening.restrictOpenMap g V).op ω) =
      (dpDifferentialsMapSheaf g.hom).app V (formsCompOne A V ω) :=
  (congrArg ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
    (formsOneEquiv_map (CrystallineThickening.restrictOpenMap g V) ω)).trans
    (restrictedToSheaf_crysDifferentials_map g V _)


/-! ### The transition maps of `F ⊗ Ω_{X/S}` on the ambient schemes -/

section Transition

variable {F} {A B : CrystallineThickening S} (g : B ⟶ A) (hF : IsSheafCrystal F)

/-- The identification `(F ⊗ Ω_{X/S})_{T_A} ≅ F_{T_A} ⊗ Ω_{T_A/S,δ}` of degree one. -/
abbrev tensorFormsAmbientIsoOne (A : CrystallineThickening S) :=
  tensorFormsAmbientIso F (formsComparisonOne A)

/-- The sheaf `V ↦ (F ⊗ Ω_{X/S})(B|_{g⁻¹ V})` on the ambient scheme of `A`, the pushforward along
`g` of the restriction to `T_B`. -/
abbrev pushforwardTensorForms (i : ℕ) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Opens.map g.hom.targetHom.hom.base).op ⋙
    ((CrystallineThickening.restrictOpenFunctor B).op ⋙ (tensorDifferentialFormsSheaf F i).obj)

/-- The presheaf `pushforwardTensorForms g i` is a sheaf on the ambient scheme of `A`. -/
theorem isSheaf_pushforwardTensorForms (i : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (pushforwardTensorForms (F := F) g i) :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf (f := g.hom.targetHom.hom.base)
    (CrystallineThickening.isSheaf_restriction B _ (tensorDifferentialFormsSheaf F i).property)

/-- **The identification `(F ⊗ Ω_{X/S})_T = F_T ⊗ Ω_{T/S,δ}` carries the transition maps of
`F ⊗ Ω_{X/S}` to the transition maps `x ⊗ ω ↦ g^* x ⊗ g^* ω`** of
`...SmallSite.crystalTensorTransition`: for a morphism `g : B ⟶ A` of `Cris(X/S)` and an open
`W` of `T_A`, restricting a section of `F ⊗ Ω_{X/S}` over `A|_W` along `g` is, on `T`, the map
`τ_g`. -/
theorem tensorFormsAmbientIsoOne_map (W : A.obj.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules F A)).val.obj (op W)) :
    (tensorDifferentialFormsSheaf F 1).obj.map (CrystallineThickening.restrictOpenMap g W).op
        ((tensorFormsAmbientIsoOne A).inv.app (op W) (ULift.up z)) =
      (tensorFormsAmbientIsoOne B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ W))
        (ULift.up (crystalTensorTransition g hF W z)) := by
  let Q := ambientTensorSheafULift F (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom)
  let φ : ∀ V : A.obj.thickening.target.scheme.Opens, V ≤ W →
      Q.obj (op V) →+ (pushforwardTensorForms g 1).obj (op V) := fun V _ ↦
    ((tensorDifferentialFormsSheaf F 1).obj.map
      (CrystallineThickening.restrictOpenMap g V).op).hom.comp
        ((tensorFormsAmbientIsoOne A).inv.app (op V)).hom
  let ψ : ∀ V : A.obj.thickening.target.scheme.Opens, V ≤ W →
      Q.obj (op V) →+ (pushforwardTensorForms g 1).obj (op V) := fun V _ ↦
    ((tensorFormsAmbientIsoOne B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom.comp
      (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((crystalTensorTransition g hF V).comp AddEquiv.ulift.toAddMonoidHom))
  refine zariski_addMonoidHom_eq.{u + 1, u + 1, u}
    (tensorFormsAmbientUnitULift F (formsComparisonOne A))
    (isSheaf_pushforwardTensorForms g 1) φ ψ ?_ ?_ ?_ (ULift.up z)
  · intro V V' _ _ h z
    change (tensorDifferentialFormsSheaf F 1).obj.map
        (CrystallineThickening.restrictOpenLE B (g.hom.targetHom.hom.preimage_mono h)).op
        ((tensorDifferentialFormsSheaf F 1).obj.map
          (CrystallineThickening.restrictOpenMap g V).op
            ((tensorFormsAmbientIsoOne A).inv.app (op V) z)) =
      (tensorDifferentialFormsSheaf F 1).obj.map
        (CrystallineThickening.restrictOpenMap g V').op
          ((tensorFormsAmbientIsoOne A).inv.app (op V') (Q.map (homOfLE h).op z))
    exact (presheaf_map_comp_apply _ _ _ _).symm.trans
      ((congrArg (fun k ↦ (tensorDifferentialFormsSheaf F 1).obj.map k.op
          ((tensorFormsAmbientIsoOne A).inv.app (op V) z))
        (CrystallineThickening.restrictOpenLE_restrictOpenMap g h)).trans
        ((presheaf_map_comp_apply _ _ _ _).trans
          (congrArg ((tensorDifferentialFormsSheaf F 1).obj.map
            (CrystallineThickening.restrictOpenMap g V').op)
            (tensorFormsAmbientIso_inv_naturality F (formsComparisonOne A) h z).symm)))
  · intro V V' _ _ h z
    change (tensorDifferentialFormsSheaf F 1).obj.map
        (CrystallineThickening.restrictOpenLE B (g.hom.targetHom.hom.preimage_mono h)).op
        ((tensorFormsAmbientIsoOne B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ V))
          (ULift.up (crystalTensorTransition g hF V z.down))) =
      (tensorFormsAmbientIsoOne B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ V'))
        (ULift.up (crystalTensorTransition g hF V' (Q.map (homOfLE h).op z).down))
    exact (tensorFormsAmbientIso_inv_naturality F (formsComparisonOne B)
      (g.hom.targetHom.hom.preimage_mono h) _).symm.trans
      (congrArg (fun t ↦ (tensorFormsAmbientIsoOne B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ V'))
        (ULift.up t)) (crystalTensorTransition_naturality g hF h z.down))
  · intro V hV p
    obtain ⟨p⟩ := p
    induction p using TensorProduct.inductionOn with
    | tmul x ω =>
      exact (congrArg ((tensorDifferentialFormsSheaf F 1).obj.map
          (CrystallineThickening.restrictOpenMap g V).op)
          (tensorFormsAmbientIso_inv_tmul F (formsComparisonOne A) V x ω)).trans
        ((ConcreteCategory.congr_hom ((CategoryTheory.toSheafify (smallTopology S)
          (tensorDifferentialFormsPresheaf F 1)).naturality
            (CrystallineThickening.restrictOpenMap g V).op) _).symm.trans
        ((tensorFormsAmbientIso_inv_tmul F (formsComparisonOne B) (g.hom.targetHom.hom ⁻¹ᵁ V)
          (F.val.map (CrystallineThickening.restrictOpenMap g V).op x)
          ((crysDifferentialForms S 1).map (CrystallineThickening.restrictOpenMap g V).op
            ω)).symm.trans
        (congrArg (fun t ↦ (tensorFormsAmbientIsoOne B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ V))
          (ULift.up t))
          ((congrArg (firstOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V)
            (crystalRestrict F (CrystallineThickening.restrictOpenMap g V) x))
            (formsCompOne_map g V ω)).trans
            (crystalTensorTransition_tmul g hF V x (formsCompOne A V ω)).symm))))
    | add p q hp hq =>
      have e2 := map_add (ConcreteCategory.hom
        ((tensorFormsAmbientUnitULift F (formsComparisonOne A)).app (op V))) (ULift.up p)
          (ULift.up q)
      exact (congrArg (φ V hV) e2).trans ((φ V hV).map_add _ _ |>.trans
        ((congrArg₂ (· + ·) hp hq).trans (((ψ V hV).map_add _ _).symm.trans
          (congrArg (ψ V hV) e2).symm)))

end Transition


/-! ### The connection as a morphism of sheaves -/

section Connection

variable {F} (hF : IsSheafCrystal F)

/-- Restriction of a sheaf on `Cris(X/S)` to the restriction `A|_T` of an object to the whole of
its ambient scheme is an isomorphism, `A|_T ⟶ A` being one. -/
abbrev restrictTopIso (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (A : CrystallineThickening S) :
    G.obj (op A) ≅ G.obj (op (A.restrictOpen ⊤)) :=
  G.mapIso (CrystallineThickening.isoRestrictOpenTop A).op

/-- **The canonical connection on the sections over an object `A = (U, T, δ)` of `Cris(X/S)`**:
a section `s` of `F` over `A` is read as the section of `F_T` over `T`, sent to
`∇(s) ∈ Γ(T, F_T ⊗ Ω_{T/S,δ})` by `...SmallSite.crystalConnection`, and read back in
`(F ⊗ Ω_{X/S})(A)` through `(F ⊗ Ω_{X/S})_T = F_T ⊗ Ω_{T/S,δ}`. -/
def crystalConnectionCrisApp (A : CrystallineThickening S) :
    (abelianSheaf F).obj.obj (op A) ⟶ (tensorDifferentialFormsSheaf F 1).obj.obj (op A) :=
  (abelianSheaf F).obj.map (A.restrictOpenHom ⊤).op ≫
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      (AddCommGrpCat.ofHom (crystalConnectionApp A hF ⊤)) ≫
    (tensorFormsAmbientIsoOne A).inv.app (op ⊤) ≫
      (restrictTopIso (tensorDifferentialFormsSheaf F 1).obj A).inv

/-- The defining property of `crystalConnectionCrisApp`: restricted to `A|_T`, it is the canonical
connection on `T`. -/
theorem crystalConnectionCrisApp_restrict (A : CrystallineThickening S)
    (s : (abelianSheaf F).obj.obj (op A)) :
    (tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
        (crystalConnectionCrisApp hF A s) =
      (tensorFormsAmbientIsoOne A).inv.app (op ⊤)
        (ULift.up (crystalConnectionApp A hF ⊤ (F.val.map (A.restrictOpenHom ⊤).op s.down))) :=
  ConcreteCategory.congr_hom (restrictTopIso (tensorDifferentialFormsSheaf F 1).obj A).inv_hom_id _

/-- The restriction to `A|_T` is injective. -/
theorem injective_restrictTop (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (A : CrystallineThickening S) :
    Function.Injective (G.map (A.restrictOpenHom ⊤).op) := fun x y h ↦ by
  have hx := ConcreteCategory.congr_hom (restrictTopIso G A).hom_inv_id x
  have hy := ConcreteCategory.congr_hom (restrictTopIso G A).hom_inv_id y
  exact hx.symm.trans ((congrArg (restrictTopIso G A).inv.hom h).trans hy)

/-- **The canonical connection is natural in the object of `Cris(X/S)`.** -/
theorem crystalConnectionCrisApp_naturality {A B : CrystallineThickening S} (g : B ⟶ A)
    (s : (abelianSheaf F).obj.obj (op A)) :
    crystalConnectionCrisApp hF B ((abelianSheaf F).obj.map g.op s) =
      (tensorDifferentialFormsSheaf F 1).obj.map g.op (crystalConnectionCrisApp hF A s) := by
  apply injective_restrictTop (tensorDifferentialFormsSheaf F 1).obj B
  refine (crystalConnectionCrisApp_restrict hF B _).trans ?_
  refine Eq.trans ?_ (presheaf_map_comp_apply _ _ _ _)
  have hsq := CrystallineThickening.restrictOpenMap_restrictOpenHom g ⊤
  refine Eq.trans ?_ (congrArg (fun k ↦ (tensorDifferentialFormsSheaf F 1).obj.map k.op
    (crystalConnectionCrisApp hF A s)) hsq)
  refine Eq.trans ?_ (presheaf_map_comp_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg ((tensorDifferentialFormsSheaf F 1).obj.map
    (CrystallineThickening.restrictOpenMap g ⊤).op) (crystalConnectionCrisApp_restrict hF A s)).symm
  refine Eq.trans ?_ (tensorFormsAmbientIsoOne_map g hF ⊤ _).symm
  refine congrArg (fun t ↦ (tensorFormsAmbientIsoOne B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤))
    (ULift.up t)) ?_
  refine Eq.trans ?_ (crystalTensorTransition_crystalConnectionApp g hF ⊤ _).symm
  refine congrArg (crystalConnectionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ ⊤)) ?_
  have e1 : F.val.map (B.restrictOpenHom ⊤).op (F.val.map g.op s.down) =
      F.val.map (B.restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ ⊤) ≫ g).op s.down :=
    (F.val.map_comp_apply g.op (B.restrictOpenHom ⊤).op s.down).symm
  have e2 : F.val.map (CrystallineThickening.restrictOpenMap g ⊤).op
      (F.val.map (A.restrictOpenHom ⊤).op s.down) =
      F.val.map (CrystallineThickening.restrictOpenMap g ⊤ ≫ A.restrictOpenHom ⊤).op s.down :=
    (F.val.map_comp_apply (A.restrictOpenHom ⊤).op
      (CrystallineThickening.restrictOpenMap g ⊤).op s.down).symm
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [hsq]

/-- **The canonical connection of a crystal, as a morphism of abelian sheaves
`∇ : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}` on `Cris(X/S)`.**  On the ambient scheme `T` of every object it
is the connection `p₁^* s - p₀^* s`, read through `(F ⊗ Ω_{X/S})_T = F_T ⊗ Ω_{T/S,δ}`
(`crystalConnectionCrisApp_restrict`). -/
@[stacks 07J6 "the canonical connection ∇ : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S} of a crystal F on Cris(X/S), \
a morphism of abelian sheaves: on every T it is p₁^* s - p₀^* s on the first-order thickening \
T' of 07J2, read through (F ⊗ Ω_{X/S})_T = F_T ⊗ Ω_{T/S,δ}"]
def crystalConnectionCris : abelianSheaf F ⟶ tensorDifferentialFormsSheaf F 1 :=
  ⟨{ app := fun A ↦ crystalConnectionCrisApp hF A.unop
     naturality := fun {A B} g ↦ by
       ext s
       exact crystalConnectionCrisApp_naturality hF g.unop s }⟩

end Connection

end Crystalline.GlobalCrystallineSituation.SmallSite

end

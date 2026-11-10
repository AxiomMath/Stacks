module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChangeOfC
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartBase
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleChartRefine
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChartRefine
public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.Chart
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.ComparisonComp

/-!
# The comparison on a chart does not change when the affine open shrinks
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

section Coherence

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- For morphisms `β : X ⟶ G`, `co : Lm ⟶ 𝟙_ C` and `φ : G ⟶ G'`, composing `(β ⊗ₘ co) ≫ ρ_G`
with `φ` equals `((β ≫ φ) ⊗ₘ co) ≫ ρ_G'`. -/
theorem tensor_rightUnitor_comp {X Lm G G' : C} (β : X ⟶ G) (co : Lm ⟶ 𝟙_ C) (φ : G ⟶ G') :
    ((β ⊗ₘ co) ≫ (ρ_ G).hom) ≫ φ = ((β ≫ φ) ⊗ₘ co) ≫ (ρ_ G').hom := by
  rw [tensorHom_def', tensorHom_def', Category.assoc, Category.assoc, Category.assoc,
    rightUnitor_naturality_assoc, rightUnitor_naturality]

end Coherence

section Generic

variable {X Y Z : Scheme.{u}}

/-- The pullback of a section over `V` to `p ⁻¹ᵁ V` is the value of the unit of the
pullback–pushforward adjunction on that section. -/
theorem pullbackSection_le_rfl (p : Y ⟶ X) (N : X.Modules) (V : X.Opens) (a : N.val.obj (op V)) :
    Scheme.Modules.pullbackSection p N V (p ⁻¹ᵁ V) le_rfl a =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N).val.app (op V) a := by
  unfold Scheme.Modules.pullbackSection
  rw [show (homOfLE (le_refl (p ⁻¹ᵁ V))).op = 𝟙 _ from Subsingleton.elim _ _,
    PresheafOfModules.map_id]
  rfl

/-- For `e : a = b`, the inverse of `pullbackCongr e` carries the pullback of a section along `b`
to its pullback along `a`. -/
theorem pullbackCongr_inv_pullbackSection {a b : Y ⟶ X} (e : a = b) (N : X.Modules) (U : X.Opens)
    (V : Y.Opens) (ha : V ≤ a ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ U) (x : N.val.obj (op U)) :
    ((Scheme.Modules.pullbackCongr e).inv.app N).val.app (op V)
        (Scheme.Modules.pullbackSection b N U V hb x) =
      Scheme.Modules.pullbackSection a N U V ha x := by
  subst e
  rfl

/-- The inverse of `pullbackComp f g` carries the pullback of a section along `f ≫ g` to the
pullback along `f` of its pullback along `g`. -/
theorem pullbackComp_inv_pullbackSection (f : Z ⟶ Y) (g : Y ⟶ X) (N : X.Modules) (U : X.Opens)
    (W : Y.Opens) (V : Z.Opens) (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U)
    (x : N.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).val.app (op V)
        (Scheme.Modules.pullbackSection (f ≫ g) N U V h x) =
      Scheme.Modules.pullbackSection f ((Scheme.Modules.pullback g).obj N) W V hf
        (Scheme.Modules.pullbackSection g N U W hg x) := by
  rw [← Scheme.Modules.pullbackSection_comp f g N U W V hg hf h x]
  change (((Scheme.Modules.pullbackComp f g).hom.app N ≫
    (Scheme.Modules.pullbackComp f g).inv.app N).val.app (op V)) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

end Generic

section Restrict

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  {U U' : s.base.affineOpens} (hUU' : U'.1 ≤ U.1) {d : ℕ} (c : s.sectionPieces U.1 d)

/-- The section `c` restricted to the smaller affine open. -/
def resC : s.sectionPieces U'.1 d := (s.algebra.piece (d : ℤ)).val.map (homOfLE hUU').op c

/-- Restricting the graded element `cHom U.1 c` to `U'` gives `cHom U'.1` of the restricted
section `resC hUU' c`. -/
theorem restrict_cHom :
    gradedSectionRestriction s U'.1 U.1 hUU' (cHom U.1 c) = cHom U'.1 (resC hUU' c) :=
  gradedSectionRestriction_of s U'.1 U.1 hUU' d c

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The transition of the chart sheaves carries `x / c^n` to `x|_{U'} / c|_{U'}^n`**, in the
fibre at a point. -/
theorem pushforwardModuleMap_fracElt (n : ℤ) (x : sectionModulePieces ℳ U.1 (n * d))
    (y : ProjectiveSpectrum (s.sectionRingGrading U'.1))
    (hy₁ : y ∈ ProjectiveSpectrum.basicOpen _ (gradedSectionRestriction s U'.1 U.1 hUU'
      (cHom U.1 c)))
    (hy₂ : y ∈ ProjectiveSpectrum.basicOpen _ (cHom U'.1 (resC hUU' c))) :
    Stacks.ProjModuleComparison.fibreMap (gradedSectionRestriction s U'.1 U.1 hUU')
        (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
        (sectionModuleRestrictₛₗ ℳ hUU') y
        (moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c)
          ⟨ProjectiveSpectrum.comapFun _ (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1
            hUU' U'.2 U.2) y, hy₁⟩ (fracElt ℳ U.1 c n x).1) =
      moduleToFiber (M := sectionModule ℳ U'.1) (s.sectionRingGrading U'.1)
        (cHom U'.1 (resC hUU' c)) ⟨y, hy₂⟩
        (fracElt ℳ U'.1 (resC hUU' c) n (sectionModuleRestrictPiece ℳ hUU' (n * d) x)).1 := by
  have e1 := fracElt_val ℳ U.1 c n x
  have e2 := fracElt_val ℳ U'.1 (resC hUU' c) n (sectionModuleRestrictPiece ℳ hUU' (n * d) x)
  refine (congrArg (fun z => Stacks.ProjModuleComparison.fibreMap
    (gradedSectionRestriction s U'.1 U.1 hUU')
    (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
    (sectionModuleRestrictₛₗ ℳ hUU') y
    (moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c)
      ⟨ProjectiveSpectrum.comapFun _ (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1
        hUU' U'.2 U.2) y, hy₁⟩ z)) e1).trans ?_
  refine Eq.trans ?_ (congrArg (moduleToFiber (M := sectionModule ℳ U'.1)
    (s.sectionRingGrading U'.1) (cHom U'.1 (resC hUU' c)) ⟨y, hy₂⟩) e2).symm
  rw [moduleToFiber_mk, moduleToFiber_mk]
  refine (Stacks.ProjModuleComparison.fibreMap_mk _ _ _ y _ _).trans ?_
  have hc := restrict_cHom hUU' c
  have hnum : sectionModuleRestrictₛₗ ℳ hUU'
      (cHom U.1 c ^ ex n • DirectSum.of (sectionModulePieces ℳ U.1) (n * d) x) =
      cHom U'.1 (resC hUU' c) ^ ex n • DirectSum.of (sectionModulePieces ℳ U'.1) (n * d)
        (sectionModuleRestrictPiece ℳ hUU' (n * d) x) := by
    rw [map_smulₛₗ, sectionModuleRestrictₛₗ_apply, sectionModuleRestrict_of, ← hc, map_pow]
    rfl
  congr 1
  apply Subtype.ext
  change s.sectionRingRestrict U'.1 U.1 hUU' (cHom U.1 c ^ n.toNat) = _
  exact (map_pow (s.sectionRingRestrict U'.1 U.1 hUU') (cHom U.1 c) n.toNat).trans
    (congrArg (· ^ n.toNat) hc)

/-- The comparison of the chart sheaves `r^*ℳ̃(U) ⟶ ℳ̃(U')`. -/
abbrev chartMap : (Scheme.Modules.pullback (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).obj
      (moduleChart ℳ U) ⟶ moduleChart ℳ U' :=
  Stacks.ProjModuleComparison.moduleMap (gradedSectionRestriction s U'.1 U.1 hUU')
    (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
    (sectionModuleRestrictₛₗ ℳ hUU') (sectionModuleRestrictₛₗ_mem_grading ℳ hUU')

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The comparison of the chart sheaves on the unit of the adjunction** is the pointwise
comparison. -/
theorem chartMap_unit (V : (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).Opens)
    (a : (moduleChart ℳ U).val.obj (op V)) :
    (chartMap ℳ hUU').val.app (op (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 ⁻¹ᵁ V))
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).unit.app (moduleChart ℳ U)).val.app
            (op V) a) =
      (Stacks.ProjModuleComparison.pushforwardModuleMap (gradedSectionRestriction s U'.1 U.1 hUU')
        (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
        (sectionModuleRestrictₛₗ ℳ hUU') (sectionModuleRestrictₛₗ_mem_grading ℳ hUU')).val.app
          (op V) a :=
  congrArg (fun t => t.val.app (op V) a)
    (Stacks.ProjModuleComparison.transpose_moduleMap (gradedSectionRestriction s U'.1 U.1 hUU')
      (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
      (sectionModuleRestrictₛₗ ℳ hUU') (sectionModuleRestrictₛₗ_mem_grading ℳ hUU'))

/-- The basic open `D₊(c|_{U'})` of the smaller chart lies in the preimage of `D₊(c)` under the
inclusion `projInclusionMap`. -/
theorem basicOpen_le_preimage :
    Proj.basicOpen (s.sectionRingGrading U'.1) (cHom U'.1 (resC hUU' c)) ≤
      projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 ⁻¹ᵁ
        Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) := by
  rw [← restrict_cHom hUU' c]
  exact le_rfl

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The transition of the chart sheaves carries `x / c^n` to `x|_{U'} / c|_{U'}^n`**, on the
sections over `D₊(c|_{U'})`. -/
theorem restrict_pushforward_fracElt (n : ℤ) (x : sectionModulePieces ℳ U.1 (n * d)) :
    (moduleChart ℳ U').val.map (homOfLE (basicOpen_le_preimage hUU' c)).op
        ((Stacks.ProjModuleComparison.pushforwardModuleMap
          (gradedSectionRestriction s U'.1 U.1 hUU')
          (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
          (sectionModuleRestrictₛₗ ℳ hUU') (sectionModuleRestrictₛₗ_mem_grading ℳ hUU')).val.app
            (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))
            (toChart ℳ U c (fracElt ℳ U.1 c n x))) =
      toChart ℳ U' (resC hUU' c)
        (fracElt ℳ U'.1 (resC hUU' c) n (sectionModuleRestrictPiece ℳ hUU' (n * d) x)) :=
  Subtype.ext <| funext fun y =>
    pushforwardModuleMap_fracElt ℳ hUU' c n x y.1 (basicOpen_le_preimage hUU' c y.2) y.2

/-- The preimage of `D₊(c)` under the inclusion `projInclusionMap` is the basic open
`D₊(c|_{U'})`. -/
theorem preimage_basicOpen_eq :
    projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 ⁻¹ᵁ
        Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) =
      Proj.basicOpen (s.sectionRingGrading U'.1) (cHom U'.1 (resC hUU' c)) := by
  rw [← restrict_cHom hUU' c]
  rfl

variable {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (hf' : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U'.1)
  (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  (g' : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U'.1))
  (hgg : g' ≫ projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 = g)

include hg hgg in
/-- If `g` lands in `D₊(c)` and `g' ≫ projInclusionMap = g`, then `g'` lands in `D₊(c|_{U'})`. -/
theorem hg_restrict :
    (⊤ : T.Opens) ≤
      g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1) (cHom U'.1 (resC hUU' c)) := by
  intro t ht
  have h1 : g.base t ∈ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) := hg ht
  rw [← hgg] at h1
  change (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2).base (g'.base t) ∈ _ at h1
  change g'.base t ∈ Proj.basicOpen (s.sectionRingGrading U'.1) (cHom U'.1 (resC hUU' c))
  rw [← preimage_basicOpen_eq hUU' c]
  exact h1

variable (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))
  (hgf' : ∀ r : s.base.ringCatSheaf.obj.obj (op U'.1),
    f.appLE U'.1 ⊤ hf' r = g'.appLE _ ⊤ (hg_restrict hUU' c g hg g' hgg)
      (Proj.awayToSection _ _ (baseFrac U' (resC hUU' c) r)))

/-- **The comparison `β` on the smaller chart is the comparison on the larger one followed by the
transition of the chart sheaves.** -/
theorem beta_restrict (n : ℤ) :
    beta ℳ U' (resC hUU' c) f hf' g' (hg_restrict hUU' c g hg g' hgg) hgf' n =
      beta ℳ U c f hf g hg hgf n ≫
        (Scheme.Modules.pullbackCongr hgg).inv.app (moduleChart ℳ U) ≫
          (Scheme.Modules.pullbackComp g' (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).inv.app
            (moduleChart ℳ U) ≫ (Scheme.Modules.pullback g').map (chartMap ℳ hUU') := by
  refine AffineOpenHomRecovery.hom_ext f U.1 hf (ℳ.piece (n * d)) U.2
    ((Scheme.Modules.pullback g').obj (moduleChart ℳ U')) fun x => ?_
  have hg' := hg_restrict hUU' c g hg g' hgg
  have hgr : (⊤ : T.Opens) ≤ (g' ≫ projInclusionMap s U'.1 U.1 hUU' U'.2 U.2) ⁻¹ᵁ
      Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) := hgg ▸ hg
  have hg'r : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 ⁻¹ᵁ
      Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)) := hgr
  have l1 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le f (ℳ.piece (n * d))
    hUU' ⊤ hf hf' x
  have l2 := beta_pullbackSection ℳ U' (resC hUU' c) f hf' g' hg' hgf' n
    (sectionModuleRestrictPiece ℳ hUU' (n * d) x)
  have l3 := fracPull_apply ℳ U' (resC hUU' c) g' hg' n
    (sectionModuleRestrictPiece ℳ hUU' (n * d) x)
  have l4 := fracChart_eq ℳ U' (resC hUU' c) n (sectionModuleRestrictPiece ℳ hUU' (n * d) x)
  have r1 := beta_pullbackSection ℳ U c f hf g hg hgf n x
  have r2 := fracPull_apply ℳ U c g hg n x
  have r3 := fracChart_eq ℳ U c n x
  have r4 := pullbackCongr_inv_pullbackSection hgg (moduleChart ℳ U) _ ⊤ hgr hg
    (toChart ℳ U c (fracElt ℳ U.1 c n x))
  have r5 := pullbackComp_inv_pullbackSection g' (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)
    (moduleChart ℳ U) _ _ ⊤ le_rfl hg'r hgr (toChart ℳ U c (fracElt ℳ U.1 c n x))
  have r6 := Scheme.Modules.pullbackSection_naturality g' (chartMap ℳ hUU') _ ⊤ hg'r
    (Scheme.Modules.pullbackSection (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)
      (moduleChart ℳ U) _ _ le_rfl (toChart ℳ U c (fracElt ℳ U.1 c n x)))
  have r7 := pullbackSection_le_rfl (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)
    (moduleChart ℳ U) _ (toChart ℳ U c (fracElt ℳ U.1 c n x))
  have r8 := chartMap_unit ℳ hUU' _ (toChart ℳ U c (fracElt ℳ U.1 c n x))
  have r9 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le g' (moduleChart ℳ U')
    (basicOpen_le_preimage hUU' c) ⊤ hg'r hg'
    ((Stacks.ProjModuleComparison.pushforwardModuleMap
          (gradedSectionRestriction s U'.1 U.1 hUU')
          (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
          (sectionModuleRestrictₛₗ ℳ hUU') (sectionModuleRestrictₛₗ_mem_grading ℳ hUU')).val.app
            (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))
            (toChart ℳ U c (fracElt ℳ U.1 c n x)))
  have r10 := restrict_pushforward_fracElt ℳ hUU' c n x
  have L := (congrArg (fun z => (beta ℳ U' (resC hUU' c) f hf' g' hg' hgf' n).val.app (op ⊤) z)
    l1.symm).trans (l2.trans (l3.trans (congrArg (Scheme.Modules.pullbackSection g'
      (moduleChart ℳ U') _ ⊤ hg') l4)))
  refine L.trans ?_
  change _ = ((Scheme.Modules.pullback g').map (chartMap ℳ hUU')).val.app (op ⊤)
    (((Scheme.Modules.pullbackComp g' (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).inv.app
      (moduleChart ℳ U)).val.app (op ⊤)
      (((Scheme.Modules.pullbackCongr hgg).inv.app (moduleChart ℳ U)).val.app (op ⊤)
        ((beta ℳ U c f hf g hg hgf n).val.app (op ⊤)
          (Scheme.Modules.pullbackSection f (ℳ.piece (n * d)) U.1 ⊤ hf x))))
  refine Eq.trans ?_ (congrArg (fun z =>
    ((Scheme.Modules.pullback g').map (chartMap ℳ hUU')).val.app (op ⊤)
      (((Scheme.Modules.pullbackComp g' (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).inv.app
        (moduleChart ℳ U)).val.app (op ⊤)
        (((Scheme.Modules.pullbackCongr hgg).inv.app (moduleChart ℳ U)).val.app (op ⊤) z)))
    (r1.trans (r2.trans (congrArg (Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg)
      r3)))).symm
  refine Eq.trans ?_ (congrArg (fun z =>
    ((Scheme.Modules.pullback g').map (chartMap ℳ hUU')).val.app (op ⊤)
      (((Scheme.Modules.pullbackComp g' (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).inv.app
        (moduleChart ℳ U)).val.app (op ⊤) z)) r4).symm
  refine Eq.trans ?_ (congrArg (fun z =>
    ((Scheme.Modules.pullback g').map (chartMap ℳ hUU')).val.app (op ⊤) z) r5).symm
  refine Eq.trans ?_ r6.symm
  refine Eq.trans ?_ (congrArg (Scheme.Modules.pullbackSection g' (moduleChart ℳ U') _ ⊤ hg'r)
    ((congrArg (fun z => (chartMap ℳ hUU').val.app _ z) r7).trans r8)).symm
  refine Eq.trans ?_ r9
  exact congrArg (Scheme.Modules.pullbackSection g' (moduleChart ℳ U') _ ⊤ hg') r10.symm

variable {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (w : (LaurentSections.Ring L (op ⊤))ˣ)
  (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        LaurentSections.pw w i)
  (hCP' : ∀ (i : ℕ) (a : s.sectionPieces U'.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf').op (ψ.sectionHom i (op U'.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from
        kappaSec U' (resC hUU' c) g' (hg_restrict hUU' c g hg g' hgg) i a) • LaurentSections.pw w i)
  (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
    DirectSum.of _ (-1) τ)
  (hd : 0 < d)

/-- **The comparison on the larger chart, followed by the chart transition, is the comparison on
the smaller chart.** -/
theorem chartIso_restrict :
    (chartIso ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).hom ≫
        (Scheme.Modules.pullbackCongr hgg).inv.app (moduleChart ℳ U) ≫
          (Scheme.Modules.pullbackComp g' (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).inv.app
            (moduleChart ℳ U) ≫ (Scheme.Modules.pullback g').map (chartMap ℳ hUU') =
      (chartIso ℳ U' (resC hUU' c) f hf' g' (hg_restrict hUU' c g hg g' hgg) hgf' ψ w hCP' hw hw'
        hd).hom :=
  (Twisting.existsUnique_hom (ℳ.toGradedModule s.mul_comm) ψ (tgt ℳ U' g')
    (bmap ℳ U' (resC hUU' c) f hf' g' (hg_restrict hUU' c g hg g' hgg) hgf' w)
    (bmap_balanced ℳ U' (resC hUU' c) f hf' g' (hg_restrict hUU' c g hg g' hgg) hgf' ψ w hCP'
      hw hw' hd)).unique
    (fun n => by
      rw [← Category.assoc, pureTensor_chartIso_hom]
      unfold bmap
      refine (tensor_rightUnitor_comp _ _ _).trans ?_
      exact congrArg (fun z => (z ⊗ₘ LaurentSections.coord w n) ≫ (ρ_ _).hom)
        (beta_restrict ℳ hUU' c f hf hf' g hg g' hgg hgf hgf' n).symm)
    (pureTensor_chartIso_hom ℳ U' (resC hUU' c) f hf' g' (hg_restrict hUU' c g hg g' hgg) hgf' ψ
      w hCP' hw hw' hd)

end Restrict

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end

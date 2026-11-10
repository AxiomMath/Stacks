module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ClassifyingData
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TwistQuadrupleChart

/-!
# The classifying morphism over a chart of the base

Let `(f : T → S, d, L, ψ)` be a quadruple whose morphism `f` factors through an affine open `U` of
the base. This file computes the morphism `h : T ⟶ Proj_S(𝒜)` the quadruple classifies: **it is
the morphism of [Stacks, Tag 01N8] attached to the Veronese family of the quadruple over `U`,
read into `Proj 𝒜(U)` and followed by the chart of `U`.**

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom_eq_of_factor`: the formula.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.NonvanishingOpen (nonvanishingOpen)
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

variable (s : Stacks.RelativeProj.Situation.{u})

/-- The invertible module of a quadruple is invertible in the spelling of
`Stacks.Ample.IsInvertibleModule`, which the Veronese families of [Stacks, Tag 01N8] use. -/
theorem Quadruple.isInvertibleModule_L {S T : Scheme.{u}} {f : T ⟶ S}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    (P : Quadruple f A d) : Stacks.Ample.IsInvertibleModule T P.L :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ P.isInvertible

/-- `Quadruple.isInvertibleModule_L` for the quadruples of a situation, at the spelling
`s.algebra` instance search meets. -/
theorem Quadruple.isInvertibleModule_situation {Y : Scheme.{u}} {f : Y ⟶ s.base} {d : ℤ}
    (P : Quadruple f s.algebra d) : Stacks.Ample.IsInvertibleModule Y P.L :=
  Quadruple.isInvertibleModule_L P

attribute [local instance] Quadruple.isInvertibleModule_situation


/-- An open of a scheme that is the whole scheme has an epimorphic inclusion. -/
theorem epi_ι_of_eq_top {Y : Scheme.{u}} (o : Y.Opens) (h : o = ⊤) : Epi o.ι := by
  subst h
  exact (Scheme.topIso Y).isIso_hom.epi_of_iso

/-- **The classifying morphism of a quadruple whose morphism factors through an affine open `U`
of the base**: it is the chart-wise morphism of the chart-wise class of the quadruple at `U`. -/
theorem classifyingHom_eq_chartHom {d : ℕ} (hd : 0 < d) {Y : Scheme.{u}}
    (U : s.base.Opens) (hU : IsAffineOpen U) (gU : Y ⟶ U.toScheme)
    (P : Quadruple (gU ≫ U.ι) s.algebra (d : ℤ)) :
    classifyingHom s (by exact_mod_cast hd) P =
      Fd.chartHom (sheafGradedAlgebra s) U (relativeProjData s) hU hd Y
        (Fd.chartClass (sheafGradedAlgebra s) U gU (Quotient.mk _ P)) := by
  set A := sheafGradedAlgebra s
  set η0 := Fd.chartClass A U gU (Quotient.mk (Quadruple.setoid (gU ≫ U.ι) (situationAlgebra A)
    (d : ℤ)) P)
  set ξ : Fd (situationAlgebra A) (d : ℤ) Y := Fd.mk (gU ≫ U.ι) P
  have hη : Fd.chartClassInv A U (Fd.pullback (ξ.1 ⁻¹ᵁ U).ι η0) =
      Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ := by
    rw [Fd.chartClassInv_pullback]
    exact congrArg (Fd.pullback _) (Fd.chartClassInv_chartClass A U gU _)
  have h1 := Fd.ι_homDegreeOpen A (relativeProjData s) hd ξ U hU _ hη
  rw [Fd.chartHom_pullback] at h1
  have := epi_ι_of_eq_top (ξ.1 ⁻¹ᵁ U) (top_unique fun y _ => (gU.base y).2)
  change Fd.homDegreeOpen A (relativeProjData s) hd ξ ≫ ((relativeProjData s).degreeOpen d).ι = _
  exact (cancel_epi (ξ.1 ⁻¹ᵁ U).ι).1 h1

/-- The chart-wise quadruple at `U` of a quadruple whose morphism factors through `U`: the base
change of [Stacks, Tag 01NT] along the inclusion of `U` followed by the transport to the
restriction spelling. -/
abbrev chartQuadruple {d : ℕ} {Y : Scheme.{u}} (U : s.base.Opens) (gU : Y ⟶ U.toScheme)
    (P : Quadruple (gU ≫ U.ι) s.algebra (d : ℤ)) :
    Quadruple gU (situationAlgebra ((sheafGradedAlgebra s).restrict U.ι)) (d : ℤ) :=
  (P.baseChangeDown U.ι gU (situationAlgebra (sheafGradedAlgebra s)) (d : ℤ)).algebraTransport
    (unitalHomInverse (restrictPullbackUnitalHom (sheafGradedAlgebra s) U.ι)
      (isIso_restrictPullbackUnitalHom_app_forall (sheafGradedAlgebra s) U.ι))
    (isIso_unitalHomInverse_app (restrictPullbackUnitalHom (sheafGradedAlgebra s) U.ι)
      (isIso_restrictPullbackUnitalHom_app_forall (sheafGradedAlgebra s) U.ι))

/-- **The classifying morphism over a chart of the base is the morphism of [Stacks, Tag 01N8]**
attached to the Veronese family of the chart-wise quadruple, read at the grading of `𝒜(U)`, into
`Proj 𝒜(U)` and followed by the chart of `U`. -/
theorem exists_classifyingHom_eq {d : ℕ} (hd : 0 < d) {Y : Scheme.{u}}
    (U : s.base.Opens) (hU : IsAffineOpen U) (gU : Y ⟶ U.toScheme)
    (P : Quadruple (gU ≫ U.ι) s.algebra (d : ℤ)) :
    ∃ (ψ : VeroneseSections ((sheafGradedAlgebra s).grading U) d P.L)
      (_ : HEq (veroneseSections (chartQuadruple s U gU P).twisting) ψ)
      (hgen : ⨆ g : (sheafGradedAlgebra s).grading U d,
        nonvanishingOpen Y P.L (psiSection ((sheafGradedAlgebra s).grading U) ψ g) = ⊤),
      classifyingHom s (by exact_mod_cast hd) P =
        toProj ((sheafGradedAlgebra s).grading U)
            (Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
              ((sheafGradedAlgebra s).grading U) hd ψ hgen) ≫
          (relativeProjData s).chart U hU := by
  set A := sheafGradedAlgebra s
  have : IsAffine U.toScheme := hU
  obtain ⟨ψ, hψ⟩ := exists_veroneseSections_restrict A U (L := P.L) U.ι_image_top
    (veroneseSections (chartQuadruple s U gU P).twisting)
  have hgen := iSup_nonvanishingOpen_psiSection_restrict_heq A U (L := P.L) U.ι_image_top
    (veroneseSections (chartQuadruple s U gU P).twisting) ψ hψ
    (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top (B := A.restrict U.ι) (d := d)
      (fun n => (A.restrict U.ι).isQuasicoherent n) (chartQuadruple s U gU P))
  refine ⟨ψ, hψ, hgen, ?_⟩
  refine (classifyingHom_eq_chartHom s hd U hU gU P).trans ?_
  refine (Fd.chartHom_eq_toProj_comp_chart A U (relativeProjData s) hU hd Y _).trans ?_
  exact congrArg (· ≫ (relativeProjData s).chart U hU)
    (Fd.toProj_chartEquiv_mk A U hU hd gU (chartQuadruple s U gU P) rfl ψ hψ hgen)

/-- **The Veronese family of the chart-wise quadruple, on a section over `U`**: it is the section
of `L^{⊗ n}` the quadruple's own `ψ` assigns, restricted to the whole test scheme and read in
the iterated tensor power. -/
theorem toFun_eq_sectionHom {d : ℕ} {Y : Scheme.{u}} (U : s.base.Opens) (gU : Y ⟶ U.toScheme)
    (P : Quadruple (gU ≫ U.ι) s.algebra (d : ℤ))
    (ψ : VeroneseSections ((sheafGradedAlgebra s).grading U) d P.L)
    (hψ : HEq (veroneseSections (chartQuadruple s U gU P).twisting) ψ) (n : ℕ)
    (a : (sheafGradedAlgebra s).sectionPieces U (n * d))
    (e : (opensMap (ringedSpaceHom (gU ≫ U.ι))).op.obj (op U) ⟶ op (⊤ : Y.Opens)) :
    ψ.toFun n ⟨DirectSum.of _ (n * d) a, (sheafGradedAlgebra s).of_mem_grading U a⟩ =
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L n).inv.app ⊤
        (((laurent P.L).piece (n : ℤ)).val.restrictₛₗ e
          (P.twisting.sectionHom (n : ℤ) (op U) a)) := by
  obtain ⟨x, hx⟩ := RelativeProjTwistChartBridge.exists_restrict_grading_heq U U U.ι_image_top
    (⟨DirectSum.of _ (n * d) a, (sheafGradedAlgebra s).of_mem_grading U a⟩ :
      (sheafGradedAlgebra s).grading U (n * d))
  have e1 := (veroneseSections_restrict_toFun_heq (sheafGradedAlgebra s) U _ U.ι_image_top _ ψ
    hψ n x _ hx).symm
  have hxU := RelativeProjTwistChartBridge.component_eq_resPiece_of_heq U.ι_image_top x _ hx
  refine e1.trans ((veroneseSections_chartTwisting' (sheafGradedAlgebra s) U gU P.twisting n x
    (homOfLE (top_le_preimage_image_top U gU)).op).trans ?_)
  refine congrArg
    (fun z => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L n).inv.app ⊤ z) ?_
  have h2 := sectionHom_resPiece (sheafGradedAlgebra s) P.twisting n (U.ι_image_top).le a
  have hyU : ((⟨DirectSum.of _ (n * d) a, (sheafGradedAlgebra s).of_mem_grading U a⟩ :
      (sheafGradedAlgebra s).grading U (n * d)) : (sheafGradedAlgebra s).sectionRing U) (n * d) =
      a := DirectSum.of_eq_same _ _
  refine (congrArg (fun z => ((laurent P.L).piece (n : ℤ)).val.restrictₛₗ
    (homOfLE (top_le_preimage_image_top U gU)).op
    (P.twisting.sectionHom (n : ℤ) (op (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) z))
    (hxU.trans (congrArg _ hyU))).trans ?_
  refine (congrArg (fun z => ((laurent P.L).piece (n : ℤ)).val.restrictₛₗ
    (homOfLE (top_le_preimage_image_top U gU)).op z) h2).trans ?_
  exact (PresheafOfModules.map_comp_apply _ _ _ _).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _)

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end

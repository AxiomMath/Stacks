module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChangeOfUParts
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Independence

/-!
# The comparison of a chart datum does not depend on the datum

A chart datum over an affine open `U` of the base restricts to one over any smaller affine open
`U'` still containing the image of `f`, with the same comparison `ℳ̃_T ≅ h^*ℳ̃`
(`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_hom_eq_restrict`). With the
independence of the section `c` on a fixed affine open this shows that any two chart data of the
same morphism give the same comparison
(`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_eq`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum

private theorem comp_inv_eq {C : Type*} [Category C] {P Q R S : C} (a : P ⟶ Q) (t : R ≅ Q)
    (t' : R ≅ S) (x : Q ⟶ S) (hx : t.inv ≫ t'.hom = x) : a ≫ t.inv = (a ≫ x) ≫ t'.inv := by
  rw [← hx]
  simp

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {T : Scheme.{u}} {f : T ⟶ s.base} {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s} (hd : 0 < d)

/-- A chart datum over `U` restricts to a smaller affine open `U'`, with the same comparison. -/
theorem iso_hom_eq_restrict (D : ChartDatum f ψ h) (hπ : h ≫ relativeProjToBase s = f)
    (U' : s.base.affineOpens) (hU : U'.1 ≤ D.U.1) (hf' : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U'.1)
    (g' : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U'.1))
    (fac' : h = g' ≫ relativeProjChart s U') :
    ∃ (hg' : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1)
        (cHom U'.1 (resC hU D.c)))
      (hgf' : ∀ r : s.base.ringCatSheaf.obj.obj (op U'.1),
        f.appLE U'.1 ⊤ hf' r = g'.appLE _ ⊤ hg'
          (Proj.awayToSection _ _ (baseFrac U' (resC hU D.c) r)))
      (hCP' : ∀ (i : ℕ) (a : s.sectionPieces U'.1 (i * d)),
        ((laurent L).piece i).val.map (homOfLE hf').op (ψ.sectionHom i (op U'.1) a) =
          (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from
            kappaSec U' (resC hU D.c) g' hg' i a) • LaurentSections.pw D.w i),
      (D.iso ℳ hd).hom =
        (chartIso ℳ U' (resC hU D.c) f hf' g' hg' hgf' ψ D.w hCP' D.hw D.hw' hd).hom ≫
          (moduleSheafPullbackChartIso ℳ U' g' fac').inv := by
  have hgg : g' ≫ projInclusionMap s U'.1 D.U.1 hU U'.2 D.U.2 = D.g := by
    refine (cancel_mono (relativeProjChart s D.U)).mp ?_
    rw [Category.assoc, relativeProjChart_transition s hU, ← fac']
    exact D.fac
  have hg' := hg_restrict hU D.c D.g D.hg g' hgg
  have hgf' : ∀ r : s.base.ringCatSheaf.obj.obj (op U'.1),
      f.appLE U'.1 ⊤ hf' r = g'.appLE _ ⊤ hg'
        (Proj.awayToSection _ _ (baseFrac U' (resC hU D.c) r)) :=
    hgf_of_fac U' (resC hU D.c) hd f hπ g' fac' hf' hg'
  have hCP' := hCP_restrict hU D.c f D.hf hf' hgg D.hg hg' D.hgf hgf' ψ D.w D.hCP
  refine ⟨hg', hgf', hCP', ?_⟩
  have hC := chartIso_restrict ℳ hU D.c f D.hf hf' D.g D.hg g' hgg D.hgf hgf' ψ D.w D.hCP hCP'
    D.hw D.hw' hd
  have hP2 := moduleSheafPullbackChartIso_restrict ℳ hU hgg D.fac fac'
  have hX : (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv ≫
      (moduleSheafPullbackChartIso ℳ U' g' fac').hom =
        (Scheme.Modules.pullbackCongr hgg).inv.app (moduleChart ℳ D.U) ≫
          (Scheme.Modules.pullbackComp g' (projInclusionMap s U'.1 D.U.1 hU U'.2 D.U.2)).inv.app
            (moduleChart ℳ D.U) ≫ (Scheme.Modules.pullback g').map (chartMap ℳ hU) := by
    rw [hP2, Iso.inv_hom_id_assoc]
  rw [iso_hom, ← hC]
  exact comp_inv_eq _ _ _ _ hX

/-- The comparison of a chart datum is unchanged by restricting it to a smaller affine open. -/
theorem shrinkBase : ShrinkBase ℳ hd :=
  fun D hπ U' hU hf' g' fac' => iso_hom_eq_restrict ℳ hd D hπ U' hU hf' g' fac'

/-- Any two chart data of the same morphism give the same comparison `ℳ̃_T ≅ h^*ℳ̃`. -/
theorem iso_eq (D₁ D₂ : ChartDatum f ψ h) (hπ : h ≫ relativeProjToBase s = f) :
    D₁.iso ℳ hd = D₂.iso ℳ hd :=
  Iso.ext (iso_hom_eq (shrinkBase ℳ hd) D₁ D₂ hπ)

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum

end

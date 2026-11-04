module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChangeOfC
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.DatumPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.LocalHom
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.PullbackCover
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing

/-!
# The comparison of a chart datum does not depend on the chart datum

For a quadruple `(f : T → S, d, L, ψ)` and a morphism `h : T ⟶ Proj_S(𝒜)` over `S`, any two chart
data give the same comparison `ℳ̃_T ≅ h^*ℳ̃`. Locally on `T` both data restrict to one affine open
`U₃` of the base inside their two affine opens, and to one factorization of `h` through the chart
over `U₃`; there the two comparisons differ only in the section `c`, on which the comparison does
not depend (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.chartIso_change`). The
comparisons are compatible with restriction to an open of `T`
(`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_pullback`), and a morphism of
sheaves of modules is determined by its restrictions to the members of an open cover.

The passage from a chart datum to its restriction to a smaller affine open of the base is the
statement `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.ShrinkBase`, which this
file takes as an argument.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_hom_eq_of_le`: two chart
  data whose affine opens both contain an affine open `U₃` over which `f` lies and through whose
  chart `h` factors give the same comparison.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_hom_eq`: **any two chart data
  give the same comparison.**
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

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

private alias solve := solve_conj

namespace ChartDatum

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {d : ℕ} (hd : 0 < d)

/-- **Shrinking the affine open of the base of a chart datum.** For a chart datum `D` of a
morphism `h` over `f`, an affine open `U'` inside the affine open of `D` over which `f` lies, and a
factorization `h = g' ≫ chart U'`, the comparison of `D` is the chart comparison over `U'` for the
restricted section `c|_{U'}` and the same unit, followed by the identification
`g'^*ℳ̃(U') ≅ h^*ℳ̃`. -/
def ShrinkBase : Prop :=
  ∀ {T : Scheme.{u}} {f : T ⟶ s.base} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s} (D : ChartDatum f ψ h)
    (_ : h ≫ relativeProjToBase s = f) (U' : s.base.affineOpens) (hU : U'.1 ≤ D.U.1)
    (hf' : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U'.1)
    (g' : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U'.1))
    (fac' : h = g' ≫ relativeProjChart s U'),
    ∃ (hg' : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1)
        (cHom U'.1 ((s.algebra.piece (d : ℤ)).val.map (homOfLE hU).op D.c)))
      (hgf' : ∀ r : s.base.ringCatSheaf.obj.obj (op U'.1),
        f.appLE U'.1 ⊤ hf' r = g'.appLE _ ⊤ hg'
          (Proj.awayToSection _ _
            (baseFrac U' ((s.algebra.piece (d : ℤ)).val.map (homOfLE hU).op D.c) r)))
      (hCP' : ∀ (i : ℕ) (a : s.sectionPieces U'.1 (i * d)),
        ((laurent L).piece i).val.map (homOfLE hf').op (ψ.sectionHom i (op U'.1) a) =
          (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from
            kappaSec U' ((s.algebra.piece (d : ℤ)).val.map (homOfLE hU).op D.c) g' hg' i a) •
            LaurentSections.pw D.w i),
      (D.iso ℳ hd).hom =
        (chartIso ℳ U' ((s.algebra.piece (d : ℤ)).val.map (homOfLE hU).op D.c) f hf' g' hg' hgf'
          ψ D.w hCP' D.hw D.hw' hd).hom ≫ (moduleSheafPullbackChartIso ℳ U' g' fac').inv

variable {ℳ hd} {T : Scheme.{u}} {f : T ⟶ s.base}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s}

/-- **Two chart data over a common smaller affine open give the same comparison.** -/
theorem iso_hom_eq_of_le (H : ShrinkBase ℳ hd) (D₁ D₂ : ChartDatum f ψ h)
    (hπ : h ≫ relativeProjToBase s = f) (U₃ : s.base.affineOpens) (h₁ : U₃.1 ≤ D₁.U.1)
    (h₂ : U₃.1 ≤ D₂.U.1) (hf₃ : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U₃.1)
    (g₃ : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U₃.1))
    (fac₃ : h = g₃ ≫ relativeProjChart s U₃) :
    (D₁.iso ℳ hd).hom = (D₂.iso ℳ hd).hom := by
  obtain ⟨hg₁, hgf₁, hCP₁, e₁⟩ := H D₁ hπ U₃ h₁ hf₃ g₃ fac₃
  obtain ⟨hg₂, hgf₂, hCP₂, e₂⟩ := H D₂ hπ U₃ h₂ hf₃ g₃ fac₃
  rw [e₁, e₂, chartIso_change ℳ U₃ _ _ f hf₃ g₃ hg₁ hg₂ hgf₁ hgf₂ ψ D₁.w D₂.w hCP₁ hCP₂ D₁.hw
    D₁.hw' D₂.hw D₂.hw' hd]

/-- The pullback of the comparison of a chart datum along `k`, through the comparison of the
pulled-back datum. -/
theorem pullback_map_iso_hom (D : ChartDatum f ψ h) {T' : Scheme.{u}} (k : T' ⟶ T) :
    (Scheme.Modules.pullback k).map (D.iso ℳ hd).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k ψ).hom ≫
        ((D.pullback k).iso ℳ hd).hom ≫
          (Scheme.Modules.pullbackComp k h).inv.app (moduleSheaf ℳ) :=
  solve (C := T'.Modules) _ _ ((Scheme.Modules.pullbackComp k h).app (moduleSheaf ℳ)) _
    (iso_pullback ℳ D hd k)

/-- The pullback of a chart datum along `k` has the same affine open of the base. -/
theorem pullback_U (D : ChartDatum f ψ h) {T' : Scheme.{u}} (k : T' ⟶ T) :
    (D.pullback k).U = D.U := rfl

/-- **Two chart data pulled back along `k` to a scheme over a common smaller affine open have the
same pulled-back comparison.** -/
theorem pullback_map_iso_hom_eq (H : ShrinkBase ℳ hd) (D₁ D₂ : ChartDatum f ψ h)
    (hπ : h ≫ relativeProjToBase s = f) {T' : Scheme.{u}} (k : T' ⟶ T)
    (U₃ : s.base.affineOpens) (h₁ : U₃.1 ≤ D₁.U.1) (h₂ : U₃.1 ≤ D₂.U.1)
    (hf₃ : (⊤ : T'.Opens) ≤ (k ≫ f) ⁻¹ᵁ U₃.1)
    (g₃ : T' ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U₃.1))
    (fac₃ : k ≫ h = g₃ ≫ relativeProjChart s U₃) :
    (Scheme.Modules.pullback k).map (D₁.iso ℳ hd).hom =
      (Scheme.Modules.pullback k).map (D₂.iso ℳ hd).hom := by
  have hπ' : (k ≫ h) ≫ relativeProjToBase s = k ≫ f := by rw [Category.assoc, hπ]
  have e := iso_hom_eq_of_le H (D₁.pullback k) (D₂.pullback k) hπ' U₃
    ((pullback_U D₁ k).symm ▸ h₁) ((pullback_U D₂ k).symm ▸ h₂) hf₃ g₃ fac₃
  rw [pullback_map_iso_hom, pullback_map_iso_hom, e]

/-- A point of `T` has an affine open of the base around its image inside the affine opens of
two chart data. -/
theorem exists_affineOpen_le (D₁ D₂ : ChartDatum f ψ h) (t : T) :
    ∃ U₃ : s.base.affineOpens, f t ∈ U₃.1 ∧ U₃.1 ≤ D₁.U.1 ∧ U₃.1 ≤ D₂.U.1 := by
  have ht : f t ∈ D₁.U.1 ⊓ D₂.U.1 := ⟨D₁.hf trivial, D₂.hf trivial⟩
  obtain ⟨U', hU', hx, hle⟩ := (Opens.isBasis_iff_nbhd.mp s.base.isBasis_affineOpens) ht
  exact ⟨⟨U', hU'⟩, hx, hle.trans inf_le_left, hle.trans inf_le_right⟩

/-- The restriction of `h` to the part of `T` over an affine open `U₃` of the base lies in the
chart over `U₃`. -/
theorem range_subset_chart (hπ : h ≫ relativeProjToBase s = f) (U₃ : s.base.affineOpens) :
    Set.range ((f ⁻¹ᵁ U₃.1).ι ≫ h).base ⊆ Set.range (relativeProjChart s U₃).base := by
  rintro _ ⟨x, rfl⟩
  have hx : (relativeProjToBase s).base (((f ⁻¹ᵁ U₃.1).ι ≫ h).base x) ∈ U₃.1 := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, hπ]
    exact x.2
  have hmem : ((f ⁻¹ᵁ U₃.1).ι ≫ h).base x ∈ (relativeProjChart s U₃).opensRange := by
    rw [opensRange_relativeProjChart]
    exact hx
  exact hmem

/-- **Any two chart data give the same comparison `ℳ̃_T ≅ h^*ℳ̃`.** -/
theorem iso_hom_eq (H : ShrinkBase ℳ hd) (D₁ D₂ : ChartDatum f ψ h)
    (hπ : h ≫ relativeProjToBase s = f) :
    (D₁.iso ℳ hd).hom = (D₂.iso ℳ hd).hom := by
  choose U₃ hU₃ h₁ h₂ using exists_affineOpen_le D₁ D₂
  refine Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_pullbackCover
    (fun t : T => f ⁻¹ᵁ (U₃ t).1) (fun t => ⟨t, hU₃ t⟩) fun t => ?_
  exact pullback_map_iso_hom_eq H D₁ D₂ hπ _ (U₃ t) (h₁ t) (h₂ t) (fun x _ => x.2)
    (IsOpenImmersion.lift (relativeProjChart s (U₃ t)) _ (range_subset_chart hπ (U₃ t)))
    (IsOpenImmersion.lift_fac _ _ _).symm

end ChartDatum

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end

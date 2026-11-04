module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Datum
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartIsoPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartFactorPullback

/-!
# Chart data along a pullback

A chart datum of `(f, ψ)` and `h : T ⟶ Proj_S(𝒜)` pulls back along a morphism `k : T' ⟶ T` of test
schemes to a chart datum of `(k ≫ f, k^*ψ)` and `k ≫ h`, and **the comparison `ℳ̃_T ≅ h^*ℳ̃` it
defines is compatible with the pullback**: the comparison of the pulled-back datum is the pullback
of the comparison, read through `k^*ℳ̃_T ≅ ℳ̃_{T'}` and the composition law `k^*h^* ≅ (k ≫ h)^*`.
This is property (2) of [Stacks, Tag 01O7] on a chart.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.pullback`: the pulled-back
  chart datum.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_pullback`: the comparison
  of the pulled-back chart datum.
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

private theorem assemble {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B E : C}
    {P Q S : D} (a : P ⟶ F.obj A) (x : A ⟶ B) (y : B ⟶ E) (p : F.obj B ⟶ Q) (p' : Q ⟶ F.obj B)
    (hp : p ≫ p' = 𝟙 _) (q : F.obj E ⟶ S) :
    (a ≫ F.map x ≫ p) ≫ (p' ≫ F.map y) ≫ q = a ≫ F.map (x ≫ y) ≫ q := by
  simp only [Category.assoc, reassoc_of% hp, Functor.map_comp]

namespace ChartDatum

variable {s : Stacks.RelativeProj.Situation.{u}} {T : Scheme.{u}} {f : T ⟶ s.base} {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s}

/-- **A chart datum along a pullback** `k : T' ⟶ T`: the same affine open and section, the
factorization `k ≫ g`, and the pulled-back unit. -/
def pullback (D : ChartDatum f ψ h) {T' : Scheme.{u}} (k : T' ⟶ T) :
    ChartDatum (k ≫ f) (ψ.pullback k) (k ≫ h) where
  U := D.U
  c := D.c
  hf := hf_pullback D.U f D.hf k
  g := k ≫ D.g
  hg := hg_pullback D.U D.c D.g D.hg k
  hgf := hgf_pullback D.U D.c D.hf D.hg k D.hgf
  w := LaurentSections.pullbackUnit' k L D.w
  hCP := hCP_pullback D.U D.c D.hf D.hg k ψ D.w D.hCP D.hw D.hw'
  hw := LaurentSections.pullbackUnit'_homogeneous k L D.w D.hw
  hw' := LaurentSections.pullbackUnit'_inv_homogeneous k L D.w D.hw'
  fac := (congrArg (k ≫ ·) D.fac).trans (Category.assoc _ _ _).symm

variable (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (D : ChartDatum f ψ h) (hd : 0 < d)

/-- **The comparison of a chart datum along a pullback** — property (2) of Tag 01O7 on a chart:
the comparison `ℳ̃_{T'} ≅ (k ≫ h)^*ℳ̃` of the pulled-back datum is the pullback along `k` of the
comparison `ℳ̃_T ≅ h^*ℳ̃`, read through `k^*ℳ̃_T ≅ ℳ̃_{T'}` and `k^*h^* ≅ (k ≫ h)^*`. -/
theorem iso_pullback {T' : Scheme.{u}} (k : T' ⟶ T) :
    ((D.pullback k).iso ℳ hd).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k ψ).inv ≫
        (Scheme.Modules.pullback k).map (D.iso ℳ hd).hom ≫
          (Scheme.Modules.pullbackComp k h).hom.app (moduleSheaf ℳ) := by
  have h1 : (chartIso ℳ (D.pullback k).U (D.pullback k).c (k ≫ f) (D.pullback k).hf
      (D.pullback k).g (D.pullback k).hg (D.pullback k).hgf (ψ.pullback k) (D.pullback k).w
      (D.pullback k).hCP (D.pullback k).hw (D.pullback k).hw' hd).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k ψ).inv ≫
        (pullbackFunctor (ringedSpaceHom k)).map
            (chartIso ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd).hom ≫
          (Scheme.Modules.pullbackComp k D.g).hom.app (moduleChart ℳ D.U) :=
    chartIso_pullback ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd k
  have h2 := congrArg Iso.inv
    (moduleSheafPullbackChartIso_comp ℳ D.U D.g D.fac k rfl (D.pullback k).fac)
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
    pullbackCompIsoOfEq, Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id] at h2
  have h2' : (moduleSheafPullbackChartIso ℳ (D.pullback k).U (D.pullback k).g
      (D.pullback k).fac).inv =
      (Scheme.Modules.pullbackComp k D.g).inv.app (moduleChart ℳ D.U) ≫
        (Scheme.Modules.pullback k).map (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv ≫
          (Scheme.Modules.pullbackComp k h).hom.app (moduleSheaf ℳ) := h2
  change (chartIso ℳ (D.pullback k).U (D.pullback k).c (k ≫ f) (D.pullback k).hf
      (D.pullback k).g (D.pullback k).hg (D.pullback k).hgf (ψ.pullback k) (D.pullback k).w
      (D.pullback k).hCP (D.pullback k).hw (D.pullback k).hw' hd ≪≫
      (moduleSheafPullbackChartIso ℳ (D.pullback k).U (D.pullback k).g
        (D.pullback k).fac).symm).hom = _
  refine (Iso.trans_hom _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) h1 ((Iso.symm_hom _).trans h2')).trans ?_
  exact assemble (C := T.Modules) (D := T'.Modules) (Scheme.Modules.pullback k)
    (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k ψ).inv
    (chartIso ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd).hom
    (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv
    ((Scheme.Modules.pullbackComp k D.g).hom.app (moduleChart ℳ D.U))
    ((Scheme.Modules.pullbackComp k D.g).inv.app (moduleChart ℳ D.U))
    (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp k D.g) (moduleChart ℳ D.U))
    ((Scheme.Modules.pullbackComp k h).hom.app (moduleSheaf ℳ))

end ChartDatum

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end

module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Inverse
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModulePullback

/-!
# Chart data of a morphism into a relative projective spectrum

A *chart datum* for a twisting `ψ` over `f : T ⟶ S` and a morphism `h : T ⟶ Proj_S(𝒜)` is the
local situation in which the comparison of property (1) of [Stacks, Tag 01O7] is built: an affine
open `U` of the base containing the image of `f`, a section `c` of `𝒜_d` over `U`, a factorization
`h = g ≫ chart U` with `g` landing in `D₊(c)`, and a unit `w` of degree one of the Laurent sections
of `L` with `ψ(a) = g^♯(a / c^i) · w^i` for `a ∈ 𝒜_{id}(U)`. Each chart datum gives an isomorphism
`ℳ̃_T ≅ h^*ℳ̃`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

variable {s : Stacks.RelativeProj.Situation.{u}} {T : Scheme.{u}} (f : T ⟶ s.base) {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (h : T ⟶ relativeProj s)

/-- **A chart datum of `(f, ψ)` and `h : T ⟶ Proj_S(𝒜)`.** -/
structure ChartDatum where
  /-- The affine open of the base. -/
  U : s.base.affineOpens
  /-- The section of `𝒜_d` over `U` whose standard open receives `T`. -/
  c : s.sectionPieces U.1 d
  hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1
  /-- The factorization of `h` through the chart over `U`. -/
  g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1)
  hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)
  hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r))
  /-- A unit of degree one of the Laurent sections of `L`. -/
  w : (LaurentSections.Ring L (op ⊤))ˣ
  hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        LaurentSections.pw w i
  hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ
  hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
    DirectSum.of _ (-1) τ
  fac : h = g ≫ relativeProjChart s U

namespace ChartDatum

variable {f ψ h} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (D : ChartDatum f ψ h) (hd : 0 < d)

/-- **The comparison `ℳ̃_T ≅ h^*ℳ̃` attached to a chart datum.** -/
def iso : src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ) :=
  chartIso ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd ≪≫
    (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).symm

/-- In degree `n`, the pure-tensor map of `ψ` followed by the comparison `D.iso ℳ hd` equals `bmap`
followed by the inverse of `moduleSheafPullbackChartIso`. -/
theorem pureTensor_iso_hom (n : ℤ) :
    Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n ≫ (D.iso ℳ hd).hom =
      bmap ℳ D.U D.c f D.hf D.g D.hg D.hgf D.w n ≫
        (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv)
      (pureTensor_chartIso_hom ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd n))

end ChartDatum

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end

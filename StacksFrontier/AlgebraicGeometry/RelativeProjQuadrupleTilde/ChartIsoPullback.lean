module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Inverse
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartPullback

/-!
# The comparison `ℳ̃_T ≅ g^*ℳ̃(U)` on one chart, along a pullback and along a strict equivalence

`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.chartIso` is the comparison of property (1)
of [Stacks, Tag 01O7] in the local situation of a chart. This file proves its two naturalities:

* **along a pullback** `k : T' ⟶ T`, the comparison for the pulled-back datum is the pullback of
  the comparison, read through `k^*ℳ̃_T ≅ ℳ̃_{T'}` (Tag 01O6 along a pullback) and the composition
  law `k^*g^* ≅ (k ≫ g)^*`: `chartIso_pullback`;
* **along an isomorphism** `e : L ≅ L'` carrying `ψ` to `ψ'`, the comparison for `ψ'` and the
  transported unit is the comparison for `ψ` read through `ℳ̃_T(ψ) ≅ ℳ̃_T(ψ')`:
  `chartIso_congr`.
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

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (U : s.base.affineOpens) {d : ℕ} (c : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (w : (LaurentSections.Ring L (op ⊤))ˣ)
  (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        LaurentSections.pw w i)
  (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
    DirectSum.of _ (-1) τ)
  (hd : 0 < d)

/-- **The chart comparison along a pullback** `k : T' ⟶ T`: the comparison for the pulled-back
datum is the pullback of the comparison, read through `k^*ℳ̃_T ≅ ℳ̃_{T'}` and
`k^*g^* ≅ (k ≫ g)^*`. -/
theorem chartIso_pullback {T' : Scheme.{u}} (k : T' ⟶ T) :
    (chartIso ℳ U c (k ≫ f) (hf_pullback U f hf k) (k ≫ g) (hg_pullback U c g hg k)
        (hgf_pullback U c hf hg k hgf) (ψ.pullback k) (LaurentSections.pullbackUnit' k L w)
        (hCP_pullback U c hf hg k ψ w hCP hw hw')
        (LaurentSections.pullbackUnit'_homogeneous k L w hw)
        (LaurentSections.pullbackUnit'_inv_homogeneous k L w hw') hd).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k ψ).inv ≫
        (pullbackFunctor (ringedSpaceHom k)).map
            (chartIso ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).hom ≫
          (Scheme.Modules.pullbackComp k g).hom.app (moduleChart ℳ U) :=
  eq_of_pureTensor_bmap_pullback U c hf hg k ψ w ℳ hgf hw hw' _
    (pureTensor_chartIso_hom ℳ U c f hf g hg hgf ψ w hCP hw hw' hd) _
    (pureTensor_chartIso_hom ℳ U c (k ≫ f) (hf_pullback U f hf k) (k ≫ g)
      (hg_pullback U c g hg k) (hgf_pullback U c hf hg k hgf) (ψ.pullback k)
      (LaurentSections.pullbackUnit' k L w) (hCP_pullback U c hf hg k ψ w hCP hw hw')
      (LaurentSections.pullbackUnit'_homogeneous k L w hw)
      (LaurentSections.pullbackUnit'_inv_homogeneous k L w hw') hd)

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso) in
/-- **The chart comparison along an isomorphism `e : L ≅ L'` carrying `ψ` to `ψ'`.** -/
theorem chartIso_congr {L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
    (e : L ≅ L') (ψ' : Twisting f s.algebra (d : ℤ) L')
    (hψ : ∀ n : ℤ, ψ.app n ≫ (congrIso e n).hom = ψ'.app n) :
    (chartIso ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).hom =
      (associatedSheafCongrIso (ℳ.toGradedModule s.mul_comm) ψ ψ' e hψ).hom ≫
        (chartIso ℳ U c f hf g hg hgf ψ' (LaurentSections.congrUnit e w)
          (hCP_congr U c hf hg ψ w e ψ' hψ hCP hw hw')
          (LaurentSections.congrUnit_homogeneous e w hw)
          (LaurentSections.congrUnit_inv_homogeneous e w hw') hd).hom :=
  eq_of_pureTensor_bmap_congr U c hf hg ψ w ℳ hgf e ψ' hψ hw hw' _
    (pureTensor_chartIso_hom ℳ U c f hf g hg hgf ψ w hCP hw hw' hd) _
    (pureTensor_chartIso_hom ℳ U c f hf g hg hgf ψ' (LaurentSections.congrUnit e w)
      (hCP_congr U c hf hg ψ w e ψ' hψ hCP hw hw')
      (LaurentSections.congrUnit_homogeneous e w hw)
      (LaurentSections.congrUnit_inv_homogeneous e w hw') hd)

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end

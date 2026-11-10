module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericLocalConstancyEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllCover

/-!
# Tag 03SC reduced to constant coefficients on normal curves

Generic local constancy
(`Stacks.EtaleCohomology.exists_opens_isFiniteLocallyConstant_etaleRestriction`) and Tag 0A3R
(`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_constantFiltration_unconditional`) discharge
two of the three inputs of
`Stacks.EtaleCohomology.TorsionCurveAssertions.of_genericLocalConstancy_of_torsion`. What remains
is the case of the constant sheaf `Z/ℓZ` on a normal curve (Tag 0A5B), the input `h0A5B`.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_constantZModAb`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.TorsionCurveAssertions

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The eight assertions of Situation 0A52 for every torsion sheaf, from the case of the constant
sheaf `Z/ℓZ` on a normal curve. -/
theorem of_constantZModAb
    (h0A5B : ∀ {ℓ : ℕ}, ℓ.Prime → ∀ (Yb : Scheme.{u}) (pY : Yb ⟶ Spec (.of k)) [IsSeparated pY]
      [LocallyOfFiniteType pY] [QuasiCompact pY]
      [HasExt.{u + 1} (Sheaf Yb.smallEtaleTopology AddCommGrpCat.{u + 1})],
      topologicalKrullDim Yb ≤ 1 → IsNormal Yb →
        TorsionCurveAssertions pY (StrongTorsionCurveAssertions.constantZModAb Yb ℓ))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    TorsionCurveAssertions f F :=
  of_genericLocalConstancy_of_torsion
    (fun Y _ _ G hG η hη N hN hηN =>
      exists_opens_isFiniteLocallyConstant_etaleRestriction Y G hG η hη N hN hηN)
    (fun hℓ => @exists_primeToEll_finiteEtale_constantFiltration_unconditional.{u + 1, u} _ hℓ)
    h0A5B f hdim F hF

end Stacks.EtaleCohomology.TorsionCurveAssertions

end

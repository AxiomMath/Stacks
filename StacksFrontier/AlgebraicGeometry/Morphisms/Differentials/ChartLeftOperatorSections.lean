module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.ChartBoxSectionRestriction

/-!
# A differential operator on the first factor of a chart, on the sections coming from an open

Let `a : X ⟶ S`, let `F`, `F'` be modules on `X` with `F` quasi-coherent, let `D : F ⟶ F'` be a
differential operator of order at most `k` on `X/S` and let `c` be an affine chart of a fibre
product `X ×_S Y`. `Stacks.FibreProductAffineChart.Chart.leftDiffOpEquiv` reads `D` on the chart
as an operator on `Γ(Spec Γ(X, U), F)`. On the global section of the inverse image attached to a
section `s` of `F` over an open `U'` of `X` containing the first factor of the chart, that operator
takes the value attached to `D s`.

## Main results

* `Stacks.FibreProductAffineChart.Chart.leftDiffOpEquiv_apply_modulesPullbackUnitTop`: the
  operator on `Γ(Spec Γ(X, U), F)` attached to `D` carries the global section of the inverse
  image coming from a section `s` of `F` over `U'` to the one coming from `D s`.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CommRingCat
open Stacks.Tag01VSPullbackTensor

universe u

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry RingHomClass

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

attribute [local instance] leftModuleAlg leftModuleBase leftTower

variable [Algebra Γ(S, c.base) Γ(X, c.left)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (F F' : X.Modules) [F.IsQuasicoherent] (k : ℕ)

/-- For a differential operator `D` of order at most `k` on `X/S` and a section `s` of `F` over
an open `U'` of `X` whose preimage in the chart's first factor is everything, the operator on
`Γ(Spec Γ(X, U), F)` attached to `D` carries the global section of the inverse image coming from
`s` to the one coming from `D s`. -/
theorem leftDiffOpEquiv_apply_modulesPullbackUnitTop (D : DiffOp.GlobalOp F F')
    (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D)
    (U' : X.Opens) (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤) (s : Γ(F, U')) :
    (c.leftDiffOpEquiv hl F F' k
          ⟨D.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1
        (modulesPullbackUnitTop c.fromSpecLeft F U' hU s)
      = modulesPullbackUnitTop c.fromSpecLeft F' U' hU (D (op U') s) := by
  have hle : c.fromSpecLeft ''ᵁ (⊤ : (Spec Γ(X, c.left)).Opens) ≤ U' := by
    rw [← hU]
    exact c.fromSpecLeft.image_preimage_le U'
  have hsrc := modulesPullbackUnitTop_restrictFunctorIsoPullback c.fromSpecLeft F U' hU s hle
  have htgt := modulesPullbackUnitTop_restrictFunctorIsoPullback c.fromSpecLeft F' U' hU
    (D (op U') s) hle
  have hinv : Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecLeft).app F).inv ⊤
        (modulesPullbackUnitTop c.fromSpecLeft F U' hU s)
      = F.presheaf.map (homOfLE hle).op s := by
    rw [modulesPullbackUnitTop, hsrc]
    exact congrArg
      (fun φ : Scheme.Modules.restrict F c.fromSpecLeft ⟶
          Scheme.Modules.restrict F c.fromSpecLeft ↦
        Scheme.Modules.Hom.app φ ⊤ (F.presheaf.map (homOfLE hle).op s))
      ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecLeft).app F).hom_inv_id
  have hnat := DiffOp.RawOp.isNatural_of_isDiffOpOfOrder a.relativeStructureSheafMap k _ (hD ⊤)
    (Over.mk (homOfLE (le_top : c.fromSpecLeft ''ᵁ (⊤ : (Spec Γ(X, c.left)).Opens) ≤ ⊤)))
    (Over.mk (homOfLE (le_top : U' ≤ ⊤))) (Over.homMk (homOfLE hle) (Subsingleton.elim _ _)) s
  exact (c.leftDiffOpEquiv_apply hl F F' k _ _).trans ((congrArg
    (fun z ↦ Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecLeft).app F').hom ⊤ z)
    ((congrArg (fun z ↦ D (op (c.fromSpecLeft ''ᵁ (⊤ : (Spec Γ(X, c.left)).Opens))) z)
      hinv).trans hnat)).trans htgt.symm)

end Chart

end Stacks.FibreProductAffineChart

end

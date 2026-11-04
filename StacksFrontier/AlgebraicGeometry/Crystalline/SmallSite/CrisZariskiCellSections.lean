module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareIso

/-!
# The `2`-cell of the square of [Stacks, Tag 07Q9], read on sections

The `2`-cell `f_{Zar, *}u_{X'/S, *} ⟶ u_{X/S, *}f_{cris, *}` of the square of topoi of
[Stacks, Tag 07Q9], `Crystalline.GlobalCrystallineSituation.SmallSite.crisZariskiCell`, is
computed on sections over an open `V` of `X`: followed by the limit formula for its target, it is
the restriction of cones along `dominationProj`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.crisZariskiCell_app_hom_app_comp_hom`: the
  `2`-cell on sections over `V`, followed by the limit formula for its target, is the
  restriction of cones along `dominationProj`.

## References

* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

variable (E : Type (u + 2)) [Category.{u + 1} E] [HasLimitsOfSize.{u, u + 1} E]

/-- The `2`-cell of the square of topoi of [Stacks, Tag 07Q9] with coefficients in `E`, read on
sections over an open `V` of `X` and then through the limit formula for its target, is the
restriction of cones along `dominationProj`. -/
theorem crisZariskiCell_app_hom_app_comp_homCoeff
    (G : Sheaf (smallTopology S) E) (V : S'.X.Opens) :
    ((crisZariskiCellCoeff S S' fS fX hf E).app G).hom.app (op V) ≫
        (crisZariskiLeftObjIsoCoeff S S' fS fX hf E G V).hom =
      ((forgetToOpens S).op.ranObjObjIsoLimit G.obj (op (fX ⁻¹ᵁ V))).hom ≫
        limit.pre (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
          (dominationProj S S' fS fX hf V) := by
  refine Eq.trans ?_ (crisZariskiRanBaseChange_app_app S S' fS fX hf E G V)
  have hpre : (crisZariskiCellPreCoeff S S' fS fX hf E).app G ≫
      ((crisZariskiLeftIsoCoeff S S' fS fX hf E).app G).hom =
        (((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
          (D := E)).app G.obj) :=
    (congrArg (· ≫ ((crisZariskiLeftIsoCoeff S S' fS fX hf E).app G).hom)
        (crisZariskiCellPreCoeff_app S S' fS fX hf E G)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ (((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
              (D := E)).app G.obj) ≫ m)
            ((crisZariskiLeftIsoCoeff S S' fS fX hf E).app G).inv_hom_id).trans
          (Category.comp_id _)))
  have hV := congrArg (fun t ↦ NatTrans.app t (op V)) hpre
  simp only [NatTrans.comp_app] at hV
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ ((dominationToOpens S S' fS fX hf).ranObjObjIsoLimit
      (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj)
      (op V)).hom) hV)

/-- The `2`-cell of the square of topoi of [Stacks, Tag 07Q9], read on sections over an open `V`
of `X` and then through the limit formula for its target, is the restriction of cones along
`dominationProj`. -/
theorem crisZariskiCell_app_hom_app_comp_hom
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (V : S'.X.Opens) :
    ((crisZariskiCell S S' fS fX hf).app G).hom.app (op V) ≫
        (crisZariskiLeftObjIso S S' fS fX hf G V).hom =
      (zariskiDirectImageObjObjIsoLimit S G (fX ⁻¹ᵁ V)).hom ≫
        limit.pre (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
          (dominationProj S S' fS fX hf V) :=
  crisZariskiCell_app_hom_app_comp_homCoeff S S' fS fX hf AddCommGrpCat.{u + 1} G V

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

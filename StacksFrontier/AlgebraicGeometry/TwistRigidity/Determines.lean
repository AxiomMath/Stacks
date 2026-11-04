module

public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Chart

/-!
# A compatible isomorphism of twist data determines the chart identifications

An isomorphism of the glued graded algebras of two twist data on a relative Proj which commutes
with the homogeneous-section maps determines every chart identification, in every integer degree:
`Stacks.AlgebraicGeometry.RelativeProjTwists.DeterminesChartIso`.

## Main results

* `Stacks.AlgebraicGeometry.TwistRigidity.isMultiplicative_chartEndo`: the chart comparison is
  multiplicative.
* `Stacks.AlgebraicGeometry.TwistRigidity.fixesDegreeSections_chartEndo`: the chart comparison
  fixes the homogeneous sections.
* `Stacks.AlgebraicGeometry.TwistRigidity.determinesChartIso`: an isomorphism of the glued graded
  algebras of two twist data which commutes with the homogeneous-section maps determines every
  chart identification.

## Implementation notes

The transport of a section along the identification of the image of a chart with the inverse
image of its affine open appears in `ψ_chart`, and the two twist data carry two different
witnesses of that identification. They are proofs of the same proposition, so the two transports
are the same function, and `Stacks.AlgebraicGeometry.TwistRigidity.app_eq_rec` is the only
transport lemma needed.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistRigidity

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- The chart comparison is multiplicative. -/
public theorem isMultiplicative_chartEndo (D E : TwistData A) (e : D.algebra ≅ E.algebra)
    (U : S.Opens) (hU : IsAffineOpen U) :
    IsMultiplicative (chartEndo D E e U hU) := by
  let := D.chartData.chart_isOpenImmersion U hU
  intro i j V a b
  refine mapSection_injective E.chartData U hU (i + j) V ?_
  calc E.chartData.mapSection U hU (i + j) V
          ((chartEndo D E e U hU (i + j)).val.app (op V)
            (absoluteTwistProduct (A.grading U) i j V a b))
      = (e.hom.app (i + j)).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
          (D.chartData.mapSection U hU (i + j) V
            (absoluteTwistProduct (A.grading U) i j V a b)) :=
        mapSection_chartEndo D E e U hU (i + j) V _
    _ = (e.hom.app (i + j)).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
          ((D.algebra.mul i j).app (op (((relativeProj A).chart U hU) ''ᵁ V))
            (D.chartData.mapSection U hU i V a) (D.chartData.mapSection U hU j V b)) :=
        app_congr _ _ (D.chartIso_mul U hU i j V a b)
    _ = (E.algebra.mul i j).app (op (((relativeProj A).chart U hU) ''ᵁ V))
          ((e.hom.app i).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
            (D.chartData.mapSection U hU i V a))
          ((e.hom.app j).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
            (D.chartData.mapSection U hU j V b)) :=
        e.hom.map_mul i j (op (((relativeProj A).chart U hU) ''ᵁ V)) _ _
    _ = (E.algebra.mul i j).app (op (((relativeProj A).chart U hU) ''ᵁ V))
          (E.chartData.mapSection U hU i V ((chartEndo D E e U hU i).val.app (op V) a))
          (E.chartData.mapSection U hU j V ((chartEndo D E e U hU j).val.app (op V) b)) :=
        mul_app_congr E.algebra i j _
          (mapSection_chartEndo D E e U hU i V a).symm
          (mapSection_chartEndo D E e U hU j V b).symm
    _ = E.chartData.mapSection U hU (i + j) V
          (absoluteTwistProduct (A.grading U) i j V
            ((chartEndo D E e U hU i).val.app (op V) a)
            ((chartEndo D E e U hU j).val.app (op V) b)) :=
        (E.chartIso_mul U hU i j V _ _).symm

/-- The chart comparison fixes the homogeneous sections. -/
public theorem fixesDegreeSections_chartEndo (D E : TwistData A) (e : D.algebra ≅ E.algebra)
    (he : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e.hom.app (n : ℤ)) = E.ψ n)
    (U : S.Opens) (hU : IsAffineOpen U) :
    FixesDegreeSections (chartEndo D E e U hU) := by
  let := D.chartData.chart_isOpenImmersion U hU
  intro k c
  obtain ⟨y, hy⟩ := c.2
  have hc : c = ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩ :=
    Subtype.ext hy.symm
  subst hc
  have hek : (e.hom.app (k : ℤ)).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
      ((D.ψ k).val.app (op U) y) = (E.ψ k).val.app (op U) y :=
    congrArg (fun φ : A.piece (k : ℤ) ⟶
        (Scheme.Modules.pushforward (relativeProj A).toBase).obj (E.algebra.piece (k : ℤ)) =>
      φ.val.app (op U) y) (he k)
  refine mapSection_injective E.chartData U hU (k : ℤ) ⊤ ?_
  calc E.chartData.mapSection U hU (k : ℤ) ⊤
          ((chartEndo D E e U hU (k : ℤ)).val.app (op ⊤)
            (degreeSection (A.grading U) k
              ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩))
      = (e.hom.app (k : ℤ)).val.app (op (((relativeProj A).chart U hU) ''ᵁ ⊤))
          (D.chartData.mapSection U hU (k : ℤ) ⊤
            (degreeSection (A.grading U) k
              ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩)) :=
        mapSection_chartEndo D E e U hU (k : ℤ) ⊤ _
    _ = (e.hom.app (k : ℤ)).val.app (op (((relativeProj A).chart U hU) ''ᵁ ⊤))
          ((D.chartData.chart_range U hU).symm ▸ ((D.ψ k).val.app (op U) y)) :=
        app_congr _ _ (D.ψ_chart U hU k y)
    _ = (D.chartData.chart_range U hU).symm ▸
          ((e.hom.app (k : ℤ)).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
            ((D.ψ k).val.app (op U) y)) :=
        app_eq_rec _ _ _
    _ = (E.chartData.chart_range U hU).symm ▸ ((E.ψ k).val.app (op U) y) := by rw [hek]
    _ = E.chartData.mapSection U hU (k : ℤ) ⊤
          (degreeSection (A.grading U) k
            ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩) :=
        (E.ψ_chart U hU k y).symm

/-- An isomorphism of the glued graded algebras of two twist data which commutes with the
homogeneous-section maps determines every chart identification, in every integer degree. -/
@[stacks 01NR "uniqueness of the affine-chart identifications"]
public theorem determinesChartIso (A : SheafGradedAlgebra S) : DeterminesChartIso A := by
  intro D E e he U hU n
  let := D.chartData.chart_isOpenImmersion U hU
  have hid : chartEndo D E e U hU n = 𝟙 (twistingSheaf (A.grading U) n) :=
    eq_id (isMultiplicative_chartEndo D E e U hU)
      (fixesDegreeSections_chartEndo D E e he U hU) n
  have hstep : (D.chartData.chartIso U hU n).hom ≫ chartEndo D E e U hU n =
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map (e.hom.app n) ≫
        (E.chartData.chartIso U hU n).hom := by
    show (D.chartData.chartIso U hU n).hom ≫ (D.chartData.chartIso U hU n).inv ≫
      ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map (e.hom.app n) ≫
        (E.chartData.chartIso U hU n).hom) = _
    exact (D.chartData.chartIso U hU n).hom_inv_id_assoc _
  exact hstep.symm.trans
    (Eq.trans (congrArg (fun g => (D.chartData.chartIso U hU n).hom ≫ g) hid)
      (Category.comp_id _))

end Stacks.AlgebraicGeometry.TwistRigidity

end

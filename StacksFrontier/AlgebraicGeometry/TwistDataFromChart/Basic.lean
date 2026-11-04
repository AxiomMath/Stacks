module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeModuleGlue.Chart
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Basic
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Pointwise
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Chart
public import StacksFrontier.AlgebraicGeometry.TwistUnique.Basic

/-!
# Commutativity of the glued product from the chart identifications

Let `D : ChartData A algebra` be a chart datum for a graded algebra `algebra` on the relative Proj
of `A`, satisfying `IsGradedChartIso`. Multiplication in `algebra` is then commutative, as the
`mul_comm` field of `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` asks, and a twist datum
is determined by `D` together with the fields `ψ`, `ψ_one`, `ψ_mul` and `ψ_chart`.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistDataFromChart.chartPull`: the chart comparison on the sections
  over an arbitrary open of the relative Proj, for a chart datum.
* `Stacks.AlgebraicGeometry.TwistDataFromChart.mk`: the twist datum with given algebra, chart datum
  satisfying `IsGradedChartIso`, and fields `ψ`, `ψ_one`, `ψ_mul` and `ψ_chart`.

## Main results

* `Stacks.AlgebraicGeometry.TwistDataFromChart.chartPull_mul`: the chart comparison carries the
  product of the glued algebra to the canonical product of absolute twist sections, in every pair
  of integer degrees and over every open of the relative Proj.
* `Stacks.AlgebraicGeometry.TwistDataFromChart.mul_comm_of_isGradedChartIso`: multiplication in the
  glued graded algebra is commutative.
* `Stacks.AlgebraicGeometry.TwistDataFromChart.absoluteTwistProduct_degreeSection` and
  `Stacks.AlgebraicGeometry.TwistDataFromChart.absoluteTwistUnit_top`: the canonical product of two
  homogeneous sections of the absolute twists is the homogeneous section attached to the product,
  and the unit section on the whole space is the one attached to `1`.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistDataFromChart

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}
  {algebra : SchemeGradedAlgebra (relativeProj A).scheme}

/-! ### Transport along an equality of degrees -/

/-- Sections `x` and `y` in degrees `k` and `l` are heterogeneously equal if the transport of `x`
along `k = l` is `y`. -/
public theorem heq_of_eqRec_eq {k l : ℤ} (e : k = l) {V : (relativeProj A).scheme.Opensᵒᵖ}
    {x : (algebra.piece k).val.obj V} {y : (algebra.piece l).val.obj V}
    (h : e ▸ x = y) : HEq x y := by
  subst e
  exact heq_of_eq h

/-- Restriction of sections commutes with transport along an equality of degrees. -/
public theorem piece_resLE_eqRec {k l : ℤ} (e : k = l)
    {V W : (relativeProj A).scheme.Opens} (h : W ≤ V)
    (x : (algebra.piece k).val.obj (op V)) :
    (algebra.piece l).val.resLE h (e ▸ x) = e ▸ ((algebra.piece k).val.resLE h x) := by
  subst e
  rfl

section Absolute

variable {R : Type u} {σ : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Transport of a section of an absolute twist along an equality of degrees does not change its
values. -/
public theorem eqRec_val {k l : ℤ} (e : k = l) {V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (s : (twistingSheaf 𝒜 k).val.obj (op V)) :
    (e ▸ s : (twistingSheaf 𝒜 l).val.obj (op V)).1 = s.1 := by
  subst e
  rfl

/-- The canonical product of two local sections of the absolute twists is commutative, as an
equation of sections in degree `j + i` after transport along `add_comm i j`. -/
public theorem absoluteTwistProduct_eqRec (i j : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj (op V)) (b : (twistingSheaf 𝒜 j).val.obj (op V)) :
    (add_comm i j ▸ absoluteTwistProduct 𝒜 i j V a b :
        (twistingSheaf 𝒜 (j + i)).val.obj (op V)) =
      absoluteTwistProduct 𝒜 j i V b a := by
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.trans (congrFun (eqRec_val 𝒜 (add_comm i j) (absoluteTwistProduct 𝒜 i j V a b)) x) ?_
  exact ThetaMultiplicative.absoluteTwistProduct_apply_comm 𝒜 i j V a b x

/-- The unit section of the degree-zero twist on the whole space is the homogeneous section
attached to `1`. -/
public theorem absoluteTwistUnit_top :
    absoluteTwistUnit 𝒜 ⊤ = degreeSection 𝒜 0 ⟨1, SetLike.one_mem_graded 𝒜⟩ := by
  refine Subtype.ext (funext fun x => ?_)
  refine (ThetaMultiplicative.absoluteTwistUnit_apply 𝒜 ⊤ x).trans ?_
  exact ((degreeSection_apply 𝒜 0 ⟨1, SetLike.one_mem_graded 𝒜⟩ x).trans
    (ThetaMultiplicative.localizedModule_mk_one_one _)).symm

/-- The canonical product of the homogeneous sections attached to `a` and `b` over the whole space
is the homogeneous section attached to `a * b`, transported along `Int.natCast_add n m`. -/
public theorem absoluteTwistProduct_degreeSection (n m : ℕ) (a : 𝒜 n) (b : 𝒜 m) :
    absoluteTwistProduct 𝒜 (n : ℤ) (m : ℤ) ⊤ (degreeSection 𝒜 n a) (degreeSection 𝒜 m b) =
      Int.natCast_add n m ▸ degreeSection 𝒜 (n + m)
        ⟨(a : R) * (b : R), SetLike.mul_mem_graded a.2 b.2⟩ := by
  set c : 𝒜 (n + m) := ⟨(a : R) * (b : R), SetLike.mul_mem_graded a.2 b.2⟩
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.trans (TwistRigidity.absoluteTwistProduct_apply 𝒜 (n : ℤ) (m : ℤ) ⊤ _ _ x) ?_
  refine Eq.trans (congrArg₂ (· * ·) (degreeSection_apply 𝒜 n a x)
    (degreeSection_apply 𝒜 m b x)) ?_
  refine Eq.trans (LocalizedModule.mk_mul_mk.trans
    (congrArg (LocalizedModule.mk ((a : R) * (b : R))) (one_mul _))) ?_
  exact (degreeSection_apply 𝒜 (n + m) c x).symm.trans
    (congrFun (eqRec_val 𝒜 (Int.natCast_add n m) (degreeSection 𝒜 (n + m) c)) x).symm

end Absolute

/-! ### The chart comparison for a bare chart datum -/

/-- The chart comparison on the sections over an open `V` of the relative Proj: restriction to the
image of the preimage of `V` in the chart, followed by the chart identification in degree `n`. -/
public def chartPull (D : ChartData A algebra) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (x : (algebra.piece n).val.obj (op V)) :
    letI := D.chart_isOpenImmersion U hU
    (twistingSheaf (A.grading U) n).val.obj (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) :=
  letI := D.chart_isOpenImmersion U hU
  (D.chartIso U hU n).hom.val.app (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
    ((algebra.piece n).val.map
      (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x)

/-- The section comparison composed with the chart comparison is the restriction map to the image
of the preimage. -/
public theorem mapSection_chartPull (D : ChartData A algebra) (U : S.Opens)
    (hU : IsAffineOpen U) (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (x : (algebra.piece n).val.obj (op V)) :
    letI := D.chart_isOpenImmersion U hU
    D.mapSection U hU n ((relativeProj A).chart U hU ⁻¹ᵁ V) (chartPull D U hU n V x) =
      (algebra.piece n).val.map
        (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x :=
  TwistRigidity.iso_inv_app_hom_app (D.chartIso U hU n)
    (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) _

/-- The chart comparison is injective on the sections over an open inside the inverse image of the
affine open. -/
public theorem chartPull_injective (D : ChartData A algebra) (U : S.Opens)
    (hU : IsAffineOpen U) (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) :
    Function.Injective (chartPull D U hU n V) := by
  let := D.chart_isOpenImmersion U hU
  have heq : ((relativeProj A).chart U hU) ''ᵁ (((relativeProj A).chart U hU) ⁻¹ᵁ V) = V :=
    TwistUnique.image_preimage_eq_self ((relativeProj A).chart U hU)
      (hV.trans (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).ge)
  have key : ∀ x : (algebra.piece n).val.obj (op V),
      (algebra.piece n).val.map (homOfLE heq.ge).op
        ((D.chartIso U hU n).inv.val.app (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
          (chartPull D U hU n V x)) = x := by
    intro x
    refine Eq.trans (congrArg ((algebra.piece n).val.map (homOfLE heq.ge).op)
      (TwistRigidity.iso_inv_app_hom_app (D.chartIso U hU n)
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) _)) ?_
    exact PresheafOfModules.map_map_eq_self (algebra.piece n).val _ _ x
  intro x y hxy
  rw [← key x, ← key y, hxy]

/-- The chart comparison commutes with transport along an equality of degrees. -/
public theorem chartPull_eqRec (D : ChartData A algebra) (U : S.Opens) (hU : IsAffineOpen U)
    {k l : ℤ} (e : k = l) (V : (relativeProj A).scheme.Opens)
    (x : (algebra.piece k).val.obj (op V)) :
    letI := D.chart_isOpenImmersion U hU
    chartPull D U hU l V (e ▸ x) = e ▸ (chartPull D U hU k V x) := by
  subst e
  rfl

/-- The chart comparison carries the product of the glued algebra to the canonical product of
absolute twist sections, in every pair of integer degrees and on the sections over every open of
the relative Proj. -/
public theorem chartPull_mul {D : ChartData A algebra} (hD : IsGradedChartIso D) (U : S.Opens)
    (hU : IsAffineOpen U) (i j : ℤ) (V : (relativeProj A).scheme.Opens)
    (x : (algebra.piece i).val.obj (op V)) (y : (algebra.piece j).val.obj (op V)) :
    letI := D.chart_isOpenImmersion U hU
    chartPull D U hU (i + j) V ((algebra.mul i j).app (op V) x y) =
      absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V)
        (chartPull D U hU i V x) (chartPull D U hU j V y) := by
  let := D.chart_isOpenImmersion U hU
  refine TwistRigidity.mapSection_injective D U hU (i + j)
    ((relativeProj A).chart U hU ⁻¹ᵁ V) ?_
  refine Eq.trans (mapSection_chartPull D U hU (i + j) V _) ?_
  refine Eq.trans ((algebra.mul i j).naturality
    (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x y) ?_
  refine Eq.trans ?_ (hD.1 U hU i j ((relativeProj A).chart U hU ⁻¹ᵁ V) _ _).symm
  exact TwistRigidity.mul_app_congr algebra i j _
    (mapSection_chartPull D U hU i V x).symm (mapSection_chartPull D U hU j V y).symm

/-! ### Commutativity of the glued product -/

/-- Multiplication in the glued graded algebra is commutative on the sections over an open inside
the inverse image of an affine open of the base. -/
public theorem mul_comm_of_le {D : ChartData A algebra} (hD : IsGradedChartIso D) (U : S.Opens)
    (hU : IsAffineOpen U) (i j : ℤ) (W : (relativeProj A).scheme.Opens)
    (hW : W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (algebra.piece i).val.obj (op W)) (y : (algebra.piece j).val.obj (op W)) :
    (add_comm i j ▸ (algebra.mul i j).app (op W) x y :
        (algebra.piece (j + i)).val.obj (op W)) = (algebra.mul j i).app (op W) y x := by
  let := D.chart_isOpenImmersion U hU
  refine chartPull_injective D U hU (j + i) W hW ?_
  refine Eq.trans (chartPull_eqRec D U hU (add_comm i j) W _) ?_
  refine Eq.trans (congrArg (fun z => (add_comm i j ▸ z :
      (twistingSheaf (A.grading U) (j + i)).val.obj
        (op ((relativeProj A).chart U hU ⁻¹ᵁ W))))
    (chartPull_mul hD U hU i j W x y)) ?_
  refine Eq.trans (absoluteTwistProduct_eqRec (A.grading U) i j _ _ _) ?_
  exact (chartPull_mul hD U hU j i W y x).symm

/-- Multiplication in the glued graded algebra is commutative, over every open of the relative Proj
and in every pair of integer degrees, as a heterogeneous equality between the pieces of degrees
`i + j` and `j + i`. -/
public theorem mul_comm_of_isGradedChartIso {D : ChartData A algebra} (hD : IsGradedChartIso D)
    (i j : ℤ) (V : (relativeProj A).scheme.Opensᵒᵖ)
    (a : (algebra.piece i).val.obj V) (b : (algebra.piece j).val.obj V) :
    HEq ((algebra.mul i j).app V a b) ((algebra.mul j i).app V b a) := by
  refine heq_of_eqRec_eq (add_comm i j) ?_
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (algebra.piece (j + i)).isSheaf
    (fun m : S.affineOpens => V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens))
    (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf
      (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)) V.unop) fun m => ?_
  have hle : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens) ≤ V.unop := inf_le_left
  refine Eq.trans (piece_resLE_eqRec (add_comm i j) hle _) ?_
  refine Eq.trans (congrArg (fun z => (add_comm i j ▸ z :
      (algebra.piece (j + i)).val.obj
        (op (V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens)))))
    ((algebra.mul i j).naturality (homOfLE hle).op a b)) ?_
  refine Eq.trans (mul_comm_of_le hD (m.1 : S.Opens) m.2 i j
    (V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens)) inf_le_right _ _) ?_
  exact ((algebra.mul j i).naturality (homOfLE hle).op b a).symm

/-! ### The reduced constructor -/

/-- The twist datum with algebra `B`, chart datum `D` satisfying `IsGradedChartIso`, and fields
`ψ`, `ψ_one`, `ψ_mul` and `ψ_chart` given by `psi`, `psi_one`, `psi_mul` and `psi_chart`; its
fields `isQuasicoherent` and `mul_comm` are
`Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.isQuasicoherent_piece` and
`Stacks.AlgebraicGeometry.TwistDataFromChart.mul_comm_of_isGradedChartIso`. -/
public def mk (B : SchemeGradedAlgebra (relativeProj A).scheme) (D : ChartData A B)
    (hD : IsGradedChartIso D)
    (psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (B.piece (n : ℤ)))
    (psi_one : ∀ U : S.Opens,
      (psi 0).val.app (op U) (A.one U) =
        B.one.eval (op ((relativeProj A).toBase ⁻¹ᵁ U)))
    (psi_mul : ∀ (U : S.Opens) (n m : ℕ) (a : A.sectionPieces U n) (b : A.sectionPieces U m),
      HEq
        ((psi (n + m)).val.app (op U)
          ((Int.natCast_add n m).symm ▸ (A.mul (n : ℤ) (m : ℤ)).app U a b))
        ((B.mul (n : ℤ) (m : ℤ)).app
          (op ((relativeProj A).toBase ⁻¹ᵁ U))
            ((psi n).val.app (op U) a) ((psi m).val.app (op U) b)))
    (psi_chart : ∀ (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) (a : A.sectionPieces U n),
      letI := D.chart_isOpenImmersion U hU
      D.mapSection U hU (n : ℤ) ⊤
        (degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩) =
        (D.chart_range U hU).symm ▸ ((psi n).val.app (op U) a)) :
    TwistData A where
  algebra := B
  isQuasicoherent := RelativeProjTwistQcoh.isQuasicoherent_piece D
  mul_comm := mul_comm_of_isGradedChartIso hD
  chartData := D
  isGradedChartIso := hD
  ψ := psi
  ψ_one := psi_one
  ψ_mul := psi_mul
  ψ_chart := psi_chart

end Stacks.AlgebraicGeometry.TwistDataFromChart

end

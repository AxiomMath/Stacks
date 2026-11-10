module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistTransportData
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise
public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Basic
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Psi
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Chart

/-!
# The chart identifications of the twists are compatible with the chart transitions

Let `D` be twist data on a relative projective spectrum `Proj_S(A)` (Tag 01NR) and let `W ⊆ U` be
affine opens of `S`. The chart over `W` factors through the chart over `U` along
`t = Proj(Γ(U, A) ⟶ Γ(W, A))`, and the twist `𝒪_{Proj Γ(U, A)}(n)` is carried to
`𝒪_{Proj Γ(W, A)}(n)` along `t` by the pointwise localization of the restriction map (Tag 01NO).
The chart identification of `D` over `W` is the chart identification over `U` restricted along `t`
followed by that comparison. The proof is relative rigidity: the discrepancy is a multiplicative
endomorphism of the twists over `W` fixing the homogeneous sections of restricted elements.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.chartTrans`: the chart transition `t`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.transTwist`: the comparison of the twists
  along `t`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.chartIso_transition`: the compatibility.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {W U : S.Opens} (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U)

include h hW hU

/-- `Proj` of the restriction map of sections along a nested pair of affine opens is defined. -/
public theorem irrelevant_le_res :
    HomogeneousIdeal.irrelevant (A.grading W) ≤
      (HomogeneousIdeal.irrelevant (A.grading U)).map (A.res h) :=
  Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens A.toGradedAlgebra
    (U := ⟨W, hW⟩) (V := ⟨U, hU⟩) h

/-- **The chart transition** `Proj Γ(W, A) ⟶ Proj Γ(U, A)` of a nested pair of affine opens. -/
public abbrev chartTrans :
    AlgebraicGeometry.Proj (A.grading W) ⟶ AlgebraicGeometry.Proj (A.grading U) :=
  Proj.map (A.res h) (irrelevant_le_res A h hW hU)

/-- The chart over the smaller affine open factors through the chart transition. -/
@[reassoc]
public theorem chartTrans_comp_chart :
    chartTrans A h hW hU ≫ (relativeProj A).chart U hU = (relativeProj A).chart W hW := by
  refine Eq.trans ?_ ((relativeProj A).chart_transition W U h hW hU)
  exact congrArg (· ≫ _) (Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens
    A.toGradedAlgebra (U := ⟨W, hW⟩) (V := ⟨U, hU⟩) h _).symm

/-- The chart transition is an open immersion, since the chart over `U` and its composite with
the chart transition (the chart over `W`) are. -/
public instance isOpenImmersion_chartTrans : IsOpenImmersion (chartTrans A h hW hU) := by
  have : IsOpenImmersion (chartTrans A h hW hU ≫ (relativeProj A).chart U hU) := by
    rw [chartTrans_comp_chart]; infer_instance
  exact IsOpenImmersion.of_comp _ ((relativeProj A).chart U hU)

/-- **The comparison of the twists along a chart transition**: the pointwise localization of the
restriction map, `𝒪_{Proj Γ(U, A)}(n)|_{Proj Γ(W, A)} ⟶ 𝒪_{Proj Γ(W, A)}(n)`. -/
public def transTwist (n : ℤ) :
    (Scheme.Modules.restrictFunctor (chartTrans A h hW hU)).obj (twistingSheaf (A.grading U) n) ⟶
      twistingSheaf (A.grading W) n :=
  ((Scheme.Modules.restrictAdjunction (chartTrans A h hW hU)).homEquiv _ _).symm
    (Stacks.ProjTwistComparison.pushforwardTwistMap (A.res h) (irrelevant_le_res A h hW hU) n)

/-- The comparison of the twists along a chart transition, at a point. -/
public theorem transTwist_app_apply (n : ℤ) (V : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (x : (twistingSheaf (A.grading U) n).val.obj (op (chartTrans A h hW hU ''ᵁ V))) (y : V) :
    ((transTwist A h hW hU n).val.app (op V) x).1 y =
      Stacks.ProjTwistComparison.fibreMap (A.res h) (irrelevant_le_res A h hW hU) y.1
        (x.1 ⟨_, ⟨y.1, y.2, rfl⟩⟩) := by
  have e : transTwist A h hW hU n =
      (Scheme.Modules.restrictFunctor (chartTrans A h hW hU)).map
        (Stacks.ProjTwistComparison.pushforwardTwistMap (A.res h) (irrelevant_le_res A h hW hU) n) ≫
        (Scheme.Modules.restrictAdjunction (chartTrans A h hW hU)).counit.app _ :=
    Adjunction.homEquiv_counit _ _ _ _
  rw [e]
  rfl

/-- The comparison of the twists along a chart transition is multiplicative. -/
public theorem transTwist_absoluteTwistProduct (i j : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (a : (twistingSheaf (A.grading U) i).val.obj (op (chartTrans A h hW hU ''ᵁ V)))
    (b : (twistingSheaf (A.grading U) j).val.obj (op (chartTrans A h hW hU ''ᵁ V))) :
    (transTwist A h hW hU (i + j)).val.app (op V)
        (absoluteTwistProduct (A.grading U) i j _ a b) =
      absoluteTwistProduct (A.grading W) i j V ((transTwist A h hW hU i).val.app (op V) a)
        ((transTwist A h hW hU j).val.app (op V) b) := by
  refine Subtype.ext (funext fun y => ?_)
  refine ((transTwist_app_apply A h hW hU (i + j) V _ y).trans ?_).trans
    (Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply
        (A.grading W) i j V _ _ y).symm
  refine (congrArg (Stacks.ProjTwistComparison.fibreMap (A.res h) (irrelevant_le_res A h hW hU) y.1)
    (Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply (A.grading U) i j
      (chartTrans A h hW hU ''ᵁ V) a b ⟨_, ⟨y.1, y.2, rfl⟩⟩)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (transTwist_app_apply A h hW hU i V a y).symm
    (transTwist_app_apply A h hW hU j V b y).symm)
  exact Stacks.ProjTwistComparison.fibreMap_mul (A.res h) (irrelevant_le_res A h hW hU) y.1 _ _

/-- The comparison of the twists along a chart transition carries the homogeneous section of an
element to the homogeneous section of its restriction. -/
public theorem transTwist_degreeSection (k : ℕ) (c : (A.grading U) k) :
    (transTwist A h hW hU (k : ℤ)).val.app (op ⊤)
        ((twistingSheaf (A.grading U) (k : ℤ)).val.map
          (homOfLE (le_top : chartTrans A h hW hU ''ᵁ ⊤ ≤ ⊤)).op
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) k c)) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading W) k
        ⟨A.res h c, (A.res h).map_mem c.2⟩ := by
  refine Subtype.ext (funext fun y => ?_)
  refine (transTwist_app_apply A h hW hU (k : ℤ) ⊤ _ y).trans ?_
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply
      (A.grading W) k _ y).symm
  refine (congrArg _ (Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply
      (A.grading U) k c _)).trans ?_
  exact (Stacks.ProjTwistComparison.fibreMap_mk (A.res h)
      (irrelevant_le_res A h hW hU) y.1 _ 1).trans
    (congrArg (LocalizedModule.mk _) (Subtype.ext (map_one (A.res h))))

/-- The image of an open of the smaller chart in the relative Proj, computed through the chart
transition. -/
public theorem image_chartTrans (V : (AlgebraicGeometry.Proj (A.grading W)).Opens) :
    (relativeProj A).chart U hU ''ᵁ (chartTrans A h hW hU ''ᵁ V) =
      (relativeProj A).chart W hW ''ᵁ V := by
  rw [← Scheme.Hom.comp_image]
  exact Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.image_congr_morphism
    (chartTrans_comp_chart A h hW hU) V

variable (D : TwistData A)

/-- **The discrepancy between the chart identifications over `W` and over `U`**: the chart
identification over `W` inverted, then the one over `U` restricted along the chart transition,
then the comparison of the twists. -/
public def transEndo (n : ℤ) :
    twistingSheaf (A.grading W) n ⟶ twistingSheaf (A.grading W) n :=
  (D.chartData.chartIso W hW n).inv ≫
    (Scheme.Modules.restrictFunctorCongr (chartTrans_comp_chart A h hW hU).symm).hom.app _ ≫
    (Scheme.Modules.restrictFunctorComp (chartTrans A h hW hU)
      ((relativeProj A).chart U hU)).hom.app _ ≫
    (Scheme.Modules.restrictFunctor (chartTrans A h hW hU)).map
      (D.chartData.chartIso U hU n).hom ≫
    transTwist A h hW hU n

/-- The discrepancy on sections. -/
public theorem transEndo_app (n : ℤ) (V : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (y : (twistingSheaf (A.grading W) n).val.obj (op V)) :
    (transEndo A h hW hU D n).val.app (op V) y =
      (transTwist A h hW hU n).val.app (op V)
        ((D.chartData.chartIso U hU n).hom.val.app (op (chartTrans A h hW hU ''ᵁ V))
          ((D.algebra.piece n).val.map (eqToHom (image_chartTrans A h hW hU V)).op
            ((D.chartData.chartIso W hW n).inv.val.app (op V) y))) := by
  refine congrArg ((transTwist A h hW hU n).val.app (op V)) (congrArg
    ((D.chartData.chartIso U hU n).hom.val.app (op (chartTrans A h hW hU ''ᵁ V))) ?_)
  exact ConcreteCategory.congr_hom (presheaf_map_comp₂ (D.algebra.piece n).val.presheaf _ _ _) _


/-- **The discrepancy is multiplicative.** -/
public theorem isMultiplicative_transEndo :
    Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative (transEndo A h hW hU D) := by
  intro i j V a b
  refine (transEndo_app A h hW hU D (i + j) V _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (absoluteTwistProduct (A.grading W) i j V)
    (transEndo_app A h hW hU D i V a).symm (transEndo_app A h hW hU D j V b).symm)
  refine Eq.trans ?_ (transTwist_absoluteTwistProduct A h hW hU i j V _ _)
  refine congrArg ((transTwist A h hW hU (i + j)).val.app (op V)) ?_
  refine Eq.trans ?_ (chartIso_hom_mul D U hU i j (chartTrans A h hW hU ''ᵁ V) _ _)
  refine congrArg ((D.chartData.chartIso U hU (i + j)).hom.val.app
    (op (chartTrans A h hW hU ''ᵁ V))) ?_
  refine Eq.trans ?_ ((D.algebra.mul i j).naturality
    (eqToHom (image_chartTrans A h hW hU V)).op _ _)
  exact congrArg ((D.algebra.piece (i + j)).val.map (eqToHom (image_chartTrans A h hW hU V)).op)
    (D.chartIso_mul W hW i j V a b)

/-- The image of the chart over `W` lies in the image of the chart over `U`. -/
public theorem chart_image_le_chart_image :
    (relativeProj A).chart W hW ''ᵁ ⊤ ≤ (relativeProj A).chart U hU ''ᵁ ⊤ :=
  (image_chartTrans A h hW hU ⊤).symm.le.trans (((relativeProj A).chart U hU).image_mono le_top)

/-- **The discrepancy fixes the homogeneous sections of restricted elements.** -/
public theorem fixesResDegreeSections_transEndo :
    Stacks.AlgebraicGeometry.RelativeTwistRigidity.FixesResDegreeSections (A.res h)
      (transEndo A h hW hU D) := by
  intro k c
  obtain ⟨c, hcm⟩ := c
  obtain ⟨b, rfl⟩ := hcm
  have hw : (⟨(A.res h) (DirectSum.of (A.sectionPieces U) k b),
      (A.res h).map_mem (A.of_mem_grading U b)⟩ : A.grading W k) =
      ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
        A.of_mem_grading W (A.resPiece h k b)⟩ :=
    Subtype.ext (A.resRingHom_of h b)
  refine (congrArg (fun w : A.grading W k => (transEndo A h hW hU D (k : ℤ)).val.app (op ⊤)
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading W) k w)) hw).trans ?_
  refine (transEndo_app A h hW hU D (k : ℤ) ⊤ _).trans ?_
  have hA : (D.chartData.chartIso W hW (k : ℤ)).inv.val.app (op ⊤)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading W) k
        ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
          A.of_mem_grading W (A.resPiece h k b)⟩) =
      (D.algebra.piece (k : ℤ)).val.map (eqToHom (D.chartData.chart_range W hW)).op
        ((D.ψ k).val.app (op W) (A.resPiece h k b)) := by
    rw [← chartIso_hom_psi D W hW k (A.resPiece h k b)]
    exact Stacks.AlgebraicGeometry.TwistRigidity.iso_inv_app_hom_app _ _ _
  have hB := PresheafOfModules.naturality_apply (D.ψ k).val (homOfLE h).op b
  have hC : (D.algebra.piece (k : ℤ)).val.map (eqToHom (image_chartTrans A h hW hU ⊤)).op
      ((D.algebra.piece (k : ℤ)).val.map (eqToHom (D.chartData.chart_range W hW)).op
        ((D.algebra.piece (k : ℤ)).val.map
          (homOfLE (show (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U from
            fun _ hx => h hx)).op
          ((D.ψ k).val.app (op U) b))) =
      (D.algebra.piece (k : ℤ)).val.map
        (homOfLE (((relativeProj A).chart U hU).image_mono
          (le_top : chartTrans A h hW hU ''ᵁ ⊤ ≤ ⊤))).op
        ((D.algebra.piece (k : ℤ)).val.map (eqToHom (D.chartData.chart_range U hU)).op
          ((D.ψ k).val.app (op U) b)) :=
    val_map₃ (D.algebra.piece (k : ℤ)) _ _ _ _ _ _
  have hnat := PresheafOfModules.naturality_apply (D.chartData.chartIso U hU (k : ℤ)).hom.val
    (homOfLE (le_top : chartTrans A h hW hU ''ᵁ ⊤ ≤ ⊤)).op
    ((D.algebra.piece (k : ℤ)).val.map (eqToHom (D.chartData.chart_range U hU)).op
      ((D.ψ k).val.app (op U) b))
  refine (congrArg (fun z => (transTwist A h hW hU (k : ℤ)).val.app (op ⊤)
    ((D.chartData.chartIso U hU (k : ℤ)).hom.val.app (op (chartTrans A h hW hU ''ᵁ ⊤))
      ((D.algebra.piece (k : ℤ)).val.map (eqToHom (image_chartTrans A h hW hU ⊤)).op z)))
    hA).trans ?_
  refine (congrArg (fun z => (transTwist A h hW hU (k : ℤ)).val.app (op ⊤)
    ((D.chartData.chartIso U hU (k : ℤ)).hom.val.app (op (chartTrans A h hW hU ''ᵁ ⊤))
      ((D.algebra.piece (k : ℤ)).val.map (eqToHom (image_chartTrans A h hW hU ⊤)).op
        ((D.algebra.piece (k : ℤ)).val.map (eqToHom (D.chartData.chart_range W hW)).op z))))
    hB).trans ?_
  refine (congrArg (fun z => (transTwist A h hW hU (k : ℤ)).val.app (op ⊤)
    ((D.chartData.chartIso U hU (k : ℤ)).hom.val.app (op (chartTrans A h hW hU ''ᵁ ⊤)) z))
    hC).trans ?_
  refine (congrArg (fun z => (transTwist A h hW hU (k : ℤ)).val.app (op ⊤) z) hnat).trans ?_
  refine (congrArg (fun z => (transTwist A h hW hU (k : ℤ)).val.app (op ⊤)
    ((twistingSheaf (A.grading U) (k : ℤ)).val.map
      (homOfLE (le_top : chartTrans A h hW hU ''ᵁ ⊤ ≤ ⊤)).op z))
    (chartIso_hom_psi D U hU k b)).trans ?_
  exact transTwist_degreeSection A h hW hU k _

/-- **The discrepancy is the identity**, by relative rigidity. -/
public theorem transEndo_eq_id (n : ℤ) : transEndo A h hW hU D n = 𝟙 _ :=
  Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res A W U h hW hU
    (isMultiplicative_transEndo A h hW hU D) (fixesResDegreeSections_transEndo A h hW hU D) n

/-- **The chart identifications are compatible with the chart transitions**: on sections over an
open `V` of `Proj Γ(W, A)`, the chart identification over `W` is the chart identification over `U`
on the image of `V`, followed by the comparison of the twists. -/
public theorem chartIso_transition (n : ℤ) (V : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (x : (D.algebra.piece n).val.obj (op ((relativeProj A).chart W hW ''ᵁ V))) :
    (D.chartData.chartIso W hW n).hom.val.app (op V) x =
      (transTwist A h hW hU n).val.app (op V)
        ((D.chartData.chartIso U hU n).hom.val.app (op (chartTrans A h hW hU ''ᵁ V))
          ((D.algebra.piece n).val.map (eqToHom (image_chartTrans A h hW hU V)).op x)) := by
  have h1 := congrArg (fun α : twistingSheaf (A.grading W) n ⟶ twistingSheaf (A.grading W) n =>
    α.val.app (op V) ((D.chartData.chartIso W hW n).hom.val.app (op V) x))
    (transEndo_eq_id A h hW hU D n)
  refine (h1.symm.trans (transEndo_app A h hW hU D n V _)).trans ?_
  exact congrArg (fun z => (transTwist A h hW hU n).val.app (op V)
    ((D.chartData.chartIso U hU n).hom.val.app (op (chartTrans A h hW hU ''ᵁ V))
      ((D.algebra.piece n).val.map (eqToHom (image_chartTrans A h hW hU V)).op z)))
    (Stacks.AlgebraicGeometry.TwistRigidity.iso_inv_app_hom_app _ _ _)

/-- The point below a point of the smaller chart lies in the chart preimage of an open when the
point does. -/
public theorem chartTrans_mem (V : (relativeProj A).scheme.Opens)
    (z : AlgebraicGeometry.Proj (A.grading W)) (hz : z ∈ (relativeProj A).chart W hW ⁻¹ᵁ V) :
    ProjectiveSpectrum.comapFun (A.res h) (irrelevant_le_res A h hW hU) z ∈
      (relativeProj A).chart U hU ⁻¹ᵁ V := by
  have hz' : z ∈ (chartTrans A h hW hU ≫ (relativeProj A).chart U hU) ⁻¹ᵁ V := by
    rw [chartTrans_comp_chart]; exact hz
  exact hz'

/-- **The chart comparisons of twist data along a chart transition, pointwise.** -/
public theorem chartPush_apply_of_le (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (x : (D.algebra.piece n).val.obj (op V))
    (z : ((relativeProj A).chart W hW ⁻¹ᵁ V : (AlgebraicGeometry.Proj (A.grading W)).Opens)) :
    ((TwistExistence.chartPush D W hW n).val.app (op V) x).1 z =
      Stacks.ProjTwistComparison.fibreMap (A.res h) (irrelevant_le_res A h hW hU) z.1
        (((TwistExistence.chartPush D U hU n).val.app (op V) x).1
          ⟨_, chartTrans_mem A h hW hU V z.1 z.2⟩) := by
  refine (congrArg (fun s => s.1 z) (chartIso_transition A h hW hU D n
    ((relativeProj A).chart W hW ⁻¹ᵁ V) ((D.algebra.piece n).val.map
      (homOfLE (((relativeProj A).chart W hW).image_preimage_le V)).op x))).trans ?_
  refine (transTwist_app_apply A h hW hU n _ _ z).trans ?_
  congr 1
  have hle : chartTrans A h hW hU ''ᵁ ((relativeProj A).chart W hW ⁻¹ᵁ V) ≤
      (relativeProj A).chart U hU ⁻¹ᵁ V := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := hp
    exact chartTrans_mem A h hW hU V q hq
  have hnat := PresheafOfModules.naturality_apply (D.chartData.chartIso U hU n).hom.val
    (homOfLE hle).op ((D.algebra.piece n).val.map
      (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x)
  have key : (D.chartData.chartIso U hU n).hom.val.app
      (op (chartTrans A h hW hU ''ᵁ ((relativeProj A).chart W hW ⁻¹ᵁ V)))
      ((D.algebra.piece n).val.map (eqToHom (image_chartTrans A h hW hU _)).op
        ((D.algebra.piece n).val.map
          (homOfLE (((relativeProj A).chart W hW).image_preimage_le V)).op x)) =
      (twistingSheaf (A.grading U) n).val.map (homOfLE hle).op
        ((TwistExistence.chartPush D U hU n).val.app (op V) x) := by
    refine Eq.trans ?_ hnat
    refine congrArg ((D.chartData.chartIso U hU n).hom.val.app _) ?_
    have hk : (relativeProj A).chart W hW ''ᵁ ((relativeProj A).chart W hW ⁻¹ᵁ V) ≤ V :=
      ((relativeProj A).chart W hW).image_preimage_le V
    have m1 : (D.algebra.piece n).val.map (eqToHom (image_chartTrans A h hW hU _)).op
        ((D.algebra.piece n).val.map (homOfLE hk).op x) =
        (D.algebra.piece n).val.map (homOfLE ((image_chartTrans A h hW hU _).le.trans hk)).op x :=
      PresheafOfModules.map_map_eq_map _ _ _ _ x
    have m2 : (D.algebra.piece n).val.map
        (homOfLE (((relativeProj A).chart U hU).image_mono hle)).op
        ((D.algebra.piece n).val.map
          (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x) =
        (D.algebra.piece n).val.map (homOfLE ((image_chartTrans A h hW hU _).le.trans hk)).op x :=
      PresheafOfModules.map_map_eq_map _ _ _ _ x
    exact m1.trans m2.symm
  rw [key]
  rfl

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end

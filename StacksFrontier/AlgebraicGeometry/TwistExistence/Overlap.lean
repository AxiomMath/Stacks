module

public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Basic
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Psi

/-!
# The chart comparisons of two twist data agree on the overlaps

`StacksFrontier/AlgebraicGeometry/TwistExistence/Chart.lean` builds, for two sets of twist data
`D`, `E` on a relative Proj and each affine open `U` of the base, the comparison
`Stacks.AlgebraicGeometry.TwistExistence.cmp D E U hU n` of their `n`-th glued pieces over the
inverse image of `U`. This file proves that any two of these comparisons agree where both are
defined, which is what a glueing argument needs.

**This is the mathematical content of the existence half of Tag 01NR's first uniqueness
assertion**, and it is where rigidity enters. For a *nested* pair of affine opens `W ⊆ U` the
comparison coming from `U`, read through the chart of `W`, is an endomorphism family of the
twists on `Proj Γ(W, A)`; it is multiplicative because it is built out of the two data's own
chart identifications, and it fixes the homogeneous sections attached to the elements restricted
from `U` because `ψ` is a morphism of sheaves and `ψ_chart` holds at both opens. Those are
exactly the two hypotheses of `Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res`, so the
endomorphism is the identity and the two comparisons agree. The general case follows by covering.

**Nothing about Tag 01NO's transition comparisons is used.** In particular the missing
multiplicativity of a composite of Tag 01NO comparisons — the one statement the glueing of the
twists themselves is conditional on,
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` — is not needed here: the
comparison of two twist data over a chart is not a composite of Tag 01NO comparisons but a
cancellation of the data's own chart identifications, whose multiplicativity *is* available, as
the field `isGradedChartIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistExistence.overlapIso`: the comparison coming from the larger
  affine open, pulled back along the chart of the smaller one.
* `Stacks.AlgebraicGeometry.TwistExistence.overlapEndo`: that pullback conjugated by the two
  data's chart identifications over the smaller open — an endomorphism family of the absolute
  twists there.

## Main results

* `Stacks.AlgebraicGeometry.TwistExistence.mapSection_overlapEndo`: the bridge, as in
  `Stacks.AlgebraicGeometry.TwistRigidity.mapSection_chartEndo`.
* `Stacks.AlgebraicGeometry.TwistExistence.isMultiplicative_overlapEndo` and
  `fixesResDegreeSections_overlapEndo`: **the two hypotheses of relative rigidity.**
* `Stacks.AlgebraicGeometry.TwistExistence.overlapEndo_eq_id`: hence the endomorphism is the
  identity.
* `Stacks.AlgebraicGeometry.TwistExistence.cmp_agreeOn_nested`: **the comparisons attached to a
  nested pair of affine opens agree** on the inverse image of the smaller.
* `Stacks.AlgebraicGeometry.TwistExistence.cmp_agreeOn`: **any two comparisons agree where both
  are defined.**

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace TopCat.Sheaf.LocalModuleEquiv

/-- **A local isomorphism commutes with transport of a section along an equality of opens.** The
two containment proofs are proofs of the same proposition once the equality is substituted
away. -/
public theorem app_rec {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} 𝒪} {W₀ : Opens X} (e : LocalModuleEquiv M N W₀)
    {V V' : Opens X} (hh : V = V') (hV : V ≤ W₀) (hV' : V' ≤ W₀) (z : M.obj (op V)) :
    e.app V' hV' (hh ▸ z) = (hh ▸ e.app V hV z : N.obj (op V')) := by
  subst hh
  rfl

end TopCat.Sheaf.LocalModuleEquiv

namespace PresheafOfModules

/-- **Transport along an equality of opens is a congruence.** Stated so that a consumer never has
to elaborate a motive mentioning `▸`. -/
public theorem rec_congr {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} 𝒪) {W W' : Opens X} (hh : W = W') {z z' : M.obj (op W)}
    (hzz : z = z') : (hh ▸ z : M.obj (op W')) = hh ▸ z' := by
  subst hh
  exact hzz

end PresheafOfModules

namespace Stacks.AlgebraicGeometry.TwistExistence

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- The inverse images of a nested pair of opens of the base are nested. -/
public theorem preimage_le_preimage (W U : S.Opens) (h : W ≤ U) :
    (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U :=
  fun _ hx => h hx

/-- The image of the chart over the smaller affine open lies in the inverse image of the
larger. -/
public theorem chart_image_le (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W) :
    (relativeProj A).chart W hW ''ᵁ (⊤ : (AlgebraicGeometry.Proj (A.grading W)).Opens) ≤
      (relativeProj A).toBase ⁻¹ᵁ U :=
  (RelativeProjTwistGlue.chart_image_top (relativeProj A) W hW).le.trans
    (preimage_le_preimage W U h)

section Nested

variable (D E : TwistData A) (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W)
  (hU : IsAffineOpen U)

include D E h hW hU

/-- **The comparison attached to the larger affine open, pulled back along the chart of the
smaller one**: an isomorphism of the restrictions of the two glued pieces to that chart. -/
public def overlapIso (n : ℤ) :
    Scheme.Modules.restrict (D.algebra.piece n) ((relativeProj A).chart W hW) ≅
      Scheme.Modules.restrict (E.algebra.piece n) ((relativeProj A).chart W hW) :=
  isoOfLocalEquiv
    (restrictLocalEquiv ((relativeProj A).chart W hW) (cmp D E U hU n)
      (chart_image_le W U h hW))

/-- **The overlap endomorphism**: the pulled-back comparison conjugated by the two data's chart
identifications over the smaller affine open. Relative rigidity will force it to be the
identity. -/
public def overlapEndo (n : ℤ) :
    twistingSheaf (A.grading W) n ⟶ twistingSheaf (A.grading W) n :=
  (D.chartData.chartIso W hW n).inv ≫ (overlapIso D E W U h hW hU n).hom ≫
    (E.chartData.chartIso W hW n).hom

/-- **The bridge.** Under the section comparisons of the two twist data over the smaller affine
open, the overlap endomorphism becomes the comparison attached to the larger one. -/
public theorem mapSection_overlapEndo (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (a : (twistingSheaf (A.grading W) n).val.obj (op V)) :
    E.chartData.mapSection W hW n V
        ((overlapEndo D E W U h hW hU n).val.app (op V) a) =
      (cmp D E U hU n).app ((relativeProj A).chart W hW ''ᵁ V)
        ((((relativeProj A).chart W hW).image_mono le_top).trans (chart_image_le W U h hW))
        (D.chartData.mapSection W hW n V a) :=
  TwistRigidity.iso_inv_app_hom_app (E.chartData.chartIso W hW n) (op V) _

/-- The overlap endomorphism sends `a` to `b` once the comparison attached to the larger affine
open sends the section of `a` to the section of `b`. -/
private theorem overlapEndo_app_eq_of_cmp_eq (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (a b : (twistingSheaf (A.grading W) n).val.obj (op V))
    (hab : (cmp D E U hU n).app ((relativeProj A).chart W hW ''ᵁ V)
        ((((relativeProj A).chart W hW).image_mono le_top).trans (chart_image_le W U h hW))
        (D.chartData.mapSection W hW n V a) = E.chartData.mapSection W hW n V b) :
    (overlapEndo D E W U h hW hU n).val.app (op V) a = b :=
  TwistRigidity.mapSection_injective E.chartData W hW n V
    ((mapSection_overlapEndo D E W U h hW hU n V a).trans hab)

/-- **The overlap endomorphism is multiplicative.** Both data's chart identifications carry the
canonical product of absolute twist sections to the product of their glued algebras, and the
comparison between the two glued algebras is multiplicative. -/
public theorem isMultiplicative_overlapEndo :
    TwistRigidity.IsMultiplicative (overlapEndo D E W U h hW hU) := by
  intro i j V a b
  refine overlapEndo_app_eq_of_cmp_eq D E W U h hW hU (i + j) V _ _ ?_
  refine Eq.trans (ChartTransRelativeProj.app_congr_arg (cmp D E U hU (i + j)) _
    (D.chartIso_mul W hW i j V a b)) ?_
  refine Eq.trans (cmp_mul D E U hU i j ((relativeProj A).chart W hW ''ᵁ V) _ _ _) ?_
  refine Eq.trans (TwistRigidity.mul_app_congr E.algebra i j _
    (mapSection_overlapEndo D E W U h hW hU i V a).symm
    (mapSection_overlapEndo D E W U h hW hU j V b).symm) ?_
  exact (E.chartIso_mul W hW i j V _ _).symm

/-- **The overlap endomorphism fixes the homogeneous sections attached to the elements restricted
from the larger affine open.** This is where `ψ` being a morphism of sheaves is used: an element
of the graded ring of sections over the smaller open which is a restriction has its homogeneous
section carried, by both data's chart identifications, to the restriction of the section over the
larger open, where the comparison is already known to commute with the section maps. -/
public theorem fixes_degreeSection_resPiece (k : ℕ) (b : A.sectionPieces U k) :
    (overlapEndo D E W U h hW hU (k : ℤ)).val.app (op ⊤)
        (degreeSection (A.grading W) k
          ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
            A.of_mem_grading W (A.resPiece h k b)⟩) =
      degreeSection (A.grading W) k
        ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
          A.of_mem_grading W (A.resPiece h k b)⟩ := by
  refine overlapEndo_app_eq_of_cmp_eq D E W U h hW hU (k : ℤ) ⊤ _ _ ?_
  refine Eq.trans (ChartTransRelativeProj.app_congr_arg (cmp D E U hU (k : ℤ)) _
    (D.ψ_chart W hW k (A.resPiece h k b))) ?_
  refine Eq.trans (TopCat.Sheaf.LocalModuleEquiv.app_rec (cmp D E U hU (k : ℤ))
    (D.chartData.chart_range W hW).symm (preimage_le_preimage W U h) _ _) ?_
  refine Eq.trans ?_ (E.ψ_chart W hW k (A.resPiece h k b)).symm
  refine PresheafOfModules.rec_congr (E.algebra.piece (k : ℤ)).val
    (D.chartData.chart_range W hW).symm ?_
  refine Eq.trans (ChartTransRelativeProj.app_congr_arg (cmp D E U hU (k : ℤ)) _
    (PresheafOfModules.naturality_apply (D.ψ k).val (homOfLE h).op b)) ?_
  refine Eq.trans ((cmp D E U hU (k : ℤ)).naturality le_rfl
    (preimage_le_preimage W U h) ((D.ψ k).val.app (op U) b)) ?_
  refine Eq.trans (congrArg ((E.algebra.piece (k : ℤ)).val.map
    (homOfLE (preimage_le_preimage W U h)).op) (cmp_psi D E U hU k b)) ?_
  exact (PresheafOfModules.naturality_apply (E.ψ k).val (homOfLE h).op b).symm

/-- **The overlap endomorphism satisfies the relative fixing hypothesis of
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res`.** -/
public theorem fixesResDegreeSections_overlapEndo :
    RelativeTwistRigidity.FixesResDegreeSections (A.res h)
      (overlapEndo D E W U h hW hU) := by
  intro k c
  obtain ⟨b, hb⟩ := c.2
  have hw : (⟨(A.res h) (c : A.sectionRing U), (A.res h).map_mem c.2⟩ : A.grading W k) =
      ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
        A.of_mem_grading W (A.resPiece h k b)⟩ :=
    Subtype.ext ((congrArg (fun z : A.sectionRing U => (A.res h) z) hb).symm.trans
      (A.resRingHom_of h b))
  exact (congrArg (fun w : A.grading W k =>
      (overlapEndo D E W U h hW hU (k : ℤ)).val.app (op ⊤)
        (degreeSection (A.grading W) k w)) hw).trans
    ((fixes_degreeSection_resPiece D E W U h hW hU k b).trans
      (congrArg (fun w : A.grading W k => degreeSection (A.grading W) k w) hw).symm)

/-- **The overlap endomorphism is the identity**, by relative rigidity. -/
public theorem overlapEndo_eq_id (n : ℤ) :
    overlapEndo D E W U h hW hU n = 𝟙 (twistingSheaf (A.grading W) n) :=
  RelativeTwistRigidity.eq_id_res A W U h hW hU
    (isMultiplicative_overlapEndo D E W U h hW hU)
    (fixesResDegreeSections_overlapEndo D E W U h hW hU) n

/-- **The comparisons attached to a nested pair of affine opens agree**, on the sections over
every open of the relative Proj inside the inverse image of the smaller. -/
public theorem cmp_agreeOn_nested (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hVU : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (hVW : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    ChartTransRelativeProj.AgreeOn (cmp D E U hU n) (cmp D E W hW n) V hVU hVW := by
  intro x
  have hIm : (relativeProj A).chart W hW ''ᵁ ((relativeProj A).chart W hW ⁻¹ᵁ V) = V :=
    TwistUnique.image_preimage_eq_self ((relativeProj A).chart W hW)
      (hVW.trans (RelativeProjTwistGlue.chart_image_top (relativeProj A) W hW).ge)
  have hid : (overlapEndo D E W U h hW hU n).val.app
      (op ((relativeProj A).chart W hW ⁻¹ᵁ V)) ((chartLoc D W hW n).app V hVW x) =
      (chartLoc D W hW n).app V hVW x :=
    congrArg (fun φ : twistingSheaf (A.grading W) n ⟶ twistingSheaf (A.grading W) n =>
      φ.val.app (op ((relativeProj A).chart W hW ⁻¹ᵁ V)) ((chartLoc D W hW n).app V hVW x))
      (overlapEndo_eq_id D E W U h hW hU n)
  have hkey := (congrArg
      (E.chartData.mapSection W hW n ((relativeProj A).chart W hW ⁻¹ᵁ V)) hid).symm.trans
    (mapSection_overlapEndo D E W U h hW hU n ((relativeProj A).chart W hW ⁻¹ᵁ V)
      ((chartLoc D W hW n).app V hVW x))
  have hleft : E.chartData.mapSection W hW n ((relativeProj A).chart W hW ⁻¹ᵁ V)
      ((chartLoc D W hW n).app V hVW x) =
      (E.algebra.piece n).val.map
        (homOfLE (((relativeProj A).chart W hW).image_preimage_le V)).op
        ((cmp D E W hW n).app V hVW x) := by
    refine Eq.trans (congrArg
      (E.chartData.mapSection W hW n ((relativeProj A).chart W hW ⁻¹ᵁ V))
      (chartLoc_cmp D E W hW n V hVW x).symm) ?_
    exact mapSection_chartLoc E W hW n V hVW ((cmp D E W hW n).app V hVW x)
  have hright : (cmp D E U hU n).app ((relativeProj A).chart W hW ''ᵁ
        ((relativeProj A).chart W hW ⁻¹ᵁ V))
      ((((relativeProj A).chart W hW).image_mono le_top).trans (chart_image_le W U h hW))
      (D.chartData.mapSection W hW n ((relativeProj A).chart W hW ⁻¹ᵁ V)
        ((chartLoc D W hW n).app V hVW x)) =
      (E.algebra.piece n).val.map
        (homOfLE (((relativeProj A).chart W hW).image_preimage_le V)).op
        ((cmp D E U hU n).app V hVU x) := by
    refine Eq.trans (ChartTransRelativeProj.app_congr_arg (cmp D E U hU n) _
      (mapSection_chartLoc D W hW n V hVW x)) ?_
    exact (cmp D E U hU n).naturality hVU
      (((relativeProj A).chart W hW).image_preimage_le V) x
  have hcombined := ((hleft.symm.trans hkey).trans hright).symm
  have hinj := PresheafOfModules.map_map_eq_self (E.algebra.piece n).val
    (homOfLE (((relativeProj A).chart W hW).image_preimage_le V)).op (homOfLE hIm.ge).op
  exact (hinj _).symm.trans
    ((congrArg ((E.algebra.piece n).val.map (homOfLE hIm.ge).op) hcombined).trans (hinj _))

end Nested

/-- **Any two chart comparisons agree where both are defined.** The two inverse images are
covered by the inverse images of the affine opens of the base below both, and over each of those
the nested case applies twice. -/
public theorem cmp_agreeOn (D E : TwistData A) (P Q : S.Opens) (hP : IsAffineOpen P)
    (hQ : IsAffineOpen Q) (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hVP : V ≤ (relativeProj A).toBase ⁻¹ᵁ P) (hVQ : V ≤ (relativeProj A).toBase ⁻¹ᵁ Q) :
    ChartTransRelativeProj.AgreeOn (cmp D E P hP n) (cmp D E Q hQ n) V hVP hVQ := by
  refine ChartTransRelativeProj.agreeOn_of_cover (E.algebra.piece n).isSheaf _ _
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ P ⊓ Q} =>
      (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens))
    (fun r V' hV'P hV'Q hV'r x => ?_) V hVP hVQ
    (ChartTransRelativeProj.le_iSup_preimage_inf A P Q V hVP hVQ)
  refine Eq.trans (cmp_agreeOn_nested D E (r.1.1 : S.Opens) P (r.2.trans inf_le_left) r.1.2 hP n
    V' hV'P hV'r x) ?_
  exact (cmp_agreeOn_nested D E (r.1.1 : S.Opens) Q (r.2.trans inf_le_right) r.1.2 hQ n
    V' hV'Q hV'r x).symm

end Stacks.AlgebraicGeometry.TwistExistence

end

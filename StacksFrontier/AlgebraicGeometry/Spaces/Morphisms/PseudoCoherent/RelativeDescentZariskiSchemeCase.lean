module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentAffineModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentCapstone
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentSituationIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen

/-!
# The Zariski form of Stacks 0DKV on an affine model, from the case of schemes

Let `D` be Situation 0DKU whose limit is a limit of schemes on affine charts, let `Z'` be an
affine object of the site with `z : h_{Z'} ⟶ Y₀`, and let `R` represent the base changes
`Yᵢ ×_{Y₀} Z'` and `Y ×_{Y₀} Z'`.  Suppose `z` factors as `h_t ≫ w` through an affine object `V`
of the site, with `t : Z' ⟶ V` flat and locally of finite presentation on underlying schemes.
Then the affine schemes representing `Yᵢ ×_{Y₀} V` form an inverse system of schemes with limit
the scheme representing `Y ×_{Y₀} V`, and `Z' ⟶ V` makes it Situation 0DI6.  Its stages and its
limit are the schemes representing `Yᵢ ×_{Y₀} Z'` and `Y ×_{Y₀} Z'`, so the conclusion of
Stacks 0DI7 for it is
`AlgebraicGeometry.Space.RelativeDescentSituation.ZariskiModelHomDescent` for `R`.

The hypotheses are those of Stacks 0DI7 for `Z' ⟶ V`.

## Main definitions

All names are in the namespace `AlgebraicGeometry.Space.RelativeDescentSituation`.

* `AffineBaseChangeRepresentation.schemeDescent`: the inverse system of schemes underlying a
  representation, with its limit.
* `AffineBaseChangeRepresentation.chartSituation`: Situation 0DI6 over it given by `Z' ⟶ V`.
* `AffineBaseChangeRepresentation.chartStageIso`: the stages of that situation are the schemes
  representing the base changes `Yⱼ ×_{Y₀} Z'` along `z`.
* `AffineBaseChangeRepresentation.chartLimitIso`: the limit of that situation is the scheme
  representing the base change `Y ×_{Y₀} Z'` along `z`.

## Main results

* `AffineBaseChangeRepresentation.zariskiModelHomDescent_iff_chartSituation`:
  `ZariskiModelHomDescent` for `R` is the conclusion of Stacks 0DI7 for the chart situation.
* `zariskiModelHomDescent_of_affineChart`: `ZariskiModelHomDescent` from Stacks 0DI7.

## Implementation notes

Stacks 0DI7, which is `homDescent_of_isPseudoCoherent_of_locallyHasFiniteTorDimension` in the
namespace `AlgebraicGeometry.RelativeDescentSituation`, is stated for index types in the universe
of the schemes, so the index type `I` of `D` lives in universe `u` here.  The fixed stage of the
chart situation is the representing object of `Y_{i₀} ×_{Y₀} V`, which is isomorphic to `V` but
not equal to it; the Tor-dimension hypothesis is asked over `V` and moved across that isomorphism
by `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_baseOpen_iff`.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category* C] {P X Y Z Z' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  {g : Y ⟶ Z}

/-- A square stays cartesian when the common target is moved along an isomorphism. -/
theorem of_comp_isIso_target (e : Z ⟶ Z') [IsIso e] (h : IsPullback fst snd (f ≫ e) (g ≫ e)) :
    IsPullback fst snd f g :=
  h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso e).symm (by simp) (by simp) (by simp)
    (by simp)

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

namespace RelativeDescentSituation

attribute [local instance] isDirected_laterIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I}

variable (D) in
/-- The chosen stage `i₀`, as a stage at or beyond itself. -/
abbrev laterIndexBase : D.LaterIndex := ⟨D.i₀, le_refl _⟩

namespace AffineBaseChangeRepresentation

variable {V : BigAffineFppf B S hS}
  {w : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ D.Y.obj (op D.i₀)}
  (RV : D.AffineBaseChangeRepresentation V w)

/-- The representing object of `Y_{i₀} ×_{Y₀} V` projects isomorphically onto `V`. -/
theorem isIso_q_laterIndexBase : IsIso (RV.q (laterIndexBase D)) := by
  have e : D.Y.map (homOfLE (laterIndexBase D).2).op = 𝟙 _ := by
    rw [show (homOfLE (laterIndexBase D).2).op = 𝟙 (op D.i₀) from Subsingleton.elim _ _]
    exact D.Y.map_id _
  have : IsIso (D.Y.map (homOfLE (laterIndexBase D).2).op) := by rw [e]; infer_instance
  have := (RV.isPullback (laterIndexBase D)).isIso_snd_of_isIso
  exact isIso_of_reflects_iso (RV.q (laterIndexBase D)) yoneda

variable (hRV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone RV.c))

/-- **The inverse system of affine schemes representing `Yᵢ ×_{Y₀} V`**, with the scheme
representing `Y ×_{Y₀} V` as its limit, and fixed index `i₀`. -/
def schemeDescent : AlgebraicGeometry.DescentSituation.{u, u} D.LaterIndex where
  system := RV.W ⋙ BigFppfOver.toScheme B S hS
  transition_affine {i j} f := by
    have := RV.isAffine_W i.unop
    have := RV.isAffine_W j.unop
    exact inferInstanceAs
      (AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (RV.W.map f)))
  quasiCompact i := by
    have := RV.isAffine_W i
    exact inferInstanceAs
      (CompactSpace ((BigFppfOver.toScheme B S hS).obj (RV.W.obj (op i))))
  quasiSeparated i := by
    have := RV.isAffine_W i
    exact inferInstanceAs
      (QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (RV.W.obj (op i))))
  limitCone := (BigFppfOver.toScheme B S hS).mapCone RV.c
  isLimit := hRV
  base := laterIndexBase D

variable {Z' : BigAffineFppf B S hS}
  (t : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj V)

/-- The morphism `Z' ⟶ V` read into the representing object of `Y_{i₀} ×_{Y₀} V`. -/
def chartMap : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ RV.W.obj (op (laterIndexBase D)) :=
  haveI := RV.isIso_q_laterIndexBase
  t ≫ inv (RV.q (laterIndexBase D))

/-- `chartMap t` followed by the projection onto `V` is `t`. -/
theorem chartMap_q : RV.chartMap t ≫ RV.q (laterIndexBase D) = t := by
  have := RV.isIso_q_laterIndexBase
  simp [chartMap]

/-- On underlying schemes, `chartMap t` followed by the projection onto `V` is `t`. -/
theorem toScheme_chartMap_comp :
    (BigFppfOver.toScheme B S hS).map (RV.chartMap t) ≫
        (BigFppfOver.toScheme B S hS).map (RV.q (laterIndexBase D)) =
      (BigFppfOver.toScheme B S hS).map t := by
  rw [← Functor.map_comp, chartMap_q]

/-- On underlying schemes, the representing object of `Y_{i₀} ×_{Y₀} V` projects
isomorphically onto `V`. -/
theorem isIso_toScheme_q_laterIndexBase :
    IsIso ((BigFppfOver.toScheme B S hS).map (RV.q (laterIndexBase D))) := by
  have := RV.isIso_q_laterIndexBase
  infer_instance

variable (hflat : Flat ((BigFppfOver.toScheme B S hS).map t))
  (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t))

include hflat in
/-- If `t` is flat on underlying schemes, then so is `chartMap t`. -/
theorem flat_toScheme_chartMap : Flat ((BigFppfOver.toScheme B S hS).map (RV.chartMap t)) := by
  have := RV.isIso_q_laterIndexBase
  rw [chartMap, Functor.map_comp, Functor.map_inv]
  infer_instance

include hlfp in
/-- If `t` is locally of finite presentation on underlying schemes, then `chartMap t` is of
finite presentation. -/
theorem finitePresentation_toScheme_chartMap :
    FinitePresentation ((BigFppfOver.toScheme B S hS).map (RV.chartMap t)) := by
  have := RV.isIso_q_laterIndexBase
  have := RV.isAffine_W (laterIndexBase D)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')) :=
    Z'.property
  refine FinitePresentation.mk ?_ inferInstance inferInstance
  rw [chartMap, Functor.map_comp, Functor.map_inv]
  infer_instance

/-- **Situation 0DI6 on the affine chart**: the inverse system `schemeDescent` of the schemes
representing `Yᵢ ×_{Y₀} V`, with `Z' ⟶ V` (read into the fixed stage) as the flat morphism of
finite presentation. -/
def chartSituation : AlgebraicGeometry.RelativeDescentSituation.{u, u} D.LaterIndex where
  descent := RV.schemeDescent hRV
  X₀ := Over.mk ((BigFppfOver.toScheme B S hS).map (RV.chartMap t))
  flat := RV.flat_toScheme_chartMap t hflat
  finitePresentation := RV.finitePresentation_toScheme_chartMap t hlfp

variable {z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ⟶ D.Y.obj (op D.i₀)}
  (ht : yoneda.map t ≫ w = z) (R : D.AffineBaseChangeRepresentation Z' z)

/-- The stage of `R` at `j` is the fibre product of `Z'` with the stage of `RV` over the fixed
stage of `RV`. -/
theorem isPullback_chartStage (j : D.LaterIndex) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (R.q j))
      ((BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t ht j))
      ((BigFppfOver.toScheme B S hS).map (RV.chartMap t))
      ((BigFppfOver.toScheme B S hS).map
        (RV.W.map (homOfLE (show laterIndexBase D ≤ j from j.2)).op)) := by
  have := RV.isIso_toScheme_q_laterIndexBase
  refine IsPullback.of_comp_isIso_target
    ((BigFppfOver.toScheme B S hS).map (RV.q (laterIndexBase D))) ?_
  rw [toScheme_chartMap_comp, ← Functor.map_comp, RV.map_q]
  exact (RV.isPullback_mapOfComp R t ht j).flip

/-- The limit of `R` is the fibre product of `Z'` with the limit of `RV` over the fixed stage
of `RV`. -/
theorem isPullback_chartLimit :
    IsPullback ((BigFppfOver.toScheme B S hS).map R.qc)
      ((BigFppfOver.toScheme B S hS).map (RV.mapOfCompPt R t ht))
      ((BigFppfOver.toScheme B S hS).map (RV.chartMap t))
      ((BigFppfOver.toScheme B S hS).map (RV.c.π.app (op (laterIndexBase D)))) := by
  have := RV.isIso_toScheme_q_laterIndexBase
  refine IsPullback.of_comp_isIso_target
    ((BigFppfOver.toScheme B S hS).map (RV.q (laterIndexBase D))) ?_
  rw [toScheme_chartMap_comp, ← Functor.map_comp, RV.π_q]
  exact (Stack.ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda
    (RV.isPullback_yoneda_mapOfCompPt R t ht)).flip

/-- **The stages of the chart situation are the schemes representing `Yⱼ ×_{Y₀} Z'`.** -/
def chartStageIso (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) :
    (BigFppfOver.toScheme B S hS).obj (R.W.obj (op j.1)) ≅
      (RV.chartSituation hRV t hflat hlfp).schemeAt j :=
  (RV.isPullback_chartStage t ht R j.1).isoPullback

/-- **The limit of the chart situation is the scheme representing `Y ×_{Y₀} Z'`.** -/
def chartLimitIso :
    (BigFppfOver.toScheme B S hS).obj R.c.pt ≅ (RV.chartSituation hRV t hflat hlfp).limitScheme :=
  (RV.isPullback_chartLimit t ht R).isoPullback

/-- `chartStageIso` followed by the map to the fixed stage is the projection `R.q j` of `R`. -/
theorem chartStageIso_hom_fst (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) :
    (RV.chartStageIso hRV t hflat hlfp ht R j).hom ≫
        (RV.chartSituation hRV t hflat hlfp).toFixedStage j =
      (BigFppfOver.toScheme B S hS).map (R.q j.1) :=
  IsPullback.isoPullback_hom_fst _

/-- `chartStageIso` followed by the second projection of the fibre product is the map from the
stage of `R` to the stage of `RV`. -/
theorem chartStageIso_hom_snd (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) :
    (RV.chartStageIso hRV t hflat hlfp ht R j).hom ≫
        pullback.snd (RV.chartSituation hRV t hflat hlfp).X₀.hom
          ((RV.chartSituation hRV t hflat hlfp).baseMap j) =
      (BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t ht j.1) :=
  IsPullback.isoPullback_hom_snd _

/-- `chartLimitIso` followed by the map to the fixed stage is the projection `R.qc` of `R`. -/
theorem chartLimitIso_hom_fst :
    (RV.chartLimitIso hRV t hflat hlfp ht R).hom ≫
        (RV.chartSituation hRV t hflat hlfp).limitToFixedStage =
      (BigFppfOver.toScheme B S hS).map R.qc :=
  IsPullback.isoPullback_hom_fst _

/-- `chartLimitIso` followed by the second projection of the fibre product is the map from the
limit of `R` to the limit of `RV`. -/
theorem chartLimitIso_hom_snd :
    (RV.chartLimitIso hRV t hflat hlfp ht R).hom ≫
        pullback.snd (RV.chartSituation hRV t hflat hlfp).X₀.hom
          ((RV.chartSituation hRV t hflat hlfp).descent.limitCone.π.app
            (op (RV.chartSituation hRV t hflat hlfp).descent.base)) =
      (BigFppfOver.toScheme B S hS).map (RV.mapOfCompPt R t ht) :=
  IsPullback.isoPullback_hom_snd _

/-- The inverse of `chartStageIso` followed by `R.q j` is the map to the fixed stage. -/
theorem chartStageIso_inv_q (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) :
    (RV.chartStageIso hRV t hflat hlfp ht R j).inv ≫ (BigFppfOver.toScheme B S hS).map (R.q j.1) =
      (RV.chartSituation hRV t hflat hlfp).toFixedStage j :=
  (Iso.inv_comp_eq _).2 (RV.chartStageIso_hom_fst hRV t hflat hlfp ht R j).symm

/-- The inverse of `chartLimitIso` followed by `R.qc` is the map from the limit to the fixed
stage. -/
theorem chartLimitIso_inv_qc :
    (RV.chartLimitIso hRV t hflat hlfp ht R).inv ≫ (BigFppfOver.toScheme B S hS).map R.qc =
      (RV.chartSituation hRV t hflat hlfp).limitToFixedStage :=
  (Iso.inv_comp_eq _).2 (RV.chartLimitIso_hom_fst hRV t hflat hlfp ht R).symm

/-- The identifications of the stages are compatible with the transitions. -/
theorem toScheme_map_comp_chartStageIso {i j : (RV.chartSituation hRV t hflat hlfp).LaterIndex}
    (h : i.1 ≤ j.1) :
    (BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op) ≫
        (RV.chartStageIso hRV t hflat hlfp ht R i).hom =
      (RV.chartStageIso hRV t hflat hlfp ht R j).hom ≫
        (RV.chartSituation hRV t hflat hlfp).transition h := by
  apply pullback.hom_ext
  · rw [Category.assoc, chartStageIso_hom_fst, Category.assoc,
      (RV.chartSituation hRV t hflat hlfp).transition_comp_toFixedStage h, chartStageIso_hom_fst]
    exact toScheme_map_comp_eq B S hS _ _ _ (R.map_q i.1 j.1 h)
  · rw [Category.assoc, chartStageIso_hom_snd, Category.assoc,
      AlgebraicGeometry.RelativeDescentSituation.transition, pullback.lift_snd,
      ← Category.assoc, chartStageIso_hom_snd]
    exact ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      ((congrArg (BigFppfOver.toScheme B S hS).map (RV.mapOfComp_naturality R t ht h)).trans
        ((BigFppfOver.toScheme B S hS).map_comp _ _))

/-- The identifications of the stages and of the limit are compatible with the projections. -/
theorem toScheme_map_π_comp_chartStageIso (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) :
    (BigFppfOver.toScheme B S hS).map (R.c.π.app (op j.1)) ≫
        (RV.chartStageIso hRV t hflat hlfp ht R j).hom =
      (RV.chartLimitIso hRV t hflat hlfp ht R).hom ≫
        (RV.chartSituation hRV t hflat hlfp).projection j := by
  apply pullback.hom_ext
  · rw [Category.assoc, chartStageIso_hom_fst, Category.assoc,
      (RV.chartSituation hRV t hflat hlfp).projection_comp_toFixedStage j, chartLimitIso_hom_fst]
    exact toScheme_map_comp_eq B S hS _ _ _ (R.π_q j.1)
  · rw [Category.assoc, chartStageIso_hom_snd, Category.assoc,
      AlgebraicGeometry.RelativeDescentSituation.projection, pullback.lift_snd,
      ← Category.assoc, chartLimitIso_hom_snd]
    exact ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      ((congrArg (BigFppfOver.toScheme B S hS).map (RV.mapOfCompPt_π R t ht j.1)).trans
        ((BigFppfOver.toScheme B S hS).map_comp _ _))

variable (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
  ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)))

/-- The bijection of derived morphism sets at a stage, from the stage of `R` to that of the chart
situation. -/
def chartHomStage (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex)
    (φ : (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j.1)).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j.1)).toLRSHom.toShHom).obj L) :
    (derivedPullback ((RV.chartSituation hRV t hflat hlfp).toFixedStage j).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((RV.chartSituation hRV t hflat hlfp).toFixedStage j).toLRSHom.toShHom).obj
        L :=
  Stacks.DerivedPullback.schemeFactorHom (RV.chartStageIso hRV t hflat hlfp ht R j).inv
    ((BigFppfOver.toScheme B S hS).map (R.q j.1))
    ((RV.chartSituation hRV t hflat hlfp).toFixedStage j)
    (RV.chartStageIso_inv_q hRV t hflat hlfp ht R j) K L φ

/-- The bijection of derived morphism sets at the limit. -/
def chartHomLimit
    (φ : (derivedPullback ((BigFppfOver.toScheme B S hS).map R.qc).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((BigFppfOver.toScheme B S hS).map R.qc).toLRSHom.toShHom).obj L) :
    (derivedPullback (RV.chartSituation hRV t hflat hlfp).limitToFixedStage.toLRSHom.toShHom).obj
        K ⟶
      (derivedPullback (RV.chartSituation hRV t hflat hlfp).limitToFixedStage.toLRSHom.toShHom).obj
        L :=
  Stacks.DerivedPullback.schemeFactorHom (RV.chartLimitIso hRV t hflat hlfp ht R).inv
    ((BigFppfOver.toScheme B S hS).map R.qc) (RV.chartSituation hRV t hflat hlfp).limitToFixedStage
    (RV.chartLimitIso_inv_qc hRV t hflat hlfp ht R) K L φ

/-- `chartHomStage` is bijective. -/
theorem bijective_chartHomStage (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) :
    Function.Bijective (RV.chartHomStage hRV t hflat hlfp ht R K L j) :=
  Stacks.DerivedPullback.bijective_schemeFactorHom _ _ _ _
    (RV.chartStageIso hRV t hflat hlfp ht R j).hom
    (RV.chartStageIso hRV t hflat hlfp ht R j).inv_hom_id
    (RV.chartStageIso hRV t hflat hlfp ht R j).hom_inv_id K L

/-- `chartHomLimit` is bijective. -/
theorem bijective_chartHomLimit : Function.Bijective (RV.chartHomLimit hRV t hflat hlfp ht R K L) :=
  Stacks.DerivedPullback.bijective_schemeFactorHom _ _ _ _
    (RV.chartLimitIso hRV t hflat hlfp ht R).hom (RV.chartLimitIso hRV t hflat hlfp ht R).inv_hom_id
    (RV.chartLimitIso hRV t hflat hlfp ht R).hom_inv_id K L

/-- The inverses of the identifications of the stages are compatible with the transitions. -/
theorem chartStageIso_inv_transition {i j : (RV.chartSituation hRV t hflat hlfp).LaterIndex}
    (h : i.1 ≤ j.1) :
    (RV.chartSituation hRV t hflat hlfp).transition h ≫
        (RV.chartStageIso hRV t hflat hlfp ht R i).inv =
      (RV.chartStageIso hRV t hflat hlfp ht R j).inv ≫
        (BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op) :=
  (CommSq.vert_inv ⟨RV.toScheme_map_comp_chartStageIso hRV t hflat hlfp ht R h⟩).w

/-- The inverses of the identifications of the stages and of the limit are compatible with the
projections. -/
theorem chartLimitIso_inv_projection (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) :
    (RV.chartSituation hRV t hflat hlfp).projection j ≫
        (RV.chartStageIso hRV t hflat hlfp ht R j).inv =
      (RV.chartLimitIso hRV t hflat hlfp ht R).inv ≫
        (BigFppfOver.toScheme B S hS).map (R.c.π.app (op j.1)) :=
  (CommSq.vert_inv ⟨RV.toScheme_map_π_comp_chartStageIso hRV t hflat hlfp ht R j⟩).w

/-- The bijections `chartHomStage` are compatible with the transition maps of derived morphism
sets. -/
theorem homTransition_chartHomStage {i j : (RV.chartSituation hRV t hflat hlfp).LaterIndex}
    (h : i.1 ≤ j.1)
    (φ : (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj L) :
    (RV.chartSituation hRV t hflat hlfp).homTransition K L h
        (RV.chartHomStage hRV t hflat hlfp ht R K L i φ) =
      RV.chartHomStage hRV t hflat hlfp ht R K L j
        (Stacks.DerivedPullback.schemeFactorHom
          ((BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op))
          ((BigFppfOver.toScheme B S hS).map (R.q i.1))
          ((BigFppfOver.toScheme B S hS).map (R.q j.1))
          (toScheme_map_comp_eq B S hS _ _ _ (R.map_q i.1 j.1 h)) K L φ) :=
  (Stacks.DerivedPullback.schemeFactorHom_comp _ _ _ _ _ _
      (RV.chartStageIso_inv_q hRV t hflat hlfp ht R i)
      (RV.chartStageIso_inv_transition hRV t hflat hlfp ht R h)
      (by rw [Category.assoc, toScheme_map_comp_eq B S hS _ _ _ (R.map_q i.1 j.1 h),
        RV.chartStageIso_inv_q hRV t hflat hlfp ht R j])
      _ K L φ).trans
    (Stacks.DerivedPullback.schemeFactorHom_comp _ _ _ _ _ _
      (toScheme_map_comp_eq B S hS _ _ _ (R.map_q i.1 j.1 h)) rfl _
      (RV.chartStageIso_inv_q hRV t hflat hlfp ht R j) K L φ).symm

/-- The bijections `chartHomStage` and `chartHomLimit` are compatible with the comparison maps
from a stage to the limit. -/
theorem homComparison_chartHomStage (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex)
    (φ : (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j.1)).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q j.1)).toLRSHom.toShHom).obj L) :
    (RV.chartSituation hRV t hflat hlfp).homComparison K L j
        (RV.chartHomStage hRV t hflat hlfp ht R K L j φ) =
      RV.chartHomLimit hRV t hflat hlfp ht R K L
        (Stacks.DerivedPullback.schemeFactorHom
          ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op j.1)))
          ((BigFppfOver.toScheme B S hS).map (R.q j.1)) ((BigFppfOver.toScheme B S hS).map R.qc)
          (toScheme_map_comp_eq B S hS _ _ _ (R.π_q j.1)) K L φ) :=
  (Stacks.DerivedPullback.schemeFactorHom_comp _ _ _ _ _ _
      (RV.chartStageIso_inv_q hRV t hflat hlfp ht R j)
      (RV.chartLimitIso_inv_projection hRV t hflat hlfp ht R j)
      (by rw [Category.assoc, toScheme_map_comp_eq B S hS _ _ _ (R.π_q j.1),
        RV.chartLimitIso_inv_qc hRV t hflat hlfp ht R])
      _ K L φ).trans
    (Stacks.DerivedPullback.schemeFactorHom_comp _ _ _ _ _ _
      (toScheme_map_comp_eq B S hS _ _ _ (R.π_q j.1)) rfl _
      (RV.chartLimitIso_inv_qc hRV t hflat hlfp ht R) K L φ).symm

/-- `ZariskiModelHomDescent` read with the stages of the chart situation as index. -/
theorem zariskiModelHomDescent_iff_laterIndex :
    ZariskiModelHomDescent R K L ↔
      ((∀ ψ : (derivedPullback ((BigFppfOver.toScheme B S hS).map R.qc).toLRSHom.toShHom).obj K ⟶
            (derivedPullback ((BigFppfOver.toScheme B S hS).map R.qc).toLRSHom.toShHom).obj L,
          ∃ (i : (RV.chartSituation hRV t hflat hlfp).LaterIndex)
            (φ : (derivedPullback
                  ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj K ⟶
              (derivedPullback
                ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj L),
            Stacks.DerivedPullback.schemeFactorHom
              ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op i.1)))
              ((BigFppfOver.toScheme B S hS).map (R.q i.1)) ((BigFppfOver.toScheme B S hS).map R.qc)
              (toScheme_map_comp_eq B S hS _ _ _ (R.π_q i.1)) K L φ = ψ) ∧
        ∀ (i : (RV.chartSituation hRV t hflat hlfp).LaterIndex)
          (φ φ' : (derivedPullback
                ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj K ⟶
            (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj L),
          Stacks.DerivedPullback.schemeFactorHom
              ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op i.1)))
              ((BigFppfOver.toScheme B S hS).map (R.q i.1)) ((BigFppfOver.toScheme B S hS).map R.qc)
              (toScheme_map_comp_eq B S hS _ _ _ (R.π_q i.1)) K L φ =
            Stacks.DerivedPullback.schemeFactorHom
              ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op i.1)))
              ((BigFppfOver.toScheme B S hS).map (R.q i.1)) ((BigFppfOver.toScheme B S hS).map R.qc)
              (toScheme_map_comp_eq B S hS _ _ _ (R.π_q i.1)) K L φ' →
            ∃ (j : (RV.chartSituation hRV t hflat hlfp).LaterIndex) (h : i.1 ≤ j.1),
              Stacks.DerivedPullback.schemeFactorHom
                  ((BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op))
                  ((BigFppfOver.toScheme B S hS).map (R.q i.1))
                  ((BigFppfOver.toScheme B S hS).map (R.q j.1))
                  (toScheme_map_comp_eq B S hS _ _ _ (R.map_q i.1 j.1 h)) K L φ =
                Stacks.DerivedPullback.schemeFactorHom
                  ((BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op))
                  ((BigFppfOver.toScheme B S hS).map (R.q i.1))
                  ((BigFppfOver.toScheme B S hS).map (R.q j.1))
                  (toScheme_map_comp_eq B S hS _ _ _ (R.map_q i.1 j.1 h)) K L φ') := by
  constructor
  · intro H
    refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
    · have H1 := H.1 ψ
      obtain ⟨j, φ, hφ⟩ := H1
      exact ⟨⟨j, j.2⟩, φ, hφ⟩
    · have H2 := H.2 i.1 φ φ' hφ
      obtain ⟨k, hk, e⟩ := H2
      exact ⟨⟨k, k.2⟩, hk, e⟩
  · intro H
    refine ⟨fun ψ => ?_, fun j φ φ' hφ => ?_⟩
    · have H1 := H.1 ψ
      obtain ⟨i, φ, hφ⟩ := H1
      exact ⟨i.1, φ, hφ⟩
    · have H2 := H.2 ⟨j, j.2⟩ φ φ' hφ
      obtain ⟨k, hk, e⟩ := H2
      exact ⟨k.1, hk, e⟩

include ht in
/-- **`ZariskiModelHomDescent` for `R` is the conclusion of Stacks 0DI7 for the chart
situation.** -/
theorem zariskiModelHomDescent_iff_chartSituation :
    ZariskiModelHomDescent R K L ↔ (RV.chartSituation hRV t hflat hlfp).HomDescent K L :=
  (RV.zariskiModelHomDescent_iff_laterIndex hRV t hflat hlfp R K L).trans
    (AlgebraicGeometry.RelativeDescentSituation.descent_transfer
      (fun i j : (RV.chartSituation hRV t hflat hlfp).LaterIndex => i.1 ≤ j.1)
      (A := fun i => (derivedPullback
          ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj K ⟶
        (derivedPullback ((BigFppfOver.toScheme B S hS).map (R.q i.1)).toLRSHom.toShHom).obj L)
      (B := fun i => (derivedPullback
          ((RV.chartSituation hRV t hflat hlfp).toFixedStage i).toLRSHom.toShHom).obj K ⟶
        (derivedPullback
          ((RV.chartSituation hRV t hflat hlfp).toFixedStage i).toLRSHom.toShHom).obj L)
      (fun {i j} h => Stacks.DerivedPullback.schemeFactorHom
        ((BigFppfOver.toScheme B S hS).map (R.W.map (homOfLE h).op))
        ((BigFppfOver.toScheme B S hS).map (R.q i.1)) ((BigFppfOver.toScheme B S hS).map (R.q j.1))
        (toScheme_map_comp_eq B S hS _ _ _ (R.map_q i.1 j.1 h)) K L)
      (fun i => Stacks.DerivedPullback.schemeFactorHom
        ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op i.1)))
        ((BigFppfOver.toScheme B S hS).map (R.q i.1)) ((BigFppfOver.toScheme B S hS).map R.qc)
        (toScheme_map_comp_eq B S hS _ _ _ (R.π_q i.1)) K L)
      (fun h => (RV.chartSituation hRV t hflat hlfp).homTransition K L h)
      ((RV.chartSituation hRV t hflat hlfp).homComparison K L)
      (RV.chartHomStage hRV t hflat hlfp ht R K L) (RV.chartHomLimit hRV t hflat hlfp ht R K L)
      (RV.bijective_chartHomStage hRV t hflat hlfp ht R K L)
      (RV.bijective_chartHomLimit hRV t hflat hlfp ht R K L)
      (fun h φ => RV.homTransition_chartHomStage hRV t hflat hlfp ht R K L h φ)
      (fun i φ => RV.homComparison_chartHomStage hRV t hflat hlfp ht R K L i φ))

end AffineBaseChangeRepresentation

/-- **The Zariski form of Stacks 0DKV on an affine model, from Stacks 0DI7.**  Let `D` be
Situation 0DKU whose limit is a limit of schemes on affine charts, `R` a representation of the
base changes along `z : h_{Z'} ⟶ Y₀` for an affine object `Z'` of the site, and suppose `z`
factors as `h_t ≫ w` through an affine object `V` with `t : Z' ⟶ V` flat and locally of finite
presentation on underlying schemes.  Let `K` and `L` be objects of `D(𝒪_{Z'})` on the Zariski
site, `K` pseudo-coherent, `L` with quasi-coherent cohomology and locally of finite Tor dimension
over `t⁻¹𝒪_V`.  Then `colim_j Hom(Lq_j^*K, Lq_j^*L) ⟶ Hom(Lq^*K, Lq^*L)` is bijective, in the
form `AlgebraicGeometry.Space.RelativeDescentSituation.ZariskiModelHomDescent`. -/
theorem zariskiModelHomDescent_of_affineChart (hD : D.IsSchemeLimit) {V Z' : BigAffineFppf B S hS}
    {z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ⟶ D.Y.obj (op D.i₀)}
    (w : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ D.Y.obj (op D.i₀))
    (t : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj V)
    (ht : yoneda.map t ≫ w = z) (hflat : Flat ((BigFppfOver.toScheme B S hS).map t))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t))
    (R : D.AffineBaseChangeRepresentation Z' z)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)))
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X :=
        ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).toRingedSpace)
      K)
    (hLqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')).Modules n).obj
        L).IsQuasicoherent)
    (hLtor : AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension
      (AlgebraicGeometry.RingedSpace.inverseImage
        ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V)).toRingedSpace
        ((BigFppfOver.toScheme B S hS).map t).base)
      (AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction ((BigFppfOver.toScheme B S hS).map t)).obj L)) :
    ZariskiModelHomDescent R K L := by
  let RV := D.affineBaseChangeRepresentation V w hD.1
  have hRV := Classical.choice (hD.2 V w RV)
  have := RV.isIso_toScheme_q_laterIndexBase
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')) :=
    Z'.property
  have htor := (Scheme.Hom.locallyHasFiniteTorDimension_baseOpen_iff
    ((BigFppfOver.toScheme B S hS).map (RV.chartMap t))
    ((BigFppfOver.toScheme B S hS).map (RV.q (laterIndexBase D))) (RV.toScheme_chartMap_comp t)
    L).1 hLtor
  exact (RV.zariskiModelHomDescent_iff_chartSituation hRV t hflat hlfp ht R K L).2
    (RelativeDescentSituation.homDescent_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
      (RV.chartSituation hRV t hflat hlfp) K L hK hLqc htor)

end RelativeDescentSituation

end AlgebraicGeometry.Space

end

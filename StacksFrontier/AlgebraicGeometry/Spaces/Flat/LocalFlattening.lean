module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.LocalFlatteningAlongSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAlongBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties

/-!
# Flattening in the local case for algebraic spaces

Stacks 0CWP: let `S` be the spectrum of a henselian local ring `A` with closed point `s`, let
`X ⟶ S` be a morphism of algebraic spaces which is locally of finite type, let `F` be a finite type
quasi-coherent `𝒪_X`-module and let `E ⊆ |X_s|`. There is a closed subscheme `Z ⊆ S` such that for
every morphism of pointed schemes `(T, t) ⟶ (S, s)`, `F_T` is flat over `T` at all points of
`|X_t|` mapping to `E` exactly when `Spec 𝒪_{T,t} ⟶ S` factors through `Z`; under finite
presentation hypotheses and for `E` closed and quasi-compact, `Z ⟶ S` is of finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_idealSheafData_isFlatOverAtPoint_iff_factors`: **Stacks 0CWP**.
* `AlgebraicGeometry.Space.exists_finitePresentation_idealSheafData_isFlatOverAtPoint_iff_factors`:
  **Stacks 0CWP**, the final assertion.
* `AlgebraicGeometry.Space.forall_isFlatOverAtPoint_iff_flatAlongAfter`: the reduction to one
  étale chart.

## Implementation notes

The proof is the source's. On an étale chart `U ⟶ X` the condition, restricted to the points of
`|X_T|` whose image lies in the image of `|U|`, is the scheme condition for `U ⟶ S`, the module
`F|_U` and the inverse image of `E` (Stacks 05PI,
`AlgebraicGeometry.LocalFlattening.exists_idealSheafData_flatAlongAfter_iff`): the base change
`U ×_S T` is an étale chart of `X_T` (`AlgebraicGeometry.Space.chartBaseChangeAlong`), flatness at
a point of `|X_T|` is read on any chart through it (Stacks 05VU), the chart restriction of `F_T` is
the pullback of `F|_U` (Stacks 03M0 with 03LW), and every point of `|X_T|` over a point of `|U|`
comes from `U ×_S T` (Stacks 03H4). The closed subscheme is the intersection over a family of
charts whose images cover `E`: all charts in general, and finitely many affine ones when `E` is
quasi-compact, the inverse image of `E` then being closed, hence quasi-compact, in each.

`X` is an algebraic space over the base scheme `S = Spec A` of the big fppf site, and
`f : X ⟶ S` is its structure morphism to the terminal algebraic space `S`. The pointed scheme
`(T, t)` is an object of the site over `S`. `X_T = X ×_S T` is the fibre product of algebraic
spaces, `|X_t|` is the set of points of `|X_T|` over `t`, and `|X_s|` is the set of points of `|X|`
over `s`, a point of `|X_t|` mapping to `|X_s|` by its image in `|X|`; its topology is the
subspace topology of `|X|` (Stacks 03BY). The closed subscheme `Z` is given by its ideal sheaf.

## References

* [Stacks Project, Tag 0CWP](https://stacks.math.columbia.edu/tag/0CWP)
* [Stacks Project, Tag 05PI](https://stacks.math.columbia.edu/tag/05PI)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- The structure morphism of an étale chart to the base `Spec A` is the image of the unique
morphism of the site to the final object. -/
theorem chartToBase_eq_map_siteTerminalHom (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (U : SmallEtale B (Spec (.of A)) hA X.1) :
    chartToBase B (Spec (.of A)) hA X U =
      (BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (siteTerminalHom B (Spec (.of A)) hA U.obj.left) :=
  congrArg (BigFppfOver.toScheme B (Spec (.of A)) hA).map (Over.mkIdTerminal.hom_ext _ _)

/-- The point of `|X|` cut out by a point of an étale chart lies over the image of that point in
`Spec A`. -/
theorem pointsMap_pointOfEtaleChart_eq {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (U : SmallEtale B (Spec (.of A)) hA X.1)
    (u : etaleChartScheme B (Spec (.of A)) hA U) :
    pointsMap B (Spec (.of A)) hA X.1 f (pointOfEtaleChart B (Spec (.of A)) hA U u) =
      (pointsEquivScheme B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))).symm
        (chartToBase B (Spec (.of A)) hA X U u) := by
  rw [chartToBase_eq_map_siteTerminalHom, pointOfEtaleChart, ← pointsMap_comp_apply,
    comp_eq_yoneda_siteTerminalHom B (Spec (.of A)) hA f U.obj.hom, pointsMap_yoneda_map_symm]

/-- The closed point of `Spec A`, as a point of the algebraic space `Spec A`. -/
abbrev closedBasePoint (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A))) :
    points B (Spec (.of A)) hA (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) :=
  (pointsEquivScheme B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))).symm
    (IsLocalRing.closedPoint A)

/-- The image of the point cut out by a point `w` of an étale chart `W`, under a morphism `φ`
with `W ⟶ Y ⟶ Z` equal to `h_W ⟶ h_T ⟶ Z`, is the image of the point `ψ w` of `T`. -/
private theorem pointsMap_pointOfEtaleChart_of_comp_eq
    {Y Z : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (W : SmallEtale B (Spec (.of A)) hA Y)
    {T : BigFppfOver B (Spec (.of A)) hA} {φ : Y ⟶ Z}
    {ψ : W.obj.left ⟶ T} {ρ : yoneda.obj T ⟶ Z} (h : W.obj.hom ≫ φ = yoneda.map ψ ≫ ρ)
    (w : etaleChartScheme B (Spec (.of A)) hA W) :
    pointsMap B (Spec (.of A)) hA Y φ (pointOfEtaleChart B (Spec (.of A)) hA W w) =
      pointsMap B (Spec (.of A)) hA _ ρ ((pointsEquivScheme B (Spec (.of A)) hA T).symm
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map ψ w)) := by
  rw [pointOfEtaleChart, ← pointsMap_comp_apply, h, pointsMap_comp_apply,
    pointsMap_yoneda_map_symm]

/-- In a cartesian square of étale charts `W ⟶ U` over `φ : Y ⟶ Z`, every point of `Y` whose
image lies in the image of `|U|` is cut out by a point of `W`. -/
private theorem exists_pointOfEtaleChart_eq_of_isPullback
    {Y Z : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} {W : SmallEtale B (Spec (.of A)) hA Y}
    {U : SmallEtale B (Spec (.of A)) hA Z} {φ : Y ⟶ Z} {ψ : W.obj.left ⟶ U.obj.left}
    (hL : IsPullback W.obj.hom (yoneda.map ψ) φ U.obj.hom) {x : points B (Spec (.of A)) hA Y}
    (hx : pointsMap B (Spec (.of A)) hA Y φ x ∈
      Set.range (pointOfEtaleChart B (Spec (.of A)) hA U)) :
    ∃ w, pointOfEtaleChart B (Spec (.of A)) hA W w = x := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B (Spec (.of A)) hA hL x
    ((pointsEquivScheme B (Spec (.of A)) hA U.obj.left).symm u) hu.symm
  obtain ⟨w, rfl⟩ := (pointsEquivScheme B (Spec (.of A)) hA W.obj.left).symm.surjective w
  exact ⟨w, hw⟩

/-- The base change `U ×_S T` of an étale chart `U` of `X` along `T ⟶ S` is an étale chart of
`X_T`, cartesian over `U` and over `T`, on which flatness of `F_T` over `T` is flatness of the
pullback of `F|_U`. -/
private theorem exists_chartBaseChange (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (U : SmallEtale B (Spec (.of A)) hA X.1) (T : BigFppfOver B (Spec (.of A)) hA)
    (g : T ⟶ Over.mk (𝟙 (B.obj hA))) :
    ∃ (W : SmallEtale B (Spec (.of A)) hA (pullback f (schemeSpaceMap g)).1)
      (p : W.obj.left ⟶ U.obj.left) (q : W.obj.left ⟶ T),
      IsPullback ((BigFppfOver.toScheme B (Spec (.of A)) hA).map p)
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map q) (chartToBase B (Spec (.of A)) hA X U)
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map g) ∧
      IsPullback W.obj.hom (yoneda.map p) (pullback.fst f (schemeSpaceMap g)).hom U.obj.hom ∧
      W.obj.hom ≫ (pullback.snd f (schemeSpaceMap g)).hom = yoneda.map q ∧
      ∀ w, (IsFlatOverAtPoint B (Spec (.of A)) hA (pullback f (schemeSpaceMap g)).2
          (pullback.snd f (schemeSpaceMap g)).hom
          ((modulePullback B (Spec (.of A)) hA (pullback.fst f (schemeSpaceMap g))).obj F)
          (pointOfEtaleChart B (Spec (.of A)) hA W w) ↔
        AlgebraicGeometry.IsFlatOverAt
          ((BigFppfOver.toScheme B (Spec (.of A)) hA).map q).toLRSHom.toShHom
          ((RingedSpaceModuleAdjunction.modulePullback
            ((BigFppfOver.toScheme B (Spec (.of A)) hA).map p).toLRSHom.toShHom).obj
            (restrictToChart B (Spec (.of A)) hA X.2 F U)) w) := by
  have sq := IsPullback.of_hasPullback f (schemeSpaceMap g)
  let U' : SmallEtale B (Spec (.of A)) hA (schemeSpace T).1 := selfChart B (Spec (.of A)) hA T
  let V : SmallEtale B (Spec (.of A)) hA (schemeSpace (Over.mk (𝟙 (B.obj hA)))).1 :=
    selfChart B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))
  let d : (SmallEtale.toOver B (Spec (.of A)) hA (schemeSpace T).1).obj U' ⟶
      (SmallEtale.toOver B (Spec (.of A)) hA (schemeSpace (Over.mk (𝟙 (B.obj hA)))).1).obj V := g
  have hd : U'.1.hom ≫ (schemeSpaceMap g).hom = yoneda.map d ≫ V.1.hom :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  let b : (SmallEtale.toOver B (Spec (.of A)) hA X.1).obj U ⟶
      (SmallEtale.toOver B (Spec (.of A)) hA (schemeSpace (Over.mk (𝟙 (B.obj hA)))).1).obj V :=
    siteTerminalHom B (Spec (.of A)) hA U.obj.left
  have hfb : U.1.hom ≫ f.hom = yoneda.map b :=
    comp_eq_yoneda_siteTerminalHom B (Spec (.of A)) hA f.hom U.obj.hom
  have hb : U.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom := hfb.trans (Category.comp_id _).symm
  let Wc := chartBaseChangeAlong sq d hd b hb
  have efst : Wc.obj.hom ≫ (pullback.fst f (schemeSpaceMap g)).hom =
      yoneda.map (pullback.fst b d) ≫ U.obj.hom := chartBaseChangeAlong_fst sq d hd b hb
  have esnd : Wc.obj.hom ≫ (pullback.snd f (schemeSpaceMap g)).hom =
      yoneda.map (pullback.snd b d) :=
    (chartBaseChangeAlong_snd sq d hd b hb).trans (Category.comp_id _)
  refine ⟨Wc, pullback.fst b d, pullback.snd b d, ?_, ?_, esnd, fun w => ?_⟩
  · rw [chartToBase_eq_map_siteTerminalHom]
    exact isPullback_chartScheme_chartBaseChangeAlong d b
  · refine IsPullback.of_right ?_ efst (AlgebraicSpaces.isPullback_hom B (Spec (.of A)) hA sq).flip
    rw [esnd, hfb]
    exact ((IsPullback.of_hasPullback b d).map yoneda).flip
  · exact (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B (Spec (.of A)) hA
      (pullback.snd f (schemeSpaceMap g)) _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B (Spec (.of A)) hA
        (pullback.fst f (schemeSpaceMap g)) F hFq)
      (chartBaseChangeAlongDiagram sq d hd b hb) w).trans
      (AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _
        (restrictToChartBaseChangeIso B (Spec (.of A)) hA
          (pullback.fst f (schemeSpaceMap g))
          F hFq U Wc (pullback.fst b d) efst.symm).symm w)

section LocalBase

variable [IsLocalRing A]

/-- The points of an étale chart of `X` lying over a subset `E` of the closed fibre of `X`. -/
def chartFibreSet (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA})
    (U : SmallEtale B (Spec (.of A)) hA X.1) : Set (etaleChartScheme B (Spec (.of A)) hA U) :=
  {u | ∃ hx, (⟨pointOfEtaleChart B (Spec (.of A)) hA U u, hx⟩ :
      {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}) ∈ E}

/-- Membership in a set of points of the closed fibre depends only on the underlying point. -/
theorem mem_fibre_congr {X : AlgebraicSpaces B (Spec (.of A)) hA}
    {f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA)))}
    (E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA})
    {a b : points B (Spec (.of A)) hA X.1} (h : a = b) (ha hb) :
    (⟨a, ha⟩ : {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}) ∈ E ↔ ⟨b, hb⟩ ∈ E := by
  subst h
  rfl

/-- **The chart reduction of Stacks 0CWP.** For an étale chart `U` of `X` and a pointed scheme
`(T, t)` over `Spec A`, flatness of `F_T` over `T` at the points of `|X_T|` above `t` whose image
in `|X|` lies in `E` and in the image of `|U|` is the scheme condition for the chart: flatness of
`(F|_U)_T` over `T` at the points of `U_T` above `t` whose image in `U` lies over `E`. -/
theorem forall_isFlatOverAtPoint_iff_flatAlongAfter (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA})
    (U : SmallEtale B (Spec (.of A)) hA X.1) (T : BigFppfOver B (Spec (.of A)) hA)
    (g : T ⟶ Over.mk (𝟙 (B.obj hA))) (t : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj T) :
    (∀ x' : points B (Spec (.of A)) hA
        (pullback f (schemeSpaceMap g)).1,
      pointsMap B (Spec (.of A)) hA _ ((pullback.snd f (schemeSpaceMap g)).hom) x' =
          (pointsEquivScheme B (Spec (.of A)) hA T).symm t →
      ∀ hx : pointsMap B (Spec (.of A)) hA X.1 f.hom
          (pointsMap B (Spec (.of A)) hA _ ((pullback.fst f (schemeSpaceMap g)).hom) x') =
          closedBasePoint A B hA,
        (⟨_, hx⟩ : {x : points B (Spec (.of A)) hA X.1 //
          pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}) ∈ E →
        pointsMap B (Spec (.of A)) hA _ ((pullback.fst f (schemeSpaceMap g)).hom) x' ∈
          Set.range (pointOfEtaleChart B (Spec (.of A)) hA U) →
        IsFlatOverAtPoint B (Spec (.of A)) hA
          (pullback f (schemeSpaceMap g)).2
          ((pullback.snd f (schemeSpaceMap g)).hom)
          ((modulePullback B (Spec (.of A)) hA
            (pullback.fst f (schemeSpaceMap g))).obj F)
          x') ↔
      LocalFlattening.FlatAlongAfter (chartToBase B (Spec (.of A)) hA X U)
        (restrictToChart B (Spec (.of A)) hA X.2 F U)
        (chartFibreSet X f E U) ((BigFppfOver.toScheme B (Spec (.of A)) hA).map g) t := by
  obtain ⟨W, p, q, hsch, hL, esnd, hflat⟩ := exists_chartBaseChange X f F hFq U T g
  have hsnd (w : etaleChartScheme B (Spec (.of A)) hA W) :=
    (pointsMap_pointOfEtaleChart_of_comp_eq W (esnd.trans (Category.comp_id _).symm) w).trans
      (pointsMap_id_apply B (Spec (.of A)) hA _)
  have hfst (w : etaleChartScheme B (Spec (.of A)) hA W) :
      pointsMap B (Spec (.of A)) hA _ (pullback.fst f (schemeSpaceMap g)).hom
          (pointOfEtaleChart B (Spec (.of A)) hA W w) =
        pointOfEtaleChart B (Spec (.of A)) hA U
          ((BigFppfOver.toScheme B (Spec (.of A)) hA).map p w) :=
    pointsMap_pointOfEtaleChart_of_comp_eq W hL.w w
  refine Iff.trans ?_ (LocalFlattening.flatAlongAfter_iff_of_isPullback hsch _ _ t).symm
  constructor
  · rintro H w hw ⟨hx, hE⟩
    have hx' := (congrArg (pointsMap B (Spec (.of A)) hA X.1 f.hom) (hfst w)).trans hx
    exact (hflat w).mp (H _ ((hsnd w).trans (congrArg _ hw)) hx'
      ((mem_fibre_congr E (hfst w) hx' hx).mpr hE) ⟨_, (hfst w).symm⟩)
  · rintro H x' hx' hx hE hU
    obtain ⟨w, rfl⟩ := exists_pointOfEtaleChart_eq_of_isPullback hL hU
    have hw : (BigFppfOver.toScheme B (Spec (.of A)) hA).map q w = t :=
      (pointsEquivScheme B (Spec (.of A)) hA T).symm.injective ((hsnd w).symm.trans hx')
    have hxU := (congrArg (pointsMap B (Spec (.of A)) hA X.1 f.hom) (hfst w)).symm.trans hx
    exact (hflat w).mpr (H w hw ⟨hxU, (mem_fibre_congr E (hfst w) hx hxU).mp hE⟩)

/-- Flatness of `F_T` at the points of `|X_t|` over `E` is the chart condition for every chart in a
family whose images cover `E`. -/
private theorem forall_isFlatOverAtPoint_iff_forall_flatAlongAfter {ι : Type*}
    (X : AlgebraicSpaces B (Spec (.of A)) hA) (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA})
    (U : ι → SmallEtale B (Spec (.of A)) hA X.1) (s : Set ι)
    (hs : ∀ e ∈ E, ∃ i ∈ s, e.1 ∈ Set.range (pointOfEtaleChart B (Spec (.of A)) hA (U i)))
    (T : BigFppfOver B (Spec (.of A)) hA) (g : T ⟶ Over.mk (𝟙 (B.obj hA)))
    (t : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj T) :
    (∀ x' : points B (Spec (.of A)) hA (pullback f (schemeSpaceMap g)).1,
      pointsMap B (Spec (.of A)) hA _ ((pullback.snd f (schemeSpaceMap g)).hom) x' =
          (pointsEquivScheme B (Spec (.of A)) hA T).symm t →
      ∀ hx : pointsMap B (Spec (.of A)) hA X.1 f.hom
          (pointsMap B (Spec (.of A)) hA _ ((pullback.fst f (schemeSpaceMap g)).hom) x') =
          closedBasePoint A B hA,
        (⟨_, hx⟩ : {x : points B (Spec (.of A)) hA X.1 //
          pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}) ∈ E →
        IsFlatOverAtPoint B (Spec (.of A)) hA
          (pullback f (schemeSpaceMap g)).2
          ((pullback.snd f (schemeSpaceMap g)).hom)
          ((modulePullback B (Spec (.of A)) hA
            (pullback.fst f (schemeSpaceMap g))).obj F)
          x') ↔
      ∀ i ∈ s, LocalFlattening.FlatAlongAfter (chartToBase B (Spec (.of A)) hA X (U i))
        (restrictToChart B (Spec (.of A)) hA X.2 F (U i))
        (chartFibreSet X f E (U i)) ((BigFppfOver.toScheme B (Spec (.of A)) hA).map g) t := by
  refine Iff.trans ?_ (forall₂_congr fun i _ =>
    forall_isFlatOverAtPoint_iff_flatAlongAfter X f F hFq E (U i) T g t)
  refine ⟨fun h i _ x' hx' hx hE _ => h x' hx' hx hE, fun h x' hx' hx hE => ?_⟩
  obtain ⟨i, hi, hxi⟩ := hs _ hE
  exact h i hi x' hx' hx hE hxi

end LocalBase

/-- Every point of an algebraic space is cut out by a point of an affine étale chart. -/
theorem exists_affine_smallEtale_pointOfEtaleChart_eq (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (x : points B (Spec (.of A)) hA X.1) :
    ∃ (U : SmallEtale B (Spec (.of A)) hA X.1) (u : etaleChartScheme B (Spec (.of A)) hA U),
      IsAffine (etaleChartScheme B (Spec (.of A)) hA U) ∧
        pointOfEtaleChart B (Spec (.of A)) hA U u = x := by
  obtain ⟨W, b, hWaff, hb, w, hw⟩ :=
    exists_affine_etale_chart_at_point B (Spec (.of A)) hA X.1 X.2 x
  refine ⟨⟨CostructuredArrow.mk b, hb⟩, pointsEquivScheme B (Spec (.of A)) hA W w, hWaff, ?_⟩
  show pointsMap B (Spec (.of A)) hA (yoneda.obj W) b
    ((pointsEquivScheme B (Spec (.of A)) hA W).symm (pointsEquivScheme B (Spec (.of A)) hA W w)) = x
  rw [Equiv.symm_apply_apply, hw]

/-- The chart condition of `chartFibreSet` forces the points to lie over the closed point. -/
theorem chartToBase_eq_closedPoint_of_mem_chartFibreSet [IsLocalRing A]
    {X : AlgebraicSpaces B (Spec (.of A)) hA}
    {f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA)))}
    {E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}}
    {U : SmallEtale B (Spec (.of A)) hA X.1} {u : etaleChartScheme B (Spec (.of A)) hA U}
    (hu : u ∈ chartFibreSet X f E U) :
    chartToBase B (Spec (.of A)) hA X U u = IsLocalRing.closedPoint A := by
  obtain ⟨hx, -⟩ := hu
  exact (pointsEquivScheme B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))).symm.injective
    ((pointsMap_pointOfEtaleChart_eq f.hom U u).symm.trans hx)

/-- If `E` is closed in the closed fibre and the chart `U` is affine, the points of `U` lying
over `E` form a compact set. -/
private theorem isCompact_chartFibreSet [IsLocalRing A] {X : AlgebraicSpaces B (Spec (.of A)) hA}
    {f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA)))}
    {E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}}
    (hEc : IsClosed E) (U : SmallEtale B (Spec (.of A)) hA X.1)
    [IsAffine (etaleChartScheme B (Spec (.of A)) hA U)] :
    IsCompact (chartFibreSet X f E U) := by
  obtain ⟨C, hC, hCE⟩ := isClosed_induced_iff.mp hEc
  have hset : chartFibreSet X f E U =
      pointOfEtaleChart B (Spec (.of A)) hA U ⁻¹' C ∩
        chartToBase B (Spec (.of A)) hA X U ⁻¹' {IsLocalRing.closedPoint A} := by
    ext v
    constructor
    · rintro ⟨hx, hv⟩
      exact ⟨by rwa [← hCE] at hv, chartToBase_eq_closedPoint_of_mem_chartFibreSet ⟨hx, hv⟩⟩
    · rintro ⟨hvC, hv⟩
      exact ⟨(pointsMap_pointOfEtaleChart_eq f.hom _ v).trans (congrArg _ hv), by rwa [← hCE]⟩
  rw [hset]
  exact ((hC.preimage (continuous_pointOfEtaleChart B (Spec (.of A)) hA U)).inter
    ((IsLocalRing.isClosed_singleton_closedPoint _).preimage
      (chartToBase B (Spec (.of A)) hA X U).continuous)).isCompact

/-- A chart of an algebraic space locally of finite type over `Spec A` is locally of finite type
over `Spec A`. -/
theorem locallyOfFiniteType_chartToBase {X : AlgebraicSpaces B (Spec (.of A)) hA}
    {f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA)))}
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (U : SmallEtale B (Spec (.of A)) hA X.1) :
    LocallyOfFiniteType (chartToBase B (Spec (.of A)) hA X U) := by
  rw [chartToBase_eq_map_siteTerminalHom]
  exact hf U.obj.left (Over.mk (𝟙 (B.obj hA))) U.obj.hom (𝟙 _)
    (siteTerminalHom B (Spec (.of A)) hA _) U.property (presheaf_etale_id B (Spec (.of A)) hA _)
    ((Category.comp_id _).trans
      (comp_eq_yoneda_siteTerminalHom B (Spec (.of A)) hA f.hom U.obj.hom).symm)

/-- A chart of an algebraic space locally of finite presentation over `Spec A` is locally of
finite presentation over `Spec A`. -/
theorem locallyOfFinitePresentation_chartToBase {X : AlgebraicSpaces B (Spec (.of A)) hA}
    {f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA)))}
    (hf : IsLocallyOfFinitePresentation B (Spec (.of A)) hA f.hom)
    (U : SmallEtale B (Spec (.of A)) hA X.1) :
    LocallyOfFinitePresentation (chartToBase B (Spec (.of A)) hA X U) := by
  rw [chartToBase_eq_map_siteTerminalHom]
  exact hf U.obj.left (Over.mk (𝟙 (B.obj hA))) U.obj.hom (𝟙 _)
    (siteTerminalHom B (Spec (.of A)) hA _) U.property (presheaf_etale_id B (Spec (.of A)) hA _)
    ((Category.comp_id _).trans
      (comp_eq_yoneda_siteTerminalHom B (Spec (.of A)) hA f.hom U.obj.hom).symm)

/-- **Stacks Project, Tag 0CWP.** Let `S = Spec A` be the spectrum of a henselian local ring with
closed point `s`, let `f : X ⟶ S` be a morphism of algebraic spaces which is locally of finite
type, let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `E ⊆ |X_s|` be a subset.
There is a closed subscheme `Z ⊆ S` such that for every morphism of pointed schemes
`(T, t) ⟶ (S, s)` the following are equivalent:

1. `F_T` is flat over `T` at all points of `|X_t|` which map to a point of `E ⊆ |X_s|`;
2. `Spec 𝒪_{T,t} ⟶ S` factors through `Z`.

Here `X` is an algebraic space over `S`, `f` its structure morphism to the terminal algebraic
space `S`, and `X_T = X ×_S T` the fibre product of algebraic spaces; the points of `|X_t|` are
the points of `|X_T|` over `t ∈ |T|`, and the closed fibre `|X_s|` is the set of points of `|X|`
over `s`, through which a point of `|X_t|` maps to `|X_s|` by its image in `|X|`. Flatness of
`F_T` over `T` at a point is Stacks 05VV at a point, and `Z` is given by its ideal sheaf. -/
@[stacks 0CWP "the closed flattening subscheme, for an arbitrary subset E of the closed fibre: \
nothing is assumed beyond the source's hypotheses"]
theorem exists_idealSheafData_isFlatOverAtPoint_iff_factors [HenselianLocalRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA) (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (hFt : SheafOfModules.IsFiniteTypeOnSite F)
    (E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}) :
    ∃ Z : (Spec (.of A)).IdealSheafData,
      ∀ (T : BigFppfOver B (Spec (.of A)) hA) (g : T ⟶ Over.mk (𝟙 (B.obj hA)))
        (t : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj T),
        (BigFppfOver.toScheme B (Spec (.of A)) hA).map g t = IsLocalRing.closedPoint A →
        ((∀ x' : points B (Spec (.of A)) hA (pullback f (schemeSpaceMap g)).1,
            pointsMap B (Spec (.of A)) hA _ (pullback.snd f (schemeSpaceMap g)).hom x' =
              (pointsEquivScheme B (Spec (.of A)) hA T).symm t →
            ∀ hx : pointsMap B (Spec (.of A)) hA X.1 f.hom
                (pointsMap B (Spec (.of A)) hA _ (pullback.fst f (schemeSpaceMap g)).hom x') =
                closedBasePoint A B hA,
              (⟨_, hx⟩ : {x : points B (Spec (.of A)) hA X.1 //
                pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}) ∈ E →
              IsFlatOverAtPoint B (Spec (.of A)) hA (pullback f (schemeSpaceMap g)).2
                (pullback.snd f (schemeSpaceMap g)).hom
                ((modulePullback B (Spec (.of A)) hA (pullback.fst f (schemeSpaceMap g))).obj F)
                x') ↔
          ∃ h : Spec (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj T).presheaf.stalk t) ⟶
              Z.subscheme,
            h ≫ Z.subschemeι = ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj T).fromSpecStalk t ≫
              (BigFppfOver.toScheme B (Spec (.of A)) hA).map g) := by
  have H (U : SmallEtale B (Spec (.of A)) hA X.1) := by
    have := locallyOfFiniteType_chartToBase hf U
    have := isQuasicoherent_restrictToChart B (Spec (.of A)) hA (X := X) F hFq U
    have := isFiniteType_restrictToChart B (Spec (.of A)) hA (X := X) F hFq hFt U
    exact LocalFlattening.exists_idealSheafData_flatAlongAfter_iff A
      (chartToBase B (Spec (.of A)) hA X U)
      (restrictToChart B (Spec (.of A)) hA X.2 F U) (chartFibreSet X f E U)
      (fun u hu => chartToBase_eq_closedPoint_of_mem_chartFibreSet hu)
  choose Z hZ using H
  refine ⟨⨆ U, Z U, fun T g t ht => ?_⟩
  rw [LocalFlattening.exists_comp_subschemeι_eq_iff_le_ker, iSup_le_iff]
  simp only [← LocalFlattening.exists_comp_subschemeι_eq_iff_le_ker]
  refine (forall_isFlatOverAtPoint_iff_forall_flatAlongAfter X f F hFq E id Set.univ
    (fun e _ => ?_) T g t).trans ?_
  · obtain ⟨U, u, -, hu⟩ := exists_affine_smallEtale_pointOfEtaleChart_eq X e.1
    exact ⟨U, trivial, u, hu⟩
  · simp only [Set.mem_univ, forall_true_left]
    exact forall_congr' fun U => hZ U _ t ht

/-- **Stacks Project, Tag 0CWP, the final assertion.** In the situation of
`AlgebraicGeometry.Space.exists_idealSheafData_isFlatOverAtPoint_iff_factors`, if moreover
`X ⟶ S` is locally of finite presentation, `F` is of finite presentation and `E ⊆ |X_s|` is
closed and quasi-compact, then the closed subscheme `Z` may be chosen with `Z ⟶ S` of finite
presentation. The topology on `|X_s|` is the subspace topology of the closed fibre in `|X|`
(Stacks 03BY). -/
@[stacks 0CWP "the finite-presentation assertion, for E closed and quasi-compact in |X_s|: \
nothing is assumed beyond the source's hypotheses"]
theorem exists_finitePresentation_idealSheafData_isFlatOverAtPoint_iff_factors
    [HenselianLocalRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA) (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (hfp : IsLocallyOfFinitePresentation B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (hFt : SheafOfModules.IsFiniteTypeOnSite F) (hFp : SheafOfModules.IsFinitePresentationOnSite F)
    (E : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA})
    (hEc : IsClosed E) (hEk : IsCompact E) :
    ∃ Z : (Spec (.of A)).IdealSheafData,
      AlgebraicGeometry.FinitePresentation Z.subschemeι ∧
      ∀ (T : BigFppfOver B (Spec (.of A)) hA) (g : T ⟶ Over.mk (𝟙 (B.obj hA)))
        (t : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj T),
        (BigFppfOver.toScheme B (Spec (.of A)) hA).map g t = IsLocalRing.closedPoint A →
        ((∀ x' : points B (Spec (.of A)) hA (pullback f (schemeSpaceMap g)).1,
            pointsMap B (Spec (.of A)) hA _ (pullback.snd f (schemeSpaceMap g)).hom x' =
              (pointsEquivScheme B (Spec (.of A)) hA T).symm t →
            ∀ hx : pointsMap B (Spec (.of A)) hA X.1 f.hom
                (pointsMap B (Spec (.of A)) hA _ (pullback.fst f (schemeSpaceMap g)).hom x') =
                closedBasePoint A B hA,
              (⟨_, hx⟩ : {x : points B (Spec (.of A)) hA X.1 //
                pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA}) ∈ E →
              IsFlatOverAtPoint B (Spec (.of A)) hA (pullback f (schemeSpaceMap g)).2
                (pullback.snd f (schemeSpaceMap g)).hom
                ((modulePullback B (Spec (.of A)) hA (pullback.fst f (schemeSpaceMap g))).obj F)
                x') ↔
          ∃ h : Spec (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj T).presheaf.stalk t) ⟶
              Z.subscheme,
            h ≫ Z.subschemeι = ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj T).fromSpecStalk t ≫
              (BigFppfOver.toScheme B (Spec (.of A)) hA).map g) := by
  choose U u hUaff hu using fun e : E => exists_affine_smallEtale_pointOfEtaleChart_eq X e.1.1
  let O (e : E) : Set {x : points B (Spec (.of A)) hA X.1 //
      pointsMap B (Spec (.of A)) hA X.1 f.hom x = closedBasePoint A B hA} :=
    Subtype.val ⁻¹' Set.range (pointOfEtaleChart B (Spec (.of A)) hA (U e))
  have hO (e : E) : IsOpen (O e) := by
    have h := isOpen_image_pointOfEtaleChart B (Spec (.of A)) hA (U e) isOpen_univ
    rw [Set.image_univ] at h
    exact h.preimage continuous_subtype_val
  obtain ⟨s, hs⟩ := hEk.elim_finite_subcover O hO
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, u _, hu _⟩)
  have H (e : E) := by
    have := hUaff e
    have := locallyOfFiniteType_chartToBase hf (U e)
    have := locallyOfFinitePresentation_chartToBase hfp (U e)
    have := isQuasicoherent_restrictToChart B (Spec (.of A)) hA (X := X) F hFq (U e)
    have := isFiniteType_restrictToChart B (Spec (.of A)) hA (X := X) F hFq hFt (U e)
    have := isFinitePresentation_restrictToChart B (Spec (.of A)) hA (X := X) F hFq hFp (U e)
    exact LocalFlattening.exists_finitePresentation_idealSheafData_flatAlongAfter_iff A
      (chartToBase B (Spec (.of A)) hA X (U e)) (restrictToChart B (Spec (.of A)) hA X.2 F (U e))
      (chartFibreSet X f E (U e)) (fun v hv => chartToBase_eq_closedPoint_of_mem_chartFibreSet hv)
      (isCompact_chartFibreSet hEc (U e))
  choose Z hZfp hZ using H
  refine ⟨s.sup Z, LocalFlattening.finitePresentation_subschemeι_finsetSup Z s
    (fun e _ => hZfp e), fun T g t ht => ?_⟩
  rw [LocalFlattening.exists_comp_subschemeι_eq_iff_le_ker, Finset.sup_le_iff]
  simp only [← LocalFlattening.exists_comp_subschemeι_eq_iff_le_ker]
  refine (forall_isFlatOverAtPoint_iff_forall_flatAlongAfter X f F hFq E U (↑s)
    (fun e he => ?_) T g t).trans (forall₂_congr fun e _ => hZ e _ t ht)
  obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp (hs he)
  exact ⟨e, he, hxe⟩

end AlgebraicGeometry.Space

end

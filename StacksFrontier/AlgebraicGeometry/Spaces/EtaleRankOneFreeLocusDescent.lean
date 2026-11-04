module

public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestrictionOver
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingOfModule

/-!
# The rank-one étale free locus along étale morphisms and on scheme charts

Let `X` be an algebraic space over a scheme `S` of a big fppf site and `F` an `𝒪_X`-module.
The rank-one étale free locus `AlgebraicGeometry.Space.etaleRankOneFreeLocus` of `F` is the set
of points of `|X|` having an étale neighbourhood on which `F` becomes the structure sheaf.  This
file proves two ways of putting points in it.

* **Along an étale morphism.**  For `φ : A ⟶ X` étale, a point of `|A|` in the locus of `φ^*F`
  maps to a point in the locus of `F`: an étale neighbourhood `a : V ⟶ A` trivializing `φ^*F`
  gives the étale neighbourhood `a ≫ φ` trivializing `F` (Stacks 03FT and the composition of
  inverse images).  So an `𝒪_X`-module whose inverse image along a surjective étale morphism is
  invertible is invertible.
* **From a scheme chart.**  For an étale scheme chart `A` of `X` and a quasi-coherent `F` whose
  restriction `F|_A` to the scheme of the chart is trivial on a Zariski open `W`, every point of
  `W` gives a point of the locus: `W` is again an étale chart of `X`, the restriction of `F` to
  it is trivial, and a quasi-coherent module on a represented algebraic space whose reading on
  the scheme is trivial is trivial (Stacks 03DX (2)).  So if `F|_A` is invertible on the scheme,
  every point of `|X|` coming from `A` lies in the locus.

In particular a quasi-coherent module on the algebraic space represented by a scheme `T` is
invertible as soon as its reading on `T` is an invertible module of the scheme.

## Main results

* `AlgebraicGeometry.Space.pointsMap_mem_etaleRankOneFreeLocus`: the locus is carried along
  étale morphisms.
* `AlgebraicGeometry.Space.isInvertibleModule_of_isInvertibleModule_modulePullback`:
  **invertibility descends along a surjective étale morphism.**
* `AlgebraicGeometry.Space.nonempty_iso_unit_of_idChartRestriction_iso_unit`: a quasi-coherent
  module on a represented algebraic space whose reading on the scheme is the structure sheaf is
  the structure sheaf.
* `AlgebraicGeometry.Space.chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_over_iso_unit` and
  `AlgebraicGeometry.Space.chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_iso`: the points of
  a scheme chart over which the restriction is trivial, respectively invertible.
* `AlgebraicGeometry.Space.isInvertibleModule_of_idChartRestriction_iso`: **a quasi-coherent
  module on a represented algebraic space whose reading on the scheme is invertible is
  invertible.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Along an étale morphism -/

/-- **The rank-one étale free locus is carried along étale morphisms.**  If `φ : A ⟶ X` is étale
and `y ∈ |A|` has an étale neighbourhood `a : V ⟶ A` with `a^*φ^*F ≅ 𝒪_V`, then `a ≫ φ` is an
étale neighbourhood of `φ(y)` with `(a ≫ φ)^*F ≅ 𝒪_V`. -/
theorem pointsMap_mem_etaleRankOneFreeLocus {A X : AlgebraicSpaces B S hS} (φ : A ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (F : Modules.{u, u} B S hS X.1 X.2) {y : points B S hS A.1}
    (hy : y ∈ etaleRankOneFreeLocus B S hS ((modulePullback B S hS φ).obj F)) :
    pointsMap B S hS A.1 φ.hom y ∈ etaleRankOneFreeLocus B S hS F := by
  obtain ⟨V, a, hae, ⟨v, rfl⟩, ⟨e⟩⟩ := hy
  refine ⟨V, a ≫ φ, isEtale_comp B S hS hae hφ, ⟨v, ?_⟩,
    ⟨((modulePullbackCompIso B S hS a φ).app F).symm ≪≫ e⟩⟩
  exact congrFun (pointsMap_comp B S hS V.1 a.hom φ.hom) v

/-- **Invertibility descends along a surjective étale morphism.**  If `φ : A ⟶ X` is étale and
surjective on points and `φ^*F` is invertible, then `F` is invertible: every point of `|X|` is
the image of a point of `|A|`, which lies in the rank-one étale free locus of the invertible
module `φ^*F`, and the locus is carried along `φ`; a module free of rank one in an étale
neighbourhood of every point is invertible (Stacks 0B8Q). -/
theorem isInvertibleModule_of_isInvertibleModule_modulePullback {A X : AlgebraicSpaces B S hS}
    (φ : A ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (hsurj : Function.Surjective (pointsMap B S hS A.1 φ.hom))
    (F : Modules.{u, u} B S hS X.1 X.2)
    (h : IsInvertibleModule A ((modulePullback B S hS φ).obj F)) :
    IsInvertibleModule X F := by
  refine (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one F).2
    (isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus B S hS F fun x => ?_)
  obtain ⟨y, rfl⟩ := hsurj x
  exact pointsMap_mem_etaleRankOneFreeLocus B S hS φ hφ F
    (mem_etaleRankOneFreeLocus_of_isInvertibleModule A _ h y)

/-! ### On a represented algebraic space -/

/-- **A quasi-coherent module on a represented algebraic space whose reading on the scheme is the
structure sheaf is the structure sheaf.**  Restriction to the small Zariski site reflects
isomorphisms between quasi-coherent modules on the small étale site of the scheme (Stacks 03DX
(2)), the structure sheaf reads as the structure sheaf
(`AlgebraicGeometry.Space.idChartRestrictionUnitIso`), and the small étale site of the scheme is
equivalent to that of the algebraic space it represents. -/
theorem nonempty_iso_unit_of_idChartRestriction_iso_unit (T : BigFppfOver B S hS)
    {hY : IsAlgebraicSpace B S hS (yoneda.obj T)} (N : Modules.{u, u} B S hS (yoneda.obj T) hY)
    (hN : N.IsQuasicoherentOnSite)
    (e : idChartRestriction B S hS T N ≅
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf) :
    Nonempty (N ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj T) hY).O)) := by
  let G := representedSmallEtaleModuleEquivalence B S hS T
  let Nu : Modules.{u, u} B S hS (yoneda.obj T) hY :=
    SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T) hY).O)
  have hqcNu : Nu.IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
  have hqcInv : ∀ (M : Modules.{u, u} B S hS (yoneda.obj T) hY), M.IsQuasicoherentOnSite →
      (G.inverse.obj M).IsQuasicoherentOnSite := fun M hM =>
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (G.counitIso.app M).symm hM)
  obtain ⟨e'⟩ := _root_.AlgebraicGeometry.SmallEtale.nonempty_iso_of_iso_restrictModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
    (G.inverse.obj N) (G.inverse.obj Nu) (hqcInv N hN) (hqcInv Nu hqcNu)
    (e ≪≫ (idChartRestrictionUnitIso B S hS T hY).symm)
  exact ⟨(G.counitIso.app N).symm ≪≫ G.functor.mapIso e' ≪≫ G.counitIso.app Nu⟩

/-! ### From a scheme chart -/

/-- **The points of a Zariski open of a scheme chart over which the chart restriction is trivial
lie in the rank-one étale free locus.**  The open `W` of the scheme of the chart `A` is itself an
étale chart of `X` (`AlgebraicGeometry.Space.chartOpens`), at which the restriction of `F` is the
restriction of `F|_A` to `W` (`AlgebraicGeometry.Space.nonempty_over_restrictToChart_chartOpens`),
hence trivial; the reading of the inverse image of `F` to the represented algebraic space of that
chart is that restriction (`AlgebraicGeometry.Space.schemeReadingChartIso`), so the inverse image
is trivial by `AlgebraicGeometry.Space.nonempty_iso_unit_of_idChartRestriction_iso_unit`. -/
theorem chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_over_iso_unit
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens)
    (e : (restrictToChart B S hS X.2 F A).over W ≅
      SheafOfModules.unit ((chartScheme A).ringCatSheaf.over W))
    (w : chartScheme A) (hw : w ∈ W) :
    chartSchemeToPoints B S hS X.1 A w ∈ etaleRankOneFreeLocus B S hS F := by
  let C := (chartOpens B S hS A).obj W
  obtain ⟨e₁⟩ := nonempty_over_restrictToChart_chartOpens B S hS X F hF A W
  have e₂ : restrictToChartScheme B S hS X.1 X.2 F C ≅
      SheafOfModules.unit (chartScheme C).ringCatSheaf :=
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 F C).symm ≪≫ e₁.symm ≪≫
      (Scheme.Modules.overEquiv W).functor.mapIso e ≪≫
      Opens.sheafOfModulesEquivOverUnit W (chartScheme A).ringCatSheaf
  obtain ⟨e₃⟩ := nonempty_iso_unit_of_idChartRestriction_iso_unit B S hS
    (chartFppfObject B S hS X C) ((modulePullback B S hS (chartToSpace B S hS X C)).obj F)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F hF)
    (schemeReadingChartIso F C ≪≫ e₂)
  refine ⟨chartSpace B S hS X C, chartToSpace B S hS X C, isEtale_chartToSpace B S hS X _, ?_,
    ⟨e₃⟩⟩
  let w' : chartScheme C := (⟨w, hw⟩ : W)
  have h : chartSchemeToPoints B S hS X.1 A w = chartSchemeToPoints B S hS X.1 C w' :=
    chartSchemeToPoints_map B S hS X.1 (chartOpensHom B S hS X A W) w'
  rw [h, chartSchemeToPoints_eq_pointsMap]
  exact ⟨_, rfl⟩

/-- **The points of a scheme chart over which the chart restriction is invertible lie in the
rank-one étale free locus.**  An invertible module on a scheme is trivial on an open
neighbourhood of every point (Stacks 0B8M), and
`AlgebraicGeometry.Space.chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_over_iso_unit`
applies there.  The restriction is given up to an isomorphism `e : F|_A ≅ L` with `L`
invertible. -/
theorem chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_iso
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (L : (chartScheme A).Modules)
    [hL : Stacks.Ample.IsInvertibleModule (chartScheme A) L]
    (e : restrictToChart B S hS X.2 F A ≅ L) (w : chartScheme A) :
    chartSchemeToPoints B S hS X.1 A w ∈ etaleRankOneFreeLocus B S hS F := by
  obtain ⟨W, hw, ⟨eW⟩⟩ := Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over _ L w
  exact chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_over_iso_unit B S hS X F hF A W
    ((SheafOfModules.overFunctor (chartScheme A).ringCatSheaf W).mapIso e ≪≫ eW) w hw

/-- **A quasi-coherent module on a represented algebraic space whose reading on the scheme is
invertible is invertible.**  Every point of the algebraic space represented by `T` comes from a
point of `T` through the identity chart (Stacks 03BX (1)), at which the restriction is the
reading; so the rank-one étale free locus is everything by
`AlgebraicGeometry.Space.chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_iso`, and the module
is invertible by Stacks 0B8Q.  The reading is given up to an isomorphism `e` with an invertible
module `L` of the scheme. -/
theorem isInvertibleModule_of_idChartRestriction_iso (T : BigFppfOver B S hS)
    {hY : IsAlgebraicSpace B S hS (yoneda.obj T)} (N : Modules.{u, u} B S hS (yoneda.obj T) hY)
    (hN : N.IsQuasicoherentOnSite) (L : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    [hL : Stacks.Ample.IsInvertibleModule _ L] (e : idChartRestriction B S hS T N ≅ L) :
    IsInvertibleModule ⟨yoneda.obj T, hY⟩ N := by
  refine (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one (Z := ⟨yoneda.obj T, hY⟩) N).2
    (isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus B S hS
      (Z := ⟨yoneda.obj T, hY⟩) N fun y => ?_)
  let t : chartScheme (idEtaleChart B S hS T) := pointsEquivScheme B S hS T y
  have hy : chartSchemeToPoints B S hS (yoneda.obj T) (idEtaleChart B S hS T) t = y :=
    (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS _ _ t).trans
      ((congrArg _ ((pointsEquivScheme B S hS T).symm_apply_apply y)).trans
        (congrFun (pointsMap_id B S hS (yoneda.obj T)) y))
  rw [← hy]
  exact chartSchemeToPoints_mem_etaleRankOneFreeLocus_of_iso B S hS ⟨yoneda.obj T, hY⟩ N hN
    (idEtaleChart B S hS T) L (hL := ‹_›)
    (restrictToChartIsoIdChartRestriction B S hS T N ≪≫ e) _

end AlgebraicGeometry.Space

end

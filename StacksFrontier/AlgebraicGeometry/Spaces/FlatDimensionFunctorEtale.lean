module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.FlatnessAtRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite

/-!
# The functor `F_n` along an étale morphism of the source

In **Situation 0CWU** — a morphism `f : X ⟶ Y` of algebraic spaces over `S`, locally of finite
type, and a quasi-coherent `𝒪_X`-module `F` of finite type — let `h : X' ⟶ X` be étale, set
`F' = h^* F` and `f' = f ∘ h`, and let `F'_n` be the functor of equation **0CWV** for
`(f', F')`. **Stacks 0CX0** says that `F_n` is a subfunctor of `F'_n`, and that `F_n = F'_n`
when `h(|X'|)` contains `Ass_{X/Y}(F)`.

## Main definitions

* `AlgebraicGeometry.Space.FlatDimensionSituation.etalePullback`: the situation `(f ∘ h, h^* F)`
  of Situation 0CWU attached to an étale `h : X' ⟶ X`.
* `AlgebraicGeometry.Space.FlatDimensionSituation.etalePullbackComparison`: the natural
  transformation `F_n ⟶ F'_n`.

## Main results

* `AlgebraicGeometry.Space.pointsMap_mem_flatLocus_iff_of_isEtale` and
  `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_comp_iff_of_isEtale`: along an étale
  morphism of sources, flatness over the target at a point and the transcendence degree of a
  point over its image do not change.
* `AlgebraicGeometry.Space.hasTrdegLtAtNonflatPoints_comp_of_isEtale` and
  `AlgebraicGeometry.Space.hasTrdegLtAtNonflatPoints_of_comp_of_isEtale`: the two halves of the
  lemma over a single base, in the form of condition (3) of Stacks 0CWS.
* `AlgebraicGeometry.Space.FlatDimensionSituation.mono_etalePullbackComparison_and_isIso`:
  **Stacks 0CX0**.

## Implementation notes

The source deduces the lemma from its scheme case, More on Flatness 05UD, on a chart diagram;
here the argument is run on condition (3) of Stacks 0CWS directly, at a test scheme `T`, for the
étale morphism `X'_T ⟶ X_T` of base changes, and the scheme input is the same as for 05UD: the
flatness criterion at the relative assassin, More on Flatness 05UA (in the form of
Stacks 0CWL, (2) ⟹ (1), read on a chart), and the strict inequality of transcendence degrees
along a specialization in a fibre, Stacks 06RU part (3).

* A commuting square of étale scheme charts of `f ∘ h` is one of `f`, with the same chart
  schemes and the same vertical morphism, and the restriction of `h^* F` to it is the restriction
  of `F` (`AlgebraicGeometry.Space.restrictToChartEtaleSourceIso`). So flatness at a point and the
  transcendence degree of a point are the same at a point of `|X'|` and at its image in `|X|`,
  which is the first assertion of the lemma.
* For the second assertion, a point `x` of `|X_T|` at which `F_T` is not flat lies on a chart
  `u`; by 05UA there is a point `u'` of the relative assassin of the chart, in the fibre through
  `u` and generalizing it, at which the chart module is not flat. Its image lies in
  `Ass_{X_T/T}(F_T)`, hence in the image of `X'_T`, by Stacks 0CW2 applied to the hypothesis on
  `h`; so the transcendence degree of `u'` is `< n`, and that of `u` is at most that of `u'`.

The relative assassin `Ass_{X/Y}(F)` is `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints`
of Stacks 0CV0: the source writes `Ass_{X/Y}(F)` for `WeakAss_{X/Y}(F)` when the fibres of `f` are
locally Noetherian, which they are as `f` is locally of finite type. The image `h(X')` is the
image of the map `|X'| ⟶ |X|` of point spaces.

Both functors are subterminal, so the subfunctor of the source is a monomorphism `F_n ⟶ F'_n`
and the equality `F_n = F'_n` is that this monomorphism is an isomorphism.

## References

* [Stacks Project, Tag 0CX0](https://stacks.math.columbia.edu/tag/0CX0)
* [Stacks Project, Tag 0CWU](https://stacks.math.columbia.edu/tag/0CWU)
* [Stacks Project, Tag 0CWV](https://stacks.math.columbia.edu/tag/0CWV)
* [Stacks Project, Tag 0CWS](https://stacks.math.columbia.edu/tag/0CWS)
* [Stacks Project, Tag 0CW2](https://stacks.math.columbia.edu/tag/0CW2)
* [Stacks Project, Tag 0CWL](https://stacks.math.columbia.edu/tag/0CWL)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 05UD](https://stacks.math.columbia.edu/tag/05UD)
* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 06RU](https://stacks.math.columbia.edu/tag/06RU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Flatness and transcendence degree along an étale morphism of sources -/

section EtaleSource

variable {Xs' Xs Ys : AlgebraicSpaces B S hS} {a : Xs' ⟶ Xs}

/-- **Flatness at a point along an étale morphism of sources.** For an étale `a : X' ⟶ X` and a
quasi-coherent `𝒪_X`-module `F`, the module `a^* F` is flat over `Y` at a point `x'` of `|X'|`
along `f ∘ a` exactly when `F` is flat over `Y` at `a(x')`. -/
theorem pointsMap_mem_flatLocus_iff_of_isEtale (ha : IsEtale B S hS a.hom) (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hF : F.IsQuasicoherentOnSite]
    (x' : points B S hS Xs'.1) :
    pointsMap B S hS Xs'.1 a.hom x' ∈ flatLocus B S hS Xs.2 f.hom F ↔
      x' ∈ flatLocus B S hS Xs'.2 (a.hom ≫ f.hom) ((modulePullback B S hS a).obj F) := by
  have : ((modulePullback B S hS a).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a F hF
  obtain ⟨d, w, rfl⟩ :=
    exists_chartDiagram_pointOfEtaleChart B S hS Xs'.2 Ys.2 (a.hom ≫ f.hom) x'
  rw [← pointOfEtaleChart_chartOfEtaleSource B S hS ha d.U w]
  exact (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F
      (chartDiagramOfEtaleSource B S hS ha f d) w).symm.trans
    ((_root_.AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _
      (restrictToChartEtaleSourceIso B S hS ha F hF d.U) w).trans
      (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS (a ≫ f)
        ((modulePullback B S hS a).obj F) d w))

/-- **The transcendence degree along an étale morphism of sources.** For an étale
`a : X' ⟶ X`, the transcendence degree of a point `x'` of `|X'|` over its image under `f ∘ a`
is the transcendence degree of `a(x')` over its image under `f`. -/
theorem hasTranscendenceDegreeAt_comp_iff_of_isEtale (ha : IsEtale B S hS a.hom)
    (f : Xs ⟶ Ys) (x' : points B S hS Xs'.1) (r : ℕ∞) :
    HasTranscendenceDegreeAt B S hS (a.hom ≫ f.hom) x' r ↔
      HasTranscendenceDegreeAt B S hS f.hom (pointsMap B S hS Xs'.1 a.hom x') r := by
  obtain ⟨d, w, rfl⟩ :=
    exists_chartDiagram_pointOfEtaleChart B S hS Xs'.2 Ys.2 (a.hom ≫ f.hom) x'
  rw [← pointOfEtaleChart_chartOfEtaleSource B S hS ha d.U w]
  exact (hasTranscendenceDegreeAt_pointOfEtaleChart_iff B S hS (a ≫ f) d w r).trans
    (hasTranscendenceDegreeAt_pointOfEtaleChart_iff B S hS f
      (chartDiagramOfEtaleSource B S hS ha f d) w r).symm

/-- **The first half of Stacks 0CX0 over one base.** If `F` satisfies condition (3) of
Stacks 0CWS for `f`, then `a^* F` satisfies it for `f ∘ a`, for every étale `a : X' ⟶ X`. -/
theorem hasTrdegLtAtNonflatPoints_comp_of_isEtale (ha : IsEtale B S hS a.hom) (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite] {n : ℕ}
    (h : HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n) :
    HasTrdegLtAtNonflatPoints B S hS Xs'.2 (a.hom ≫ f.hom) ((modulePullback B S hS a).obj F)
      n := by
  intro x' hx'
  obtain ⟨r, hr, hrn⟩ := h (pointsMap B S hS Xs'.1 a.hom x') fun hm =>
    hx' ((pointsMap_mem_flatLocus_iff_of_isEtale B S hS ha f F x').1 hm)
  exact ⟨r, (hasTranscendenceDegreeAt_comp_iff_of_isEtale B S hS ha f x' r).2 hr, hrn⟩

/-- **The second half of Stacks 0CX0 over one base.** Let `f : X ⟶ Y` be locally of finite type,
let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `a : X' ⟶ X` be étale with
`Ass_{X/Y}(F) ⊆ a(|X'|)`. If `a^* F` satisfies condition (3) of Stacks 0CWS for `f ∘ a`, then `F`
satisfies it for `f`. -/
theorem hasTrdegLtAtNonflatPoints_of_comp_of_isEtale (ha : IsEtale B S hS a.hom) (f : Xs ⟶ Ys)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    [hF : F.IsQuasicoherentOnSite] (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (hAss : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS Xs'.1 a.hom)) {n : ℕ}
    (h : HasTrdegLtAtNonflatPoints B S hS Xs'.2 (a.hom ≫ f.hom)
      ((modulePullback B S hS a).obj F) n) :
    HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n := by
  intro x hx
  obtain ⟨d, u, rfl⟩ := exists_chartDiagram_pointOfEtaleChart B S hS Xs.2 Ys.2 f.hom x
  set q := chartDiagramSchemeMap B S hS f d
  have : LocallyOfFiniteType q := locallyOfFiniteType_chartDiagramSchemeMap B S hS f hf d
  have : SheafOfModules.IsQuasicoherent (chartDiagramRestrictSource B S hS f F d) :=
    isQuasicoherent_restrictToChart B S hS Xs F hF d.U
  have : SheafOfModules.IsFiniteType (chartDiagramRestrictSource B S hS f F d) :=
    isFiniteType_restrictToChart B S hS Xs F hF hFft d.U
  -- `F` is not flat at `u` on the chart
  have hnu : ¬ IsFlatOverAt q.toLRSHom.toShHom (chartDiagramRestrictSource B S hS f F d) u :=
    fun hu => hx ((isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).1 hu)
  -- a point of the relative assassin of the chart generalizing `u` in its fibre, not flat
  obtain ⟨u', hu'q, hu'ass, hu'sp, hu'nf⟩ : ∃ u' : chartScheme d.U, q.base u' = q.base u ∧
      u' ∈ Stacks.Divisors.relativeAssassin q (chartDiagramRestrictSource B S hS f F d) ∧
      u' ⤳ u ∧
      ¬ IsFlatOverAt q.toLRSHom.toShHom (chartDiagramRestrictSource B S hS f F d) u' := by
    by_contra hcon
    push Not at hcon
    exact hnu (isFlatOverAt_of_forall_mem_relativeAssassin_specializes q _ u hcon)
  -- its image in `|X|` lies in the relative assassin, hence comes from `|X'|`
  have hpe : pointOfEtaleChart B S hS d.U u' = chartSchemeToPoints B S hS Xs.1 d.U u' :=
    (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS Xs.1 d.U u').symm
  have hx₁ass : pointOfEtaleChart B S hS d.U u' ∈ relativeWeaklyAssociatedPoints B S hS f F := by
    rw [hpe]
    exact isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram B S hS f F hF d
      u' hu'ass
  obtain ⟨x₁', hx₁'⟩ := hAss hx₁ass
  have hx₁'nf : x₁' ∉ flatLocus B S hS Xs'.2 (a.hom ≫ f.hom) ((modulePullback B S hS a).obj F) :=
    fun hm => hu'nf ((isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u').2
      (hx₁' ▸ (pointsMap_mem_flatLocus_iff_of_isEtale B S hS ha f F x₁').2 hm))
  obtain ⟨r, hr, hrn⟩ := h x₁' hx₁'nf
  have hr' : HasTranscendenceDegreeAt B S hS f.hom (pointOfEtaleChart B S hS d.U u') r := by
    rw [← hx₁']
    exact (hasTranscendenceDegreeAt_comp_iff_of_isEtale B S hS ha f x₁' r).1 hr
  have hru' := (hasTranscendenceDegreeAt_pointOfEtaleChart_iff B S hS f d u' r).1 hr'
  -- the transcendence degree at `u` is at most the one at `u'`
  let : Algebra ((etaleChartScheme B S hS d.V).residueField (q u))
      ((etaleChartScheme B S hS d.U).residueField u) := (q.residueFieldMap u).hom.toAlgebra
  refine ⟨Cardinal.toENat (Algebra.trdeg ((etaleChartScheme B S hS d.V).residueField (q u))
      ((etaleChartScheme B S hS d.U).residueField u)),
    (hasTranscendenceDegreeAt_pointOfEtaleChart_iff B S hS f d u _).2 rfl, ?_⟩
  refine lt_of_le_of_lt ?_ (hru'.trans_lt hrn)
  rcases eq_or_ne u' u with rfl | hne
  · exact le_rfl
  · have hstrict := trdeg_residueField_fiber_lt_of_specialization q hu'sp hne hu'q rfl
    have key : ∀ (s : chartScheme d.V) (e : q u' = s),
        let : Algebra ((etaleChartScheme B S hS d.V).residueField s)
            ((etaleChartScheme B S hS d.U).residueField u') :=
          (((etaleChartScheme B S hS d.V).residueFieldCongr e).inv ≫
            q.residueFieldMap u').hom.toAlgebra
        let : Algebra ((etaleChartScheme B S hS d.V).residueField (q u'))
            ((etaleChartScheme B S hS d.U).residueField u') :=
          (q.residueFieldMap u').hom.toAlgebra
        Algebra.trdeg ((etaleChartScheme B S hS d.V).residueField s)
            ((etaleChartScheme B S hS d.U).residueField u') =
          Algebra.trdeg ((etaleChartScheme B S hS d.V).residueField (q u'))
            ((etaleChartScheme B S hS d.U).residueField u') := by
      rintro s rfl
      rfl
    exact (Cardinal.toENat.monotone' hstrict.le).trans_eq (congrArg Cardinal.toENat (key _ hu'q))

end EtaleSource

/-! ### The situation along an étale morphism -/

namespace FlatDimensionSituation

variable {B S hS}

/-- **The situation `(f ∘ h, h^* F)` of Stacks 0CX0.** For Situation 0CWU on `f : X ⟶ Y` and `F`
and an étale morphism `h : X' ⟶ X`, the morphism `f' = f ∘ h` is again locally of finite type and
`F' = h^* F` is again quasi-coherent of finite type, so `(f', F')` is again Situation 0CWU. -/
abbrev etalePullback (D : FlatDimensionSituation.{u} B S hS) {X' : AlgebraicSpaces B S hS}
    (h : X' ⟶ D.X) (hh : IsEtale B S hS h.hom) : FlatDimensionSituation.{u} B S hS where
  X := X'
  Y := D.Y
  f := h ≫ D.f
  F := (modulePullback B S hS h).obj D.F
  quasicoherent :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS h D.F D.quasicoherent
  locallyOfFiniteType :=
    isLocallyOfFiniteType_comp B S hS X'.2 D.X.2 D.Y.2 h.hom D.f.hom
      (isLocallyOfFiniteType_of_isEtale B S hS D.X.2 hh) D.locallyOfFiniteType
  finiteType := isFiniteTypeOnSite_modulePullback B S hS h D.F D.finiteType

variable (D : FlatDimensionSituation.{u} B S hS) {X' : AlgebraicSpaces B S hS}
  (h : X' ⟶ D.X) (hh : IsEtale B S hS h.hom)

/-- The morphism `X'_T ⟶ X_T` of base changes to a test scheme `T` induced by `h : X' ⟶ X`. -/
def etalePullbackBaseChangeMap (T : SchemesOver D.Y) :
    baseChangeSpace (h ≫ D.f) T ⟶ baseChangeSpace D.f T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f
      ((schemesOverToOver D.Y).obj T).hom).lift
    (baseChangeProjection (h ≫ D.f) T ≫ h) (baseChangeInclusion (h ≫ D.f) T)
    (by
      rw [Category.assoc]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS (h ≫ D.f)
        ((schemesOverToOver D.Y).obj T).hom).w)

/-- The morphism `X'_T ⟶ X_T` followed by the projection `X_T ⟶ X` is the projection
`X'_T ⟶ X'` followed by `h`. -/
@[reassoc (attr := simp)]
theorem etalePullbackBaseChangeMap_projection (T : SchemesOver D.Y) :
    D.etalePullbackBaseChangeMap h T ≫ baseChangeProjection D.f T =
      baseChangeProjection (h ≫ D.f) T ≫ h :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f
    ((schemesOverToOver D.Y).obj T).hom).lift_fst _ _ _

/-- The morphism `X'_T ⟶ X_T` commutes with the morphisms of `X'_T` and `X_T` to `T`. -/
@[reassoc (attr := simp)]
theorem etalePullbackBaseChangeMap_inclusion (T : SchemesOver D.Y) :
    D.etalePullbackBaseChangeMap h T ≫ baseChangeInclusion D.f T =
      baseChangeInclusion (h ≫ D.f) T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f
    ((schemesOverToOver D.Y).obj T).hom).lift_snd _ _ _

/-- `X'_T = X_T ×_X X'`: the square of `X'_T ⟶ X_T` over `h` is cartesian, by cancelling the
cartesian square defining `X_T` from the one defining `X'_T`. -/
theorem isPullback_etalePullbackBaseChangeMap (T : SchemesOver D.Y) :
    IsPullback (baseChangeProjection (h ≫ D.f) T) (D.etalePullbackBaseChangeMap h T) h
      (baseChangeProjection D.f T) := by
  refine IsPullback.of_bot (v₂₁ := baseChangeInclusion D.f T) (v₂₂ := D.f)
    (h₃₁ := ((schemesOverToOver D.Y).obj T).hom) ?_
    (D.etalePullbackBaseChangeMap_projection h T).symm
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f ((schemesOverToOver D.Y).obj T).hom)
  have hs : IsPullback (baseChangeProjection (h ≫ D.f) T) (baseChangeInclusion (h ≫ D.f) T)
      (h ≫ D.f) ((schemesOverToOver D.Y).obj T).hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS (h ≫ D.f) ((schemesOverToOver D.Y).obj T).hom
  exact (D.etalePullbackBaseChangeMap_inclusion h T).symm ▸ hs

include hh in
/-- The morphism `X'_T ⟶ X_T` is étale, as a base change of `h`. -/
theorem isEtale_etalePullbackBaseChangeMap (T : SchemesOver D.Y) :
    IsEtale B S hS (D.etalePullbackBaseChangeMap h T).hom :=
  isEtale_of_isPullback B S hS _ _ _ _ (D.isPullback_etalePullbackBaseChangeMap h T) hh

/-- The base change `F'_T` of `F' = h^* F` is the inverse image of `F_T` along `X'_T ⟶ X_T`. -/
def etalePullbackBaseChangeModuleIso (T : SchemesOver D.Y) :
    (D.etalePullback h hh).toFlatnessSituation.baseChangeModule T ≅
      (modulePullback B S hS (D.etalePullbackBaseChangeMap h T)).obj
        (D.toFlatnessSituation.baseChangeModule T) :=
  ((modulePullbackTriangle B S hS
      (rfl : baseChangeProjection (h ≫ D.f) T ≫ h = baseChangeProjection (h ≫ D.f) T ≫ h)).app
        D.F).symm ≪≫
    (modulePullbackTriangle B S hS (D.etalePullbackBaseChangeMap_projection h T)).app D.F

/-- The base change `F_T` of `F` to a test scheme `T` is quasi-coherent. -/
private theorem isQuasicoherentOnSite_baseChangeModule (T : SchemesOver D.Y) :
    (D.toFlatnessSituation.baseChangeModule T).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (baseChangeProjection D.f T) D.F D.quasicoherent

/-- The condition of Stacks 0CWT at a test scheme, in the form of condition (3) of
Stacks 0CWS. -/
theorem isFlatInDimensionsGEAfterBaseChange_iff_hasTrdegLt (T : SchemesOver D.Y) (n : ℕ) :
    D.IsFlatInDimensionsGEAfterBaseChange T n ↔
      HasTrdegLtAtNonflatPoints B S hS (baseChangeSpace D.f T).2
        (baseChangeInclusion D.f T).hom (D.toFlatnessSituation.baseChangeModule T) n := by
  have hqc := D.isQuasicoherentOnSite_baseChangeModule T
  exact isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt B S hS
    (baseChangeInclusion D.f T) (D.toFlatnessSituation.baseChangeModule T)
    (D.isLocallyOfFiniteType_baseChangeInclusion T)
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS _ _ hqc)
    (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS _ _ hqc
      (D.isFiniteTypeOnSite_baseChangeModule T)) n

/-- The condition of Stacks 0CWT at a test scheme for `(f ∘ h, h^* F)`, read on the étale
morphism `X'_T ⟶ X_T` of base changes and the inverse image of `F_T` along it, in the form of
condition (3) of Stacks 0CWS. -/
theorem etalePullback_isFlatInDimensionsGEAfterBaseChange_iff (T : SchemesOver D.Y) (n : ℕ) :
    (D.etalePullback h hh).IsFlatInDimensionsGEAfterBaseChange T n ↔
      HasTrdegLtAtNonflatPoints B S hS (baseChangeSpace (h ≫ D.f) T).2
        ((D.etalePullbackBaseChangeMap h T).hom ≫ (baseChangeInclusion D.f T).hom)
        ((modulePullback B S hS (D.etalePullbackBaseChangeMap h T)).obj
          (D.toFlatnessSituation.baseChangeModule T)) n := by
  have hqcT := D.isQuasicoherentOnSite_baseChangeModule T
  have hqc : ((modulePullback B S hS (D.etalePullbackBaseChangeMap h T)).obj
      (D.toFlatnessSituation.baseChangeModule T)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hqcT
  have hft : SheafOfModules.IsFiniteTypeOnSite
      ((modulePullback B S hS (D.etalePullbackBaseChangeMap h T)).obj
        (D.toFlatnessSituation.baseChangeModule T)) :=
    isFiniteTypeOnSite_modulePullback B S hS _ _ (D.isFiniteTypeOnSite_baseChangeModule T)
  have hlft : IsLocallyOfFiniteType B S hS
      ((D.etalePullbackBaseChangeMap h T).hom ≫ (baseChangeInclusion D.f T).hom) :=
    isLocallyOfFiniteType_comp B S hS (baseChangeSpace (h ≫ D.f) T).2 (baseChangeSpace D.f T).2
      ((schemeSpaceFunctor B S hS).obj T.left).2 _ _
      (isLocallyOfFiniteType_of_isEtale B S hS (baseChangeSpace D.f T).2
        (D.isEtale_etalePullbackBaseChangeMap h hh T))
      (D.isLocallyOfFiniteType_baseChangeInclusion T)
  have hincl : (baseChangeInclusion (h ≫ D.f) T).hom =
      (D.etalePullbackBaseChangeMap h T).hom ≫ (baseChangeInclusion D.f T).hom :=
    congrArg (fun k => k.hom) (D.etalePullbackBaseChangeMap_inclusion h T).symm
  refine (isFlatOverInDimensionsGEOnEveryChartDiagram_iff_of_moduleIso B S hS _ _
    (D.etalePullbackBaseChangeModuleIso h hh T) n).trans ?_
  change IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS (baseChangeSpace (h ≫ D.f) T).2
    (baseChangeInclusion (h ≫ D.f) T).hom _ n ↔ _
  rw [hincl]
  exact isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt B S hS
    (D.etalePullbackBaseChangeMap h T ≫ baseChangeInclusion D.f T) _ hlft
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS _ _ hqc)
    (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS _ _ hqc hft) n

/-- **The first assertion of Stacks 0CX0, at a test scheme.** If `F_T` is flat over `T` in
dimensions `≥ n`, then so is `F'_T`. -/
theorem etalePullback_isFlatInDimensionsGEAfterBaseChange (T : SchemesOver D.Y) (n : ℕ)
    (hT : D.IsFlatInDimensionsGEAfterBaseChange T n) :
    (D.etalePullback h hh).IsFlatInDimensionsGEAfterBaseChange T n := by
  have hqcT := D.isQuasicoherentOnSite_baseChangeModule T
  exact (D.etalePullback_isFlatInDimensionsGEAfterBaseChange_iff h hh T n).2
    (hasTrdegLtAtNonflatPoints_comp_of_isEtale B S hS
      (D.isEtale_etalePullbackBaseChangeMap h hh T) (baseChangeInclusion D.f T) _
      ((D.isFlatInDimensionsGEAfterBaseChange_iff_hasTrdegLt T n).1 hT))

/-- **The second assertion of Stacks 0CX0, at a test scheme.** If `Ass_{X/Y}(F) ⊆ h(|X'|)` and
`F'_T` is flat over `T` in dimensions `≥ n`, then so is `F_T`. -/
theorem isFlatInDimensionsGEAfterBaseChange_of_etalePullback
    (hAss : relativeWeaklyAssociatedPoints B S hS D.f D.F ⊆
      Set.range (pointsMap B S hS X'.1 h.hom))
    (T : SchemesOver D.Y) (n : ℕ)
    (hT : (D.etalePullback h hh).IsFlatInDimensionsGEAfterBaseChange T n) :
    D.IsFlatInDimensionsGEAfterBaseChange T n := by
  have hqcT := D.isQuasicoherentOnSite_baseChangeModule T
  have hAssT := relativeWeaklyAssociatedPoints_baseChange_subset_range B S hS
    (AlgebraicSpaces.isPullback_hom B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f ((schemesOverToOver D.Y).obj T).hom))
    (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback_etalePullbackBaseChangeMap h T).flip)
    D.F hAss
  exact (D.isFlatInDimensionsGEAfterBaseChange_iff_hasTrdegLt T n).2
    (hasTrdegLtAtNonflatPoints_of_comp_of_isEtale B S hS
      (D.isEtale_etalePullbackBaseChangeMap h hh T) (baseChangeInclusion D.f T)
      (D.isLocallyOfFiniteType_baseChangeInclusion T) _
      (D.isFiniteTypeOnSite_baseChangeModule T) hAssT
      ((D.etalePullback_isFlatInDimensionsGEAfterBaseChange_iff h hh T n).1 hT))

/-- The natural transformation `F_n ⟶ F'_n` from the functor of equation 0CWV for `(f, F)` to
the one for `(f ∘ h, h^* F)`: both are subterminal, and the condition defining the first implies
the one defining the second at every test scheme. -/
def etalePullbackComparison (n : ℕ) :
    D.flatDimensionFunctor n ⟶ (D.etalePullback h hh).flatDimensionFunctor n where
  app T := ↾fun x => ⟨x.1, D.etalePullback_isFlatInDimensionsGEAfterBaseChange h hh T.unop n x.2⟩
  naturality T T' g := by
    have := (D.etalePullback h hh).flatDimensionFunctor_obj_subsingleton n T'.unop
    exact ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _

/-- **Stacks 0CX0.** In Situation 0CWU, let `h : X' ⟶ X` be an étale morphism, set `F' = h^* F`
and `f' = f ∘ h`, and let `F'_n` be the functor of equation 0CWV for `(f' : X' ⟶ Y, F')`. Then
`F_n` is a subfunctor of `F'_n` — the canonical natural transformation `F_n ⟶ F'_n` is a
monomorphism — and if `h(|X'|) ⊇ Ass_{X/Y}(F)` then `F_n = F'_n` — that monomorphism is an
isomorphism. -/
@[stacks 0CX0 "the full statement at the source's hypotheses, nothing granted or assumed: \
Situation 0CWU (f locally of finite type, F quasi-coherent of finite type) and h etale only. \
'F_n is a subfunctor of F'_n' is that the canonical natural transformation F_n -> F'_n between \
these subterminal functors is a monomorphism, and 'F_n = F'_n' is that it is an isomorphism. \
Ass_{X/Y}(F) is the relative weak assassin of Stacks 0CV0, which the source writes Ass_{X/Y}(F) \
as the fibres of f are locally Noetherian, and h(X') is the image of |X'| -> |X|"]
theorem mono_etalePullbackComparison_and_isIso (n : ℕ) :
    Mono (D.etalePullbackComparison h hh n) ∧
      (relativeWeaklyAssociatedPoints B S hS D.f D.F ⊆
          Set.range (pointsMap B S hS X'.1 h.hom) →
        IsIso (D.etalePullbackComparison h hh n)) := by
  refine ⟨?_, fun hAss => ?_⟩
  · have : ∀ T, Mono ((D.etalePullbackComparison h hh n).app T) := by
      intro T
      have := D.flatDimensionFunctor_obj_subsingleton n T.unop
      exact (mono_iff_injective _).2 fun _ _ _ => Subsingleton.elim _ _
    exact NatTrans.mono_of_mono_app _
  · rw [NatTrans.isIso_iff_isIso_app]
    intro T
    have := D.flatDimensionFunctor_obj_subsingleton n T.unop
    have := (D.etalePullback h hh).flatDimensionFunctor_obj_subsingleton n T.unop
    rw [isIso_iff_bijective]
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y =>
      ⟨⟨y.1, D.isFlatInDimensionsGEAfterBaseChange_of_etalePullback h hh hAss T.unop n y.2⟩,
        Subsingleton.elim _ _⟩⟩

end FlatDimensionSituation

end AlgebraicGeometry.Space

end

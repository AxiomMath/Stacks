module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkUnitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberThroughPoint

/-!
# Carrying a chart of `X` through `ξ` to a chart of `Spec(𝒪_{U, u})`

Let `X` be a decent algebraic space over a scheme `S`, let `Z ⊂ X` be a prime divisor with
generic point `ξ`, and let `(U, u)` be the chosen affine elementary étale neighbourhood of `ξ`.
The chart `j : Spec(𝒪_{U, u}) ⟶ X` carries the closed point to `ξ`. So an étale chart `V` of
`X` whose image contains `ξ` can be *base changed* along `j`, and the resulting chart of
`Spec(𝒪_{U, u})` has the closed point in its image: a cartesian square of presheaves is
surjective on pairs of points agreeing downstairs (Stacks 03H4), and the closed point and the
point of `V` over `ξ` are such a pair.

## Main definitions

* `AlgebraicGeometry.Space.chartToIdEtaleChart` is the canonical morphism from a chart of a
  representable algebraic space to its identity chart.
* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkBaseChangeChart` and
  `AlgebraicGeometry.Space.PrimeDivisor.genericStalkBaseChangeDiagram` are the base change of a
  chart of `X` along `j` and the commuting square of charts it sits in.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartRatio` is the ratio of a meromorphic
  section against a free generator of `ℒ` over a chart of `X`, carried to a chart of
  `Spec(𝒪_{U, u})` over the base change.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.pointsMap_genericStalkMorphism_eq_genericPoint`: the
  closed point of `Spec(𝒪_{U, u})` lies over the generic point `ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor.representable_genericStalkMorphism`: `j` is
  representable, so charts of `X` can be base changed along it.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_mem_range_genericStalkBaseChangeChart`: the base
  change of a chart through `ξ` has the closed point in its image.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_eval_eq_tmul_genericStalkBaseChange`: over
  the charts of a covering sieve of that base change, the pullback of a section presented over
  the chart as `c` times a free generator is the pullback of `c` times a free generator;
  `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_eval_eq_one_tmul_genericStalkBaseChange` is
  the case `c = 1` of `AlgebraicGeometry.Space.GeneratesOnChart`.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio`:
  over those charts the coefficient `t / s_ξ` of Stacks 0EPR is a unit of the regular functions
  times the ratio `t / e` of `t` against the generator over the chart of `X`.
* `PrimeDivisor.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_generatesOnChart`: the
  coefficient of Stacks 0EPR is the image of a unit of `𝒪_{U, u}` wherever the section generates
  `ℒ` on a chart through `ξ`.
* `AlgebraicGeometry.Space.canonicalRatioIsUnitOnGeneratingChart`: **the field `generating` of
  the data of Stacks 0EPW at the canonical choices, with no hypothesis.**

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-- **The closed point of `Spec(𝒪_{U, u})` lies over the generic point `ξ`.** A point `q` of
`Spec(𝒪_{U, u})` whose underlying point under `AlgebraicGeometry.Space.pointsToScheme` is the
closed point is carried by `j : Spec(𝒪_{U, u}) ⟶ X` to `ξ`. -/
theorem PrimeDivisor.pointsMap_genericStalkMorphism_eq_genericPoint
    (q : points B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (hq : pointsToScheme B S hS (Z.genericStalkSpec B S hS hX hdec) q =
      IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec)) :
    pointsMap B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkMorphism B S hS hX hdec).hom q =
      Z.genericPoint B S hS X := by
  -- the image of `q` in the chart `U`
  have hr : pointsToScheme B S hS (Z.genericChart B S hS hX hdec).scheme
        (pointsMap B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (yoneda.map (Z.genericStalkSpecToChart B S hS hX hdec)) q) =
      (Z.genericChart B S hS hX hdec).point := by
    refine (pointsToScheme_pointsMap_yoneda B S hS
      (Z.genericStalkSpecToChart B S hS hX hdec) q).trans ?_
    rw [Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec, hq]
    exact Scheme.fromSpecStalk_closedPoint
  -- so it is the point `u` of the elementary étale neighbourhood
  have heq : pointsMap B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (yoneda.map (Z.genericStalkSpecToChart B S hS hX hdec)) q =
      presheafPoint B S hS (Z.genericChart B S hS hX hdec).scheme
        (Z.genericChart B S hS hX hdec).point
        (Z.genericChart B S hS hX hdec).residueField_contained :=
    injective_pointsToScheme B S hS (Z.genericChart B S hS hX hdec).scheme
      (hr.trans (pointsToScheme_presheafPoint B S hS (Z.genericChart B S hS hX hdec).scheme
        (Z.genericChart B S hS hX hdec).point
        (Z.genericChart B S hS hX hdec).residueField_contained).symm)
  exact (pointsMap_comp_apply B S hS (yoneda.map (Z.genericStalkSpecToChart B S hS hX hdec))
    (Z.genericChart B S hS hX hdec).toSpace q).trans
      ((congrArg (pointsMap B S hS (yoneda.obj (Z.genericChart B S hS hX hdec).scheme)
        (Z.genericChart B S hS hX hdec).toSpace) heq).trans
          (Z.genericChart B S hS hX hdec).map_point)

/-! ### A chart of a representable algebraic space maps to the identity chart -/

/-- **The canonical morphism from a chart of a representable algebraic space to its identity
chart**, given by the Yoneda preimage of the structure morphism of the chart. -/
def chartToIdEtaleChart {T : BigFppfOver B S hS} (P : SmallEtale B S hS (yoneda.obj T)) :
    P ⟶ idEtaleChart B S hS T :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage P.obj.hom)
    ((Category.comp_id _).trans (yoneda.map_preimage _)))

/-- The morphism of the site underlying
`AlgebraicGeometry.Space.chartToIdEtaleChart` is the Yoneda preimage of the chart's structure
morphism. -/
theorem toOver_map_chartToIdEtaleChart {T : BigFppfOver B S hS}
    (P : SmallEtale B S hS (yoneda.obj T)) :
    (SmallEtale.toOver B S hS (yoneda.obj T)).map (chartToIdEtaleChart B S hS P) =
      yoneda.preimage P.obj.hom :=
  rfl

/-! ### The base change of a chart of `X` to `Spec(𝒪_{U, u})` -/

/-- **The morphism `j : Spec(𝒪_{U, u}) ⟶ X` is representable**, the diagonal of an algebraic
space being representable. -/
theorem PrimeDivisor.representable_genericStalkMorphism :
    yoneda.relativelyRepresentable (Z.genericStalkMorphism B S hS hX hdec).hom :=
  Functor.relativelyRepresentable.of_diag hX.diagonal_representable _

/-- **The base change of an étale chart of `X` to `Spec(𝒪_{U, u})`.** -/
abbrev PrimeDivisor.genericStalkBaseChangeChart (V : SmallEtale B S hS X) :
    SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1 :=
  (smallBaseChange B S hS (Z.genericStalkMorphism B S hS hX hdec)
    (Z.representable_genericStalkMorphism B S hS hX hdec)).obj V

/-- **The commuting square of charts over `j` at the base change of an étale chart of `X`.**
`V` is a chart of `X`, its base change is a chart of `Spec(𝒪_{U, u})`, and the square is the
cartesian one defining the base change. -/
def PrimeDivisor.genericStalkBaseChangeDiagram (V : SmallEtale B S hS X) :
    ChartDiagram B S hS (Z.genericStalkSpace B S hS hX hdec).1 X
      (Z.genericStalkMorphism B S hS hX hdec).hom where
  U := Z.genericStalkBaseChangeChart B S hS hX hdec V
  V := V
  g := (Z.representable_genericStalkMorphism B S hS hX hdec).snd V.obj.hom
  comm := ((Z.representable_genericStalkMorphism B S hS hX hdec).isPullback V.obj.hom).w

/-- **The base change of a chart of `X` through `ξ` has the closed point of `Spec(𝒪_{U, u})` in
its image.** -/
theorem PrimeDivisor.exists_mem_range_genericStalkBaseChangeChart (V : SmallEtale B S hS X)
    (hmem : Z.genericPoint B S hS X ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom)) :
    ∃ p : chartScheme (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage
          (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom) p =
        IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec) := by
  obtain ⟨b, hb⟩ := hmem
  obtain ⟨q, hq⟩ := surjective_pointsToScheme B S hS (Z.genericStalkSpec B S hS hX hdec)
    (IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec))
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
    ((Z.representable_genericStalkMorphism B S hS hX hdec).isPullback V.obj.hom) q b
    ((Z.pointsMap_genericStalkMorphism_eq_genericPoint B S hS hX hdec q hq).trans hb.symm)
  refine ⟨pointsToScheme B S hS _ w, ?_⟩
  refine Eq.trans (pointsToScheme_pointsMap_yoneda B S hS (yoneda.preimage
    (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom) w).symm ?_
  refine Eq.trans (congrArg (pointsToScheme B S hS (Z.genericStalkSpec B S hS hX hdec))
    (congrArg (fun φ ↦ pointsMap B S hS _ φ w) (yoneda.map_preimage
      (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom))) ?_
  exact (congrArg (pointsToScheme B S hS (Z.genericStalkSpec B S hS hX hdec)) hw).trans hq

/-! ### The inverse image of the generating section over the charts of a covering sieve -/

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

include hX in
/-- **The inverse image of a presentation of `t` against a free generator of `ℒ` over a chart of
`X` is a presentation over the charts of a covering sieve of the base-changed chart.** If `ℒ` is
free on `e` over the étale chart `V` of `X` and `t|_V = c · e`, then over the charts of a
covering sieve of the base change of `V` to `Spec(𝒪_{U, u})` the pullback of `t` is the pullback
of `c` times a free generator of the pullback of `ℒ`. -/
theorem PrimeDivisor.exists_sieve_eval_eq_tmul_genericStalkBaseChange
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj (op V))
    (hpres : t.eval (op V) = toMeromorphicSectionSheaf B S hS X hX L V
      (c ⊗ₜ[chartRing B S hS X hX V] e V (𝟙 V) :
        (meromorphicSectionModule B S hS X hX L).obj (op V))) :
    ∃ T : Sieve (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      T ∈ SmallEtale.topology B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkBaseChangeChart B S hS hX hdec V) ∧
        ∀ ⦃Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1⦄
          (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V), T ι →
            ∃ g : ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj
              L).val.obj (op Q),
              (Function.Bijective fun r : chartRing B S hS
                  (Z.genericStalkSpace B S hS hX hdec).1
                  (Z.genericStalkSpace B S hS hX hdec).2 Q ↦ r • g) ∧
                (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
                      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
                      t).eval (op Q) =
                  toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2
                    ((modulePullback B S hS
                      (Z.genericStalkMorphism B S hS hX hdec)).obj L) Q
                    ((((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
                          (Z.genericStalkSpace B S hS hX hdec).1
                          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map ι.op).hom
                        (chartMeromorphicPullbackHom B S hS
                          (Z.genericStalkMorphism B S hS hX hdec)
                          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
                          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V) c)) ⊗ₜ[chartRing
                      B S hS (Z.genericStalkSpace B S hS hX hdec).1
                      (Z.genericStalkSpace B S hS hX hdec).2 Q] g :
                      (meromorphicSectionModule B S hS
                        (Z.genericStalkSpace B S hS hX hdec).1
                        (Z.genericStalkSpace B S hS hX hdec).2
                        ((modulePullback B S hS
                          (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj (op Q)) := by
  set jm := Z.genericStalkMorphism B S hS hX hdec with hjm
  set hj := Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec with hhj
  set d := Z.genericStalkBaseChangeDiagram B S hS hX hdec V with hd
  -- the presentation over the base-changed chart itself
  have hEid : modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) (𝟙 d.U) =
      (modulePullbackChartFMap B S hS jm L).app d (e d.V (𝟙 d.V)) :=
    CategoryTheory.congr_fun
      (((modulePullback B S hS jm).obj L).val.presheaf.map_id (op d.U))
      ((modulePullbackChartFMap B S hS jm L).app d (e d.V (𝟙 d.V)))
  have hvalue : (pullbackMeromorphicSection B S hS jm L hj t).eval (op d.U) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 ((modulePullback B S hS jm).obj L) d.U
        ((chartMeromorphicPullbackHom B S hS jm hj d c) ⊗ₜ[chartRing B S hS
            (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 d.U]
          modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) (𝟙 d.U) :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS jm).obj L)).obj (op d.U)) := by
    refine Eq.trans (pullbackMeromorphicSection_eval_chartDiagram B S hS jm L hj t d
      (c ⊗ₜ[chartRing B S hS X hX d.V] e d.V (𝟙 d.V) :
        (meromorphicSectionModule B S hS X hX L).obj (op d.V)) hpres) ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
      ((modulePullback B S hS jm).obj L) d.U) ?_
    refine Eq.trans (chartPullbackMeromorphicSectionsSheaf_tmul B S hS jm L hj d c
      (e d.V (𝟙 d.V))) ?_
    exact congrArg (fun z : ((modulePullback B S hS jm).obj L).val.obj (op d.U) ↦
      ((chartMeromorphicPullbackHom B S hS jm hj d c) ⊗ₜ[chartRing B S hS
          (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 d.U] z :
        (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
          ((modulePullback B S hS jm).obj L)).obj (op d.U))) hEid.symm
  have hEcompat : ∀ (W₁ W₂ : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
      (k₁ : W₁ ⟶ d.U) (g : W₂ ⟶ W₁),
      (((modulePullback B S hS jm).obj L).val.map g.op).hom
          (modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) k₁) =
        modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) (g ≫ k₁) :=
    fun _ _ k₁ g ↦ modulePullbackChartSectionRestrict_map B S hS jm L d (e d.V (𝟙 d.V)) k₁ g
  have hXrestrict := eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    ((modulePullback B S hS jm).obj L) (pullbackMeromorphicSection B S hS jm L hj t) d.U
    (fun W₁ k₁ ↦ modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) k₁)
    hEcompat (chartMeromorphicPullbackHom B S hS jm hj d c) hvalue
  obtain ⟨T, hT, hTbij⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS jm L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) d e hecompat hebij
  refine ⟨T, hT, fun Q ι hι ↦ ⟨modulePullbackChartSectionRestrict B S hS jm L d
    (e d.V (𝟙 d.V)) (𝟙 Q ≫ ι), hTbij ι hι Q (𝟙 Q), ?_⟩⟩
  refine Eq.trans (hXrestrict Q ι) (congrArg (toMeromorphicSectionSheaf B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    ((modulePullback B S hS jm).obj L) Q) ?_)
  exact congrArg (fun z : ((modulePullback B S hS jm).obj L).val.obj (op Q) ↦
    ((((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
          (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map ι.op).hom
        (chartMeromorphicPullbackHom B S hS jm hj d c)) ⊗ₜ[chartRing B S hS
        (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q] z :
      (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS jm).obj L)).obj (op Q)))
    (congrArg (modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)))
      (Category.id_comp ι).symm)

include hX in
/-- **The inverse image of a generating section of `ℒ` is a free generator with coefficient `1`
over the charts of a covering sieve of the base-changed chart.** If `t` generates `ℒ` over the
étale chart `V` of `X`, then over the charts of a covering sieve of the base change of `V` to
`Spec(𝒪_{U, u})` the pullback of `t` is `1` times a free generator of the pullback of `ℒ`. -/
theorem PrimeDivisor.exists_sieve_eval_eq_one_tmul_genericStalkBaseChange
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X)
    (hgen : GeneratesOnChart B S hS hX L t V) :
    ∃ T : Sieve (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      T ∈ SmallEtale.topology B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkBaseChangeChart B S hS hX hdec V) ∧
        ∀ ⦃Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1⦄
          (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V), T ι →
            ∃ g : ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj
              L).val.obj (op Q),
              (Function.Bijective fun r : chartRing B S hS
                  (Z.genericStalkSpace B S hS hX hdec).1
                  (Z.genericStalkSpace B S hS hX hdec).2 Q ↦ r • g) ∧
                (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
                      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
                      t).eval (op Q) =
                  toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2
                    ((modulePullback B S hS
                      (Z.genericStalkMorphism B S hS hX hdec)).obj L) Q
                    ((1 : (meromorphicChartSheaf B S hS
                        (Z.genericStalkSpace B S hS hX hdec).1
                        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q)) ⊗ₜ[chartRing
                      B S hS (Z.genericStalkSpace B S hS hX hdec).1
                      (Z.genericStalkSpace B S hS hX hdec).2 Q] g :
                      (meromorphicSectionModule B S hS
                        (Z.genericStalkSpace B S hS hX hdec).1
                        (Z.genericStalkSpace B S hS hX hdec).2
                        ((modulePullback B S hS
                          (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj (op Q)) := by
  obtain ⟨e, hecompat, hebij, hpres⟩ := hgen
  obtain ⟨T, hT, hTpres⟩ := Z.exists_sieve_eval_eq_tmul_genericStalkBaseChange B S hS hX hdec
    L hL t V e hecompat hebij 1 hpres
  refine ⟨T, hT, fun Q ι hι ↦ ?_⟩
  obtain ⟨g, hgbij, hgpres⟩ := hTpres ι hι
  refine ⟨g, hgbij, hgpres.trans (congrArg (toMeromorphicSectionSheaf B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) Q) ?_)⟩
  refine congrArg (fun z : (meromorphicChartSheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q) ↦
    (z ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q] g :
      (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
          (op Q))) ?_
  exact (congrArg (((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
      ι.op).hom)
      (map_one (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
        (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V)))).trans
    (map_one (((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
        ι.op).hom))

/-! ### The chart ratio and the coefficient at `ξ`, compared over a common chart -/

/-- **The ratio of `t` against the generator of `ℒ` over the chart `V` of `X`, read on a chart
of `Spec(𝒪_{U, u})` over the base change of `V`.** This is `AlgebraicGeometry.Space.chartRatio`
pulled back along `j : Spec(𝒪_{U, u}) ⟶ X` through the square of
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkBaseChangeDiagram` and then restricted. -/
def PrimeDivisor.baseChangeChartRatio (L : Modules.{u, u} B S hS X hX)
    (t : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V) :
    (meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q) :=
  ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map ι.op).hom
    (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V)
      (chartRatio B S hS X hX L V e hecompat hebij t))

include hX in
/-- **The two readings of one meromorphic section agree up to a unit over a common chart.** Let
`ℒ` be free on `e` over an étale chart `V` of `X` and let `t` be a meromorphic section of `ℒ`.
Over the charts of a covering sieve of the base change of `V` to `Spec(𝒪_{U, u})` the
restriction of the coefficient `t / s_ξ` of Stacks 0EPR is a unit of the regular functions there
times the pullback of the ratio `t / e` of `t` against the generator over `V`. -/
theorem PrimeDivisor.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k) :
    ∃ T : Sieve (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      T ∈ SmallEtale.topology B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkBaseChangeChart B S hS hX hdec V) ∧
        ∀ ⦃Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1⦄
          (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V), T ι →
            ∃ v : (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2 Q)ˣ,
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                  (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
                  (ι ≫ chartToIdEtaleChart B S hS
                    (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom
                (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
              algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                  (Z.genericStalkSpace B S hS hX hdec).2 Q)
                ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                  (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q))
                (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                  (Z.genericStalkSpace B S hS hX hdec).2 Q) *
                Z.baseChangeChartRatio B S hS hX hdec L t V e hecompat hebij ι := by
  obtain ⟨T, hT, hTpres⟩ := Z.exists_sieve_eval_eq_tmul_genericStalkBaseChange B S hS hX hdec
    L hL t V e hecompat hebij (chartRatio B S hS X hX L V e hecompat hebij t)
    (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X hX L V e hecompat hebij t)
  refine ⟨T, hT, fun Q ι hι ↦ ?_⟩
  obtain ⟨g, hgbij, hgpres⟩ := hTpres ι hι
  exact Z.genericStalkCoefficient_eq_mul_of_eval_eq_smul B S hS hX hdec L hL t Q
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) g hgbij
    (Z.baseChangeChartRatio B S hS hX hdec L t V e hecompat hebij ι) hgpres

/-! ### The field `generating` of Stacks 0EPW at the canonical choices -/

attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

/-- The morphism of schemes under
`AlgebraicGeometry.Space.chartToIdEtaleChart`, read as a morphism to `Spec(𝒪_{U, u})`. -/
theorem PrimeDivisor.genericStalkChartMap_chartToIdEtaleChart
    (P : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1) :
    Z.genericStalkChartMap B S hS hX hdec P (chartToIdEtaleChart B S hS P) =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage P.obj.hom) :=
  rfl

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hX hInt hN in
/-- **The coefficient of Stacks 0EPR is the image of a unit of `𝒪_{U, u}` wherever the section
generates `ℒ` on a chart through `ξ`.** -/
theorem PrimeDivisor.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_generatesOnChart
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X)
    (hmem : Z.genericPoint B S hS X ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom))
    (hgen : GeneratesOnChart B S hS hX L t V) :
    ∃ w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)), IsUnit w ∧
      Z.genericStalkCoefficient B S hS hX hdec L hL t =
        algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) w := by
  obtain ⟨T, hT, hTpres⟩ :=
    Z.exists_sieve_eval_eq_one_tmul_genericStalkBaseChange B S hS hX hdec L hL t V hgen
  obtain ⟨p, hp⟩ := Z.exists_mem_range_genericStalkBaseChangeChart B S hS hX hdec V hmem
  obtain ⟨Q, ι, hι, hQaff, w₀, hw₀⟩ := SmallEtale.exists_affine_mem_range_of_mem_topology
    B S hS (Z.genericStalkSpace B S hS hX hdec).1 hT p
  obtain ⟨g, hgbij, hpresQ⟩ := hTpres ι hι
  obtain ⟨v, hv⟩ := Z.genericStalkCoefficient_eq_mul_of_eval_eq_smul B S hS hX hdec L hL t Q
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) g hgbij
    1 hpresQ
  refine Z.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_chart B S hS hX hdec L hL
    hInt hN t Q (ι ≫ chartToIdEtaleChart B S hS
      (Z.genericStalkBaseChangeChart B S hS hX hdec V)) hQaff w₀ ?_
    (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 Q) v.isUnit (hv.trans (mul_one _))
  have hcomp : Z.genericStalkChartMap B S hS hX hdec Q
        (ι ≫ chartToIdEtaleChart B S hS
          (Z.genericStalkBaseChangeChart B S hS hX hdec V)) =
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS
          (Z.genericStalkSpace B S hS hX hdec).1).map ι) ≫
        (BigFppfOver.toScheme B S hS).map (yoneda.preimage
          (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom) :=
    Functor.map_comp (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1 ⋙
      BigFppfOver.toScheme B S hS) ι _
  rw [hcomp]
  exact (congrArg ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
    (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom)) hw₀).trans hp

include hX hInt hN in
/-- **The field `generating` of the data of Stacks 0EPW holds at the canonical choices**, on a
decent, locally Noetherian, integral algebraic space — with no hypothesis: the `Prop`
`AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart` holds. -/
theorem canonicalRatioIsUnitOnGeneratingChart :
    CanonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN :=
  canonicalRatioIsUnitOnGeneratingChart_of_isUnit_genericStalkCoefficient B S hS hX hdec hInt hN
    fun L hL W V hmem hgen ↦
      W.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_generatesOnChart B S hS hX hdec
        hInt hN L hL (regularMeromorphicSection B S hS hX hInt hN L hL) V hmem hgen

end AlgebraicGeometry.Space

end

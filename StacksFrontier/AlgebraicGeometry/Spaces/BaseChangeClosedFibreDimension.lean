module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPointProduct

/-!
# The closed fibre of a base change of algebraic spaces, at a point closed in its fibre

Let `h : U' ⟶ U` be a morphism of algebraic spaces over `S`, let `k : W ⟶ U` be another, and let
`a` be a geometric point of the fibre product `W ×_U U'`. The first projection
`pr₁ : W ×_U U' ⟶ W` is the base change of `h` along `k`, and the question this file answers is
whether its closed fibre at `a` has the same Krull dimension as the closed fibre of `h` itself at
the image of `a` in `U'`:

`dim(𝒪_{W ×_U U', a} / 𝔪_{𝒪_{W, pr₁(a)}}·𝒪_{W ×_U U', a})
    = dim(𝒪_{U', pr₂(a)} / 𝔪_{𝒪_{U, h(pr₂(a))}}·𝒪_{U', pr₂(a)})`.

This is the fact the Step C identity of **Stacks 0DS9** is reduced to —
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`
takes it as the two hypotheses `hfst` and `hsnd`, one for each leg of the doubled base change.

## Closedness is carried, and is not removable

The displayed identity is FALSE without a closedness hypothesis on `a` in its fibre, and the
refutation lives in this repository: `AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_eq`
(**Stacks 02FY**, `local_ring_differences`) measures the discrepancy, which is the transcendence
degree lost when the image of a closed point fails to be closed. The docstring of
`AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_of_isPullback_of_isClosed` records an explicit
counterexample to the unconditional statement, and the docstring of the Step C identity records a
second one which is on the diagonal — so being on the diagonal does not help either.

What IS unconditionally invariant under base change is `topologicalKrullDimAt`
(`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback`, Stacks 02FY part (1)); the
`ringKrullDim` of a local ring is not. The route taken here passes to `topologicalKrullDimAt`,
moves across the base change, and returns to `ringKrullDim` at closed points by **Stacks 0A21** —
all of which is already packaged in
`AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_of_isPullback_of_isClosed`, and this file does not
re-derive it.

The closedness hypotheses are therefore conditions on CHART points: the identity of étale local
rings is read off a square of étale scheme charts, and it is the chart point that must be closed
in the chart fibre. They are stated here exactly as the scheme-level theorem wants them.

## Main results

* `AlgebraicGeometry.Space.ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed`: the
  identity above, for a given pair of chart squares whose underlying square of chart schemes is
  cartesian and whose chart points are closed in their chart fibres.
* `AlgebraicGeometry.Space.exists_pointed_chart_square_of_isPullback`: such a pair of chart
  squares exists at every geometric point, with affine target charts.
* `AlgebraicGeometry.Space.exists_chart_square_ringKrullDim_closedFibre_eq_of_isPullback`: the two
  put together — the usable form, in which the square is returned together with the implication
  from closedness of its chart points to the identity.

Everything is stated for an arbitrary cartesian square of presheaves `IsPullback π₁ π₂ k h`
rather than for the chosen fibre product `W ×_U U'`, so that it applies to a base change however
that base change was constructed.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W U U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_BaseChangeClosedFibreDimension :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The chosen pullback of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_BaseChangeClosedFibreDimension
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

-- `CategoryTheory.MorphismProperty.pullbackMap` is applied below to the representable étale
-- property of morphisms of presheaves, so that property has to be an instance of stability
-- under base change; it is the general relative property, at no statement of its own.
attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- For a commutative square `π₁ ≫ k = π₂ ≫ h` of presheaves and étale neighbourhoods `N` and `V`
of the two feet of a geometric point `a`, the chosen lifts of `a` to `N` and `V` have the same
image over the common target. -/
theorem map_point_comp_eq_of_comp_eq {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : W ⟶ U}
    {h : U' ⟶ U} {π₁ : Z ⟶ W} {π₂ : Z ⟶ U'} (hw : π₁ ≫ k = π₂ ≫ h)
    {a : GeometricPoint B S hS Z} (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
    (V : SmallEtaleNeighborhood (geometricPointMap π₂ a)) :
    yoneda.map N.point ≫ (N.chart.obj.hom ≫ k) = yoneda.map V.point ≫ (V.chart.obj.hom ≫ h) := by
  apply yonedaEquiv.injective
  change k.app (Opposite.op a.val.siteObject)
      (N.chart.obj.hom.app (Opposite.op a.val.siteObject) N.point) =
    h.app (Opposite.op a.val.siteObject)
      (V.chart.obj.hom.app (Opposite.op a.val.siteObject) V.point)
  calc k.app (Opposite.op a.val.siteObject)
        (N.chart.obj.hom.app (Opposite.op a.val.siteObject) N.point)
      = (π₁ ≫ k).app (Opposite.op a.val.siteObject) a.val.value :=
        congrArg _ N.point_comp
    _ = (π₂ ≫ h).app (Opposite.op a.val.siteObject) a.val.value :=
        congrArg (fun t => t.app (Opposite.op a.val.siteObject) a.val.value) hw
    _ = h.app (Opposite.op a.val.siteObject)
        (V.chart.obj.hom.app (Opposite.op a.val.siteObject) V.point) :=
        congrArg _ V.point_comp.symm

/-- **Cancelling a cartesian square of representables.** If `yoneda.obj p` is the fibre product
of `f` and `g` (with projections `pr` and `gh`), and `yoneda.obj m` is the fibre product of `f` and
`t = yoneda.map gk ≫ g` (with projections `p₂` and `gfst`), then there is a comparison
`gsnd : m ⟶ p` with `gsnd ≫ pr = p₂` making `m` the fibre product of `gh` and `gk`. -/
theorem exists_isPullback_of_yoneda_isPullback.{v, w} {C : Type w} [Category.{v} C]
    {T : Cᵒᵖ ⥤ Type v} {m n p q x : C} {f : yoneda.obj x ⟶ T} {g : yoneda.obj q ⟶ T}
    {t : yoneda.obj n ⟶ T} {gfst : m ⟶ n} {p₂ : m ⟶ x} {pr : p ⟶ x} {gh : p ⟶ q} {gk : n ⟶ q}
    (sqP : IsPullback (yoneda.map pr) (yoneda.map gh) f g) (hk : yoneda.map gk ≫ g = t)
    (sqM : IsPullback (yoneda.map p₂) (yoneda.map gfst) f t) :
    ∃ gsnd : m ⟶ p, gsnd ≫ pr = p₂ ∧ IsPullback gsnd gfst gh gk := by
  have hw : yoneda.map p₂ ≫ f = yoneda.map (gfst ≫ gk) ≫ g := by
    rw [yoneda.map_comp, Category.assoc, hk]
    exact sqM.w
  obtain ⟨gsnd, hmap⟩ : ∃ gsnd, yoneda.map gsnd = sqP.lift _ _ hw := ⟨_, yoneda.map_preimage _⟩
  have hpr : gsnd ≫ pr = p₂ := yoneda.map_injective (by rw [yoneda.map_comp, hmap, sqP.lift_fst])
  have hgh : gsnd ≫ gh = gfst ≫ gk :=
    yoneda.map_injective (by rw [yoneda.map_comp, hmap, sqP.lift_snd])
  refine ⟨gsnd, hpr, IsPullback.of_map yoneda hgh (IsPullback.of_right ?_
    (by rw [← yoneda.map_comp, ← yoneda.map_comp, hgh]) sqP)⟩
  rw [← yoneda.map_comp, hpr, hk]
  exact sqM

/-- If `p ≫ m` is the chosen lift of a geometric point to a neighbourhood `N`, then `p` is sent
to the geometric point's value by the chart of `N` precomposed with `yoneda.map m`. -/
private theorem app_yoneda_map_comp_eq_value {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {x : GeometricPoint B S hS F} (N : SmallEtaleNeighborhood x) {T : BigFppfOver B S hS}
    (m : T ⟶ N.chart.obj.left) {p : x.val.siteObject ⟶ T} (hp : p ≫ m = N.point) :
    (yoneda.map m ≫ N.chart.obj.hom).app (Opposite.op x.val.siteObject) p = x.val.value := by
  change N.chart.obj.hom.app _ (p ≫ m) = _
  rw [hp]
  exact N.point_comp

/-- **The chart of a fibre product built from charts of its two legs, with the geometric point
lifted.** For `k : W ⟶ U` and `h : U' ⟶ U` morphisms of algebraic spaces over `S`, a geometric
point `a` of `W ×_U U'` and PRESCRIBED small étale neighbourhoods `N` of its first foot and `V` of
its second, the representable fibre product `N ×_U V` is a small étale neighbourhood of `a`, and
its square over the two chart maps is cartesian.

Étaleness is the composite of two base changes of the chart maps, which is
`CategoryTheory.MorphismProperty.pullbackMap` for the representable étale property — the same
argument that makes a fibre product of algebraic spaces an algebraic space in
`AlgebraicGeometry.Space.isAlgebraicSpace_pullback`. What that proof does not provide, and what is
the whole point here, is the LIFT of `a`: it comes from the two chosen lifts of `N` and `V`
through `CategoryTheory.Functor.relativelyRepresentable.lift'`, the two agreeing over `U` because
both feet of a geometric point of a fibre product have the same image there. -/
private theorem exists_pointed_chart_pullback
    (hU : IsAlgebraicSpace B S hS U) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : W ⟶ U)
    (h : U' ⟶ U) (π₁ : Z ⟶ W) (π₂ : Z ⟶ U') (hsq : IsPullback π₁ π₂ k h)
    (a : GeometricPoint B S hS Z)
    (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
    (V : SmallEtaleNeighborhood (geometricPointMap π₂ a)) :
    ∃ (M : SmallEtaleNeighborhood a) (p₁ : M.chart.obj.left ⟶ N.chart.obj.left)
      (p₂ : M.chart.obj.left ⟶ V.chart.obj.left),
      M.chart.obj.hom ≫ π₁ = yoneda.map p₁ ≫ N.chart.obj.hom ∧
        M.point ≫ p₁ = N.point ∧ M.point ≫ p₂ = V.point ∧
          IsPullback (yoneda.map p₂) (yoneda.map p₁)
            (V.chart.obj.hom ≫ h) (N.chart.obj.hom ≫ k) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable (N.chart.obj.hom ≫ k) :=
    Functor.relativelyRepresentable.of_diag hU.diagonal_representable _
  have hcompat := map_point_comp_eq_of_comp_eq B S hS hsq.w N V
  set χ := (hrep.isPullback (V.chart.obj.hom ≫ h)).isoPullback.hom ≫
    pullback.map (N.chart.obj.hom ≫ k) (V.chart.obj.hom ≫ h) k h
      N.chart.obj.hom V.chart.obj.hom (𝟙 U) (by simp) (by simp) ≫
    hsq.isoPullback.inv with hχ
  have hχfst : χ ≫ π₁ =
      yoneda.map (hrep.fst' (V.chart.obj.hom ≫ h)) ≫ N.chart.obj.hom := by
    rw [hχ, Category.assoc, Category.assoc, hsq.isoPullback_inv_fst, pullback.lift_fst,
      ← Category.assoc, IsPullback.isoPullback_hom_fst, hrep.map_fst']
  have hχsnd : χ ≫ π₂ =
      yoneda.map (hrep.snd (V.chart.obj.hom ≫ h)) ≫ V.chart.obj.hom := by
    rw [hχ, Category.assoc, Category.assoc, hsq.isoPullback_inv_snd, pullback.lift_snd,
      ← Category.assoc, IsPullback.isoPullback_hom_snd]
  have hχetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf χ := by
    rw [hχ]
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (MorphismProperty.RespectsIso.postcomp _ _ _
        (MorphismProperty.pullbackMap N.chart.property V.chart.property rfl rfl))
  set Mpoint := hrep.lift' N.point V.point hcompat
  have hMp₁ : Mpoint ≫ hrep.fst' (V.chart.obj.hom ≫ h) = N.point := hrep.lift'_fst _ _ _
  have hMp₂ : Mpoint ≫ hrep.snd (V.chart.obj.hom ≫ h) = V.point := hrep.lift'_snd _ _ _
  have hMpc : χ.app (Opposite.op a.val.siteObject) Mpoint = a.val.value := by
    refine yonedaEquiv.symm.injective (hsq.hom_ext ?_ ?_) <;>
      rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right] <;>
      refine congrArg yonedaEquiv.symm ?_
    · change (χ ≫ π₁).app (Opposite.op a.val.siteObject) Mpoint = _
      rw [hχfst]
      exact app_yoneda_map_comp_eq_value B S hS N _ hMp₁
    · change (χ ≫ π₂).app (Opposite.op a.val.siteObject) Mpoint = _
      rw [hχsnd]
      exact app_yoneda_map_comp_eq_value B S hS V _ hMp₂
  exact ⟨⟨⟨CostructuredArrow.mk χ, hχetale⟩, Mpoint, hMpc⟩,
    hrep.fst' (V.chart.obj.hom ≫ h), hrep.snd (V.chart.obj.hom ≫ h), hχfst, hMp₁, hMp₂,
    (hrep.isPullback' (V.chart.obj.hom ≫ h)).flip⟩

/-- **A chart of `W` over a prescribed chart of `U`, with the cartesian square it sits in.** This
is `AlgebraicGeometry.Space.exists_pointed_chart_over` with the fibre-product square it is built
from retained, rather than only the morphisms: the chart is `V ×_U Q`, so its square over the
chart map of `V` and the chart map of `Q` is cartesian, and that is what a consumer comparing it
with another fibre product needs. -/
private theorem exists_pointed_chart_over_isPullback (k : W ⟶ U)
    (w : GeometricPoint B S hS W) (V : SmallEtaleNeighborhood w)
    (Q : SmallEtaleNeighborhood (geometricPointMap k w)) :
    ∃ (N : SmallEtaleNeighborhood w) (qq : N.chart.obj.left ⟶ Q.chart.obj.left)
      (pr : N.chart.obj.left ⟶ V.chart.obj.left),
      N.chart.obj.hom ≫ k = yoneda.map qq ≫ Q.chart.obj.hom ∧
        N.point ≫ qq = Q.point ∧ N.point ≫ pr = V.point ∧
          IsPullback (yoneda.map pr) (yoneda.map qq)
            (V.chart.obj.hom ≫ k) Q.chart.obj.hom := by
  have hetsn : Etale ((BigFppfOver.toScheme B S hS).map
      (Q.chart.property.rep.snd (V.chart.obj.hom ≫ k))) :=
    Q.chart.property.property_snd _
  have hcompat : yoneda.map Q.point ≫ Q.chart.obj.hom =
      yoneda.map V.point ≫ (V.chart.obj.hom ≫ k) := by
    apply yonedaEquiv.injective
    change Q.chart.obj.hom.app (Opposite.op w.val.siteObject) Q.point =
      k.app (Opposite.op w.val.siteObject)
        (V.chart.obj.hom.app (Opposite.op w.val.siteObject) V.point)
    rw [V.point_comp]
    exact point_comp_geometricPointMap B S hS k w Q
  set Npoint := Q.chart.property.rep.lift (yoneda.map Q.point) V.point hcompat
  have hsnd : Npoint ≫ Q.chart.property.rep.snd (V.chart.obj.hom ≫ k) = V.point :=
    Q.chart.property.rep.lift_snd _ _ hcompat
  have hfst : yoneda.map Npoint ≫ Q.chart.property.rep.fst (V.chart.obj.hom ≫ k) =
      yoneda.map Q.point :=
    Q.chart.property.rep.lift_fst (yoneda.map Q.point) V.point hcompat
  have hNpc : (yoneda.map (Q.chart.property.rep.snd (V.chart.obj.hom ≫ k)) ≫
      V.chart.obj.hom).app (Opposite.op w.val.siteObject) Npoint = w.val.value :=
    app_yoneda_map_comp_eq_value B S hS V _ hsnd
  refine ⟨⟨⟨CostructuredArrow.mk (yoneda.map
      (Q.chart.property.rep.snd (V.chart.obj.hom ≫ k)) ≫ V.chart.obj.hom),
      AlgebraicGeometry.Space.etale_comp_of_scheme B S hS _ V.chart.obj.hom hetsn
        V.chart.property⟩, Npoint, hNpc⟩,
    Q.chart.property.rep.fst' (V.chart.obj.hom ≫ k),
    Q.chart.property.rep.snd (V.chart.obj.hom ≫ k), ?_, ?_, hsnd,
    (Q.chart.property.rep.isPullback' (V.chart.obj.hom ≫ k)).flip⟩
  · rw [Q.chart.property.rep.map_fst' (V.chart.obj.hom ≫ k),
      Q.chart.property.rep.w (V.chart.obj.hom ≫ k), ← Category.assoc]
    rfl
  · refine yoneda.map_injective ?_
    change yoneda.map Npoint ≫
      yoneda.map (Q.chart.property.rep.fst' (V.chart.obj.hom ≫ k)) = yoneda.map Q.point
    rw [Q.chart.property.rep.map_fst' (V.chart.obj.hom ≫ k)]
    exact hfst

/-- **A pointed square of étale charts for a base change, whose square of chart schemes is
cartesian.** For `k : W ⟶ U` and `h : U' ⟶ U` morphisms of algebraic spaces over `S` and a
geometric point `a` of `W ×_U U'`, there are chart squares

* `(M, N, gfst)` of the base change `pr₁ : W ×_U U' ⟶ W` at `a`, with `N` AFFINE, and
* `(P, Q, gh)` of `h` at `pr₂(a)`, with `Q` AFFINE,

together with `gsnd : M ⟶ P` over `pr₂` carrying the chosen lift of `a` to the chosen lift of
`pr₂(a)`, and `gk : N ⟶ Q`, such that the square of CHART SCHEMES

```
M ---gsnd---> P
|             |
gfst          gh
↓             ↓
N ---gk ----> Q
```

is cartesian. This is the configuration that
`AlgebraicGeometry.Space.ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed`
consumes, and the cartesian square is what lets the scheme-level comparison of Stacks 02FY be
applied to the two chart fibres.

The charts are chosen in a specific order, and the order is what makes the square cartesian. One
affine chart `Q` of `U` is fixed at the common foot of the two projections of `a` — the two feet
agree by `AlgebraicGeometry.Space.geometricPointMap_pullback_feet_eq`, which is what lets a single
chart serve both legs. Then `N` is an affine chart of `W` over `Q`
(`AlgebraicGeometry.Space.exists_pointed_affine_chart_over`), `P` is the chart `Q ×_U V` of `U'`
over `Q` for some chart `V` of `U'`, and `M` is the chart `N ×_U V` of `W ×_U U'`. With these
choices `M = N ×_Q P`, because `N ×_U V = N ×_Q (Q ×_U V)`: the square is obtained by cancelling
the cartesian square of `P` out of the cartesian square of `M`, which is
`CategoryTheory.IsPullback.of_right`. Taking instead the obvious comparison object `N ×_U P` would
NOT give a cartesian square — it is larger than `N ×_Q P` by the diagonal of `Q ⟶ U` — so the
choice of `P` as a fibre product over `U` with `Q` is not a convenience. -/
theorem exists_pointed_chart_square_of_isPullback
    (hW : IsAlgebraicSpace B S hS W) (hU : IsAlgebraicSpace B S hS U)
    (hU' : IsAlgebraicSpace B S hS U') {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : W ⟶ U)
    (h : U' ⟶ U) (π₁ : Z ⟶ W) (π₂ : Z ⟶ U') (hsq : IsPullback π₁ π₂ k h)
    (hZ : IsAlgebraicSpace B S hS Z) (a : GeometricPoint B S hS Z) :
    ∃ (M : SmallEtaleNeighborhood a)
      (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
      (P : SmallEtaleNeighborhood (geometricPointMap π₂ a))
      (Q : SmallEtaleNeighborhood (geometricPointMap h (geometricPointMap π₂ a)))
      (gfst : M.chart.obj.left ⟶ N.chart.obj.left)
      (gsnd : M.chart.obj.left ⟶ P.chart.obj.left)
      (gh : P.chart.obj.left ⟶ Q.chart.obj.left)
      (gk : N.chart.obj.left ⟶ Q.chart.obj.left),
      IsAffine (chartScheme N.chart) ∧ IsAffine (chartScheme Q.chart) ∧
        M.chart.obj.hom ≫ π₁ = yoneda.map gfst ≫ N.chart.obj.hom ∧
          P.chart.obj.hom ≫ h = yoneda.map gh ≫ Q.chart.obj.hom ∧
            M.point ≫ gfst = N.point ∧ P.point ≫ gh = Q.point ∧
              M.point ≫ gsnd = P.point ∧
                IsPullback ((BigFppfOver.toScheme B S hS).map gsnd)
                  ((BigFppfOver.toScheme B S hS).map gfst)
                  ((BigFppfOver.toScheme B S hS).map gh)
                  ((BigFppfOver.toScheme B S hS).map gk) := by
  have hfeet : (π₁ ≫ k).app (Opposite.op a.val.siteObject) a.val.value =
      (π₂ ≫ h).app (Opposite.op a.val.siteObject) a.val.value :=
    congrArg (fun t => t.app (Opposite.op a.val.siteObject) a.val.value) hsq.w
  -- an affine chart `Q` of `U` at the common foot, and some chart `V` of `U'` at the second foot
  obtain ⟨V, Q, -, -, -, hQaff⟩ :=
    exists_compatible_affine_chart_square B S hS hU' hU h (geometricPointMap π₂ a)
  -- some chart of `W` at the first foot, to refine
  obtain ⟨-, Vw, -, -, -⟩ := exists_compatible_chart_square B S hS hZ hW π₁ a
  -- `Q` read as a neighbourhood of the first foot's image, the two images being the same point
  have hQpt : Q.chart.obj.hom.app
      (Opposite.op (geometricPointMap k (geometricPointMap π₁ a)).val.siteObject) Q.point =
      (geometricPointMap k (geometricPointMap π₁ a)).val.value := by
    change Q.chart.obj.hom.app (Opposite.op a.val.siteObject) Q.point =
      (π₁ ≫ k).app (Opposite.op a.val.siteObject) a.val.value
    rw [hfeet]
    exact point_comp_geometricPointMap B S hS h (geometricPointMap π₂ a) Q
  -- an affine chart `N` of `W` over `Q`
  obtain ⟨N, -, gk, hNaff, hkcomm₀, -, hkpt₀⟩ :=
    exists_pointed_affine_chart_over B S hS hW k (geometricPointMap π₁ a) Vw
      ⟨Q.chart, Q.point, hQpt⟩
  have hkcomm : yoneda.map gk ≫ Q.chart.obj.hom = N.chart.obj.hom ≫ k := hkcomm₀
  -- the chart `P = Q ×_U V` of `U'` over `Q`
  obtain ⟨P, gh, pr, hghcomm, hghpt, hprpt, sqP⟩ :=
    exists_pointed_chart_over_isPullback B S hS h (geometricPointMap π₂ a) V Q
  -- the chart `M = N ×_U V` of `Z = W ×_U U'`
  obtain ⟨M, gfst, p₂, hcomm₁, hMp₁, hMp₂, sqM⟩ :=
    exists_pointed_chart_pullback B S hS hU k h π₁ π₂ hsq a N V
  -- the comparison `M ⟶ P`, by cancelling the cartesian square of `P = Q ×_U V`
  obtain ⟨gsnd, hgsndPr, hsqSite⟩ := exists_isPullback_of_yoneda_isPullback sqP hkcomm sqM
  -- the chosen lift of `a` is carried to the chosen lift of the second foot: the two composites
  -- with the projections of `P` agree, and `P` is a fibre product
  have hgsndPr' : (M.point ≫ gsnd) ≫ pr = P.point ≫ pr := by
    rw [Category.assoc, hgsndPr, hMp₂, hprpt]
  have hgsndGh' : (M.point ≫ gsnd) ≫ gh = P.point ≫ gh := by
    rw [Category.assoc, hsqSite.w, ← Category.assoc, hMp₁, hghpt]
    exact hkpt₀
  have hgsndPoint : M.point ≫ gsnd = P.point :=
    yoneda.map_injective (sqP.hom_ext
      (((yoneda.map_comp _ _).symm.trans
        (congrArg (fun t => yoneda.map t) hgsndPr')).trans (yoneda.map_comp _ _))
      (((yoneda.map_comp _ _).symm.trans
        (congrArg (fun t => yoneda.map t) hgsndGh')).trans (yoneda.map_comp _ _)))
  exact ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hghcomm, hMp₁, hghpt,
    hgsndPoint, hsqSite.map (BigFppfOver.toScheme B S hS)⟩

/-- **The closed fibre of a base change has the dimension of the closed fibre of the original
morphism, at a point closed in its fibre.** For `h : U' ⟶ U` and `k : W ⟶ U` morphisms of
algebraic spaces over `S` and a geometric point `a` of `W ×_U U'`,

`dim(𝒪_{W ×_U U', a} / 𝔪_{𝒪_{W, pr₁(a)}}) = dim(𝒪_{U', pr₂(a)} / 𝔪_{𝒪_{U, h(pr₂(a))}})`,

`pr₁ : W ×_U U' ⟶ W` being the base change of `h` along `k`.

THE TWO CLOSEDNESS HYPOTHESES `hcl₁` AND `hcl₂` ARE NOT REMOVABLE; see the module documentation
of `StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean` for the
counterexamples, and `AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_of_isPullback_of_isClosed`
for the scheme-level statement with the same hypotheses, which is what this reduces to. They are
conditions on the chart points: the left-hand side is computed in the chart square
`(M, N, gfst)` of `pr₁` and the right-hand side in the chart square `(P, Q, gh)` of `h`, and what
must be closed is the chart point of `M` in the fibre of `gfst` and its image under `gsnd` in the
fibre of `gh`.

The two chart squares are related by the hypothesis `hsq` that the square of CHART SCHEMES is
cartesian — the chart-level incarnation of `W ×_U U'` being the fibre product — together with
`hmp`, which says that the chosen lift of `a` is carried to the chosen lift of `pr₂(a)`. A square
with these properties exists at every geometric point: see
`AlgebraicGeometry.Space.exists_pointed_chart_square_of_isPullback`.

Both chart squares must have affine target chart, which is what the bridge
`AlgebraicGeometry.Space.ringKrullDim_closedFibreEtaleLocalRing_eq_fiberStalk` between the étale
local ring and the local ring of a scheme-theoretic fibre requires. -/
theorem ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed
    (hW : IsAlgebraicSpace B S hS W) (hU : IsAlgebraicSpace B S hS U)
    (hU' : IsAlgebraicSpace B S hS U') {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : U' ⟶ U)
    (π₁ : Z ⟶ W) (π₂ : Z ⟶ U') (hZ : IsAlgebraicSpace B S hS Z)
    (hh : IsLocallyOfFiniteType B S hS h)
    (a : GeometricPoint B S hS Z)
    (M : SmallEtaleNeighborhood a)
    (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
    (gfst : M.chart.obj.left ⟶ N.chart.obj.left)
    (hcomm₁ : M.chart.obj.hom ≫ π₁ = yoneda.map gfst ≫ N.chart.obj.hom)
    (hpoint₁ : M.point ≫ gfst = N.point) (hNaff : IsAffine (chartScheme N.chart))
    (P : SmallEtaleNeighborhood (geometricPointMap π₂ a))
    (Q : SmallEtaleNeighborhood (geometricPointMap h (geometricPointMap π₂ a)))
    (gh : P.chart.obj.left ⟶ Q.chart.obj.left)
    (hcomm₂ : P.chart.obj.hom ≫ h = yoneda.map gh ≫ Q.chart.obj.hom)
    (hpoint₂ : P.point ≫ gh = Q.point) (hQaff : IsAffine (chartScheme Q.chart))
    (gsnd : M.chart.obj.left ⟶ P.chart.obj.left)
    (gk : N.chart.obj.left ⟶ Q.chart.obj.left)
    (hsq : IsPullback ((BigFppfOver.toScheme B S hS).map gsnd)
      ((BigFppfOver.toScheme B S hS).map gfst) ((BigFppfOver.toScheme B S hS).map gh)
      ((BigFppfOver.toScheme B S hS).map gk))
    (hmp : M.point ≫ gsnd = P.point)
    (hcl₁ : IsClosed ({((BigFppfOver.toScheme B S hS).map gfst).asFiber
                         ((chartGeometricPoint M).hom
                           (IsLocalRing.closedPoint
                             (chartGeometricPoint M).residueField))} : Set _))
    (hcl₂ : IsClosed ({((BigFppfOver.toScheme B S hS).map gh).asFiber
                         (((BigFppfOver.toScheme B S hS).map gsnd) ((chartGeometricPoint M).hom
                           (IsLocalRing.closedPoint
                             (chartGeometricPoint M).residueField)))} : Set _)) :
    ringKrullDim (closedFibreEtaleLocalRing B S hS hZ π₁ a) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS hU' h (geometricPointMap π₂ a)) := by
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map gh) :=
    hh _ _ P.chart.obj.hom Q.chart.obj.hom gh P.chart.property Q.chart.property hcomm₂.symm
  have hps : ((BigFppfOver.toScheme B S hS).map gsnd)
      ((chartGeometricPoint M).hom
        (IsLocalRing.closedPoint (chartGeometricPoint M).residueField)) =
      (chartGeometricPoint P).hom
        (IsLocalRing.closedPoint (chartGeometricPoint P).residueField) :=
    congrArg (fun t => ((BigFppfOver.toScheme B S hS).map t)
      (show (BigFppfOver.toScheme B S hS).obj a.val.siteObject from
        IsLocalRing.closedPoint a.val.carrier)) hmp
  rw [ringKrullDim_closedFibreEtaleLocalRing_eq_fiberStalk B S hS hZ hW π₁ a
      M N gfst hcomm₁ hpoint₁ hNaff _ rfl _ rfl,
    ringKrullDim_closedFibreEtaleLocalRing_eq_fiberStalk B S hS hU' hU h
      (geometricPointMap π₂ a) P Q gh hcomm₂ hpoint₂ hQaff _ rfl _ rfl,
    ← hps]
  exact ringKrullDim_stalk_fiber_eq_of_isPullback_of_isClosed hsq _ hcl₁ hcl₂

/-- **The closed fibre of a base change, in usable form: a chart square computing it always
exists, and at a point closed in its fibre it has the dimension of the closed fibre of the
original morphism.** For `h : U' ⟶ U` and `k : W ⟶ U` morphisms of algebraic spaces over `S`
with `h` locally of finite type, and a geometric point `a` of `W ×_U U'`, there is a pair of
pointed chart squares — one for the base change `pr₁ : W ×_U U' ⟶ W` at `a`, one for `h` at
`pr₂(a)` — with affine target charts and with cartesian square of chart schemes, such that
CLOSEDNESS OF THE CHART POINT IN THE TWO CHART FIBRES IMPLIES

`dim(𝒪_{W ×_U U', a} / 𝔪_{𝒪_{W, pr₁(a)}}) = dim(𝒪_{U', pr₂(a)} / 𝔪_{𝒪_{U, h(pr₂(a))}})`.

This is `AlgebraicGeometry.Space.exists_pointed_chart_square_of_isPullback` and
`AlgebraicGeometry.Space.ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed` put
together, and it is the form in which the two hypotheses `hfst` and `hsnd` of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq` are
to be discharged: each leg of the doubled base change there is a base change of `h`, so each
hypothesis is one instance of the conclusion below, and what a caller must supply is the
closedness — which is exactly the hypothesis the whole of **Stacks 0DS9** turns on, and which is
NOT removable.

The closedness is stated at the charts, not at `a`, because the dimension of the closed fibre of
a map of étale local rings is read off a square of étale scheme charts and there is no other place
for it to live. The square is returned rather than discarded so that a caller can establish the
closedness for the charts it is actually given. -/
theorem exists_chart_square_ringKrullDim_closedFibre_eq_of_isPullback
    (hW : IsAlgebraicSpace B S hS W) (hU : IsAlgebraicSpace B S hS U)
    (hU' : IsAlgebraicSpace B S hS U') {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : W ⟶ U)
    (h : U' ⟶ U) (π₁ : Z ⟶ W) (π₂ : Z ⟶ U') (hsq₀ : IsPullback π₁ π₂ k h)
    (hZ : IsAlgebraicSpace B S hS Z) (hh : IsLocallyOfFiniteType B S hS h)
    (a : GeometricPoint B S hS Z) :
    ∃ (M : SmallEtaleNeighborhood a)
      (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
      (P : SmallEtaleNeighborhood (geometricPointMap π₂ a))
      (Q : SmallEtaleNeighborhood (geometricPointMap h (geometricPointMap π₂ a)))
      (gfst : M.chart.obj.left ⟶ N.chart.obj.left)
      (gsnd : M.chart.obj.left ⟶ P.chart.obj.left)
      (gh : P.chart.obj.left ⟶ Q.chart.obj.left)
      (gk : N.chart.obj.left ⟶ Q.chart.obj.left),
      IsAffine (chartScheme N.chart) ∧ IsAffine (chartScheme Q.chart) ∧
        M.chart.obj.hom ≫ π₁ = yoneda.map gfst ≫ N.chart.obj.hom ∧
          P.chart.obj.hom ≫ h = yoneda.map gh ≫ Q.chart.obj.hom ∧
            M.point ≫ gfst = N.point ∧ P.point ≫ gh = Q.point ∧
              M.point ≫ gsnd = P.point ∧
                IsPullback ((BigFppfOver.toScheme B S hS).map gsnd)
                    ((BigFppfOver.toScheme B S hS).map gfst)
                    ((BigFppfOver.toScheme B S hS).map gh)
                    ((BigFppfOver.toScheme B S hS).map gk) ∧
                  (IsClosed ({((BigFppfOver.toScheme B S hS).map gfst).asFiber
                                ((chartGeometricPoint M).hom (IsLocalRing.closedPoint
                                  (chartGeometricPoint M).residueField))} : Set _) →
                    IsClosed ({((BigFppfOver.toScheme B S hS).map gh).asFiber
                                 (((BigFppfOver.toScheme B S hS).map gsnd)
                                   ((chartGeometricPoint M).hom (IsLocalRing.closedPoint
                                     (chartGeometricPoint M).residueField)))} : Set _) →
                      ringKrullDim (closedFibreEtaleLocalRing B S hS hZ π₁ a) =
                        ringKrullDim (closedFibreEtaleLocalRing B S hS hU' h
                          (geometricPointMap π₂ a))) := by
  obtain ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hcomm₂, hpoint₁, hpoint₂,
    hmp, hsq⟩ :=
    exists_pointed_chart_square_of_isPullback B S hS hW hU hU' k h π₁ π₂ hsq₀ hZ a
  exact ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hcomm₂, hpoint₁, hpoint₂, hmp,
    hsq, fun hcl₁ hcl₂ => ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed B S hS
      hW hU hU' h π₁ π₂ hZ hh a M N gfst hcomm₁ hpoint₁ hNaff P Q gh hcomm₂ hpoint₂ hQaff
      gsnd gk hsq hmp hcl₁ hcl₂⟩

end AlgebraicGeometry.Space

end

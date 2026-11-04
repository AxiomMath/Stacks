module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs

/-!
# Chart base change along a representable morphism is almost cocontinuous

Let `f : Z ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`. Base change of étale scheme charts along `f` is the functor
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4):

`X_étale ⥤ Z_étale`, `U ↦ U ×_X Z`.

This file proves the **space-level analogue of [Stacks, Tag 04DX], part (7)**: when every chart
base change `U ×_X Z ⟶ U` — a morphism of *schemes*, by representability — is integral and
universally injective, that functor is almost cocontinuous in the sense of [Stacks, Tag 04B7].
In particular this holds for a closed immersion of algebraic spaces.

## The shape of the argument

The argument is the one of [Stacks, Tag 04DV] run on the small étale site of an algebraic space
instead of that of a scheme. Fix an étale chart `U` of `X` with underlying scheme `U'`, write
`j : W' ⟶ U'` for the base-change projection of schemes, and let `S` be a covering sieve of
`U ×_X Z` for the small étale topology of `Z`.

A covering sieve of the small étale site of an algebraic space is exactly one whose arrows are
jointly surjective on the points of the underlying scheme of the chart
(`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`), so the arrows of `S`
cover `W'`. Each arrow `a : A ⟶ U ×_X Z` of `S` has étale underlying morphism of schemes, so
property (C) of [Stacks, Tag 04DW] for `j` supplies a scheme `V` étale over `U'` together with a
surjection `W' ×_{U'} V ⟶ A'` over `W'`. Those `V` need not be small enough to be objects of the
size-bounded site, so each is replaced by its affine opens: an affine scheme étale over `U'` is
quasi-compact and locally of finite type over `U'`, hence no larger than `U'` by
[Stacks, Tag 04T7], and therefore is an object of `B`. Each such affine, mapped to `U'`, becomes
an étale chart of `X` over `U`.

The image of `j` is closed, since an integral morphism is universally closed; adjoining to that
family the open complement `U' ∖ j(W')`, again an étale chart of `X` over `U`, produces a family
of charts over `U` that is jointly surjective on the points of `U'`, hence a covering sieve `T`.
Each member of `T` satisfies one of the two alternatives of almost cocontinuity: the base change
of the open complement has empty underlying scheme, hence is sheaf theoretically empty, while the
base change of an affine chart coming from `A` factors through `A` and so lies in `S`.

## Main definitions

* `AlgebraicGeometry.Space.chartOfEtaleSchemeHom` and
  `AlgebraicGeometry.Space.chartOfEtaleSchemeHomMap`: an étale morphism of schemes into the scheme
  underlying an étale chart of `F`, whose source is an object of `B`, read as an étale chart of
  `F` over the given one. This is the étale analogue of
  `AlgebraicGeometry.Space.openChart`.

## Main results

* `AlgebraicGeometry.Space.exists_geometricFiber_chartOfEtaleSchemeHom` and
  `AlgebraicGeometry.Space.exists_chartOfEtaleSchemeHom_hom`: lifts of a geometric point and
  morphisms of charts out of `chartOfEtaleSchemeHom` are read off from the underlying schemes.
* `AlgebraicGeometry.Space.smallBaseChange_isAlmostCocontinuous`: the space-level analogue of
  [Stacks, Tag 04DV] — chart base change is almost cocontinuous as soon as every chart base
  change of schemes has property (C) and is a closed map.
* `smallBaseChange_isAlmostCocontinuous_of_isIntegralHom_of_universallyInjective`, in the same
  namespace: the space-level analogue of **[Stacks, Tag 04DX], part (7)**.
* `AlgebraicGeometry.Space.smallBaseChange_isAlmostCocontinuous_of_isClosedImmersion`: the case of
  a closed immersion of algebraic spaces, which is the case the source singles out.

## Implementation notes

The hypotheses of the general statement are taken **chartwise**, that is, for the base-change
projections `hf.snd U.1.hom` indexed by the étale charts `U` of `X`, rather than as a property of
`f` itself. That is exactly what the proof consumes, and for a morphism of algebraic spaces whose
defining property is tested on represented base changes — as `IsIntegralHom`,
`UniversallyInjective` and `IsClosedImmersion` all are — the chartwise form is an immediate
consequence, which is what the two corollaries record.

Property (C) is needed only for the chart base changes themselves, not for all étale base changes
of `f`: the scheme-level [Stacks, Tag 04DV] quantifies over every étale `V ⟶ Y` because its
sites' objects *are* those `V`, and here the objects are the charts.

Closedness of the image of a chart base change is deduced from integrality through
`AlgebraicGeometry.Scheme.Hom.isClosedMap`, exactly as at the scheme level; and property (C) from
integrality together with universal injectivity through [Stacks, Tag 04DW], which needs the
chart base change to be a homeomorphism onto a closed subset of the chart.

The index type of the refining family lies in `Type (u + 1)`, because it is indexed by the arrows
of the given covering sieve of a site whose objects lie in `Type (u + 1)`. That costs nothing:
`CategoryTheory.Sieve.ofArrows` takes an index type in an arbitrary universe, and the covering
criterion `AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range` is stated for an
arbitrary sieve.

## References

* [Stacks Project, Tag 04DX](https://stacks.math.columbia.edu/tag/04DX)
* [Stacks Project, Tag 04DV](https://stacks.math.columbia.edu/tag/04DV)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04B7](https://stacks.math.columbia.edu/tag/04B7)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étale charts from étale morphisms of schemes -/

section ChartOfEtale

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS F)
    {T : Scheme.{u}} (hT : B.Contains T) (m : T ⟶ chartScheme U) (hm : Etale m)

/-- An étale morphism of schemes `m : T ⟶ U'` into the scheme `U'` underlying an étale chart `U`
of `F`, with `T` an object of the size-bounded site, read as an étale chart of `F`: the composite
of `m` with the chart `U` is representable and étale by part (1) of Stacks 03EC.

This is the étale analogue of `AlgebraicGeometry.Space.openChart`, which is the case of an open
immersion. -/
def chartOfEtaleSchemeHom : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk
      (yoneda.map (BigFppfOver.siteMapOver B S hS
        ((SmallEtale.toOver B S hS F).obj U) hT m) ≫ U.1.hom),
    etale_comp_of_scheme B S hS _ U.1.hom hm U.property⟩

/-- The morphism of étale charts from `AlgebraicGeometry.Space.chartOfEtaleSchemeHom` to the
ambient chart. -/
def chartOfEtaleSchemeHomMap : chartOfEtaleSchemeHom B S hS U hT m hm ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (BigFppfOver.siteMapOver B S hS ((SmallEtale.toOver B S hS F).obj U) hT m) rfl)

/-- The morphism of schemes underlying
`AlgebraicGeometry.Space.chartOfEtaleSchemeHomMap` is the given one. -/
theorem toScheme_map_toOver_map_chartOfEtaleSchemeHomMap :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
      (chartOfEtaleSchemeHomMap B S hS U hT m hm)) = m := rfl

/-- An affine open of a scheme étale over the scheme underlying an étale chart `U` of `F` is an
object of the size-bounded site. -/
theorem contains_of_isOpenImmersion_of_etale {V Y : Scheme.{u}} (w : V ⟶ chartScheme U)
    [Etale w] (e : Y ⟶ V) [AlgebraicGeometry.IsOpenImmersion e] [IsAffine Y] : B.Contains Y :=
  (Scheme.size_le_of_locallyOfFiniteType (e ≫ w)).trans_lt
    ((SmallEtale.toOver B S hS F).obj U).left.property

/-- A lift of a geometric point into an étale chart `U` and a lift of its scheme point to an
étale scheme over `U` give a lift into the corresponding chart. -/
theorem exists_geometricFiber_chartOfEtaleSchemeHom (x : GeometricPoint B S hS F)
    (t : GeometricFiber B S hS F x U)
    (q : (BigFppfOver.toScheme B S hS).obj x.val.siteObject ⟶ T)
    (hq : q ≫ m = (BigFppfOver.toScheme B S hS).map t.1) :
    ∃ t' : GeometricFiber B S hS F x (chartOfEtaleSchemeHom B S hS U hT m hm),
      (geometricFiber B S hS F x).map (chartOfEtaleSchemeHomMap B S hS U hT m hm) t' = t ∧
      (BigFppfOver.toScheme B S hS).map t'.1 = q := by
  let q' : x.val.siteObject ⟶ (SmallEtale.toOver B S hS F).obj
      (chartOfEtaleSchemeHom B S hS U hT m hm) :=
    Over.homMk (ObjectProperty.homMk q) (by
      apply ObjectProperty.hom_ext
      show q ≫ m ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj U).hom = _
      rw [← Category.assoc, hq]
      exact congrArg B.inclusion.map (Over.w t.1))
  have hq' : q' ≫ (SmallEtale.toOver B S hS F).map
      (chartOfEtaleSchemeHomMap B S hS U hT m hm) = t.1 := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rwa [Functor.map_comp]
  refine ⟨⟨q', ?_⟩, Subtype.ext hq', rfl⟩
  show U.1.hom.app (Opposite.op x.val.siteObject) (q' ≫ (SmallEtale.toOver B S hS F).map
    (chartOfEtaleSchemeHomMap B S hS U hT m hm)) = x.val.value
  exact (congrArg (U.1.hom.app (Opposite.op x.val.siteObject)) hq').trans t.2

/-- A morphism of schemes out of the scheme of `AlgebraicGeometry.Space.chartOfEtaleSchemeHom`
lying over a morphism of charts is a morphism of charts. -/
theorem exists_chartOfEtaleSchemeHom_hom {W U' : SmallEtale B S hS F} (a : W ⟶ U') (k : U ⟶ U')
    (f : T ⟶ chartScheme W)
    (hf : f ≫ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map a) =
      m ≫ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map k)) :
    ∃ b : chartOfEtaleSchemeHom B S hS U hT m hm ⟶ W,
      b ≫ a = chartOfEtaleSchemeHomMap B S hS U hT m hm ≫ k ∧
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map b) = f := by
  let bO : (SmallEtale.toOver B S hS F).obj (chartOfEtaleSchemeHom B S hS U hT m hm) ⟶
      (SmallEtale.toOver B S hS F).obj W :=
    Over.homMk (ObjectProperty.homMk f) (by
      apply ObjectProperty.hom_ext
      show f ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj W).hom =
        m ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj U).hom
      have ha := congrArg B.inclusion.map (Over.w ((SmallEtale.toOver B S hS F).map a))
      have hk := congrArg B.inclusion.map (Over.w ((SmallEtale.toOver B S hS F).map k))
      rw [Functor.map_comp] at ha hk
      rw [← ha, ← hk, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj U').hom) hf)
  have hbO : bO ≫ (SmallEtale.toOver B S hS F).map a =
      (SmallEtale.toOver B S hS F).map (chartOfEtaleSchemeHomMap B S hS U hT m hm) ≫
        (SmallEtale.toOver B S hS F).map k := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rwa [Functor.map_comp, Functor.map_comp]
  have hw : yoneda.map bO ≫ W.1.hom = (chartOfEtaleSchemeHom B S hS U hT m hm).1.hom := by
    have hwa : yoneda.map ((SmallEtale.toOver B S hS F).map a) ≫ U'.1.hom = W.1.hom :=
      CostructuredArrow.w a.hom
    have hwk : yoneda.map ((SmallEtale.toOver B S hS F).map k) ≫ U'.1.hom = U.1.hom :=
      CostructuredArrow.w k.hom
    have hwg : yoneda.map ((SmallEtale.toOver B S hS F).map
        (chartOfEtaleSchemeHomMap B S hS U hT m hm)) ≫ U.1.hom =
        (chartOfEtaleSchemeHom B S hS U hT m hm).1.hom :=
      CostructuredArrow.w (chartOfEtaleSchemeHomMap B S hS U hT m hm).hom
    rw [← hwa, ← Category.assoc, ← Functor.map_comp, hbO, Functor.map_comp, Category.assoc,
      hwk, hwg]
  exact ⟨ObjectProperty.homMk (CostructuredArrow.homMk bO hw),
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hbO), rfl⟩

end ChartOfEtale


/-! ### Two geometric steps -/

section Steps

variable {Z X : AlgebraicSpaces B S hS}

/-- **The factorization step.** Let `f : Z ⟶ X` be a representable morphism of algebraic spaces,
let `U` be an étale chart of `X`, let `A` be an étale chart of `Z` and let
`a : A ⟶ U ×_X Z` be an arrow of the small étale site of `Z`. Write `j : W' ⟶ U'` for the
base-change projection of schemes at `U`, and suppose given a morphism of schemes
`w : V ⟶ U'` together with a morphism `r : W' ×_{U'} V ⟶ A'` over `W'`. Then for every object
`T` of the size-bounded site and every `mt : T ⟶ V` whose composite with `w` is étale, the base
change along `f` of the chart `mt ≫ w : T ⟶ U'` factors through `A` over `U ×_X Z`.

This is the step at which property (C) of [Stacks, Tag 04DW] is spent: `r` is the morphism that
property supplies, and only the triangle `r ≫ a' = pr₁` is used here, not its surjectivity. -/
private theorem exists_smallBaseChange_map_factor
    (f : Z ⟶ X) (hf : yoneda.relativelyRepresentable f.hom) (U : SmallEtale B S hS X.1)
    (A : SmallEtale B S hS Z.1) (a : A ⟶ (smallBaseChange B S hS f hf).obj U)
    {V : Scheme.{u}} (w : V ⟶ chartScheme U)
    (r : pullback ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)) w ⟶ chartScheme A)
    (hr : r ≫ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z.1).map a) =
      pullback.fst ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)) w)
    {T : Scheme.{u}} (hT : B.Contains T) (mt : T ⟶ V) (hm : Etale (mt ≫ w)) :
    ∃ d : (smallBaseChange B S hS f hf).obj
        (chartOfEtaleSchemeHom B S hS U hT (mt ≫ w) hm) ⟶ A,
      (smallBaseChange B S hS f hf).map
          (chartOfEtaleSchemeHomMap B S hS U hT (mt ≫ w) hm) = d ≫ a := by
  have hcomm : (BigFppfOver.toScheme B S hS).map
        (representablePullbackMap B S hS f hf
          (chartOfEtaleSchemeHomMap B S hS U hT (mt ≫ w) hm)) ≫
        (BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom) =
      ((BigFppfOver.toScheme B S hS).map (hf.snd
          (chartOfEtaleSchemeHom B S hS U hT (mt ≫ w) hm).1.hom) ≫ mt) ≫ w :=
    (representablePullbackMap_isPullback_scheme B S hS f hf
      (chartOfEtaleSchemeHomMap B S hS U hT (mt ≫ w) hm)).w.trans
      (Category.assoc _ _ _).symm
  obtain ⟨n, hn⟩ : ∃ n : chartScheme ((smallBaseChange B S hS f hf).obj
        (chartOfEtaleSchemeHom B S hS U hT (mt ≫ w) hm)) ⟶ chartScheme A,
      n ≫ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z.1).map a) =
        (BigFppfOver.toScheme B S hS).map (representablePullbackMap B S hS f hf
          (chartOfEtaleSchemeHomMap B S hS U hT (mt ≫ w) hm)) := by
    refine ⟨pullback.lift _ _ hcomm ≫ r, ?_⟩
    rw [Category.assoc, hr]
    exact pullback.lift_fst _ _ _
  have hover : n ≫ B.inclusion.map ((SmallEtale.toOver B S hS Z.1).obj A).hom =
      B.inclusion.map ((SmallEtale.toOver B S hS Z.1).obj
        ((smallBaseChange B S hS f hf).obj
          (chartOfEtaleSchemeHom B S hS U hT (mt ≫ w) hm))).hom := by
    rw [← BigFppfOver.toScheme_map_comp_hom ((SmallEtale.toOver B S hS Z.1).map a),
      ← Category.assoc, hn]
    exact BigFppfOver.toScheme_map_comp_hom
      (representablePullbackMap B S hS f hf
        (chartOfEtaleSchemeHomMap B S hS U hT (mt ≫ w) hm))
  obtain ⟨psi, hpsi⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS n hover
  have hpsifac : psi ≫ (SmallEtale.toOver B S hS Z.1).map a =
      representablePullbackMap B S hS f hf
        (chartOfEtaleSchemeHomMap B S hS U hT (mt ≫ w) hm) := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rwa [Functor.map_comp, hpsi]
  have hwa : yoneda.map ((SmallEtale.toOver B S hS Z.1).map a) ≫
      ((smallBaseChange B S hS f hf).obj U).1.hom = A.1.hom := CostructuredArrow.w a.hom
  have htri : yoneda.map psi ≫ A.1.hom =
      ((smallBaseChange B S hS f hf).obj
        (chartOfEtaleSchemeHom B S hS U hT (mt ≫ w) hm)).1.hom := by
    rw [← hwa, ← Category.assoc, ← yoneda.map_comp, hpsifac]
    exact CostructuredArrow.w ((smallBaseChange B S hS f hf).map
      (chartOfEtaleSchemeHomMap B S hS U hT (mt ≫ w) hm)).hom
  exact ⟨ObjectProperty.homMk (CostructuredArrow.homMk psi htri),
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hpsifac.symm)⟩

/-- The underlying map of the inclusion of an open subchart has range the open. -/
private theorem range_toScheme_map_toOver_map_openChartInclusion
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS F) (O : (chartScheme U).Opens) :
    Set.range ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (openChartInclusion B S hS F U O))).base =
        (O : Set (chartScheme U)) := by
  rw [toScheme_map_toOver_map_openChartInclusion]
  exact O.range_ι

/-- **The emptiness step.** The base change along a representable `f : Z ⟶ X` of an open
subchart of an étale chart `U` of `X` that misses the image of the base-change projection
`U ×_X Z ⟶ U` has empty underlying scheme.

A point of that base change would give a point of the open and a point of `U ×_X Z` with the
same image in `U'`, so a point of the open inside the image of the projection. -/
private theorem isEmpty_chartScheme_smallBaseChange_openChart
    (f : Z ⟶ X) (hf : yoneda.relativelyRepresentable f.hom) (U : SmallEtale B S hS X.1)
    (O : (chartScheme U).Opens)
    (hO : ∀ y : chartScheme U, y ∈ (O : Set (chartScheme U)) →
      y ∉ Set.range ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).base) :
    IsEmpty (chartScheme ((smallBaseChange B S hS f hf).obj
      (openChart B S hS X.1 U O))) := by
  refine ⟨fun pt => ?_⟩
  have hval : ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).base
        (((BigFppfOver.toScheme B S hS).map (representablePullbackMap B S hS f hf
          (openChartInclusion B S hS X.1 U O))).base pt) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
            (openChartInclusion B S hS X.1 U O))).base
        (((BigFppfOver.toScheme B S hS).map (hf.snd
          (openChart B S hS X.1 U O).1.hom)).base pt) :=
    congrArg (fun k : Scheme.Hom _ _ => k.base pt)
      (representablePullbackMap_isPullback_scheme B S hS f hf
        (openChartInclusion B S hS X.1 U O)).w
  exact hO _ ((Set.ext_iff.1 (range_toScheme_map_toOver_map_openChartInclusion B S hS U O) _).1
    ⟨_, rfl⟩) ⟨_, hval⟩

/-- Let `j : W' ⟶ U'` and `w : V ⟶ U'` be morphisms of schemes and let `r : W' ×_{U'} V ⟶ A'` be
a surjection over `W'` along `a' : A' ⟶ W'`. Then every point of `U'` that is the image under `j`
of a point in the image of `a'` is hit by an affine open of `V`. -/
theorem exists_affineCover_comp_base_eq {W' U' V A' : Scheme.{u}} (j : W' ⟶ U') (w : V ⟶ U')
    (r : pullback j w ⟶ A') [Surjective r] (a' : A' ⟶ W') (hr : r ≫ a' = pullback.fst j w)
    {p : W'} {x : U'} (hp : p ∈ Set.range a') (hx : j.base p = x) :
    ∃ (b : V.affineCover.I₀) (z : V.affineCover.X b), (V.affineCover.f b ≫ w).base z = x := by
  obtain ⟨y, hy⟩ := hp
  obtain ⟨t, ht⟩ := r.surjective y
  have hfst : (pullback.fst j w).base t = p := by
    have h : a'.base (r.base t) = (pullback.fst j w).base t :=
      congrArg (fun k : Scheme.Hom _ _ => k.base t) hr
    rwa [← h, ht]
  have hsnd : w.base ((pullback.snd j w).base t) = x := by
    have h : j.base ((pullback.fst j w).base t) = w.base ((pullback.snd j w).base t) :=
      congrArg (fun k : Scheme.Hom _ _ => k.base t) (pullback.condition (f := j) (g := w))
    rwa [← h, hfst]
  obtain ⟨b, z, hz⟩ := V.affineCover.exists_eq ((pullback.snd j w).base t)
  exact ⟨b, z, (congrArg w.base hz).trans hsnd⟩

/-- The sieve generated by a family of charts over `U` satisfies the alternative of almost
cocontinuity for base change along `f` as soon as each member of the family does. -/
theorem forall_ofArrows_isEmpty_or_mem (f : Z ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
    {U : SmallEtale B S hS X.1} (Sv : Sieve ((smallBaseChange B S hS f hf).obj U))
    {ι : Type*} (Wc : ι → SmallEtale B S hS X.1) (ar : ∀ k, Wc k ⟶ U)
    (h : ∀ k, IsEmpty (chartScheme ((smallBaseChange B S hS f hf).obj (Wc k))) ∨
      Sv.arrows ((smallBaseChange B S hS f hf).map (ar k))) :
    ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), Sieve.ofArrows Wc ar g →
      SheafTheoreticallyEmptySite (SmallEtale.topology B S hS Z.1)
          ((smallBaseChange B S hS f hf).obj V) ∨
        Sv ((smallBaseChange B S hS f hf).map g) := by
  intro V g hg
  obtain ⟨k, c, rfl⟩ := (Sieve.mem_ofArrows_iff Wc ar g).mp hg
  rcases h k with hemp | hin
  · refine Or.inl (SmallEtale.bot_mem_topology B S hS Z.1 _ ⟨fun pt => hemp.false ?_⟩)
    exact ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z.1).map
      ((smallBaseChange B S hS f hf).map c))).base pt
  · rw [Functor.map_comp]
    exact Or.inr (Sv.downward_closed hin _)

end Steps

/-! ### Almost cocontinuity -/

variable {Z X : AlgebraicSpaces B S hS}

/-- **The space-level analogue of [Stacks, Tag 04DV].** Let `f : Z ⟶ X` be a representable
morphism of algebraic spaces over `S`. If for every étale chart `U` of `X` the base-change
projection of schemes `U ×_X Z ⟶ U` has property (C) of [Stacks, Tag 04DW] and is a closed map,
then base change of étale scheme charts along `f` is almost cocontinuous for the small étale
topologies. -/
theorem smallBaseChange_isAlmostCocontinuous (f : Z ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hC : ∀ U : SmallEtale B S hS X.1, Stacks.EtaleCohomology.HasPropertyC
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)))
    (hcl : ∀ U : SmallEtale B S hS X.1, IsClosedMap
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).base) :
    IsAlmostCocontinuous (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1) := by
  classical
  intro U Sv hSv
  -- Property (C) at the chart `U`, applied to each arrow of the given covering sieve.
  have hdata : ∀ i : Σ A : SmallEtale B S hS Z.1,
      {a : A ⟶ (smallBaseChange B S hS f hf).obj U // Sv.arrows a},
      ∃ (V : Scheme.{u}) (w : V ⟶ chartScheme U), Etale w ∧
        ∃ r : pullback ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)) w ⟶
            chartScheme i.1,
          Surjective r ∧
            r ≫ (BigFppfOver.toScheme B S hS).map
                ((SmallEtale.toOver B S hS Z.1).map i.2.1) =
              pullback.fst ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)) w :=
    fun i => hC U _ (etale_toScheme_toOver_map B S hS Z.1 i.2.1)
  choose Vs ws hws rs hrs hfacs using hdata
  -- Affine opens of those schemes are objects of the size-bounded site, and étale over `U'`.
  have hinst : ∀ i (b : (Vs i).affineCover.I₀),
      AlgebraicGeometry.IsOpenImmersion ((Vs i).affineCover.f b) ∧ Etale (ws i) :=
    fun i b => ⟨(Vs i).affineCover.map_prop b, hws i⟩
  have hsize : ∀ i (b : (Vs i).affineCover.I₀), B.Contains ((Vs i).affineCover.X b) :=
    fun i b => have := (hinst i b).1; have := (hinst i b).2
      contains_of_isOpenImmersion_of_etale B S hS U (ws i) ((Vs i).affineCover.f b)
  have hetale : ∀ i (b : (Vs i).affineCover.I₀), Etale ((Vs i).affineCover.f b ≫ ws i) :=
    fun i b => have := (hinst i b).1; have := (hinst i b).2; inferInstance
  -- The open complement of the image of the base-change projection.
  let O : (chartScheme U).Opens :=
    ⟨(Set.range ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).base)ᶜ,
      (hcl U).isClosed_range.isOpen_compl⟩
  -- The refining family of charts over `U`.
  let Wc : (Σ i : Σ A : SmallEtale B S hS Z.1,
        {a : A ⟶ (smallBaseChange B S hS f hf).obj U // Sv.arrows a},
        (Vs i).affineCover.I₀) ⊕ PUnit.{u + 2} → SmallEtale B S hS X.1 :=
    fun
      | .inl p => chartOfEtaleSchemeHom B S hS U (hsize p.1 p.2)
          ((Vs p.1).affineCover.f p.2 ≫ ws p.1) (hetale p.1 p.2)
      | .inr _ => openChart B S hS X.1 U O
  let ar : ∀ k, Wc k ⟶ U :=
    fun
      | .inl p => chartOfEtaleSchemeHomMap B S hS U (hsize p.1 p.2)
          ((Vs p.1).affineCover.f p.2 ≫ ws p.1) (hetale p.1 p.2)
      | .inr _ => openChartInclusion B S hS X.1 U O
  refine ⟨Sieve.ofArrows Wc ar, ?_, ?_⟩
  · -- The family is jointly surjective on the points of `U'`, hence generates a covering sieve.
    rw [SmallEtale.mem_topology_iff_exists_mem_range]
    intro x
    by_cases hx : x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).base
    · obtain ⟨wpt, hwpt⟩ := hx
      obtain ⟨A, a, ha, y, hy⟩ :=
        (SmallEtale.mem_topology_iff_exists_mem_range B S hS Z.1 Sv).1 hSv wpt
      have := hrs ⟨A, ⟨a, ha⟩⟩
      obtain ⟨b, z, hz⟩ := exists_affineCover_comp_base_eq _ (ws ⟨A, ⟨a, ha⟩⟩)
        (rs ⟨A, ⟨a, ha⟩⟩) _ (hfacs ⟨A, ⟨a, ha⟩⟩) ⟨y, hy⟩ hwpt
      refine ⟨Wc (.inl ⟨⟨A, ⟨a, ha⟩⟩, b⟩), ar (.inl ⟨⟨A, ⟨a, ha⟩⟩, b⟩),
        (Sieve.mem_ofArrows_iff Wc ar _).2
          ⟨.inl ⟨⟨A, ⟨a, ha⟩⟩, b⟩, 𝟙 _, (Category.id_comp _).symm⟩, z, hz⟩
    · refine ⟨Wc (.inr PUnit.unit), ar (.inr PUnit.unit),
        (Sieve.mem_ofArrows_iff Wc ar _).2
          ⟨.inr PUnit.unit, 𝟙 _, (Category.id_comp _).symm⟩, ?_⟩
      exact (Set.ext_iff.1 (range_toScheme_map_toOver_map_openChartInclusion B S hS U O) x).2 hx
  · -- The dichotomy on the members of the refining sieve.
    refine forall_ofArrows_isEmpty_or_mem B S hS f hf Sv Wc ar fun k => ?_
    cases k with
    | inl p =>
        obtain ⟨d, hd⟩ := exists_smallBaseChange_map_factor B S hS f hf U p.1.1 p.1.2.1
          (ws p.1) (rs p.1) (hfacs p.1) (hsize p.1 p.2)
          ((Vs p.1).affineCover.f p.2) (hetale p.1 p.2)
        have hgoal : Sv.arrows ((smallBaseChange B S hS f hf).map
            (chartOfEtaleSchemeHomMap B S hS U (hsize p.1 p.2)
              ((Vs p.1).affineCover.f p.2 ≫ ws p.1) (hetale p.1 p.2))) := by
          rw [hd]
          exact Sv.downward_closed p.1.2.2 d
        exact Or.inr hgoal
    | inr q =>
        exact Or.inl (isEmpty_chartScheme_smallBaseChange_openChart B S hS f hf U O
          fun _ hy => hy)

/-- **The space-level analogue of [Stacks, Tag 04DX], part (7).** Let `f : Z ⟶ X` be a
representable morphism of algebraic spaces over `S` such that every base-change projection of
schemes `U ×_X Z ⟶ U` at an étale chart `U` of `X` is integral and universally injective — for
instance a closed immersion. Then base change of étale scheme charts along `f`,

`X_étale ⥤ Z_étale`, `U ↦ U ×_X Z`,

is almost cocontinuous for the small étale topologies.

Integrality makes each chart base change universally closed, hence a closed map, and together
with universal injectivity a homeomorphism onto a closed subset of the chart, which is the
hypothesis of [Stacks, Tag 04DW] and so gives property (C). Those are the two inputs of the
space-level [Stacks, Tag 04DV]. -/
@[stacks 04DX "part (7) for algebraic spaces: chart base change is almost cocontinuous"]
theorem smallBaseChange_isAlmostCocontinuous_of_isIntegralHom_of_universallyInjective
    (f : Z ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
    (hint : ∀ U : SmallEtale B S hS X.1, AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)))
    (huniv : ∀ U : SmallEtale B S hS X.1, AlgebraicGeometry.UniversallyInjective
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom))) :
    IsAlmostCocontinuous (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1) := by
  refine smallBaseChange_isAlmostCocontinuous B S hS f hf (fun U => ?_) (fun U => ?_)
  · have := hint U
    have := huniv U
    have hemb : Topology.IsClosedEmbedding
        ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).base :=
      Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
        ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).continuous
        ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).injective
        (Scheme.Hom.isClosedMap ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)))
    intro V0 g hg
    exact Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding _ hemb g hg
  · have := hint U
    exact Scheme.Hom.isClosedMap ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom))

/-- **The space-level analogue of [Stacks, Tag 04DX], part (7), for a closed immersion.** For a
closed immersion `i : Z ⟶ X` of algebraic spaces over `S`, base change of étale scheme charts
along `i` is almost cocontinuous for the small étale topologies.

Every represented base change of a closed immersion of algebraic spaces is a closed immersion of
schemes, hence integral and a homeomorphism onto a closed subset, which is what the general
statement consumes. -/
theorem smallBaseChange_isAlmostCocontinuous_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    IsAlmostCocontinuous (smallBaseChange B S hS i hi.rep)
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1) := by
  have h (U : SmallEtale B S hS X.1) : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd U.1.hom)) := hi.property_snd U.1.hom
  exact smallBaseChange_isAlmostCocontinuous_of_isIntegralHom_of_universallyInjective B S hS i
    hi.rep (fun U => have := h U; inferInstance) (fun U => have := h U; inferInstance)

end AlgebraicGeometry.Space

end

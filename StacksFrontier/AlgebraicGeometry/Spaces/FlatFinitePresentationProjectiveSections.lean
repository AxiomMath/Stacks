module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# Projective sections of a flat finitely presented module near a point of an algebraic space

Tag 0CVY asserts, for a morphism `f : X ⟶ Y` of algebraic spaces over `S`, a quasi-coherent
`𝒪_X`-module `𝓕` and a point `x ∈ |X|` with image `y ∈ |Y|`, under the three hypotheses that
`f` be locally of finite presentation, `𝓕` be of finite presentation and `𝓕` be flat at `x`
over `Y`, the existence of a commutative diagram of pointed schemes
```
(X, x) ←—— (X', x')
  |           |
  ↓           ↓
(Y, y) ←—— (Y', y')
```
whose horizontal arrows `g : X' → X` and `Y' → Y` are étale, in which `X'` and `Y'` are
affine, and such that `Γ(X', g^*𝓕)` is a projective `Γ(Y', 𝒪_{Y'})`-module.

The source proves it in one sentence: *as formulated this proposition immediately reduces to
the case of schemes, which is More on Flatness, Proposition 05ID*. **That reduction is what is
proved here**, and it is proved in the stronger of the two possible forms: the pointed diagram
of the conclusion, with both charts affine, is produced outright, with no hypothesis on `f` or
on `𝓕` at all.

## Main definitions

No new definitions are introduced.  The three hypotheses of the tag are the development's own
chartwise conditions: `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` of Stacks 03XP
part (1) for `f`, and for `𝓕` the restrictions `AlgebraicGeometry.Space.restrictToChart` to
the étale scheme charts, exactly as `AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV does
for flatness over the target.

## Main results

* `AlgebraicGeometry.Space.exists_hom_openSub_resLE`: a morphism of the big fppf site restricts
  to a morphism of the open subobjects cut out by a pair of Zariski opens, one carried into the
  other. This is what makes the two charts of the diagram affine.
* `AlgebraicGeometry.Space.exists_isAffine_etale_chart_square_at_point`: the diagram of the
  conclusion of Tag 0CVY. Every point `x` of the source of a morphism of algebraic spaces over
  `S` lies in the image of a commuting square of étale scheme charts whose two charts are
  **affine**, through a point of the source chart over `x`, and the induced point of the target
  chart lies over the image of `x`. Unconditional.
* `AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections`: the full
  conclusion of Tag 0CVY, projectivity of the sections included, under the tag's own three
  hypotheses; the case of schemes, Tag 05ID, enters through
  `AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections`.

## Implementation notes

### How the case of schemes enters

The case of schemes — Tag 05ID — is used read inside the big fppf site: for a morphism
`h : D ⟶ E` of the site whose morphism of schemes is locally of finite presentation, a
quasi-coherent `𝒪_D`-module `G` of finite presentation and a point `d` of `D` at which `G` is
flat over `E`, there are étale morphisms `p : D' ⟶ D` and `q : E' ⟶ E` of the site with `D'`
and `E'` affine, a morphism `k : D' ⟶ E'` with `k ≫ q = p ≫ h`, and a point of `D'` over `d`,
such that `Γ(D', p^*G)` is projective over `Γ(E', 𝒪_{E'})`.

It is `AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections` below, which
carries Tag 05ID into the site: the two elementary étale neighbourhoods that
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`
produces are affine, hence compact, so a morphism locally of finite type out of them does not
raise the cardinal size and both are objects of the site. So the conclusion below is the tag's
conclusion in full, with no clause dropped and nothing replaced by a weaker object, and
`exists_isAffine_etale_charts_projective_sections` states it with no hypothesis beyond the
tag's own three.

### Why the module appears as a pullback rather than as a restriction to a chart

The conclusion names `Γ(X', g^*𝓕)` as `Γ((Scheme.Modules.pullback p) (𝓕|_U), ⊤)`, where `U` is
the étale chart of `X` the étale morphism `g : X' → X` factors through and `𝓕|_U` is
`AlgebraicGeometry.Space.restrictToChart`. That is forced: `restrictToChart` has no
functoriality in the chart in this development — nothing identifies `𝓕|_{U'}` for a chart `U'`
over `U` with the pullback of `𝓕|_U` along `U' → U` — so the pullback spelling is the only one
in which the module of the conclusion can be named at all. It is the faithful one: `g` is the
composite `X' → U → X`, and the sections of the pullback of `𝓕|_U` along `X' → U` are the
sections of `g^*𝓕`.

### The construction of the diagram

`AlgebraicGeometry.Space.exists_etaleChartAtPoint` (Tag 02X1 with Tag 03H5) already supplies a
commuting square of étale charts of `f` with a point of the source chart over `x`; what it
does not supply is affineness of either chart. Both are arranged by passing to Zariski opens,
which is legitimate because an open subscheme of an object of the site is again one — of no
greater size — and the inclusion is an open immersion, hence étale, so
`AlgebraicGeometry.Space.openChart` turns a Zariski open of a chart into a chart. An affine
open `O_V` of the target chart around the image of the chart point is chosen first, then an
affine open `O_U` of the source chart around the chart point and inside the preimage of `O_V`;
the restricted morphism of schemes is `AlgebraicGeometry.Scheme.Hom.resLE`, and it is the image
of a morphism of the site by `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`, the
fullness of the passage to schemes over the morphisms commuting with the structure morphisms.

The chart point is produced through the comparison bijection of Stacks 03BX clause (1),
`AlgebraicGeometry.Space.pointsEquivScheme`: the point of `|X'|` required by the conclusion is
the one the chosen scheme point of the affine open corresponds to, and the two conditions on
it — that it lie over `x`, and that its image in the target chart lie over the image of `x` —
are read off from naturality of that bijection
(`AlgebraicGeometry.Space.pointsToScheme_pointsMap_yoneda`) and from commutativity of the
square. No field-valued representative is chosen a second time.

## References

* [Stacks Project, Tag 0CVY](https://stacks.math.columbia.edu/tag/0CVY)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **A morphism of the site restricts to a morphism of the open subobjects cut out by a pair
of Zariski opens.** If `h : D ⟶ E` is a morphism of the big fppf site of `S` and `O'` is a
Zariski open of the scheme of `D` carried into a Zariski open `O` of the scheme of `E`, then
the open subobjects `AlgebraicGeometry.Space.openSub` they cut out are related by a morphism of
the site whose morphism of schemes is `AlgebraicGeometry.Scheme.Hom.resLE`, and which commutes
with the two inclusions.

Existence rather than a construction is asserted, because the morphism of the site is produced
by `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`; its morphism of schemes is pinned
down, which is all a consumer uses. This is the form over an arbitrary morphism of the site of
`AlgebraicGeometry.Space.exists_openChartHom_resLE`, which asks for a morphism of étale charts
of one and the same presheaf and so cannot be used across a morphism of algebraic spaces. -/
theorem exists_hom_openSub_resLE (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {D E : BigFppfOver B S hS} (h : D ⟶ E)
    (O : ((BigFppfOver.toScheme B S hS).obj E).Opens)
    (O' : ((BigFppfOver.toScheme B S hS).obj D).Opens)
    (hle : O' ≤ (BigFppfOver.toScheme B S hS).map h ⁻¹ᵁ O) :
    ∃ n : openSub D O' ⟶ openSub E O,
      (BigFppfOver.toScheme B S hS).map n =
          ((BigFppfOver.toScheme B S hS).map h).resLE O O' hle ∧
        n ≫ openSubHom E O = openSubHom D O' ≫ h := by
  have hoverSub : ∀ (A : BigFppfOver B S hS)
      (W : ((BigFppfOver.toScheme B S hS).obj A).Opens),
      B.inclusion.map (openSub A W).hom = W.ι ≫ B.inclusion.map A.hom := by
    intro A W
    have h1 : (openSubHom A W).left ≫ A.hom = (openSub A W).hom := Over.w _
    rw [← h1, B.inclusion.map_comp]
    exact congrArg (· ≫ B.inclusion.map A.hom) (toScheme_map_openSubHom B S hS A W)
  have hover : (BigFppfOver.toScheme B S hS).map h ≫ B.inclusion.map E.hom =
      B.inclusion.map D.hom :=
    congrArg (fun q => B.inclusion.map q) (Over.w h)
  have hkey : ((BigFppfOver.toScheme B S hS).map h).resLE O O' hle ≫ O.ι =
      O'.ι ≫ (BigFppfOver.toScheme B S hS).map h :=
    Scheme.Hom.resLE_comp_ι _ hle
  obtain ⟨n, hn⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := openSub D O') (Y := openSub E O)
    (((BigFppfOver.toScheme B S hS).map h).resLE O O' hle) (by
      rw [hoverSub, hoverSub]
      calc ((BigFppfOver.toScheme B S hS).map h).resLE O O' hle ≫
              O.ι ≫ B.inclusion.map E.hom
          = (((BigFppfOver.toScheme B S hS).map h).resLE O O' hle ≫ O.ι) ≫
              B.inclusion.map E.hom := (Category.assoc _ _ _).symm
        _ = (O'.ι ≫ (BigFppfOver.toScheme B S hS).map h) ≫
              B.inclusion.map E.hom := by rw [hkey]
        _ = O'.ι ≫ (BigFppfOver.toScheme B S hS).map h ≫ B.inclusion.map E.hom :=
            Category.assoc _ _ _
        _ = O'.ι ≫ B.inclusion.map D.hom := by rw [hover])
  refine ⟨n, hn, (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hn, toScheme_map_openSubHom,
    toScheme_map_openSubHom]
  exact hkey

/-- A scheme point `d` of `D` lifts to a point of `D` over `x` along `h` and `u`, once `h d` is
the scheme point of a point `w` of `E` with `u w = x`. -/
private theorem pointsMap_yoneda_comp_pointsEquivScheme_symm (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {D E : BigFppfOver B S hS} (h : D ⟶ E) (u : yoneda.obj E ⟶ X)
    (d : (BigFppfOver.toScheme B S hS).obj D) (w : points B S hS (yoneda.obj E))
    (x : points B S hS X) (hd : (BigFppfOver.toScheme B S hS).map h d = pointsToScheme B S hS E w)
    (hw : pointsMap B S hS _ u w = x) :
    pointsMap B S hS _ (yoneda.map h ≫ u) ((pointsEquivScheme B S hS D).symm d) = x := by
  rw [pointsMap_comp, Function.comp_apply, ← hw]
  congr 1
  refine injective_pointsToScheme B S hS E ?_
  rw [pointsToScheme_pointsMap_yoneda]
  exact (congrArg ((BigFppfOver.toScheme B S hS).map h)
    ((pointsEquivScheme B S hS D).apply_symm_apply d)).trans hd

/-- **Stacks Project, Tag 0CVY: the diagram of the conclusion.** Every point `x` of the source
of a morphism `f : X ⟶ Y` of algebraic spaces over `S` lies in the image of a commuting square
of étale scheme charts

```
(X, x) ←—— (U, x')
  |          |
  ↓          ↓
(Y, f x) ←— (V, y')
```

whose two charts `U` and `V` are **affine**, through a point `x'` of `U` lying over `x`; the
point `y'` of `V` it induces then lies over the image of `x`.

This is the diagram of pointed schemes which Tag 0CVY asserts, and it is produced here with
none of the tag's three hypotheses: neither `f` nor any module on `X` enters. What Tag 0CVY
adds to it is the projectivity of `Γ(U, 𝓕|_U)` over `Γ(V, 𝒪_V)` after a further shrinking,
which is the case of schemes, Tag 05ID; that is
`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections`.

The three conclusions after affineness are, in order: the square of charts commutes over `f`;
the chart point lies over `x`; and the image of the chart point in the target chart lies over
the image of `x` in `|Y|`. -/
@[stacks 0CVY "the commutative diagram of pointed schemes of the conclusion — affine étale \
charts of the source and of the target, through the given point and through its image, with a \
morphism between them over f — and nothing of the projectivity of the sections, which is the \
case of schemes, Tag 05ID"]
theorem exists_isAffine_etale_chart_square_at_point
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    ∃ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
      (x' : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))),
      IsAffine (chartScheme U) ∧ IsAffine (chartScheme V) ∧
        U.obj.hom ≫ f = yoneda.map g ≫ V.obj.hom ∧
        pointsMap B S hS _ U.obj.hom x' = x ∧
        pointsMap B S hS _ V.obj.hom (pointsMap B S hS _ (yoneda.map g) x') =
          pointsMap B S hS X f x := by
  classical
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hX hY f x
  set w : points B S hS (yoneda.obj c.U) := c.representative.class B S hS (yoneda.obj c.U)
    with hwdef
  obtain ⟨OV, hOVaff, hvOV, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj c.V).Opens))
    (x := (BigFppfOver.toScheme B S hS).map c.h (pointsToScheme B S hS c.U w)) trivial
  obtain ⟨OU, hOUaff, huOU, hle⟩ := exists_isAffineOpen_mem_and_subset
    (show pointsToScheme B S hS c.U w ∈
      (BigFppfOver.toScheme B S hS).map c.h ⁻¹ᵁ OV from hvOV)
  obtain ⟨n, -, hsq⟩ := exists_hom_openSub_resLE B S hS c.h OV OU hle
  have hcomm : (yoneda.map (openSubHom c.U OU) ≫ c.a) ≫ f =
      yoneda.map n ≫ yoneda.map (openSubHom c.V OV) ≫ c.b := by
    rw [← Category.assoc (yoneda.map n), ← yoneda.map_comp, hsq, yoneda.map_comp,
      Category.assoc, Category.assoc, c.comm]
  have hbase := pointsMap_yoneda_comp_pointsEquivScheme_symm B S hS (openSubHom c.U OU) c.a
    (⟨pointsToScheme B S hS c.U w, huOU⟩ : OU) w x (by rw [toScheme_map_openSubHom]; rfl)
    c.maps_to
  refine ⟨openChart B S hS X ⟨CostructuredArrow.mk c.a, c.a_etale⟩ OU,
    openChart B S hS Y ⟨CostructuredArrow.mk c.b, c.b_etale⟩ OV, n,
    (pointsEquivScheme B S hS (openSub c.U OU)).symm ⟨pointsToScheme B S hS c.U w, huOU⟩,
    hOUaff, hOVaff, hcomm, hbase, ?_⟩
  change pointsMap B S hS _ (yoneda.map (openSubHom c.V OV) ≫ c.b)
    (pointsMap B S hS _ (yoneda.map n) _) = _
  rw [← Function.comp_apply
      (f := pointsMap B S hS _ (yoneda.map (openSubHom c.V OV) ≫ c.b)),
    ← pointsMap_comp, ← hcomm, pointsMap_comp, Function.comp_apply, hbase]

/-- **The case of schemes of Tag 0CVY, read inside the big fppf site.** Let `h : D ⟶ E` be a
morphism of the big fppf site of `S` whose morphism of schemes is locally of finite
presentation, let `G` be a quasi-coherent `𝒪_D`-module of finite presentation and let `d` be a
point of `D` at which `G` is flat over `E`. Then there are étale morphisms `p : D' ⟶ D` and
`q : E' ⟶ E` of the site with `D'` and `E'` affine, a morphism `k : D' ⟶ E'` over `h`, and a
point of `D'` over `d`, such that `Γ(D', p^*G)` is projective over `Γ(E', 𝒪_{E'})`.

This is Tag 05ID, carried into the site: the two elementary étale neighbourhoods it produces
are affine, hence compact, so a morphism locally of finite type out of them does not raise the
cardinal size and both are objects of the site. -/
theorem exists_isAffine_etale_hom_projective_sections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D E : BigFppfOver B S hS) (h : D ⟶ E)
    (G : ((BigFppfOver.toScheme B S hS).obj D).Modules)
    (d : (BigFppfOver.toScheme B S hS).obj D)
    (hfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h))
    (hqc : G.IsQuasicoherent) (hGfp : G.IsFinitePresentation)
    (hflat : AlgebraicGeometry.IsFlatOverAt
      (LocallyRingedSpace.forgetToSheafedSpace.map
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom) G d) :
    ∃ (D' E' : BigFppfOver B S hS) (p : D' ⟶ D) (q : E' ⟶ E) (k : D' ⟶ E')
      (d' : (BigFppfOver.toScheme B S hS).obj D'),
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      k ≫ q = p ≫ h ∧
      (BigFppfOver.toScheme B S hS).map p d' = d ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj D') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj E') ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map p)).obj G
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤)) := by
  have := hfp
  have := hqc
  have := hGfp
  obtain ⟨V, U, g, -, -, hover, -, hUaff, hVaff, hproj⟩ :=
    AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt
      ((BigFppfOver.toScheme B S hS).map h) G d hflat
  have := hUaff
  have := hVaff
  have hUsize : B.Contains U.scheme :=
    (Scheme.size_le_of_locallyOfFiniteType U.toBase).trans_lt D.left.property
  have hVsize : B.Contains V.scheme :=
    (Scheme.size_le_of_locallyOfFiniteType V.toBase).trans_lt E.left.property
  have hbaseD : (BigFppfOver.toScheme B S hS).map h ≫ B.inclusion.map E.hom =
      B.inclusion.map D.hom :=
    congrArg (fun w => B.inclusion.map w) (Over.w h)
  let D' : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk (U.toBase ≫ B.inclusion.map D.hom) :
      B.obj hUsize ⟶ B.obj hS))
  let E' : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk (V.toBase ≫ B.inclusion.map E.hom) :
      B.obj hVsize ⟶ B.obj hS))
  have hk : (ObjectProperty.homMk g : B.obj hUsize ⟶ B.obj hVsize) ≫ E'.hom = D'.hom := by
    refine ObjectProperty.hom_ext _ ?_
    change g ≫ V.toBase ≫ B.inclusion.map E.hom = U.toBase ≫ B.inclusion.map D.hom
    rw [← Category.assoc, hover, Category.assoc, hbaseD]
  refine ⟨D', E',
      Over.homMk (ObjectProperty.homMk U.toBase : B.obj hUsize ⟶ D.left) rfl,
      Over.homMk (ObjectProperty.homMk V.toBase : B.obj hVsize ⟶ E.left) rfl,
      Over.homMk (ObjectProperty.homMk g : B.obj hUsize ⟶ B.obj hVsize) hk, U.point,
      U.etale_toBase, V.etale_toBase, ?_, U.map_point, hUaff, hVaff, hproj⟩
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp]
  change g ≫ V.toBase = U.toBase ≫ (BigFppfOver.toScheme B S hS).map h
  exact hover

/-- **Stacks Project, Tag 0CVY.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `F` be an `𝒪_X`-module and let `x` be a point of `|X|`. Assume

1. `f` is locally of finite presentation (`hfp`, Stacks 03XP part (1));
2. `F` is quasi-coherent and of finite presentation (`hqc`, `hFfp`), chartwise: its
   restriction to every étale scheme chart of `X` is;
3. `F` is flat at `x` over `Y` (`hflat`), chartwise: on every commuting square of étale charts
   and at every point of the source chart over `x`, the restriction of `F` to the source chart
   is flat over the target chart there.

Then there are an étale chart `U` of `X`, an étale chart `V` of `Y`, affine objects `X'`, `Y'`
of the site with étale morphisms `p : X' ⟶ U` and `q : Y' ⟶ V`, a morphism `k : X' ⟶ Y'` and a
point `x''` of `|X'|` such that the composites `X' → X` and `Y' → Y` are étale, the square
commutes over `f`, `x''` lies over `x`, its image in `|Y'|` lies over the image of `x`, and the
sections `Γ(X', p^*(F|_U))` form a projective `Γ(Y', 𝒪_{Y'})`-module.

The conclusion is the conclusion of Tag 0CVY, with no clause dropped, and nothing is assumed
beyond the tag's own hypotheses. The source's proof of Tag 0CVY is the remark that the
statement reduces to the case of schemes, Tag 05ID; that case, read inside the big fppf site,
is `AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections`. See the module
docstring on this, and on why the module of the conclusion is named as a pullback of a chart
restriction.

The hypotheses (2) and (3) are stated chartwise, which is how this development states these
conditions for a module on an algebraic space: compare
`AlgebraicGeometry.Space.IsFlatOver`, the definition of Stacks 05VV, which is the chartwise
condition on every commuting square of étale charts. They are not weakenings: the chartwise
form is one of the equivalent conditions of Stacks 05VU, which the source's definition
Stacks 05VV names.

Everything in the conclusion except the projectivity comes from
`AlgebraicGeometry.Space.exists_isAffine_etale_chart_square_at_point`, which is unconditional;
the hypotheses are used only to feed the case of schemes. -/
@[stacks 0CVY "the full conclusion — the pointed affine étale diagram and the projectivity of \
the sections — with the case of schemes, Tag 05ID, supplied by \
exists_isAffine_etale_hom_projective_sections, and with the tag's conditions (2) and (3) on \
the module in their étale-chartwise form"]
theorem exists_isAffine_etale_charts_projective_sections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X hX) (x : points B S hS X)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hqc : ∀ U : SmallEtale B S hS X, (restrictToChart B S hS hX F U).IsQuasicoherent)
    (hFfp : ∀ U : SmallEtale B S hS X, (restrictToChart B S hS hX F U).IsFinitePresentation)
    (hflat : ∀ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
      (x' : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))),
      U.obj.hom ≫ f = yoneda.map g ≫ V.obj.hom →
      pointsMap B S hS _ U.obj.hom x' = x →
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom)
        (restrictToChart B S hS hX F U) (pointsToScheme B S hS _ x')) :
    ∃ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (U' E' : BigFppfOver B S hS)
      (p : U' ⟶ (SmallEtale.toOver B S hS X).obj U)
      (q : E' ⟶ (SmallEtale.toOver B S hS Y).obj V) (k : U' ⟶ E')
      (x'' : points B S hS (yoneda.obj U')),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map p ≫ U.obj.hom) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ V.obj.hom) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj U') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj E') ∧
      (yoneda.map p ≫ U.obj.hom) ≫ f = yoneda.map k ≫ yoneda.map q ≫ V.obj.hom ∧
      pointsMap B S hS _ (yoneda.map p ≫ U.obj.hom) x'' = x ∧
      pointsMap B S hS _ (yoneda.map q ≫ V.obj.hom)
          (pointsMap B S hS _ (yoneda.map k) x'') = pointsMap B S hS X f x ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map p)).obj
           (restrictToChart B S hS hX F U)
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤)) := by
  classical
  obtain ⟨U, V, g, x', hUaff, hVaff, hsquare, hxpt, -⟩ :=
    exists_isAffine_etale_chart_square_at_point B S hS hX hY f x
  obtain ⟨D', E', p, q, k, d', hpE, hqE, hcomm, hd', hD'aff, hE'aff, hproj⟩ :=
    exists_isAffine_etale_hom_projective_sections B S hS _ _ g (restrictToChart B S hS hX F U)
      (pointsToScheme B S hS _ x')
      (hfp _ _ U.obj.hom V.obj.hom g U.property V.property hsquare.symm)
      (hqc U) (hFfp U) (hflat U V g x' hsquare hxpt)
  have hbase := pointsMap_yoneda_comp_pointsEquivScheme_symm B S hS p U.obj.hom d' _ x hd' hxpt
  have hsq : (yoneda.map p ≫ U.obj.hom) ≫ f =
      yoneda.map k ≫ yoneda.map q ≫ V.obj.hom := by
    rw [Category.assoc, hsquare, ← Category.assoc, ← yoneda.map_comp, ← hcomm,
      yoneda.map_comp, Category.assoc]
  refine ⟨U, V, D', E', p, q, k, (pointsEquivScheme B S hS D').symm d',
    etale_comp_of_scheme B S hS _ U.obj.hom hpE U.property,
    etale_comp_of_scheme B S hS _ V.obj.hom hqE V.property,
    hD'aff, hE'aff, hsq, hbase, ?_, hproj⟩
  rw [← Function.comp_apply (f := pointsMap B S hS _ (yoneda.map q ≫ V.obj.hom)),
    ← pointsMap_comp, ← hsq, pointsMap_comp, Function.comp_apply, hbase]

/-- **Stacks Project, Tag 0CVY.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`
which is locally of finite presentation, let `𝓕` be an `𝒪_X`-module which is quasi-coherent and
of finite presentation on every étale chart, and let `x` be a point of `X` at which `𝓕` is flat
over `Y`. Then `x` lies in the image of a commuting square of étale charts, refined by affine
objects `U'` of `X` and `E'` of `Y` of the site, through a point of `U'`, such that
`Γ(U', 𝓕|_{U'})` is a projective `Γ(E', 𝒪_{E'})`-module.

This is `AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections`, whose
proof feeds the case of schemes, Tag 05ID, through
`AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections`. -/
@[stacks 0CVY]
theorem exists_isAffine_etale_charts_projective_sections_of_isFlatOverAt
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X hX) (x : points B S hS X)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hqc : ∀ U : SmallEtale B S hS X, (restrictToChart B S hS hX F U).IsQuasicoherent)
    (hFfp : ∀ U : SmallEtale B S hS X, (restrictToChart B S hS hX F U).IsFinitePresentation)
    (hflat : ∀ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
      (x' : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))),
      U.obj.hom ≫ f = yoneda.map g ≫ V.obj.hom →
      pointsMap B S hS _ U.obj.hom x' = x →
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom)
        (restrictToChart B S hS hX F U) (pointsToScheme B S hS _ x')) :
    ∃ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (U' E' : BigFppfOver B S hS)
      (p : U' ⟶ (SmallEtale.toOver B S hS X).obj U)
      (q : E' ⟶ (SmallEtale.toOver B S hS Y).obj V) (k : U' ⟶ E')
      (x'' : points B S hS (yoneda.obj U')),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map p ≫ U.obj.hom) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ V.obj.hom) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj U') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj E') ∧
      (yoneda.map p ≫ U.obj.hom) ≫ f = yoneda.map k ≫ yoneda.map q ≫ V.obj.hom ∧
      pointsMap B S hS _ (yoneda.map p ≫ U.obj.hom) x'' = x ∧
      pointsMap B S hS _ (yoneda.map q ≫ V.obj.hom)
          (pointsMap B S hS _ (yoneda.map k) x'') = pointsMap B S hS X f x ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map p)).obj
           (restrictToChart B S hS hX F U)
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤)) :=
  exists_isAffine_etale_charts_projective_sections B S hS hX hY f F x hfp hqc hFfp hflat

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction

/-!
# The restriction to a chart is the restriction of the étale pullback at the identity chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `V` be an étale scheme
chart of `X`, with underlying object `A` of the big fppf category over `S`.  The restriction of
an `𝒪_X`-module to the Zariski site of the scheme of `V`, `restrictToChartScheme` at `V`, is the
same thing as pulling the module back along the structure morphism of `V` — an étale morphism of
algebraic spaces, so the pullback is restriction of sections — and then restricting the result to
the Zariski site of the scheme of `A` along the identity chart of `yoneda.obj A`.

Both readings restrict the sections of the module to the Zariski opens of the chart's scheme,
read as étale charts of `X` and of the chart space respectively, and extend scalars along the
same map; and the chart space is `yoneda.obj A` definitionally, by
`AlgebraicGeometry.Space.chartSpace_eq_yoneda`.  So the identity is an equality and not merely an
isomorphism, and its content is that the two index functors agree:
`AlgebraicGeometry.Space.openChartFunctor_idEtaleChart_comp_smallEtalePostcomp`.

## Main definitions

* `AlgebraicGeometry.Space.zariskiSheafify` is Zariski sheafification of a presheaf of modules on
  a scheme, and `AlgebraicGeometry.Space.chartZariskiPresheafOf` is the presheaf of sections on
  the Zariski opens of a chart, so that
  `AlgebraicGeometry.Space.restrictToChartScheme` is the former applied to the latter.
* `AlgebraicGeometry.Space.etalePresheafPullback` is the restriction of the sections of a
  presheaf of modules along postcomposition of étale charts with an étale morphism.

## Main results

* `AlgebraicGeometry.Space.openChartFunctor_idEtaleChart_comp_smallEtalePostcomp`: reading a
  Zariski open of the chart's scheme as an étale chart of the chart space and then composing
  with the structure morphism of the chart is reading it as an étale chart of `X`.
* `AlgebraicGeometry.Space.restrictToChartScheme_eq_atIdEtaleChart`: **the restriction of an
  `𝒪_X`-module to the scheme of an étale chart is the restriction, at the identity chart, of its
  étale pullback to the chart space.**

## Implementation notes

The equality of the two restrictions is *true* by `Eq.refl` and not *provable* by it: the two
sides differ by one collapse of a composite of two restrictions of sections into a restriction
along the composite index functor, and a blind definitional check unfolds the Zariski
sheafification on both sides before it gets there and exhausts the elaborator.  The proof
therefore performs the collapse explicitly, by `AlgebraicGeometry.Space.pushforward_comp_eq` —
Mathlib's `CategoryTheory.PresheafOfModules.pushforwardComp` read as the equality of functors
which it is, that isomorphism being `CategoryTheory.Iso.refl` — and keeps every other step a
definitional check between terms with the same head whose arguments match one by one.

`AlgebraicGeometry.Space.etalePresheafPullback` and
`AlgebraicGeometry.Space.chartZariskiPresheafOf` take their presheaf argument explicitly, rather
than being stated for modules, so that the steps compose by `congrArg` on a first-order function
rather than by a higher-order rewrite.

Both carry their `CategoryTheory.Category` instances as local instances introduced in the body:
the structure sheaf of a small étale ringed site is not reducible to the shape instance search
needs, the same workaround as in
`AlgebraicGeometry.Space.chartRestrictionPresheaf`.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

/-! ### Composing two restrictions of sections -/

/-- **A restriction of the sections of a presheaf of modules along a functor, followed by a
restriction along a second functor which extends scalars, is the restriction along the
composite.**

This is `CategoryTheory.PresheafOfModules.pushforwardComp` with the first change of scalars the
identity, read as the equality of functors which it is: that isomorphism is
`CategoryTheory.Iso.refl`. -/
theorem pushforward_id_comp_eq {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*}
    [Category E] {R : Eᵒᵖ ⥤ RingCat.{u}} {G : D ⥤ E} {P : Cᵒᵖ ⥤ RingCat.{u}} {K : C ⥤ D}
    (φ : P ⟶ K.op ⋙ (G.op ⋙ R)) :
    PresheafOfModules.pushforward.{v} (F := G) (𝟙 (G.op ⋙ R)) ⋙
        PresheafOfModules.pushforward.{v} (F := K) φ =
      PresheafOfModules.pushforward.{v} (F := K ⋙ G) φ :=
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two halves of the restriction to a chart's scheme -/

/-- Zariski sheafification of a presheaf of modules on a scheme. -/
noncomputable def zariskiSheafify (T : Scheme.{u})
    (P : PresheafOfModules.{u} T.ringCatSheaf.obj) : SheafOfModules.{u} T.ringCatSheaf := by
  let : HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact (PresheafOfModules.sheafification.{u} (𝟙 T.ringCatSheaf.obj)).obj P

/-- The sections of a presheaf of `𝒪_Y`-modules on the Zariski opens of an étale chart `U` of
`Y`, with scalars extended along
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`. -/
noncomputable def chartZariskiPresheafOf {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (U : SmallEtale B S hS Y)
    (Q : PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y hY).O)).obj) :
    PresheafOfModules.{u} (chartScheme U).ringCatSheaf.obj :=
  let catY : Category (PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y hY).O)).obj) :=
    inferInstance
  let catU : Category (PresheafOfModules.{u} (chartScheme U).ringCatSheaf.obj) := inferInstance
  @Functor.obj _ catY _ catU
    (PresheafOfModules.pushforward.{u} (chartSchemeRestrictionRingHom B S hS Y U)) Q

/-- **The restriction of a module to the scheme of an étale chart is the Zariski sheafification
of its sections on the Zariski opens of the chart.** -/
theorem restrictToChartScheme_eq_zariskiSheafify {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (U : SmallEtale B S hS Y)
    (N : Modules.{u, u} B S hS Y hY) :
    restrictToChartScheme B S hS Y hY N U =
      zariskiSheafify (chartScheme U)
        (chartZariskiPresheafOf B S hS hY U (SheafOfModules.uliftForPresentation N).val) :=
  rfl

/-! ### The étale pullback on presheaves -/

section Etale

variable {X' X : AlgebraicSpaces B S hS} (p : X' ⟶ X) (hp : IsEtale B S hS p.hom)

/-- The restriction of the sections of a presheaf of `𝒪_X`-modules along postcomposition of
étale charts of `X'` with an étale morphism `p : X' ⟶ X`: the sections over a chart of `X'` are
the sections over the composite chart of `X`.

This is `AlgebraicGeometry.Space.etaleModulePullback` on presheaves. -/
noncomputable def etalePresheafPullback
    (Q : PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj) :
    PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).obj :=
  let catX : Category (PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj) :=
    inferInstance
  let catX' : Category (PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).obj) :=
    inferInstance
  @Functor.obj _ catX _ catX'
    (PresheafOfModules.pushforward.{u} (F := smallEtalePostcomp B S hS p hp)
      (𝟙 ((smallEtalePostcomp B S hS p hp).op ⋙
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj))) Q

/-- Raising the universe of the sections commutes with the étale pullback: both leave the
underlying object of the site of a chart, and hence its ring of regular functions, unchanged. -/
theorem uliftForPresentation_etaleModulePullback_val (F : Modules.{u, u} B S hS X.1 X.2) :
    (SheafOfModules.uliftForPresentation ((etaleModulePullback B S hS p hp).obj F)).val =
      etalePresheafPullback B S hS p hp (SheafOfModules.uliftForPresentation F).val :=
  rfl

end Etale

/-! ### The identity chart of the chart space -/

section IdChart

variable (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1)

/-- **Reading a Zariski open of a chart's scheme as an étale chart of the chart space and then
composing with the structure morphism of the chart is reading it as an étale chart of `X`.**

This is the whole content of
`AlgebraicGeometry.Space.restrictToChartScheme_eq_atIdEtaleChart`, and it holds definitionally:
the structure morphism of the identity chart is an identity. -/
theorem openChartFunctor_idEtaleChart_comp_smallEtalePostcomp :
    openChartFunctor B S hS (chartSpace B S hS X V).1
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)) ⋙
        smallEtalePostcomp B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V) =
      openChartFunctor B S hS X.1 V :=
  rfl

/-- The sections on the Zariski opens of the identity chart of the chart space, of the étale
pullback of a presheaf, are its sections on the Zariski opens of the chart of `X`. -/
theorem chartZariskiPresheafOf_etalePresheafPullback
    (Q : PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj) :
    chartZariskiPresheafOf B S hS (chartSpace B S hS X V).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))
        (etalePresheafPullback B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V) Q) =
      chartZariskiPresheafOf B S hS X.2 V Q :=
  Functor.congr_obj
    (pushforward_id_comp_eq.{u, u}
      (R := ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj)
      (G := smallEtalePostcomp B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V))
      (K := openChartFunctor B S hS (chartSpace B S hS X V).1
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)))
      (chartSchemeRestrictionRingHom B S hS (chartSpace B S hS X V).1
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))))
    Q

/-- **The restriction of an `𝒪_X`-module to the scheme of an étale chart `V` is the restriction,
at the identity chart, of its étale pullback to the chart space.**

The chart space is the Yoneda algebraic space of the chart's object definitionally, and the two
restrictions read the sections on the same Zariski opens of the same scheme; the identity is the
agreement of the two index functors,
`AlgebraicGeometry.Space.openChartFunctor_idEtaleChart_comp_smallEtalePostcomp`. -/
theorem restrictToChartScheme_eq_atIdEtaleChart (F : Modules.{u, u} B S hS X.1 X.2) :
    restrictToChartScheme B S hS X.1 X.2 F V =
      restrictToChartScheme B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2
        ((etaleModulePullback B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).obj F)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)) := by
  have hP : chartZariskiPresheafOf B S hS (chartSpace B S hS X V).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))
        (SheafOfModules.uliftForPresentation
          ((etaleModulePullback B S hS (chartToSpace B S hS X V)
            (isEtale_chartToSpace B S hS X V)).obj F)).val =
      chartZariskiPresheafOf B S hS X.2 V (SheafOfModules.uliftForPresentation F).val := by
    rw [uliftForPresentation_etaleModulePullback_val]
    exact chartZariskiPresheafOf_etalePresheafPullback B S hS X V _
  exact (restrictToChartScheme_eq_zariskiSheafify B S hS X.2 V F).trans
    ((congrArg (zariskiSheafify (chartScheme V)) hP.symm).trans
      (restrictToChartScheme_eq_zariskiSheafify B S hS (chartSpace B S hS X V).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))
        ((etaleModulePullback B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).obj F)).symm)

end IdChart

end AlgebraicGeometry.Space

end

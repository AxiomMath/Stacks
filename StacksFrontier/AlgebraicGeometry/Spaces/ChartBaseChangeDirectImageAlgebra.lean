module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeDirectImageAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction

/-!
# The direct-image algebra of a representable morphism is base change of étale scheme charts

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  `AlgebraicGeometry.Space.chartRanIso` identifies the direct image of
sheaves of *sets* along `f` with restriction along base change of étale scheme charts, and
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso` identifies the structure map `f♯` of
Stacks 03G8 with pullback of regular functions along the cartesian projections `V ×_Y X ⟶ V`.
Both are statements about sheaves of *rings*.

This file carries them to sheaves of commutative rings and then to the direct-image **algebra**
`f_*𝒪_X` of Stacks 03G8: for a representable morphism,

`f_*𝒪_X = (V ↦ Γ(V ×_Y X, 𝒪))` as a sheaf of commutative `𝒪_Y`-algebras,

the structure-algebra map being pullback along the cartesian projection.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeAlgebra` is the right-hand side: the restriction of
  `𝒪_X` along `AlgebraicGeometry.Space.smallBaseChange`, with
  `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat` as its structure-algebra map.
* `AlgebraicGeometry.Space.pushforwardAlgebraChartRingIso` is the comparison of the underlying
  sheaves of commutative rings.

## Main results

* `AlgebraicGeometry.Space.hom_comp_pushforwardAlgebraChartRingIso`: the comparison carries the
  structure-algebra map of `f_*𝒪_X` to pullback along the cartesian projections.
* `AlgebraicGeometry.Space.pushforwardAlgebraChartIso`: **the direct-image algebra of a
  representable morphism of algebraic spaces is the restriction of the structure sheaf of the
  source along base change of étale scheme charts, as an algebra.**
* `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraChartIso` and
  `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraChartIso_sections`: the same read on the
  Zariski site of an étale scheme chart `V` of `Y`, where the sections over a Zariski open `O`
  of `chartScheme V` are the regular functions on the base change of the chart that `O` cuts
  out.

## Implementation notes

**What this supplies for Definition 0822, and what it does not.**  The two clauses of
Definition 0822 that remain open — that `ν_*𝒪_{X'}` is `𝒪'` and that `f` factors through `ν` —
were reduced, in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn`, to rewriting the chart restriction of a
direct image as a direct image along a base change: Stacks 04CF is proved for the chart
restriction of a direct-image algebra
(`AlgebraicGeometry.Space.pushforwardAlgebraRight_overPullbackIso`), but its target is the
localized direct image along the base-changed morphism of *sites*, over
`AlgebraicGeometry.Space.chartBaseChange`, an object of
`AlgebraicGeometry.Space.SpacesEtale`.

This file supplies that rewriting **for a representable morphism**, and in that case the base
change is an étale *scheme* chart rather than an object of the spaces-étale site, so no
comparison of the two sites is needed at all: the localized direct image is replaced by
restriction along `AlgebraicGeometry.Space.smallBaseChange`, which is a functor of small étale
sites.  That is the generality the two clauses need for the morphism `ν`, which is affine by
`AlgebraicGeometry.Space.isAffineHom_chartRelativeSpecQuotientHom` and therefore representable,
and for the morphism `w` of schemes out of a scheme chart of `Y ×_X V₂`.

It is **not** the general case, and the general case is not an oversight.  A quasi-compact
quasi-separated morphism of algebraic spaces is not representable, so for the morphism `f` of
Definition 0822 itself the sections of `f_*𝒪_Y` over a chart are a limit over *all* étale scheme
charts above `Y ×_X V` with no initial object
(`AlgebraicGeometry.Space.chartIsLimit`), and nothing here applies.  Rewriting
`AlgebraicGeometry.Space.chartLocalizedCommRingDirectImage` for such an `f` as
`AlgebraicGeometry.Space.pushforwardAlgebra` of the base-changed morphism of *spaces* needs the
slice of the spaces-étale site at `Y ×_X V` to be identified with the small étale site of the
algebraic space `Y ×_X V`; the two halves of that identification are available as equivalences
of sites (`AlgebraicGeometry.Space.SpacesEtale.sliceEquivSmall` and
`AlgebraicGeometry.Space.comparisonFunctor`) but only at `Type (u + 1)`, while the sheaves of
rings here live at `Type u`, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineChartLocality` record.  That
universe gap is untouched by this file.

**Where the Zariski site still intervenes, and what is now available there.**  What
`AlgebraicGeometry.Space.chartRelativeSpecLift` consumes is a map into the *scheme-level*
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra` of a morphism of schemes
`w : W ⟶ chartScheme V`, i.e. a sheaf on the Zariski site of `chartScheme V`.  The last
declaration below restricts the comparison to that site and computes its sections, and the
sections it produces over a Zariski open `O` are the regular functions on `(openChart V O) ×_Y X`,
the base change of the chart `O` cuts out, whereas `w_*𝒪_W` has the regular functions on
`w^{-1}O`.

**The interchange identifying the two is now proved**, in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenInterchange`: `(openChart V O) ×_Y X`
is the open chart of `V ×_Y X` that `O` pulls back to, by
`AlgebraicGeometry.Space.smallBaseChangeOpenChartIso`, cartesian over both projections and
natural in the open — `AlgebraicGeometry.Space.smallBaseChangeOpenChartFunctorIso` states it as
an isomorphism of the two functors `(chartScheme V).Opens ⥤ SmallEtale B S hS X.1`, which is the
form a sheaf on the Zariski site of the chart consumes.  As predicted it is uniqueness of fibre
products: `AlgebraicGeometry.Space.isPullback_openSubHomOfRestrict`, generalised in place in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenChartCovering` to an arbitrary morphism
of the big fppf category over `S`, pasted under the cartesian square of the representability
witness.

**The assembly is** in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeDirectImageAlgebraPushforward`:
`AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso` is
`chartSchemeDirectImageAlgebra B S hS Y (Over.mk f) V ≅
Stacks.AffineAlgebraEquivalence.pushforwardAlgebra (smallBaseChangeSchemeProjection B S hS f hf V)`
as an isomorphism of sheaves of *algebras*.  Its sheaf-of-commutative-rings half is mechanical —
the presheaf underlying the left-hand side is
`(openChartFunctor V ⋙ smallBaseChange f hf).op ⋙ structurePresheaf X.1`, which
`AlgebraicGeometry.Space.smallBaseChangeOpenChartFunctorIso` carries to
`(Opens.map q.base ⋙ openChartFunctor (V ×_Y X)).op ⋙ structurePresheaf X.1`, and
`AlgebraicGeometry.Space.openChartFunctor_comp_toScheme` — an *equality* of functors — turns the
second factor into `((chartScheme (V ×_Y X)).restrictFunctor ⋙ Over.forget _).op ⋙ Scheme.Γ`,
which `AlgebraicGeometry.Scheme.restrictFunctorΓ` identifies with the structure presheaf of the
chart scheme.  The `CategoryTheory.Under` half — that the structure-algebra map
`AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat`, restricted to the chart and read
through those identifications, is the comorphism `q.c` of the cartesian projection — is
`AlgebraicGeometry.Space.hom_comp_chartBaseChangeAlgebraPushforwardRingIso`, and it needs no new
geometry either: over a Zariski open it is
`AlgebraicGeometry.Space.smallBaseChangeOpenChartLeftIso_hom_comp_projection` followed by
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict`.

**Why the comparison is assembled from two general transports rather than written out.**  The
sections of `f_*𝒪_X` over a chart carry the commutative ring structure *transported* along the
direct image, in the sense of `Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf`, while the
sections of the restriction along `AlgebraicGeometry.Space.smallBaseChange` carry the ring
structure of `𝒪_X` itself.  Those are two structures on types that are not the same structure,
so the comparison cannot be the identity map; the two general facts that make it one anyway are
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCongr`, which transports the inverse image of
a sheaf of commutative rings along a natural isomorphism of the inverse-image functors of
sheaves of sets, and `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which says that the
transport along a restriction functor *is* restriction.  Both are the identity on underlying
sheaves of sets, which is what makes the structure-map identity below reduce to the ring-level
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`.

**No `stacks` attribute is carried.**  Stacks 04CF is registered on
`AlgebraicGeometry.Space.commRingDirectImage_comp_overPullbackIso`, for an arbitrary morphism
and with the restriction taken on the slice of the spaces-étale site, and Stacks 03G8 part (2)
on `AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage`.  What is added
here is the algebra-level reading of the representable case, which is the assertion of neither.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange
attribute [local instance]
  AlgebraicGeometry.Space.preservesFiniteProducts_smallBaseChange_sheafPushforwardContinuous

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The restriction of the structure sheaf along chart base change, as an algebra -/

/-- The restriction of `𝒪_X` along base change of étale scheme charts, read as a sheaf of
commutative `𝒪_Y`-algebras: over an étale chart `V` of `Y` its sections are the regular
functions on the base-changed chart `V ×_Y X`, and its structure-algebra map is pullback of
regular functions along the cartesian projection `V ×_Y X ⟶ V`. -/
def chartBaseChangeAlgebra (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    AlgebraSheaf.{u, u} B S hS Y.1 Y.2 :=
  AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS f hf)

/-- The underlying sheaf of commutative rings of `AlgebraicGeometry.Space.chartBaseChangeAlgebra`
is the pushforward of `𝒪_X` along base change of étale scheme charts. -/
@[simp]
theorem chartBaseChangeAlgebra_right (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (chartBaseChangeAlgebra B S hS f hf).right =
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (structureSheaf B S hS X.1 X.2) :=
  rfl

/-- The sections of `AlgebraicGeometry.Space.chartBaseChangeAlgebra` over an étale chart `V` of
`Y` are the sections of `𝒪_X` over the base-changed chart `V ×_Y X`. -/
theorem chartBaseChangeAlgebra_sections (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (chartBaseChangeAlgebra B S hS f hf).right.obj.obj (op V) =
      (structureSheaf B S hS X.1 X.2).obj.obj (op ((smallBaseChange B S hS f hf).obj V)) :=
  rfl

/-! ### The comparison -/

/-- **The comparison of the underlying sheaves of commutative rings.**  For a representable
morphism the direct image `f_*𝒪_X` of Stacks 03G8 is the restriction of `𝒪_X` along base change
of étale scheme charts.

It is the transport of `AlgebraicGeometry.Space.chartRanIso`, the same statement for sheaves of
sets, along `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCongr`, followed by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which identifies the transported ring
structure of a restriction with the restricted ring structure.  Both steps are the identity on
underlying sheaves of sets. -/
def pushforwardAlgebraChartRingIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (pushforwardAlgebra B S hS (Over.mk f)).right ≅
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (structureSheaf B S hS X.1 X.2) :=
  pullbackCommRingSheafCongr.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
      (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf)
      (structureSheaf B S hS X.1 X.2) ≪≫
    restrictionCommRingIso.{u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1)
      (smallBaseChange B S hS f hf) (structureSheaf B S hS X.1 X.2)

/-- Forgetting commutativity, the comparison is the ring-level comparison
`AlgebraicGeometry.Space.chartRingSheafMap` followed by
`Stacks.Sheaves.ToposPullback.restrictionRingIso`: both transports are the identity on
underlying sheaves of sets, so nothing is lost in forgetting commutativity. -/
theorem forgetCommRingSheaf_map_pushforwardAlgebraChartRingIso_hom (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (pushforwardAlgebraChartRingIso B S hS f hf).hom =
      chartRingSheafMap B S hS f hf ≫
        (restrictionRingIso (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)
          (structureRingSheaf B S hS X)).hom :=
  rfl

/-- The structure-algebra map of the direct-image algebra is the structure map `f♯` of the
morphism of small étale ringed topoi of Stacks 03G8: the algebra is built from `f♯` by
`AlgebraicGeometry.Space.AlgebraSheaf.ofHom`, so this needs no computation. -/
theorem pushforwardAlgebra_hom {Z : AlgebraicSpaces B S hS} (T : Over Z) :
    (pushforwardAlgebra B S hS T).hom = (smallEtaleRingedToposHom B S hS T.hom).fSharp :=
  rfl

/-- **The comparison carries the structure-algebra map of `f_*𝒪_X` to pullback of regular
functions along the cartesian projections.**

This is `AlgebraicGeometry.Space.structureSharp_comp_chartRanIso` — the same identity for
sheaves of rings — read on sheaves of commutative rings, which is legitimate because forgetting
commutativity is fully faithful on sheaves
(`Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf`).  The structure-algebra map of
`f_*𝒪_X` is `AlgebraicGeometry.Space.structureSharp` after that forgetting, by
`AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp`; it cannot be identified with it
before, `AlgebraicGeometry.Space.structureSharpCommRing` being irreducible. -/
theorem hom_comp_pushforwardAlgebraChartRingIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (pushforwardAlgebra B S hS (Over.mk f)).hom ≫
        (pushforwardAlgebraChartRingIso B S hS f hf).hom =
      smallBaseChangeSharpCommRingCat B S hS f hf := by
  have : (sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).Faithful :=
    (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
      (SmallEtale.topology B S hS Y.1)).faithful
  refine (sheafCompose (SmallEtale.topology B S hS Y.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map_injective ?_
  rw [Functor.map_comp, forgetCommRingSheaf_map_pushforwardAlgebraChartRingIso_hom]
  exact (congrArg (· ≫ _) (forgetCommRingSheaf_map_fSharp B S hS f)).trans
    (structureSharp_comp_chartRanIso B S hS f hf)

/-- The structure-algebra map identity of
`AlgebraicGeometry.Space.hom_comp_pushforwardAlgebraChartRingIso`, read on sections over an
étale chart of `Y`. -/
theorem pushforwardAlgebraChartRingIso_algebraMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (r : (structureSheaf B S hS Y.1 Y.2).obj.obj U) :
    ((pushforwardAlgebraChartRingIso B S hS f hf).hom.hom.app U).hom
        ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap U r) =
      (chartBaseChangeAlgebra B S hS f hf).algebraMap U r :=
  ConcreteCategory.congr_hom
    (congrArg (fun m : structureSheaf B S hS Y.1 Y.2 ⟶
        ((smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
          (structureSheaf B S hS X.1 X.2) => m.hom.app U)
      (hom_comp_pushforwardAlgebraChartRingIso B S hS f hf)) r

/-- **The direct-image algebra of a representable morphism of algebraic spaces is the
restriction of the structure sheaf of the source along base change of étale scheme charts.**

For a representable `f : X ⟶ Y` the sheaf of commutative `𝒪_Y`-algebras `f_*𝒪_X` of Stacks 03G8
is `V ↦ Γ(V ×_Y X, 𝒪)`, with structure-algebra map pullback of regular functions along the
cartesian projection `V ×_Y X ⟶ V`. -/
def pushforwardAlgebraChartIso (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    pushforwardAlgebra B S hS (Over.mk f) ≅ chartBaseChangeAlgebra B S hS f hf where
  hom :=
    { right := (pushforwardAlgebraChartRingIso B S hS f hf).hom
      comm := pushforwardAlgebraChartRingIso_algebraMap B S hS f hf }
  inv :=
    { right := (pushforwardAlgebraChartRingIso B S hS f hf).inv
      comm := fun U r => by
        rw [← pushforwardAlgebraChartRingIso_algebraMap B S hS f hf U r]
        exact ConcreteCategory.congr_hom
          (congrArg (fun m : (pushforwardAlgebra B S hS (Over.mk f)).right ⟶
              (pushforwardAlgebra B S hS (Over.mk f)).right => m.hom.app U)
            (pushforwardAlgebraChartRingIso B S hS f hf).hom_inv_id)
          ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap U r) }
  hom_inv_id :=
    AlgebraSheaf.Hom.ext (pushforwardAlgebraChartRingIso B S hS f hf).hom_inv_id
  inv_hom_id :=
    AlgebraSheaf.Hom.ext (pushforwardAlgebraChartRingIso B S hS f hf).inv_hom_id

/-! ### On the Zariski site of an étale scheme chart -/

/-- **The chart-scheme restriction of the direct-image algebra of a representable morphism.**
This is `AlgebraicGeometry.Space.pushforwardAlgebraChartIso` restricted to the Zariski site of
an étale scheme chart `V` of `Y`. -/
def chartSchemeDirectImageAlgebraChartIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    chartSchemeDirectImageAlgebra B S hS Y (Over.mk f) V ≅
      chartSchemeAlgebra B S hS Y (chartBaseChangeAlgebra B S hS f hf) V :=
  (chartSchemeAlgebraFunctor B S hS Y V).mapIso (pushforwardAlgebraChartIso B S hS f hf)

/-- The sections over a Zariski open `O` of `chartScheme V` of the chart-scheme restriction of
`f_*𝒪_X`, for a representable `f`, are the regular functions on the base change along `f` of the
étale chart that `O` cuts out.

This is the computation `AlgebraicGeometry.Space.chartSchemeAlgebra_sections` at the right-hand
side of `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraChartIso`; see the implementation
notes for what still separates it from the scheme-level `w_*𝒪_W` of a morphism of schemes. -/
theorem chartSchemeDirectImageAlgebraChartIso_sections (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (O : (chartScheme V).Opens) :
    (chartSchemeAlgebra B S hS Y (chartBaseChangeAlgebra B S hS f hf) V).sections O =
      (structureSheaf B S hS X.1 X.2).obj.obj
        (op ((smallBaseChange B S hS f hf).obj (openChart B S hS Y.1 V O))) :=
  rfl

end AlgebraicGeometry.Space

end

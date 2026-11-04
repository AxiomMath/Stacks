module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.StructureSheafLocalizationPushforward

/-!
# The comparison of sheaves of meromorphic functions along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` for which
pullbacks of meromorphic functions are defined, in the sense of
`AlgebraicGeometry.Space.PullbacksMeromorphicSections` (Stacks 0EN8).  Base change of étale
scheme charts along `f` is a continuous functor `Y_étale ⥤ X_étale` (Stacks 03G2, part (4)), so
restriction along it carries sheaves on the small étale site of `X` to sheaves on that of `Y`;
write `f_*` for that direct image.  This file builds the comparison

`𝒦_Y ⟶ f_* 𝒦_X`

of sheaves of meromorphic functions, and shows it is the unique morphism of sheaves of rings
lying over the structure map `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X` of small-chart base change.

That structure map is `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat`: over a chart
`V` of `Y` it is pullback of functions along the cartesian projection `V ×_Y X ⟶ V`.  The
hypothesis on `f` says exactly that it carries the regular sections `𝒮_Y(V)` into
`𝒮_X(V ×_Y X)`, so the comparison is the functoriality of the sheafified localization of
Stacks 0EMC, `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap`,
applied to the small étale ringed sites and to the multiplicative subpresheaves of regular
sections.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeChartDiagram` is the commuting square of étale charts
  formed by a chart of `Y` and its base change.
* `AlgebraicGeometry.Space.meromorphicFunctionSheafPullback` is the comparison
  `𝒦_Y ⟶ f_* 𝒦_X`.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMapOfContinuous` is
  the functoriality of the sheafified localization with continuity of the functor taken as an
  explicit argument rather than as an instance.

## Main results

* `AlgebraicGeometry.Space.le_comap_smallBaseChangeSharpCommRingCat`: the structure map of
  small-chart base change carries regular sections to regular sections.  This is the whole
  arithmetic content, and it is the hypothesis of Stacks 0EN8 verbatim.
* `AlgebraicGeometry.Space.smallBaseChangeSharp_comp_meromorphicFunctionSheafPullback`: the
  square relating the two maps `𝒪 ⟶ 𝒦` to the structure map and to the comparison commutes, and
  `AlgebraicGeometry.Space.meromorphicFunctionSheafPullback_app_toMeromorphicFunctionSheaf` is
  the same statement on sections.
* `AlgebraicGeometry.Space.meromorphicFunctionSheafPullback_unique`: that square determines the
  comparison uniquely, so it is *the* morphism of sheaves of rings over `f^♯`.

## Implementation notes

The route through the universal property of the sheafified localization is taken because the
chartwise fraction rule `a/b ↦ f^♯a/f^♯b` of
`AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions` is a map out of the *presheaf*
`𝒮_Y⁻¹𝒪_Y`, and turning such an `f`-map into a homomorphism into the direct image needs
`AlgebraicGeometry.Space.chartCorrespondence` (Stacks 03G4) for a presheaf source, which is
available only for a sheaf.  The universal property needs no `f`-map at all: only a morphism of
*sheaves* `𝒪_Y ⟶ f_* 𝒪_X` carrying `𝒮_Y` into `𝒮_X`, which is what the structure map of
small-chart base change already is.

Continuity of base change is taken as an *explicit* argument of
`localizationSheafMapOfContinuous`, and the two ringed sites are passed by name at the
application site.  Both are needed.  Continuity of base change is a theorem rather than an
instance, and the topology of a ringed site is reached only through the site's projection, so
instance search at such an application has to reconcile
`(smallEtaleRingedSite B S hS Y.1 Y.2).J` with `AlgebraicGeometry.Space.SmallEtale.topology`;
with the ringed sites left to be inferred as well, that defeq problem exhausts the heartbeat
limit, and with them supplied the search simply fails, since the registered form of the
hypothesis is keyed on the second spelling.  With both supplied the construction elaborates in
seconds.

The chart diagram of a base-changed chart has the representability square `hr.w` as its
commutativity on the nose: the chart of `X` underlying it is the base-changed chart, whose
structure morphism *is* the first projection, so no transport along an identification of
objects is involved.

Both sheaves of meromorphic functions are taken at the universe of the schemes, which is where
sheafification of presheaves of commutative rings on the small étale site is available.

## References

* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ v₃ v₄ w u

namespace AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

section ExplicitContinuity

variable {A : RingedSite.{v₁, v₂, w}} {C : RingedSite.{v₃, v₄, w}}
  [HasWeakSheafify A.J CommRingCat.{w}] [HasWeakSheafify C.J CommRingCat.{w}]
  (T : MultiplicativeSubpresheaf A) (F : A.C ⥤ C.C) (hF : F.IsContinuous A.J C.J)
  (U : MultiplicativeSubpresheaf C)
  (φ : A.O ⟶ (letI := hF; F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).obj C.O)
  (hφ : ∀ V, T.obj V ≤ (U.obj (F.op.obj V)).comap (φ.hom.app V).hom)

/-- **The sheafified localization is functorial along a continuous functor**, with continuity
taken as an explicit argument.

This is `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap`, whose
continuity hypothesis is an instance.  Continuity of a functor between the small étale sites of
algebraic spaces is a theorem rather than an instance, and leaving the hypothesis to instance
search at such an application makes the elaborator reconcile the topology of a ringed site with
its own spelling while the search is still open, which exhausts the heartbeat limit. -/
noncomputable def localizationSheafMapOfContinuous :
    (presheafToSheaf A.J CommRingCat.{w}).obj T.localizationPresheaf ⟶
      (letI := hF; F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).obj
        ((presheafToSheaf C.J CommRingCat.{w}).obj U.localizationPresheaf) :=
  letI := hF
  T.localizationSheafMap F U φ hφ

/-- The induced morphism lies over `φ`, on sections: localizing a section of `A.O` over `V` and
then applying it is applying `φ` and then localizing over `F V`. -/
theorem localizationSheafMapOfContinuous_app_toLocalizationSheaf (V : A.Cᵒᵖ)
    (r : A.O.obj.obj V) :
    ((localizationSheafMapOfContinuous T F hF U φ hφ).hom.app V).hom
        ((T.toLocalizationSheaf.hom.app V).hom r) =
      (U.toLocalizationSheaf.hom.app (F.op.obj V)).hom ((φ.hom.app V).hom r) :=
  let := hF
  T.localizationSheafMap_app_toLocalizationSheaf F U φ hφ V r

/-- The induced morphism lies over `φ`: the square relating the two localization maps
`𝒪 ⟶ 𝒪⁻¹` to `φ` and to the induced morphism commutes. -/
theorem localizationSheafMapOfContinuous_comp :
    T.toLocalizationSheaf ≫ localizationSheafMapOfContinuous T F hF U φ hφ =
      φ ≫ (letI := hF; F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).map
        U.toLocalizationSheaf :=
  let := hF
  T.localizationSheafMap_comp F U φ hφ

/-- The induced morphism is the only morphism of sheaves of rings lying over `φ`. -/
theorem localizationSheafMapOfContinuous_unique
    (g : (presheafToSheaf A.J CommRingCat.{w}).obj T.localizationPresheaf ⟶
      (letI := hF; F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).obj
        ((presheafToSheaf C.J CommRingCat.{w}).obj U.localizationPresheaf))
    (hg : T.toLocalizationSheaf ≫ g =
      φ ≫ (letI := hF; F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).map
        U.toLocalizationSheaf) :
    g = localizationSheafMapOfContinuous T F hF U φ hφ :=
  let := hF
  T.localizationSheafMap_unique F U φ hφ g hg

end ExplicitContinuity

end AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hr : yoneda.relativelyRepresentable f.hom)

/-- The commuting square of étale charts formed by a chart `V` of `Y` and its base change along
a representable morphism: the chart of `X` is the base-changed chart, the vertical morphism is
the cartesian projection `V ×_Y X ⟶ V`, and the square commutes because it is the
representability square of `f` at `V`. -/
noncomputable def baseChangeChartDiagram (V : SmallEtale B S hS Y.1) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := (smallBaseChange B S hS f hr).obj V
  V := V
  g := hr.snd V.1.hom
  comm := hr.w V.1.hom

/-- **The structure map of small-chart base change carries regular sections to regular
sections**, when pullbacks of meromorphic functions are defined for `f`.  This is the hypothesis
of Stacks 0EN8 applied to the commuting square of a chart and its base change, and it is what
makes the comparison of sheaves of meromorphic functions exist. -/
theorem le_comap_smallBaseChangeSharpCommRingCat
    (hf : PullbacksMeromorphicSections B S hS f.hom) (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (regularSectionsSubpresheaf B S hS Y.1 Y.2).obj V ≤
      ((regularSectionsSubpresheaf B S hS X.1 X.2).obj
          ((smallBaseChange B S hS f hr).op.obj V)).comap
        ((smallBaseChangeSharpCommRingCat B S hS f hr).hom.app V).hom :=
  fun s hs => hf (baseChangeChartDiagram B S hS f hr V.unop) s hs

/-- **The comparison `𝒦_Y ⟶ f_* 𝒦_X` of sheaves of meromorphic functions.**  When pullbacks of
meromorphic functions are defined for a representable morphism `f : X ⟶ Y` of algebraic spaces,
the structure map of small-chart base change extends to the sheaves of meromorphic functions:
over a chart `V` of `Y` the fraction `a/b` with regular denominator goes to `f^♯a/f^♯b`, which
is defined because `f^♯b` is again regular. -/
noncomputable def meromorphicFunctionSheafPullback
    (hf : PullbacksMeromorphicSections B S hS f.hom) :
    meromorphicFunctionSheaf B S hS Y.1 Y.2 ⟶
      ((smallBaseChange B S hS f hr).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (meromorphicFunctionSheaf B S hS X.1 X.2) :=
  RingedSite.MultiplicativeSubpresheaf.localizationSheafMapOfContinuous
    (A := smallEtaleRingedSite B S hS Y.1 Y.2) (C := smallEtaleRingedSite B S hS X.1 X.2)
    (regularSectionsSubpresheaf B S hS Y.1 Y.2) (smallBaseChange B S hS f hr)
    (isContinuous_smallBaseChange B S hS f hr) (regularSectionsSubpresheaf B S hS X.1 X.2)
    (smallBaseChangeSharpCommRingCat B S hS f hr)
    (le_comap_smallBaseChangeSharpCommRingCat B S hS f hr hf)

/-- **The comparison lies over the structure map, on sections.**  Regarding a function on a chart
`V` of `Y` as meromorphic and then applying the comparison is pulling it back along the
cartesian projection and then regarding it as meromorphic. -/
theorem meromorphicFunctionSheafPullback_app_toMeromorphicFunctionSheaf
    (hf : PullbacksMeromorphicSections B S hS f.hom) (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (r : (structurePresheaf B S hS Y.1).obj V) :
    ((meromorphicFunctionSheafPullback B S hS f hr hf).hom.app V).hom
        (((toMeromorphicFunctionSheaf B S hS Y.1 Y.2).hom.app V).hom r) =
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app
          ((smallBaseChange B S hS f hr).op.obj V)).hom
        (((smallBaseChangeSharpCommRingCat B S hS f hr).hom.app V).hom r) :=
  RingedSite.MultiplicativeSubpresheaf.localizationSheafMapOfContinuous_app_toLocalizationSheaf
    (A := smallEtaleRingedSite B S hS Y.1 Y.2) (C := smallEtaleRingedSite B S hS X.1 X.2)
    _ _ (isContinuous_smallBaseChange B S hS f hr) _ _
    (le_comap_smallBaseChangeSharpCommRingCat B S hS f hr hf) V r

/-- **The comparison lies over the structure map.**  The square relating the two maps `𝒪 ⟶ 𝒦` to
the structure map of small-chart base change and to the comparison of sheaves of meromorphic
functions commutes. -/
theorem smallBaseChangeSharp_comp_meromorphicFunctionSheafPullback
    (hf : PullbacksMeromorphicSections B S hS f.hom) :
    toMeromorphicFunctionSheaf B S hS Y.1 Y.2 ≫ meromorphicFunctionSheafPullback B S hS f hr hf =
      smallBaseChangeSharpCommRingCat B S hS f hr ≫
        ((smallBaseChange B S hS f hr).sheafPushforwardContinuous CommRingCat.{u}
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).map
          (toMeromorphicFunctionSheaf B S hS X.1 X.2) :=
  RingedSite.MultiplicativeSubpresheaf.localizationSheafMapOfContinuous_comp
    (A := smallEtaleRingedSite B S hS Y.1 Y.2) (C := smallEtaleRingedSite B S hS X.1 X.2)
    _ _ (isContinuous_smallBaseChange B S hS f hr) _ _
    (le_comap_smallBaseChangeSharpCommRingCat B S hS f hr hf)

/-- **The comparison is the only morphism over the structure map.**  Any morphism of sheaves of
rings `𝒦_Y ⟶ f_* 𝒦_X` making the square of
`AlgebraicGeometry.Space.smallBaseChangeSharp_comp_meromorphicFunctionSheafPullback` commute is
the comparison, by the universal property of the sheafified localization. -/
theorem meromorphicFunctionSheafPullback_unique
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (g : meromorphicFunctionSheaf B S hS Y.1 Y.2 ⟶
      ((smallBaseChange B S hS f hr).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (meromorphicFunctionSheaf B S hS X.1 X.2))
    (hg : toMeromorphicFunctionSheaf B S hS Y.1 Y.2 ≫ g =
      smallBaseChangeSharpCommRingCat B S hS f hr ≫
        ((smallBaseChange B S hS f hr).sheafPushforwardContinuous CommRingCat.{u}
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).map
          (toMeromorphicFunctionSheaf B S hS X.1 X.2)) :
    g = meromorphicFunctionSheafPullback B S hS f hr hf :=
  RingedSite.MultiplicativeSubpresheaf.localizationSheafMapOfContinuous_unique
    (A := smallEtaleRingedSite B S hS Y.1 Y.2) (C := smallEtaleRingedSite B S hS X.1 X.2)
    _ _ (isContinuous_smallBaseChange B S hS f hr) _ _
    (le_comap_smallBaseChangeSharpCommRingCat B S hS f hr hf) g hg

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullbacks of meromorphic functions along a morphism of algebraic spaces

Pullbacks of meromorphic functions are *defined* for a morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S` when, for every commuting square of étale charts `U` of `X` over `V` of `Y`,
the pullback along the underlying morphism of schemes carries the regular sections of `𝒪_Y` over
`V` to regular sections of `𝒪_X` over `U`.  This is what is needed for the sheaf of meromorphic
functions to be functorial, since `𝒦` is built by inverting exactly those sections.

Flatness is sufficient: the underlying morphism of schemes of every commuting square of charts
of a flat morphism is flat, and pullbacks of meromorphic functions are defined along a flat
morphism of schemes.

When the condition holds, a fraction `a/b` over a chart `V` of `Y` with regular denominator
pulls back to the fraction `f^♯a/f^♯b` over a chart `U` of `X` above it: the pulled back
denominator is again regular, hence again invertible.  These chartwise maps on the sectionwise
localizations are compatible with étale restriction of both charts, so they form an `f`-map in
the sense of Stacks 03G3.

## Main definitions

* `AlgebraicGeometry.Space.PullbacksMeromorphicSections` is the condition of Stacks 0EN8.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions` is the fraction rule
  `a/b ↦ f^♯a/f^♯b` on the sectionwise localizations over a chart diagram, and
  `AlgebraicGeometry.Space.fmapMeromorphicFunctions` is the `f`-map of Stacks 03G3 they form.

## Main results

* `AlgebraicGeometry.Space.pullbacksMeromorphicSections_of_flat` is Stacks 0EN9, part (2):
  pullbacks of meromorphic functions are defined along a flat morphism.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_mk'` is the fraction rule in
  closed form, and `AlgebraicGeometry.Space.isUnit_chartPullbackMeromorphicFunctions` says a
  regular denominator stays invertible after pullback.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_comp` is the compatibility with
  étale restriction of the two charts.

## Implementation notes

Both the condition and flatness are conditions on the commuting squares of étale charts, so
neither needs the algebraicity of the source and target: both are stated for arbitrary
presheaves on the big fppf site of `S`, which is how Stacks 0EN8 and 0EN9 are applied.  The
fraction rule, on the other hand, is a map between the sectionwise localizations
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationPresheaf` of Stacks 0EMC,
which are indexed by the ringed site, so there the algebraicity is carried.

The squares are indexed by `AlgebraicGeometry.Space.ChartDiagram`, the commuting squares of
Stacks 03G3, and regularity over a chart is
`AlgebraicGeometry.Space.IsRegularSection`; the pullback on sections over the charts is the
map on global sections of the scheme morphism in the square.

The comparison `𝒦_Y ⟶ f_*𝒦_X` of sheaves of meromorphic functions, which the text after
Stacks 0EN8 asserts and which Stacks 0ENC consumes, is built from the fraction rule in
`AlgebraicGeometry.Space.meromorphicFunctionSheafComparison`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicFunctionsComparison.lean`): the sections of
the direct image over a chart of `Y` are a limit over chart diagrams, so the chartwise rule
assembles into a map out of the presheaf `𝒮_Y⁻¹𝒪_Y`, which sheafification extends to `𝒦_Y`.

That comparison is read back chartwise in
`AlgebraicGeometry.Space.chartMeromorphicFunctionPullback`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicFunctionsChartPullback.lean`), giving the
fraction rule of this file on the *sheaves*: a homomorphism `𝒦_Y(V) ⟶ 𝒦_X(U)` over a chart
diagram, again for an arbitrary `f`.

Of Stacks 0ENC itself, the global pullback map `Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F))` of part (1) is
proved for `𝒦(F)` read as the *first* of the two descriptions in Stacks 0EN5 — the
sheafification of the presheaf of sectionwise localizations — by
`AlgebraicGeometry.Space.pullbackSheafifiedRegularSections`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicPullbackGlobalSections.lean`), and for the
*second* — the sheafification of `F ⊗_{𝒪} 𝒦`, which is the description
`AlgebraicGeometry.Space.MeromorphicSection` uses — by
`AlgebraicGeometry.Space.pullbackMeromorphicSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullback.lean`), built the same
way over the chartwise rule on the sheaves.  What is still *not* proved is Stacks 0EMD, the
local isomorphism `F ⊗_{𝒪} 𝒮⁻¹𝒪 ⟶ F ⊗_{𝒪} 𝒦` identifying the two descriptions — neither map
uses it.  Part (2) is stated through
`AlgebraicGeometry.Space.IsRegularMeromorphicSection` and proved, for an *invertible* `𝒪_Y`-module,
by `AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionPullbackRegular.lean`).

The obstruction is *not* that the module universes fail to meet.  The input of
`AlgebraicGeometry.Space.meromorphicSectionPresheaf` is an `𝒪_Y`-module whose sections may be
in the universe of the schemes, which is exactly where the inverse image of modules of Stacks
03LU lives; `AlgebraicGeometry.Space.chartPullbackMeromorphicSections` and the `f`-map
`AlgebraicGeometry.Space.fmapMeromorphicSections` they assemble into are built over that
meeting, for an arbitrary sheaf of `𝒪_Y`-modules.  The obstruction is that `𝒦(-)` *lands* one
universe higher: the small étale site has its objects one universe above its rings of sections,
so sheafifying a presheaf of modules on it needs coefficients there,
`meromorphicSectionPresheaf` lifts the sectionwise localizations before sheafifying, and
`AlgebraicGeometry.Space.meromorphicSectionSheaf` is therefore a sheaf of modules at the higher
universe — where the direct and inverse images of modules on the small étale sites do not
exist.  So the step from the chartwise `f`-map to the global map cannot be taken through those
functors.  It has to be taken at the higher universe on presheaves, and the two pieces it needs
are both nearby rather than absent: the descent of an `f`-map to a map into a direct image,
`AlgebraicGeometry.Space.descendedHom`, which is stated for sheaves of sets at that universe
and uses the sheaf condition of its target only to *write* the arrow, and the identification
`AlgebraicGeometry.Space.restrictSectionsToCharts` of the sections over the terminal object with
the sections over the charts, which is universe-polymorphic in the coefficients.  Joining them
to the sheafification used here also needs the canonical map into it to be locally bijective on
underlying sets, which is what `PresheafOfModules.toSheafify` is.  That assembly *is* carried
out twice: for the sheafification of the sectionwise localizations in
`AlgebraicGeometry.Space.pullbackSheafifiedRegularSections`, and for
`AlgebraicGeometry.Space.MeromorphicSection` in
`AlgebraicGeometry.Space.pullbackMeromorphicSection`, the latter over the chartwise rule on the
sheaves of meromorphic functions.  Part (2) is proved over that assembly, for an invertible
module, in
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionPullbackRegular.lean`.  The declarations
carrying the
tag 0ENC say in their tag clause exactly what they do and do not assert.

Note also that part (2) of Stacks 0ENC says "invertible `𝒪_X`-module" where the morphism
`f : X ⟶ Y` forces an `𝒪_Y`-module.  The scheme-level form of the same lemma, Stacks 02OY, says
`𝒪_Y`-module — that reading is the correct one, and 02OY's own text was corrected to it.

## References

* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 0EN9](https://stacks.math.columbia.edu/tag/0EN9)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0EN8.** *Pullbacks of meromorphic functions are defined for `f : X ⟶ Y`* when, for
every commuting square of an étale chart `U` of `X` over an étale chart `V` of `Y`, the pullback
`f^♯` along the underlying morphism of schemes carries every regular section of `𝒪_Y` over `V`
to a regular section of `𝒪_X` over `U`. -/
@[stacks 0EN8]
abbrev PullbacksMeromorphicSections {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (d : ChartDiagram B S hS X Y f) (s : (structurePresheaf B S hS Y).obj (op d.V)),
    IsRegularSection B S hS Y d.V s →
      IsRegularSection B S hS X d.U
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op s)

/-- **Stacks 0EN9, part (2).** Pullbacks of meromorphic functions are defined along a flat
morphism `f : X ⟶ Y`: the morphism of schemes underlying a commuting square of étale charts of
`f` is flat, and pullbacks of meromorphic functions are defined along a flat morphism of
schemes. -/
@[stacks 0EN9 "part (2): flat", ega "IV 20.3.13" "flat: pullback defined"]
theorem pullbacksMeromorphicSections_of_flat {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsFlat B S hS f) : PullbacksMeromorphicSections B S hS f := by
  intro d s hs
  have : Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  have hvalue : pullbackSection ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom ⊤ ⊤ (by simp) s =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op s := by
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, CostructuredArrow.proj_obj,
      Over.forget_obj, pullbackSection, Functor.comp_map, Over.forget_map, ObjectProperty.ι_map,
      Scheme.Hom.toLRSHom, Opens.map_top, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      CommRingCat.hom_id, TopCat.Presheaf.pushforward_obj_obj, Scheme.Γ_obj, Scheme.Γ_map,
      Scheme.Hom.appTop, Scheme.Hom.app, Quiver.Hom.unop_op]
    exact RingHom.id_apply _
  simpa only [hvalue] using _root_.AlgebraicGeometry.pullbacksMeromorphicSections_of_flat
    ((BigFppfOver.toScheme B S hS).map d.g) ⊤ ⊤ (by simp) s hs

/-! ### The local fraction rule for pullback of meromorphic functions -/

section FractionRule

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The sections over an étale chart `U` of the presheaf of sectionwise localizations
`U ↦ 𝒮_F(U)⁻¹𝒪_F(U)` are an algebra over the sections of `𝒪_F` over `U`.

This is the instance of Stacks 0EMC, restated at the spelling `𝒪_F(U)` of the ring of
sections: there it is stated through the projections of the ringed site, which instance search
does not unfold. -/
noncomputable instance regularSectionsLocalizationAlgebra (U : SmallEtale B S hS F) :
    Algebra ((structurePresheaf B S hS F).obj (op U))
      ((regularSectionsSubpresheaf B S hS F hF).localizationPresheaf.obj (op U)) :=
  inferInstanceAs (Algebra ((structurePresheaf B S hS F).obj (op U))
    (Localization (regularSections B S hS F U)))

/-- The sections over an étale chart `U` of the presheaf of sectionwise localizations are the
localization of `𝒪_F(U)` at its regular sections, at the spelling of the ring of sections which
instance search reaches. -/
instance regularSectionsLocalizationIsLocalization (U : SmallEtale B S hS F) :
    IsLocalization (regularSections B S hS F U)
      ((regularSectionsSubpresheaf B S hS F hF).localizationPresheaf.obj (op U)) :=
  inferInstanceAs (IsLocalization (regularSections B S hS F U)
    (Localization (regularSections B S hS F U)))

/-- Restriction along a morphism of étale charts carries a function, viewed as a fraction with
denominator `1`, to its restriction viewed the same way. -/
theorem localizationPresheaf_map_toLocalizationPresheaf {U V : SmallEtale B S hS F} (k : V ⟶ U)
    (r : (structurePresheaf B S hS F).obj (op U)) :
    ((regularSectionsSubpresheaf B S hS F hF).localizationPresheaf.map k.op).hom
        (((regularSectionsSubpresheaf B S hS F hF).toLocalizationPresheaf.app (op U)).hom r) =
      ((regularSectionsSubpresheaf B S hS F hF).toLocalizationPresheaf.app (op V)).hom
        ((structurePresheaf B S hS F).map k.op r) :=
  (ConcreteCategory.congr_hom
    ((regularSectionsSubpresheaf B S hS F hF).toLocalizationPresheaf.naturality k.op) r).symm

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
  (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- Pullback of functions along the morphism of schemes of a chart diagram: the map
`f^♯ : 𝒪_Y(V) ⟶ 𝒪_X(U)` attached to a commuting square of étale charts. -/
abbrev chartSectionPullback (d : ChartDiagram B S hS X Y f) :
    (structurePresheaf B S hS Y).obj (op d.V) ⟶ (structurePresheaf B S hS X).obj (op d.U) :=
  Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op

/-- **The local fraction rule `a/b ↦ f^♯a/f^♯b`.**  When pullbacks of meromorphic functions
are defined for `f`, the pullback along a chart diagram carries the sectionwise localization
`𝒮_Y(V)⁻¹𝒪_Y(V)` into `𝒮_X(U)⁻¹𝒪_X(U)`: a denominator regular over `V` pulls back to one
regular over `U`, so the universal property of the localization applies. -/
@[stacks 0ENC "part (1), chartwise: the local fraction rule a/b ↦ f♯a/f♯b over an étale chart \
diagram, on the presheaf of sectionwise localizations. The global map \
Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F)) of part (1) is asserted for ONE of the two spellings of 𝒦(F): \
AlgebraicGeometry.Space.pullbackSheafifiedRegularSections gives it with 𝒦(F) read as the first \
description in Stacks 0EN5, the sheafification of the presheaf of sectionwise localizations. It \
is asserted for AlgebraicGeometry.Space.MeromorphicSection, which realizes Stacks 0EN5 \
through the other description there, the sheafification of F ⊗_𝒪 𝒦, by \
AlgebraicGeometry.Space.pullbackMeromorphicSection. Stacks 0EMD, which identifies the two \
descriptions, is not proved and neither map uses it. Part (2), stated through \
AlgebraicGeometry.Space.IsRegularMeromorphicSection, is not asserted here; it is proved for an \
invertible module by \
AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection. \
Erratum: part (2) as printed reads 'invertible \
𝒪_X-module', but pulling back along f : X ⟶ Y needs an 𝒪_Y-module, which is what the \
scheme-level form of the lemma, 02OY, says"]
noncomputable def chartPullbackMeromorphicFunctions
    (hf : PullbacksMeromorphicSections B S hS f) (d : ChartDiagram B S hS X Y f) :
    (regularSectionsSubpresheaf B S hS Y hY).localizationPresheaf.obj (op d.V) →+*
      (regularSectionsSubpresheaf B S hS X hX).localizationPresheaf.obj (op d.U) :=
  IsLocalization.map (M := regularSections B S hS Y d.V)
    (T := regularSections B S hS X d.U) _
    (chartSectionPullback B S hS d).hom fun _ ht => hf d _ ht

/-- The fraction rule extends pullback of regular functions: a function, viewed as a fraction
with denominator `1`, pulls back to its pullback viewed the same way. -/
theorem chartPullbackMeromorphicFunctions_toLocalizationPresheaf
    (hf : PullbacksMeromorphicSections B S hS f) (d : ChartDiagram B S hS X Y f)
    (r : (structurePresheaf B S hS Y).obj (op d.V)) :
    chartPullbackMeromorphicFunctions B S hS hX hY hf d
        (((regularSectionsSubpresheaf B S hS Y hY).toLocalizationPresheaf.app (op d.V)).hom r) =
      ((regularSectionsSubpresheaf B S hS X hX).toLocalizationPresheaf.app (op d.U)).hom
        ((chartSectionPullback B S hS d).hom r) :=
  IsLocalization.map_eq (M := regularSections B S hS Y d.V) (T := regularSections B S hS X d.U)
    _ r

/-- The fraction rule in closed form: the fraction `a/b` with regular denominator `b` over the
chart `V` goes to the fraction `f^♯a/f^♯b` over the chart `U`. -/
theorem chartPullbackMeromorphicFunctions_mk'
    (hf : PullbacksMeromorphicSections B S hS f) (d : ChartDiagram B S hS X Y f)
    (a : (structurePresheaf B S hS Y).obj (op d.V)) (b : regularSections B S hS Y d.V) :
    chartPullbackMeromorphicFunctions B S hS hX hY hf d
        (IsLocalization.mk'
          ((regularSectionsSubpresheaf B S hS Y hY).localizationPresheaf.obj (op d.V)) a b) =
      IsLocalization.mk'
        ((regularSectionsSubpresheaf B S hS X hX).localizationPresheaf.obj (op d.U))
        ((chartSectionPullback B S hS d).hom a)
        (⟨(chartSectionPullback B S hS d).hom b, hf d b b.2⟩ :
          regularSections B S hS X d.U) :=
  IsLocalization.map_mk' (M := regularSections B S hS Y d.V) (T := regularSections B S hS X d.U)
    _ a b

/-- A section of `𝒪_Y` regular over the chart `V` pulls back to a unit of the sectionwise
localization `𝒮_X(U)⁻¹𝒪_X(U)`: its pullback is regular over `U`, hence inverted there.  This is
why the fraction rule is defined at all. -/
theorem isUnit_chartPullbackMeromorphicFunctions
    (hf : PullbacksMeromorphicSections B S hS f) (d : ChartDiagram B S hS X Y f)
    (b : regularSections B S hS Y d.V) :
    IsUnit (chartPullbackMeromorphicFunctions B S hS hX hY hf d
      (((regularSectionsSubpresheaf B S hS Y hY).toLocalizationPresheaf.app
        (op d.V)).hom b.1)) := by
  rw [chartPullbackMeromorphicFunctions_toLocalizationPresheaf]
  exact IsLocalization.map_units
    ((regularSectionsSubpresheaf B S hS X hX).localizationPresheaf.obj (op d.U))
    (⟨(chartSectionPullback B S hS d).hom b.1, hf d b.1 b.2⟩ : regularSections B S hS X d.U)

/-- The fraction rule is compatible with simultaneous étale restriction of the source and the
target chart of a diagram: restricting a fraction and then pulling it back is pulling it back
and then restricting. -/
theorem chartPullbackMeromorphicFunctions_comp
    (hf : PullbacksMeromorphicSections B S hS f) (d d' : ChartDiagram B S hS X Y f)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y).map j) :
    (chartPullbackMeromorphicFunctions B S hS hX hY hf d').comp
        ((regularSectionsSubpresheaf B S hS Y hY).localizationPresheaf.map j.op).hom =
      ((regularSectionsSubpresheaf B S hS X hX).localizationPresheaf.map i.op).hom.comp
        (chartPullbackMeromorphicFunctions B S hS hX hY hf d) := by
  refine IsLocalization.ringHom_ext (regularSections B S hS Y d.V)
    (S := (regularSectionsSubpresheaf B S hS Y hY).localizationPresheaf.obj (op d.V))
    (RingHom.ext fun r => ?_)
  change chartPullbackMeromorphicFunctions B S hS hX hY hf d'
      (((regularSectionsSubpresheaf B S hS Y hY).localizationPresheaf.map j.op).hom
        (((regularSectionsSubpresheaf B S hS Y hY).toLocalizationPresheaf.app (op d.V)).hom r)) =
    ((regularSectionsSubpresheaf B S hS X hX).localizationPresheaf.map i.op).hom
      (chartPullbackMeromorphicFunctions B S hS hX hY hf d
        (((regularSectionsSubpresheaf B S hS Y hY).toLocalizationPresheaf.app (op d.V)).hom r))
  rw [localizationPresheaf_map_toLocalizationPresheaf,
    chartPullbackMeromorphicFunctions_toLocalizationPresheaf,
    chartPullbackMeromorphicFunctions_toLocalizationPresheaf,
    localizationPresheaf_map_toLocalizationPresheaf]
  congr 1
  have hc := congrArg (fun k => Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op) h
  exact (ConcreteCategory.congr_hom hc r).symm

/-- The chartwise fraction rules assemble into an `f`-map of presheaves of sets from the
sectionwise localization `𝒮_Y⁻¹𝒪_Y` to `𝒮_X⁻¹𝒪_X`, in the sense of Stacks 03G3: pullback of
meromorphic functions is compatible with étale restriction of both charts of a diagram. -/
@[stacks 0ENC "part (1), chartwise: the fraction rule is canonical, being an f-map of \
Stacks 03G3 on the presheaves of sectionwise localizations. The global pullback map of part (1) \
is asserted for the sheafification of those presheaves, the first of the two descriptions of \
𝒦 in Stacks 0EN5, by AlgebraicGeometry.Space.pullbackSheafifiedRegularSections, and for the \
second, AlgebraicGeometry.Space.MeromorphicSection, by \
AlgebraicGeometry.Space.pullbackMeromorphicSection. Part (2) is not asserted here; it is \
proved for an invertible module by \
AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection"]
noncomputable def fmapMeromorphicFunctions (hf : PullbacksMeromorphicSections B S hS f) :
    FMap B S hS X Y f
      ((regularSectionsSubpresheaf B S hS X hX).localizationPresheaf ⋙
        CategoryTheory.forget CommRingCat.{u})
      ((regularSectionsSubpresheaf B S hS Y hY).localizationPresheaf ⋙
        CategoryTheory.forget CommRingCat.{u}) where
  app d := chartPullbackMeromorphicFunctions B S hS hX hY hf d
  naturality d d' i j h s :=
    RingHom.congr_fun (chartPullbackMeromorphicFunctions_comp B S hS hX hY hf d d' i j h) s

end FractionRule

end AlgebraicGeometry.Space

end

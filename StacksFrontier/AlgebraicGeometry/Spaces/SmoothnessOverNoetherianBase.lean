module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Smoothness of a morphism of algebraic spaces over a Noetherian base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian. Two criteria for smoothness are proved here.

The first is global infinitesimal lifting: `f` is smooth exactly when every solid square

  `Spec B ⟶ X`, `Spec B' ⟶ Y`, over a small extension `B' ⟶ B` of Artinian local rings whose
  map `Spec B' ⟶ Y` is locally of finite type,

admits a dotted arrow `Spec B' ⟶ X`. This is the global companion of the pointwise criterion
`AlgebraicGeometry.Space.isSmoothAt_tfae_liftsAt` (Stacks 0APN).

The second tests smoothness, and étaleness, above a closed subspace `Z ⊆ Y` on the base changes
of `f` to the infinitesimal neighbourhoods `Zₙ ⊆ Y` of `Z`: if `Xₙ = Zₙ ×_Y X ⟶ Zₙ` is smooth
for every `n`, then `f` is smooth at every point above `Z`, and likewise for étaleness.

## Main results

* **Stacks 0APP** is `AlgebraicGeometry.Space.isSmooth_iff_forall_exists_lift_isSmallExtension`
  in `StacksFrontier.AlgebraicGeometry.Spaces.SmoothnessOverNoetherianBaseLifting`.
* Parts (1) and (2) of **Stacks 0APQ** are
  `AlgebraicGeometry.Space.isSmoothAt_of_isSmooth_nthOrderInfinitesimalNeighbourhood` and
  `AlgebraicGeometry.Space.isEtaleAt_of_isEtale_nthOrderInfinitesimalNeighbourhood` in
  `StacksFrontier.AlgebraicGeometry.Spaces.SmoothnessOnInfinitesimalNeighbourhoods`.

## Implementation notes

The spectra of the two test rings are presented as objects of the big fppf site together with
isomorphisms of their underlying schemes with those spectra, since the site contains only
schemes below its cutoff; a lifting problem is then a pair of sections of `X` and `Y` over those
objects, exactly as in `AlgebraicGeometry.Space.LiftsAt`, but with no condition on where the
closed point goes. Local Noetherianness of the target is the étale-local scheme property of
Stacks 03E6, `AlgebraicGeometry.Space.HasEtaleLocalProperty`.

The implication from smoothness is the formal smoothness of a smooth morphism, step (II) of
Stacks 04AM, which this library carries only relative to the descent statement
`AlgebraicGeometry.Space.FormallySmoothEtaleDescent`; that descent is therefore an explicit
hypothesis here, as it is in `AlgebraicGeometry.Space.liftsAt_of_isSmoothAt`. The converse
implication is unconditional: on a commuting square of étale charts `h : U ⟶ V` of `f`, with
`V` locally Noetherian and `h` locally of finite type, the scheme-level global criterion
`AlgebraicGeometry.smooth_iff_lifts_finiteType_smallExtensions` (Stacks 02HY) reduces
smoothness of `h` to lifting problems for `h`; each is pushed into `X` along the chart, solved
there, and pulled back to `U` because the chart is formally étale (Stacks 04AL), the pullback
being compatible with the chart of `Y` because that chart is formally étale too. Finite type of
the scheme-level test map is what places the two Artinian spectra below the cutoff of the site,
by `AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`.

### Why the test map is only required to be locally of finite type

The source asks the test map `Spec B' ⟶ Y` to be of finite type, that is locally of finite type
and quasi-compact in the sense of Stacks 03HE. Over a target which is not quasi-separated that
asks too much: the base change of such a map along a morphism from a quasi-compact algebraic
space need not have quasi-compact source, so no test map at all satisfies the restriction, the
right-hand side holds for want of a test map, and the left-hand side can fail. The hypothesis
kept here is therefore `AlgebraicGeometry.Space.IsLocallyOfFiniteType`, which quantifies over
more test squares than the source does and is never vacuous. The implication from smoothness is
proved for every test square, so it is stronger than the source's; the implication towards
smoothness assumes lifting for more squares than the source does, so it is weaker.

### The infinitesimal neighbourhoods, and what is assumed about them

This library has no construction of the infinitesimal neighbourhoods of a closed subspace of an
algebraic space from the subspace alone:
`AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood` takes as data an étale chart
together with a relation-invariant sheaf of ideals on it, because the surjectivity half of
Stacks 03MB, which would produce that ideal from the closed immersion, is missing. The family
of neighbourhoods therefore appears here as a family of morphisms
`jₙ : Zₙ ⟶ Y` with `j₀` the given closed immersion, and the one property of that family which
the proof uses is carried as the explicit hypothesis `hfactor`: a morphism to `Y` from the
spectrum of an Artinian local ring whose image meets `Z` factors through some `Zₙ`. That is the
step "the maximal ideal of `B'` is nilpotent (as `B'` is Artinian) and hence the morphism `β`
factors through `Zₙ`" of the source, and it is the algebraic-space analogue of
`AlgebraicGeometry.exists_nthOrderToBase_factorization`. The base changes are likewise carried
as cartesian squares, which is what `Xₙ = Zₙ ×_Y X` says.

The smooth half then runs the pointwise criterion of Stacks 0APN: a lifting problem for `f` at
a point above `Z` is pushed into `Xₙ` through the cartesian square and solved there, because a
smooth morphism of algebraic spaces is formally smooth. That last step is step (II) of Stacks
04AM, so the descent hypothesis `AlgebraicGeometry.Space.FormallySmoothEtaleDescent` is carried
here too.

The étale half is the smooth half together with unramifiedness at the point. Two statements
needed for it are present in this library for schemes but not for algebraic spaces, and are
carried as explicit hypotheses: that étaleness at a point is smoothness together with
unramifiedness at that point (Stacks 02GK, which for schemes is
`AlgebraicGeometry.etaleAt_iff_smoothAt_and_unramifiedAt`), and that unramifiedness of the
zeroth base change gives unramifiedness of `f` at every point below it (for schemes, Stacks 03ZH
part (2) together with `AlgebraicGeometry.unramifiedAt_iff_of_isPullback`; for algebraic spaces,
`AlgebraicGeometry.Space.setOf_isUnramifiedAt_eq_preimage_of_isPullback` is the same statement
for cartesian squares in the category of algebraic spaces rather than of presheaves). Everything
else in the étale half is proved: étaleness of each base change gives smoothness of each base
change by `AlgebraicGeometry.Space.isSmooth_of_isEtale` and unramifiedness of the zeroth by
`AlgebraicGeometry.Space.isUnramified_of_isEtale`, and the point of `X₀` above the given point
is produced by `AlgebraicGeometry.Space.exists_points_of_isPullback`. The source instead derives
part (2) from part (1) and "a morphism is étale if and only if it is smooth of relative
dimension zero", which this library does not have for algebraic spaces either.

## References

* [Stacks Project, Tag 02GK](https://stacks.math.columbia.edu/tag/02GK)
* [Stacks Project, Tag 02HY](https://stacks.math.columbia.edu/tag/02HY)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
* [Stacks Project, Tag 0APP](https://stacks.math.columbia.edu/tag/0APP)
* [Stacks Project, Tag 0APQ](https://stacks.math.columbia.edu/tag/0APQ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The two implications -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A commuting square of sections over a morphism of the site gives the compatibility of the
corresponding elements required to state a lifting problem. -/
private theorem app_yonedaEquiv_eq_map_of_comp_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y) (h : α ≫ f = yoneda.map i ≫ β) :
    f.app (op T) (yonedaEquiv α) = Y.map i.op (yonedaEquiv β) := by
  rw [← yonedaEquiv_comp, yonedaEquiv_naturality, h]

/-- Under the Yoneda correspondence, `IsLift` says that a morphism solves a lifting problem. -/
private theorem isLift_yonedaEquiv_iff
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y) (γ : yoneda.obj T' ⟶ X) :
    IsLift f i (yonedaEquiv α) (yonedaEquiv β) (yonedaEquiv γ) ↔
      yoneda.map i ≫ γ = α ∧ γ ≫ f = β := by
  rw [IsLift, yonedaEquiv_naturality, ← yonedaEquiv_comp, yonedaEquiv.apply_eq_iff_eq,
    yonedaEquiv.apply_eq_iff_eq]

/-- A formally smooth morphism of algebraic spaces solves every lifting problem presented by a
small extension of Artinian local rings. -/
private theorem exists_lift_of_formallySmooth_isSmallExtension
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hformal : FormallySmooth f)
    {R' R : CommRingCat.{u}} (φ : R' ⟶ R)
    (hφ : InfinitesimalLifting.IsSmallExtension φ)
    (T T' : BigFppfOver B S hS) (i : T ⟶ T')
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R')
    (hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv)
    (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y)
    (hcomm : α ≫ f = yoneda.map i ≫ β) :
    ∃ γ : yoneda.obj T' ⟶ X, yoneda.map i ≫ γ = α ∧ γ ≫ f = β := by
  have hsq := InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ
  have hsite : IsSquareZeroClosedImmersion B S hS i :=
    isSquareZeroClosedImmersion_of_specMap B S hS φ hsq.2.2.1 hsq.2.2.2 T T' i e e' hi
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.hom
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := IsAffine.of_isIso e'.hom
  obtain ⟨z, hz⟩ := hformal T T' ‹_› ‹_› i hsite (yonedaEquiv α) (yonedaEquiv β)
    (app_yonedaEquiv_eq_map_of_comp_eq B S hS f i α β hcomm)
  obtain ⟨γ, rfl⟩ := yonedaEquiv.surjective z
  exact ⟨γ, (isLift_yonedaEquiv_iff B S hS f i α β γ).1 hz⟩

/-- A solution of a lifting problem in the source algebraic space pulls back to a solution of
the corresponding lifting problem for a commuting square of étale charts: the source chart is
formally étale, so the lift through it exists and is unique, and the target chart is formally
étale too, which identifies the image of that lift with the given section of the target
chart. -/
private theorem exists_lift_chart_of_exists_lift_space
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    {R' R : CommRingCat.{u}} (φ : R' ⟶ R)
    (hsq : InfinitesimalLifting.IsSquareZeroSurjection φ)
    (T T' : BigFppfOver B S hS) (i : T ⟶ T')
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R')
    (hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv)
    (α : yoneda.obj T ⟶ yoneda.obj U) (β : yoneda.obj T' ⟶ yoneda.obj V)
    (hlift : ∃ γX : yoneda.obj T' ⟶ X,
      yoneda.map i ≫ γX = α ≫ a ∧ γX ≫ f = β ≫ b)
    (hαβ : α ≫ yoneda.map h = yoneda.map i ≫ β) :
    ∃ γ : yoneda.obj T' ⟶ yoneda.obj U,
      yoneda.map i ≫ γ = α ∧ γ ≫ yoneda.map h = β := by
  have hsite : IsSquareZeroClosedImmersion B S hS i :=
    isSquareZeroClosedImmersion_of_specMap B S hS φ hsq.2.2.1 hsq.2.2.2 T T' i e e' hi
  obtain ⟨γX, hγX⟩ := hlift
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.hom
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := IsAffine.of_isIso e'.hom
  have haFormal : FormallyEtale a := formallyEtale_of_etale B S hS a ha
  have hbFormal : FormallyEtale b := formallyEtale_of_etale B S hS b hb
  obtain ⟨z, hz, -⟩ := haFormal T T' ‹_› ‹_› i hsite (yonedaEquiv α) (yonedaEquiv γX)
    (app_yonedaEquiv_eq_map_of_comp_eq B S hS a i α γX hγX.1.symm)
  obtain ⟨γ, rfl⟩ := yonedaEquiv.surjective z
  obtain ⟨hγα, hγa⟩ := (isLift_yonedaEquiv_iff B S hS a i α γX γ).1 hz
  obtain ⟨zb, -, huniq⟩ := hbFormal T T' ‹_› ‹_› i hsite
    (yonedaEquiv (α ≫ yoneda.map h)) (yonedaEquiv (β ≫ b))
    (app_yonedaEquiv_eq_map_of_comp_eq B S hS b i _ _ (by rw [hαβ, Category.assoc]))
  have hcandidate := (isLift_yonedaEquiv_iff B S hS b i (α ≫ yoneda.map h) (β ≫ b)
    (γ ≫ yoneda.map h)).2 ⟨by rw [← Category.assoc, hγα],
      by rw [Category.assoc, hcomm, ← Category.assoc, hγa]; exact hγX.2⟩
  have hβlift := (isLift_yonedaEquiv_iff B S hS b i (α ≫ yoneda.map h) (β ≫ b) β).2 ⟨hαβ.symm, rfl⟩
  exact ⟨γ, hγα, yonedaEquiv.injective ((huniq _ hcandidate).trans (huniq _ hβlift).symm)⟩

/-- A section of the target algebraic space over a site object, which factors through an étale
chart by a morphism of the site that is locally of finite type, is locally of finite type as a
morphism of algebraic spaces.

The identity is a surjective étale chart of the source, so the single commuting square it forms
with the given chart of the target computes the property by Stacks 03MJ. -/
private theorem isLocallyOfFiniteType_comp_etaleChart
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {T' V : BigFppfOver B S hS} (b : yoneda.obj V ⟶ Y) (k : T' ⟶ V)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hk : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k)) :
    IsLocallyOfFiniteType B S hS (yoneda.map k ≫ b) := by
  let F := BigFppfOver.toScheme B S hS
  let : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : (MorphismProperty.inverseImage (@Etale.{u}) F).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ F
  let : (MorphismProperty.inverseImage (@Surjective.{u}) F).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ F
  have key (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hP : ∀ X, P (𝟙 X)) :
      (P.inverseImage F).presheaf (𝟙 (yoneda.obj T')) := by
    apply MorphismProperty.relative.of_exists
    intro W g
    refine ⟨W, g, 𝟙 W, ?_, ?_⟩
    · simpa only [yoneda.map_id] using CategoryTheory.IsPullback.of_id_snd
    · change P (F.map (𝟙 W))
      rw [F.map_id]
      exact hP _
  apply (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_yoneda B S hS T') hY (yoneda.map k ≫ b)).mpr
  exact ⟨T', V, 𝟙 _, b, k, key _ fun _ => inferInstance, hb,
    key _ fun _ => inferInstance, by simp, hk⟩

/-! ### The criterion -/

/-! ### Checking smoothness on the infinitesimal neighbourhoods of a closed subspace -/

end AlgebraicGeometry.Space

end

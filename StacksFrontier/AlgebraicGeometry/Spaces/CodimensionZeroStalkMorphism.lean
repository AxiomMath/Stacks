module

public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.DiscreteFibre
public import StacksFrontier.AlgebraicGeometry.Scheme.IsPullbackPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# The canonical morphism from the spectrum of a codimension-zero local ring

Let `X` be an algebraic space over a scheme `S` with a presentation `P` of its schematic locus
at the points of codimension `0` (`AlgebraicGeometry.Space.CodimensionZeroPresentation`), and
let `η` be such a point.  This file collects the properties of the canonical morphism
`j_η : Spec(𝒪_{X, η}) ⟶ X`:

* it is representable, and every scheme morphism obtained from it by base change along an étale
  chart is a flat preimmersion;
* the spectrum of `𝒪_{X, η}` is a one-point space, and every point of it maps to `η`;
* every étale chart of `Spec(𝒪_{X, η})` is a scheme all of whose local rings have Krull
  dimension zero.

These are the inputs for identifying the sections of the direct image `j_{η, *}𝒪_{X, η}` over an
affine étale chart of `X`.

## Main results

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.schemePointAt_mem_genericPoints`: the
  chosen point of the presenting scheme above `η` is a generic point of an irreducible
  component.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.relative_fromSpecStalk`: a property of
  scheme morphisms which contains the open immersions, is stable under base change and
  composition and holds for `Spec 𝒪_{X, η} ⟶ X'` holds for every base change of `j_η`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.representable_fromSpecStalk`,
  `…flat_relative_fromSpecStalk`, `…isPreimmersion_relative_fromSpecStalk`: `j_η` is
  representable, and every base change of it is flat and a preimmersion.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.pointsMap_fromSpecStalk`: every point of
  `Spec(𝒪_{X, η})` maps to `η`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.ringKrullDim_stalk_specStalkChart`: the
  local rings of an étale chart of `Spec(𝒪_{X, η})` have Krull dimension zero.

## Implementation notes

The morphism `j_η` is `Spec 𝒪_{X, η} ⟶ X'` followed by the presentation `X' ⟶ X` of the dense
open subspace, which is an isomorphism followed by an open immersion.  So a property of scheme
morphisms transfers to `j_η` as soon as it contains the open immersions and is stable under
base change and composition; that is `relative_fromSpecStalk`, and flatness and the preimmersion
property are the two instances of it used here.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : CodimensionZeroPresentation B S hS X)

/-! ### The presenting chart is an open immersion -/

/-- The chart presenting the dense open subspace is an open immersion: it is an isomorphism of
presheaves followed by the inclusion of an open subspace. -/
theorem presheaf_isOpenImmersion_chart :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf P.chart := by
  have hiso : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf P.iso.hom := by
    have hrep := Functor.relativelyRepresentable.of_isIso yoneda P.iso.hom
    refine MorphismProperty.relative_of_snd hrep fun A g => ?_
    show @AlgebraicGeometry.IsOpenImmersion.{u} _ _
      ((BigFppfOver.toScheme B S hS).map (hrep.snd g))
    have : IsIso (yoneda.map (hrep.snd g)) := (hrep.isPullback g).isIso_snd_of_isIso
    let : IsIso (hrep.snd g) := Yoneda.fullyFaithful.isIso_of_isIso_map _
    infer_instance
  exact MorphismProperty.comp_mem _ _ _ hiso P.isOpenSubspace.2

/-- The chart presenting the dense open subspace is étale. -/
theorem isEtale_chart : IsEtale B S hS P.chart := by
  refine isEtale_of_presheaf_etale B S hS
    ((MorphismProperty.relative_monotone (F := yoneda) ?_) _ P.presheaf_isOpenImmersion_chart)
  intro A C f hf
  change @AlgebraicGeometry.IsOpenImmersion.{u} _ _ ((BigFppfOver.toScheme B S hS).map f) at hf
  show Etale ((BigFppfOver.toScheme B S hS).map f)
  let := hf
  infer_instance

variable {x : points B S hS X} (hx : localRingDimension B S hS x = 0)

/-! ### The chosen point of the presenting scheme is a generic point -/

/-- **The point of the presenting scheme above a point of codimension `0` is the generic point
of an irreducible component**, because codimension `0` is read on every étale chart. -/
theorem schemePointAt_mem_genericPoints (hX : IsAlgebraicSpace B S hS X) :
    P.schemePointAt hx ∈ genericPoints P.schemeObj := by
  refine (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX x).mp hx
    P.scheme P.chart (P.schemePointAt hx) P.isEtale_chart ?_
  have h := chartPoint_pointsToScheme B S hS P.scheme P.chart (P.chartPointAt hx)
  rwa [P.pointsMap_chart_chartPointAt hx] at h

/-- **The spectrum of the local ring at a point of codimension `0` is a one-point space.** -/
theorem subsingleton_primeSpectrum_stalk (hX : IsAlgebraicSpace B S hS X) :
    Subsingleton (PrimeSpectrum (P.stalk hx)) :=
  subsingleton_primeSpectrum_stalk_of_mem_genericPoints
    (X := P.schemeObj) ⟨P.schemePointAt hx, P.schemePointAt_mem_genericPoints hx hX⟩

/-- The local ring at a point of codimension `0` has Krull dimension zero. -/
theorem ringKrullDim_stalk_eq_zero (hX : IsAlgebraicSpace B S hS X) :
    ringKrullDim (P.stalk hx) = 0 :=
  (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints P.schemeObj (P.schemePointAt hx)).mpr
    (P.schemePointAt_mem_genericPoints hx hX)

/-! ### Properties of the canonical morphism -/

/-- **A property of scheme morphisms transfers to `j_η`.** If `Q` contains the open immersions,
is stable under base change and composition, respects isomorphisms and holds for the canonical
morphism `Spec 𝒪_{X, η} ⟶ X'` of the presenting scheme, then every scheme morphism obtained
from `j_η : Spec(𝒪_{X, η}) ⟶ X` by base change has `Q`. -/
theorem relative_fromSpecStalk (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
    [Q.IsStableUnderComposition] [Q.RespectsIso]
    (hopen : @AlgebraicGeometry.IsOpenImmersion.{u} ≤ Q)
    (hstalk : Q (P.schemeObj.fromSpecStalk (P.schemePointAt hx))) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (P.fromSpecStalk hx) := by
  set R := MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)
  have : R.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS Q
  have hle : MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS) ≤ R := fun _ _ f hf => hopen _ hf
  have hchart : R.presheaf P.chart :=
    (MorphismProperty.relative_monotone (F := yoneda) hle) _ P.presheaf_isOpenImmersion_chart
  have hstalk' : R (P.specStalkToScheme hx) := by
    show Q ((BigFppfOver.toScheme B S hS).map (P.specStalkToScheme hx))
    rw [P.toScheme_map_specStalkToScheme hx]
    exact hstalk
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.relative_map hstalk') hchart

/-- **The canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X` is representable.** -/
theorem representable_fromSpecStalk (hX : IsAlgebraicSpace B S hS X) :
    yoneda.relativelyRepresentable (P.fromSpecStalk hx) :=
  Functor.relativelyRepresentable.of_diag hX.diagonal_representable _

/-- **Every base change of `j_η` along an étale chart is flat.** -/
theorem flat_relative_fromSpecStalk :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Flat.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (P.fromSpecStalk hx) := by
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact P.relative_fromSpecStalk hx _ (fun _ _ f hf => by let := hf; infer_instance)
    (flat_fromSpecStalk P.schemeObj (P.schemePointAt hx))

/-- **Every base change of `j_η` along an étale chart is a preimmersion.** -/
theorem isPreimmersion_relative_fromSpecStalk :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsPreimmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (P.fromSpecStalk hx) := by
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.IsPreimmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.IsPreimmersion.{u}) :=
    ⟨fun f g hf hg => by let := hf; let := hg; infer_instance⟩
  exact P.relative_fromSpecStalk hx _ (fun _ _ f hf => by let := hf; infer_instance)
    inferInstance

/-! ### Points and local rings of the spectrum of the stalk -/

/-- The underlying scheme of `Spec(𝒪_{X, η})` has a single point. -/
private theorem subsingleton_toScheme_obj_specStalk (hX : IsAlgebraicSpace B S hS X) :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj (P.specStalk hx)) :=
  have := P.subsingleton_primeSpectrum_stalk hx hX
  inferInstanceAs (Subsingleton (PrimeSpectrum (P.stalk hx)))

/-- **Every point of `Spec(𝒪_{X, η})` maps to `η`.** The spectrum of the local ring at a point
of codimension `0` has a single point, and the canonical morphism takes the closed point to the
chosen point of the presenting scheme above `η`. -/
theorem pointsMap_fromSpecStalk (hX : IsAlgebraicSpace B S hS X)
    (z : points B S hS (yoneda.obj (P.specStalk hx))) :
    pointsMap B S hS (yoneda.obj (P.specStalk hx)) (P.fromSpecStalk hx) z = x := by
  have := P.subsingleton_toScheme_obj_specStalk hx hX
  have : IsLocalRing (P.stalk hx) :=
    inferInstanceAs (IsLocalRing (P.schemeObj.presheaf.stalk (P.schemePointAt hx)))
  have h1 : pointsMap B S hS (yoneda.obj (P.specStalk hx))
      (yoneda.map (P.specStalkToScheme hx)) z = P.chartPointAt hx := by
    refine injective_pointsToScheme B S hS P.scheme ?_
    rw [pointsToScheme_pointsMap_yoneda, P.toScheme_map_specStalkToScheme hx]
    rw [Subsingleton.elim (pointsToScheme B S hS (P.specStalk hx) z)
      (IsLocalRing.closedPoint (P.stalk hx))]
    exact Scheme.fromSpecStalk_closedPoint
  rw [show P.fromSpecStalk hx = yoneda.map (P.specStalkToScheme hx) ≫ P.chart from rfl,
    pointsMap_comp_apply, h1]
  exact P.pointsMap_chart_chartPointAt hx

/-- **The local rings of an étale chart of `Spec(𝒪_{X, η})` have Krull dimension zero**: the
chart is étale over a one-point scheme whose local ring is `𝒪_{X, η}`, and Krull dimension of
local rings is an étale invariant. -/
theorem ringKrullDim_stalk_specStalkChart (hX : IsAlgebraicSpace B S hS X)
    (W : SmallEtale B S hS (yoneda.obj (P.specStalk hx)))
    (z : (BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (yoneda.obj (P.specStalk hx))).obj W)) :
    ringKrullDim (((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (yoneda.obj (P.specStalk hx))).obj W)).presheaf.stalk z) = 0 := by
  have := P.subsingleton_toScheme_obj_specStalk hx hX
  set Q := MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
    (BigFppfOver.toScheme B S hS)
  have : Q.IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS @AlgebraicGeometry.Etale.{u}
  have hg : Q (yoneda.preimage W.1.hom) :=
    (MorphismProperty.relative_map_iff (F := yoneda) (P := Q)).mp (by simpa using W.2)
  let : Etale ((BigFppfOver.toScheme B S hS).map (yoneda.preimage W.1.hom)) := hg
  refine (ringKrullDim_stalk_eq_of_etale
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage W.1.hom)) z).trans ?_
  refine (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints _ _).mpr ?_
  refine (mem_genericPoints_iff_isMax _ _).mpr fun y _ => ?_
  exact le_of_eq (Subsingleton.elim _ _)

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end

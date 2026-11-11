module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpacePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiberLocalRingDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityFlatInjection

/-!
# Weak association along a flat morphism with zero-dimensional fibre local ring

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `G` be an
`𝒪_Y`-module and let `x ∈ |X|` with image `y ∈ |Y|`. If `y` is weakly associated to `G`, `f` is
flat at `x` and the local ring of the fibre of `f` at `x` has dimension zero in the sense of
Stacks 04NM, then `x` is weakly associated to `f^*G`. This is Stacks 0CUA.

## Main results

* `IsLocalRing.radical_eq_maximalIdeal_of_ringKrullDim_quotient_eq_zero`: an ideal inside the
  maximal ideal of a local ring with zero-dimensional quotient has the maximal ideal as its
  radical.
* `AlgebraicGeometry.Space.hasFiberLocalRingDimension_image_iff`: the dimension of the local
  ring of the fibre at the image of a geometric point `x̄` (Stacks 04NM) is the Krull dimension
  of `𝒪_{X, x̄} / 𝔪_{Y, ȳ} 𝒪_{X, x̄}`.
* `Space.radical_map_maximalIdeal_etaleLocalRingMap_eq_of_hasFiberLocalRingDimension`: when
  that dimension is zero, the maximal ideal of `𝒪_{X, x̄}` is the radical of the ideal generated
  by the maximal ideal of `𝒪_{Y, ȳ}`.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_modulePullback_of_hasFiberLocalRingDimension`:
  **Stacks 0CUA**.

## Implementation notes

The source reduces to a commuting square of étale scheme charts `U ⟶ V` and the scheme case,
Stacks 05F0. Here the reduction is made at the étale local rings instead: the definition of
weak association of a point of an algebraic space,
`AlgebraicGeometry.Space.IsWeaklyAssociatedPoint`, is weak association of the maximal ideal of
the étale local ring to the geometric stalk, and the ring-level form of the lemma at a flat
local homomorphism whose closed fibre is zero-dimensional is
`isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_of_flat_of_radical_eq`, used by
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_modulePullback`. What this file adds is the
translation of the hypothesis of Stacks 04NM, a condition on the local ring of the fibre of one
(equivalently every) chart square at the point, into the radical condition at the étale local
rings. The chart square is taken with affine target, where
`AlgebraicGeometry.Space.ringKrullDim_closedFibreEtaleLocalRing_eq_fiberStalk` (Stacks 05WS and
06LK) identifies the dimension of the closed fibre of `𝒪_{Y, ȳ} → 𝒪_{X, x̄}` with that of the
local ring of the fibre of the chart morphism, and
`AlgebraicGeometry.Space.hasFiberLocalRingDimension_iff_of_chart` (Stacks 04NC) reads the
condition of Stacks 04NM off that same square.

The module `G` is any `𝒪_Y`-module; the source's quasi-coherence is not used.

## References

* [Stacks Project, Tag 0CUA](https://stacks.math.columbia.edu/tag/0CUA)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 05F0](https://stacks.math.columbia.edu/tag/05F0)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

/-- An ideal inside the maximal ideal of a local ring whose quotient has Krull dimension zero
has the maximal ideal as its radical: every prime containing it is maximal. -/
theorem IsLocalRing.radical_eq_maximalIdeal_of_ringKrullDim_quotient_eq_zero {A : Type*}
    [CommRing A] [IsLocalRing A] {I : Ideal A} (hI : I ≤ maximalIdeal A)
    (h : ringKrullDim (A ⧸ I) = 0) : I.radical = maximalIdeal A := by
  refine le_antisymm ((maximalIdeal.isMaximal A).isPrime.radical_le_iff.mpr hI) ?_
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun p ⟨hIp, hp⟩ => ?_
  have : Ring.KrullDimLE 0 (A ⧸ I) := Ring.krullDimLE_iff.mpr h.le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ p := by rwa [Ideal.mk_ker]
  have hp' : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hmax : (p.map (Ideal.Quotient.mk I)).IsMaximal := Ring.krullDimLE_zero_iff.mp this _ hp'
  have hq : ((p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← IsLocalRing.eq_maximalIdeal hq,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  refine sup_le le_rfl ?_
  rw [← RingHom.ker_eq_comap_bot]
  exact hker

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The dimension of the local ring of the fibre (Stacks 04NM) at the étale local rings.**
At the image of a geometric point `x̄`, the local ring of the fibre of `f` has dimension `d`
exactly when the closed fibre `𝒪_{F, x̄} / 𝔪_{G, ȳ} 𝒪_{F, x̄}` of the canonical homomorphism of
étale local rings has Krull dimension `d`. -/
theorem hasFiberLocalRingDimension_image_iff (d : ℕ∞) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : GeometricPoint B S hS F) :
    HasFiberLocalRingDimension d B S hS hF hG f x.image ↔
      ringKrullDim (closedFibreEtaleLocalRing B S hS hF f x) = (d : WithBot ℕ∞) := by
  obtain ⟨U, V, g, hcomm, hpoint, hVaffine⟩ :=
    exists_compatible_affine_chart_square B S hS hF hG f x
  set p : FieldValuedPoint B S hS (yoneda.obj U.chart.obj.left) :=
    { carrier := x.val.carrier
      contained := x.val.contained
      toBase := x.val.toBase
      value := U.point } with hp
  have hmap : FieldValuedPoint.map B S hS _ U.chart.obj.hom p = x.val :=
    congrArg (fun z : F.obj (Opposite.op x.val.siteObject) => { x.val with value := z })
      U.point_comp
  let c : EtaleChartAtPoint B S hS f x.image :=
    { U := U.chart.obj.left
      V := V.chart.obj.left
      a := U.chart.obj.hom
      b := V.chart.obj.hom
      h := g
      a_etale := U.chart.property
      b_etale := V.chart.property
      comm := hcomm.symm
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := congrArg (FieldValuedPoint.class B S hS F) hmap }
  rw [hasFiberLocalRingDimension_iff_of_chart B S hS d hF hG f x.image c,
    ringKrullDim_closedFibreEtaleLocalRing_eq_fiberStalk B S hS hF hG f x U V g hcomm hpoint
      hVaffine _ rfl c.sourcePoint rfl]

/-- **A zero-dimensional local ring of the fibre, read at the étale local rings.** If the local
ring of the fibre of `f` at the image of a geometric point `x̄` has dimension zero
(Stacks 04NM), then the maximal ideal of `𝒪_{F, x̄}` is the radical of the ideal generated by
the maximal ideal of `𝒪_{G, ȳ}`. -/
theorem radical_map_maximalIdeal_etaleLocalRingMap_eq_of_hasFiberLocalRingDimension
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (x : GeometricPoint B S hS F) (h : HasFiberLocalRingDimension 0 B S hS hF hG f x.image) :
    letI : IsLocalRing (etaleLocalRing B S hS G (geometricPointMap f x)) :=
      isLocalRing_etaleLocalRing B S hS G hG (geometricPointMap f x)
    letI : IsLocalRing (etaleLocalRing B S hS F x) := isLocalRing_etaleLocalRing B S hS F hF x
    (Ideal.map (etaleLocalRingMap hF f x)
        (maximalIdeal (etaleLocalRing B S hS G (geometricPointMap f x)))).radical =
      maximalIdeal (etaleLocalRing B S hS F x) := by
  let : IsLocalRing (etaleLocalRing B S hS G (geometricPointMap f x)) :=
    isLocalRing_etaleLocalRing B S hS G hG (geometricPointMap f x)
  let : IsLocalRing (etaleLocalRing B S hS F x) := isLocalRing_etaleLocalRing B S hS F hF x
  have hdim := (hasFiberLocalRingDimension_image_iff B S hS 0 hF hG f x).mp h
  have hjac : (⊥ : Ideal (etaleLocalRing B S hS G (geometricPointMap f x))).jacobson =
      maximalIdeal (etaleLocalRing B S hS G (geometricPointMap f x)) :=
    IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top
  have : IsLocalHom (etaleLocalRingMap hF f x) := isLocalHom_etaleLocalRingMap B S hS hF hG f x
  refine IsLocalRing.radical_eq_maximalIdeal_of_ringKrullDim_quotient_eq_zero
    (map_maximalIdeal_le _) ?_
  have hdim' : ringKrullDim (etaleLocalRing B S hS F x ⧸ Ideal.map (etaleLocalRingMap hF f x)
      (⊥ : Ideal (etaleLocalRing B S hS G (geometricPointMap f x))).jacobson) = 0 := by
    simpa using hdim
  rwa [hjac] at hdim'

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0CUA.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let
`G` be an `𝒪_Y`-module and let `x ∈ |X|` with image `y = f(x) ∈ |Y|`. If `y` is weakly
associated to `G`, `f` is flat at `x`, and the local ring of the fibre of `f` at `x` has
dimension zero (Stacks 04NM), then `x` is weakly associated to `f^*G`. -/
@[stacks 0CUA "for an arbitrary 𝒪_Y-module G; the source takes G quasi-coherent"]
theorem isWeaklyAssociatedPoint_modulePullback_of_hasFiberLocalRingDimension (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (x : points B S hS X.1)
    (hG : IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x))
    (hflat : IsFlatAt B S hS f.hom x)
    (hdim : HasFiberLocalRingDimension 0 B S hS X.2 Y.2 f.hom x) :
    IsWeaklyAssociatedPoint B S hS X ((modulePullback B S hS f).obj G) x := by
  obtain ⟨xbar, rfl⟩ := exists_geometricPoint_liesOver B S hS x
  exact isWeaklyAssociatedPoint_modulePullback B S hS f xbar.image xbar rfl hflat G
    (radical_map_maximalIdeal_etaleLocalRingMap_eq_of_hasFiberLocalRingDimension B S hS X.2 Y.2
      f.hom xbar hdim) hG

end AlgebraicGeometry.Space

end

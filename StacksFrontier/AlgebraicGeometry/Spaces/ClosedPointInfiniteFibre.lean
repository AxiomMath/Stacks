module

public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# From finite fibres over the closed points to finite fibres over all points

Let `g : X ⟶ Z` be a morphism of algebraic spaces over `S` which is locally of finite type and
universally closed, with `X` and `Z` decent and the point space `|X|` a Jacobson space. If some
point of `|Z|` has an infinite fibre, then some closed point of `|Z|` has an infinite fibre;
equivalently, finiteness of the fibres over the closed points of `|Z|` gives finiteness of the
fibres over all points of `|Z|`. A fibre of such a `g` is finite exactly when `g` is
quasi-finite at each of its points.

## Main results

* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_finite_setFibre`: a finite set-theoretic fibre
  forces quasi-finiteness at each of its points.
* `AlgebraicGeometry.Space.finite_setFibre_of_isQuasiFiniteAboveFieldValuedPoint`: the converse,
  for a universally closed `g`.
* `AlgebraicGeometry.Space.finite_fibre_iff_forall_isQuasiFiniteAt`: the two together, stated
  for a point of `|Z|` rather than for a field-valued point.
* `AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre`: an infinite fibre over
  some point gives an infinite fibre over a closed point.
* `AlgebraicGeometry.Space.forall_finite_fibre_of_forall_isClosed`: finite fibres over the closed
  points give finite fibres over all points.

## References

* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 07W4](https://stacks.math.columbia.edu/tag/07W4)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_closedPointInfiniteFibre
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### A finite fibre and quasi-finiteness above it -/

/-- **A finite set-theoretic fibre forces quasi-finiteness at each of its points.** For a
morphism `g` of decent algebraic spaces locally of finite type, if the set-theoretic fibre of `g`
over a field-valued point `p` of `Z` is finite, then `g` is quasi-finite above `p`. -/
theorem isQuasiFiniteAt_of_finite_setFibre (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (g : X ⟶ Z)
    (hlft : IsLocallyOfFiniteType B S hS g) (hXdec : IsDecentSpace B S hS X)
    (hZdec : IsDecentSpace B S hS Z) (p : FieldValuedPoint B S hS Z)
    (hfinite : (setFibre B S hS g p).Finite) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS g p := by
  rcases Set.eq_empty_or_nonempty (setFibre B S hS g p) with hempty | hne
  · intro x hx
    exact absurd (hempty ▸ hx) (Set.notMem_empty x)
  · exact (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hZ hlft
      p).mp
      (discreteTopology_points_fieldFibre_of_finite_of_isDecent B S hS hX hZ g p hlft
        (isDecent_of_isDecentSpace_source B S hS hX hZ g hXdec)
        (finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent B S hS hX hZ g p hlft
          hXdec hZdec hfinite))

/-- **Quasi-finiteness above a point makes the set-theoretic fibre finite, for a universally
closed morphism.** For a universally closed morphism `g` of algebraic spaces locally of finite
type which is quasi-finite above a field-valued point `p` of `Z`, the set-theoretic fibre of `g`
over `p` is finite. -/
theorem finite_setFibre_of_isQuasiFiniteAboveFieldValuedPoint (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (g : X ⟶ Z)
    (hlft : IsLocallyOfFiniteType B S hS g) (huc : UniversallyClosed B S hS g)
    (p : FieldValuedPoint B S hS Z)
    (hqf : IsQuasiFiniteAboveFieldValuedPoint B S hS g p) :
    (setFibre B S hS g p).Finite := by
  rcases Set.eq_empty_or_nonempty (setFibre B S hS g p) with hempty | hne
  · exact hempty ▸ Set.finite_empty
  · let hdisc : DiscreteTopology (points B S hS (fieldFibre B S hS g p)) :=
      (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hZ hlft
        p).mpr hqf
    exact finite_setFibre_of_universallyClosed_of_discrete_fibre B S hS hX hZ g huc p
      (pointsHomeomorphOfIso B S hS
        (pullbackSymmetry g (yonedaEquiv.symm p.value))).discreteTopology

/-- **A fibre of a universally closed morphism of decent algebraic spaces is finite exactly
when the morphism is quasi-finite at each of its points.** For `g : X ⟶ Z` locally of finite
type and universally closed, with `X` and `Z` decent, the fibre of `g` over a point `y` of `|Z|`
is finite if and only if `g` is quasi-finite at every point of `|X|` mapping to `y`. -/
theorem finite_fibre_iff_forall_isQuasiFiniteAt (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (g : X ⟶ Z)
    (hlft : IsLocallyOfFiniteType B S hS g) (huc : UniversallyClosed B S hS g)
    (hXdec : IsDecentSpace B S hS X) (hZdec : IsDecentSpace B S hS Z)
    (y : points B S hS Z) :
    {x : points B S hS X | pointsMap B S hS X g x = y}.Finite ↔
      ∀ x : points B S hS X, pointsMap B S hS X g x = y → IsQuasiFiniteAt B S hS g x := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · exact isQuasiFiniteAt_of_finite_setFibre B S hS hX hZ g hlft hXdec hZdec p h x hx
  · exact finite_setFibre_of_isQuasiFiniteAboveFieldValuedPoint B S hS hX hZ g hlft huc
      p fun x hx ↦ h x hx

/-! ### The passage to a closed point -/

/-- **An infinite fibre over some point gives an infinite fibre over a closed point.**  Let
`g : X ⟶ Z` be a morphism of algebraic spaces over `S` which is locally of finite type and
universally closed, let `X` and `Z` be decent and let `|X|` be a Jacobson space. If
the fibre of `g` over some point of `|Z|` is infinite, then the fibre over some *closed* point
of `|Z|` is infinite. -/
theorem exists_isClosed_singleton_infinite_fibre (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (g : X ⟶ Z)
    (hlft : IsLocallyOfFiniteType B S hS g) (huc : UniversallyClosed B S hS g)
    (hXdec : IsDecentSpace B S hS X) (hZdec : IsDecentSpace B S hS Z)
    (hjac : JacobsonSpace (points B S hS X)) (y : points B S hS Z)
    (hinf : {x : points B S hS X | pointsMap B S hS X g x = y}.Infinite) :
    ∃ w : points B S hS Z, IsClosed {w} ∧
      {x : points B S hS X | pointsMap B S hS X g x = w}.Infinite := by
  let := hjac
  have hQ : IsClosed {x : points B S hS X | IsQuasiFiniteAt B S hS g x}ᶜ :=
    (isOpen_setOf_isQuasiFiniteAt B S hS g).isClosed_compl
  have hne : {x : points B S hS X | IsQuasiFiniteAt B S hS g x}ᶜ.Nonempty := by
    by_contra h
    refine hinf ?_
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact (finite_fibre_iff_forall_isQuasiFiniteAt B S hS hX hZ g hlft huc hXdec hZdec
      y).2 fun x _ ↦ Set.eq_univ_iff_forall.1 h x
  obtain ⟨x, hxQ, hxc⟩ := nonempty_inter_closedPoints hne hQ.isLocallyClosed
  refine ⟨pointsMap B S hS X g x, ?_, ?_⟩
  · rw [← Set.image_singleton]
    exact isClosed_of_universallyClosed B S hS hZ g huc _ hxc
  · exact fun hfin ↦ hxQ ((finite_fibre_iff_forall_isQuasiFiniteAt B S hS hX hZ g hlft huc hXdec
      hZdec _).1 hfin x rfl)

/-- **Finite fibres over the closed points of `|Z|` give finite fibres over every point of
`|Z|`.** Let `g : X ⟶ Z` be a morphism of algebraic spaces over `S` which is locally of finite
type and universally closed, let `X` and `Z` be decent and let `|X|` be a Jacobson space. If the
fibre of `g` over every closed point of `|Z|` is finite, then the fibre over every point of `|Z|`
is finite. -/
theorem forall_finite_fibre_of_forall_isClosed (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (g : X ⟶ Z)
    (hlft : IsLocallyOfFiniteType B S hS g) (huc : UniversallyClosed B S hS g)
    (hXdec : IsDecentSpace B S hS X) (hZdec : IsDecentSpace B S hS Z)
    (hjac : JacobsonSpace (points B S hS X))
    (hclosed : ∀ w : points B S hS Z, IsClosed {w} →
      {x : points B S hS X | pointsMap B S hS X g x = w}.Finite)
    (y : points B S hS Z) :
    {x : points B S hS X | pointsMap B S hS X g x = y}.Finite := by
  by_contra hfin
  obtain ⟨w, hwc, hwinf⟩ := exists_isClosed_singleton_infinite_fibre B S hS hX hZ g hlft huc
    hXdec hZdec hjac y hfin
  exact hwinf (hclosed w hwc)

end AlgebraicGeometry.Space

end

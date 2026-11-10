module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Pullback
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated

/-!
# Criteria for pullbacks of meromorphic functions to be defined

Pullback of meromorphic functions along a morphism of schemes `f : X ⟶ Y` is defined as soon
as `f` does not move any point where the structure sheaf of `X` has an associated prime off
the generic points of `Y`. This file collects the criteria of the source: in terms of weakly
associated points, of generic points for a reduced or a locally Noetherian source without
embedded points, of the generic point for an integral source, and flatness.

## Main results

* `AlgebraicGeometry.pullbacksMeromorphicSections_of_mapsTo_genericPoints`: the criterion in
  terms of weakly associated points.
* `AlgebraicGeometry.pullbacksMeromorphicSections_of_reduced`: a reduced source.
* `AlgebraicGeometry.pullbacksMeromorphicSections_of_isIntegral`: an integral source.
* `AlgebraicGeometry.pullbacksMeromorphicSections_of_isDominant`: a dominant morphism of
  integral schemes.
* `AlgebraicGeometry.pullbacksMeromorphicSections_of_associatedPoints`: a locally Noetherian
  source, in terms of associated points.
* `AlgebraicGeometry.pullbacksMeromorphicSections_of_noEmbeddedPoints`: a locally Noetherian
  source without embedded points.
* `AlgebraicGeometry.pullbacksMeromorphicSections_of_flat`: a flat morphism.

## Implementation notes

Generic points of irreducible components are Mathlib's `genericPoints`, and the point-mapping
hypotheses are stated as `Set.MapsTo`. Every criterion is reduced, through the affine criterion
`AlgebraicGeometry.pullbacksMeromorphicSections_of_affine`, to the statement that the maps on
rings of sections over compatible affine opens preserve nonzerodivisors.

## References

* [Stacks Project, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry


/-- The prime naming a generic point of an irreducible component lying in an affine open is a
minimal prime of the ring of sections over that open. -/
lemma primeIdealOf_mem_minimalPrimes_of_mem_genericPoints
    {Y : Scheme.{u}} (V : Opens Y) (hV : IsAffineOpen V) (y : Y) (hyV : y ∈ V)
    (hy : y ∈ genericPoints Y) :
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal ∈ minimalPrimes Γ(Y, V) := by
  rw [← PrimeSpectrum.vanishingIdeal_singleton,
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  have hpre := preimage_mem_irreducibleComponents hy hV.fromSpec.isOpenEmbedding
    ⟨y, subset_closure (Set.mem_singleton y), by rwa [hV.range_fromSpec]⟩
  rw [hV.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    hV.fromSpec.continuous] at hpre
  have heq : hV.fromSpec ⁻¹' {y} = {hV.primeIdealOf ⟨y, hyV⟩} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hp => hV.fromSpec.isOpenEmbedding.injective
      (hp.trans (hV.fromSpec_primeIdealOf ⟨y, hyV⟩).symm),
      by rintro rfl; exact hV.fromSpec_primeIdealOf ⟨y, hyV⟩⟩
  rwa [heq] at hpre

/-- If a morphism of schemes maps every weakly associated point of its source to the generic
point of an irreducible component of its target, then pullbacks of meromorphic functions are
defined for the morphism. -/
@[stacks 02OU "weakly_associated"]
lemma pullbacksMeromorphicSections_of_mapsTo_genericPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.MapsTo f (Stacks.Divisors.schemeWeaklyAssociatedPoints X) (genericPoints Y)) :
    PullbacksMeromorphicSections f.1 := by
  apply pullbacksMeromorphicSections_of_affine f
  intro V U hV hU hUV s hs
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro m hm
  by_contra hm0
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes
    (I := (Γ(X, U) ∙ m).annihilator) (by
      simpa [Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot] using hm0)
  let p : PrimeSpectrum Γ(X, U) := ⟨q, hq.isPrime⟩
  let x : X := hU.fromSpec p
  have hxU : x ∈ U := by
    change x ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self p
  have hqx : q = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    (congrArg PrimeSpectrum.asIdeal <| hU.fromSpec.isOpenEmbedding.injective
      (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)).symm
  have hxwa : x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X := by
    rw [Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff,
      ← AlgebraicGeometry.isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) U hU x hxU, ← hqx]
    exact ⟨m, hq⟩
  have hfxV : f x ∈ V := hUV hxU
  apply hs.notMem_of_mem_minimalPrimes (by
    simpa [Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul Γ(Y, V) Γ(Y, V))]
      using primeIdealOf_mem_minimalPrimes_of_mem_genericPoints V hV (f x) hfxV (hf hxwa))
  rw [← IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU]
  change f.appLE V U hUV s ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  rw [← hqx]
  apply hq.1.2
  rw [Submodule.mem_annihilator_span_singleton]
  exact hm

/-- **Stacks Project, Tag 02OU (reduced source).** If a morphism from a reduced scheme sends
every generic point of an irreducible component to a generic point of an irreducible component,
then pullbacks of meromorphic functions along it are defined. -/
@[stacks 02OU "reduced_source"]
theorem pullbacksMeromorphicSections_of_reduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsReduced X] (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    PullbacksMeromorphicSections f.toLRSHom :=
  pullbacksMeromorphicSections_of_mapsTo_genericPoints f (by
    simpa only [AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints] using hf)

/-- **Stacks Project, Tag 02OU (integral source).** If the source of a morphism of schemes is
integral and its generic point maps to a generic point of an irreducible component of the target,
then pullbacks of meromorphic functions are defined. -/
@[stacks 02OU "integral_source"]
lemma pullbacksMeromorphicSections_of_isIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    (h : f (genericPoint X) ∈ genericPoints Y) :
    PullbacksMeromorphicSections f.toLRSHom := pullbacksMeromorphicSections_of_reduced f
  (by simpa only [genericPoints_eq_singleton, Set.mapsTo_singleton] using h)

/-- **Stacks Project, Tag 02OU.** Pullbacks of meromorphic functions are defined along a
dominant morphism between integral schemes. -/
@[stacks 02OU "dominant_integral", ega "IV 21.4.5" "(iii), X,X' integral"]
lemma pullbacksMeromorphicSections_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    PullbacksMeromorphicSections f.toLRSHom := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  apply pullbacksMeromorphicSections_of_reduced f
  simpa [genericPoints_eq_singleton] using ((genericPoint_spec Y).eq h).symm

/-- **Stacks Project, Tag 02OU (associated points).** If every associated point of a locally
Noetherian source scheme maps to the generic point of an irreducible component of the target,
then pullbacks of meromorphic functions are defined. -/
@[stacks 02OU "associated_points", ega "IV 21.4.5" "(ii), to generic points"]
theorem pullbacksMeromorphicSections_of_associatedPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X]
    (h : ∀ x ∈ Stacks.Divisors.schemeAssociatedPoints X,
      ∃ Z ∈ irreducibleComponents Y, IsGenericPoint (f x) Z) :
    PullbacksMeromorphicSections f.toLRSHom := by
  refine pullbacksMeromorphicSections_of_mapsTo_genericPoints f (fun x hx => ?_)
  obtain ⟨Z, hZ, hg⟩ := h x (by
    simpa only [Stacks.Divisors.schemeWeaklyAssociatedPoints,
      ← AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints X
        (SheafOfModules.unit X.ringCatSheaf)] using hx)
  simpa only [genericPoints, Set.mem_ofPred_eq, hg.def] using hZ

/-- **Stacks Project, Tag 02OU (no embedded points).** If a morphism from a locally Noetherian
scheme without embedded points sends every generic point of an irreducible component to a
generic point of an irreducible component, then pullbacks of meromorphic functions along it are
defined. -/
@[stacks 02OU "no_embedded_points"]
theorem pullbacksMeromorphicSections_of_noEmbeddedPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X]
    (hX : AlgebraicGeometry.HasNoEmbeddedPoints X)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    PullbacksMeromorphicSections f.toLRSHom := by
  apply pullbacksMeromorphicSections_of_associatedPoints
  intro x hx
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : genericPoints X := genericPoints.ofComponent C
  have hηx : η.1 ⤳ x := specializes_iff_mem_closure.mpr <|
    (genericPoints.isGenericPoint_ofComponent C).symm ▸ mem_irreducibleComponent
  have hη_eq : η.1 = x := by
    by_contra hne
    exact hX x ⟨hx, ⟨η.1,
      AlgebraicGeometry.mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent
        X C.property (genericPoints.isGenericPoint_ofComponent C),
      hηx, hne⟩⟩
  exact ⟨closure ({f x} : Set Y), hf (hη_eq ▸ η.property), isGenericPoint_closure⟩

/-- Pullbacks of meromorphic functions are defined along a flat morphism of schemes. -/
@[stacks 02OU "flat", ega "IV 21.4.5" "(i)"]
theorem pullbacksMeromorphicSections_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PullbacksMeromorphicSections f.toLRSHom := by
  apply pullbacksMeromorphicSections_of_affine f
  intro V U hV hU hUV s hs
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Module.Flat Γ(Y, V) Γ(X, U) := Flat.flat_appLE f hV hU hUV
  exact IsSMulRegular.of_flat hs


end AlgebraicGeometry

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchCount
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria

/-!
# Geometric unibranchness descends along a flat morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x` be a point of
`|X|` at which `f` is flat. If `X` is geometrically unibranch at `x`, then `Y` is geometrically
unibranch at the image point `f(x)`.

## Main results

* `AlgebraicGeometry.Space.isGeometricallyUnibranchAt_of_isFlatAt`: geometric unibranchness at
  a point descends along a morphism of algebraic spaces that is flat at that point.

## Implementation notes

The descent happens on the étale local rings. A geometric point `x̄` above `x` has a unique
minimal prime in `𝒪_{X, x̄}` by the branch criteria of Tag 06DK, and the induced homomorphism
`𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` is flat by Tag 04NG. A flat local homomorphism of local rings is
faithfully flat, hence injective, so every minimal prime of the source is the contraction of a
minimal prime of the target — going down, Tag 00HS — and `𝒪_{Y, f(x̄)}` has a unique minimal
prime as well.

That conclusion is transported back to the charts of `Y` by Tag 04KF: the étale local ring at a
geometric point is a strict henselization of the local ring of a chart at the point the
geometric point selects, so that chart has exactly one geometric branch there. Having one
geometric branch is an étale-local property of germs of schemes, so by Tag 04N2 it holds on
*every* étale chart of `Y` above `f(x)`, which is the chart condition of Tag 06DL defining
geometric unibranchness at a point of an algebraic space.

## References

* [Stacks Project, Tag 06DQ](https://stacks.math.columbia.edu/tag/06DQ)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-- **Going down for minimal primes.** If `φ : R →+* T` is injective and `T` has a unique
minimal prime, then so does `R`: every minimal prime of `R` is the contraction of a minimal
prime of `T`. -/
private theorem existsUnique_minimalPrimes_of_injective {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (hφ : Function.Injective φ) (hT : ∃! q : Ideal T, q ∈ minimalPrimes T) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  obtain ⟨q, hq, hqu⟩ := hT
  have huniq : ∀ p : Ideal R, p ∈ minimalPrimes R → p = q.comap φ := by
    intro p hp
    obtain ⟨q', hq', heq⟩ := Ideal.exists_minimalPrimes_comap_eq (I := (⊥ : Ideal T)) φ p
      (by simpa only [Ideal.comap_bot_of_injective φ hφ] using hp)
    rw [hqu q' hq'] at heq
    exact heq.symm
  have : (q.comap φ).IsPrime := hq.1.1.comap φ
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := q.comap φ) bot_le
  exact ⟨p, hp, fun p' hp' ↦ (huniq p' hp').trans (huniq p hp).symm⟩

/-- **Stacks 00HS for local rings.** A flat local homomorphism of local rings is faithfully
flat, hence injective, so a unique minimal prime in the target forces one in the source. -/
private theorem existsUnique_minimalPrimes_of_flat {R T : Type*} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] (φ : R →+* T) [IsLocalHom φ] (hφ : φ.Flat)
    (hT : ∃! q : Ideal T, q ∈ minimalPrimes T) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  let : Algebra R T := φ.toAlgebra
  have : Module.Flat R T := hφ
  have : IsLocalHom (algebraMap R T) := ‹IsLocalHom φ›
  have : Module.FaithfullyFlat R T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact existsUnique_minimalPrimes_of_injective φ (FaithfulSMul.algebraMap_injective R T) hT

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 04KF.** The number of geometric branches of a chart at the point selected by a
small étale neighbourhood of a geometric point is the number of minimal primes of the étale
local ring there, the latter being a strict henselization of the former's local ring. -/
private theorem numberOfGeometricBranches_chart_eq_encard_minimalPrimes
    (hF : IsAlgebraicSpace B S hS F) {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) :
    numberOfGeometricBranches (chartScheme V.chart)
        ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)) =
      Set.encard (minimalPrimes (etaleLocalRing B S hS F x)) := by
  have hV : (bigEtaleSiteOfFppfSite B).Contains (chartScheme V.chart) :=
    V.chart.obj.left.left.property
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let κ := separableClosure (ResidueField R) (chartGeometricPoint V).residueField
  let T := IsLocalRing.henselizationTower R κ
  refine (encard_minimalPrimes_eq_numberOfGeometricBranchesOfLocalRing R κ
    T.strictHenselization).symm.trans ?_
  exact (Set.encard_congr (bijOn_minimalPrimes_ringEquiv
    (strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B) hV T)).equiv).symm

/-- **Stacks 06DQ.** Let `f : F ⟶ G` be a morphism of algebraic spaces over a scheme `S` and
let `x` be a point of `|F|`. If `f` is flat at `x` and `F` is geometrically unibranch at `x`,
then `G` is geometrically unibranch at `f(x)`. -/
@[stacks 06DQ]
theorem isGeometricallyUnibranchAt_of_isFlatAt (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : points B S hS F)
    (hf : IsFlatAt B S hS f x) (hx : IsGeometricallyUnibranchAt B S hS F x) :
    IsGeometricallyUnibranchAt B S hS G (pointsMap B S hS F f x) := by
  obtain ⟨xb, hxb⟩ := exists_geometricRepresentative B S hS F x
  have hcrit : IsGeometricallyUnibranchAt B S hS F x ↔
      HasUniqueMinimalPrimeAtGeometricPoints B S hS F x :=
    (uniqueBranch_tfae B S hS F hF x).out 4 5
  have huX : ∃! q : Ideal (etaleLocalRing B S hS F xb), q ∈ minimalPrimes _ :=
    hcrit.mp hx xb hxb
  rw [← hxb] at hf
  have hflat := (isFlatAt_iff_etaleLocalRingMap_flat hF hG f xb).mp hf
  let : IsLocalRing (etaleLocalRing B S hS F xb) :=
    isLocalRing_etaleLocalRing B S hS F hF xb
  let : IsLocalRing (etaleLocalRing B S hS G (geometricPointMap f xb)) :=
    isLocalRing_etaleLocalRing B S hS G hG (geometricPointMap f xb)
  have := isLocalHom_etaleLocalRingMap B S hS hF hG f xb
  have huY : ∃! q : Ideal (etaleLocalRing B S hS G (geometricPointMap f xb)),
      q ∈ minimalPrimes _ :=
    existsUnique_minimalPrimes_of_flat _ hflat huX
  obtain ⟨W, a, hsurj, hetale⟩ := hG.exists_atlas
  obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS G hG
    (geometricPointMap f xb) a hsurj hetale
  have himage : (geometricPointMap f xb).image = pointsMap B S hS F f x := by
    rw [geometricPointMap_image, hxb]
  have hbranch : numberOfGeometricBranches (chartScheme V.chart)
      ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)) = 1 := by
    rw [numberOfGeometricBranches_chart_eq_encard_minimalPrimes B S hS hG V]
    obtain ⟨q, hq, hqu⟩ := huY
    rw [Set.encard_eq_one]
    exact ⟨q, Set.eq_singleton_iff_unique_mem.mpr ⟨hq, hqu⟩⟩
  have hall := (forall_etale_chart_iff_exists_etale_chart B S hS G hG
    (pointsMap B S hS F f x)
    (fun Z : GermOfScheme.{u} ↦ numberOfGeometricBranches Z.scheme Z.point = 1)
    (GermOfScheme.isEtaleLocal_numberOfGeometricBranches_eq 1)).mpr
      ⟨V.chart.obj.left, V.chart.obj.hom, V.chart.property, chartFieldValuedPoint V,
        (chartFieldValuedPoint_pointsMap V).trans himage, hbranch⟩
  intro U p hp
  exact (isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).mpr
    ((numberOfGeometricBranches_eq_one_iff _ _).mp (hall U.1.left U.1.hom U.2 p hp))

end AlgebraicGeometry.Space

end

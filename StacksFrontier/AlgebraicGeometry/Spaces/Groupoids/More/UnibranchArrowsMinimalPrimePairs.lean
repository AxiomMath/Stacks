module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.IdentityArrowRetractions
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.UnibranchEtaleLocalRingCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.UniqueBranchOneGeometricPoint

/-!
# Geometric unibranchness of an arrow space from Tag 06DU at its étale local rings

Let `G` be a groupoid in algebraic spaces whose object space is the spectrum of a field `k`.
This file reduces geometric unibranchness of the arrow space of `G` ([Stacks Project, Tag 06E4])
to a condition on étale local rings at a single geometric point of each restriction of `G` along
an algebraically closed extension `k'/k`: the étale local ring of the restricted arrow space at
the identity arrow at the tautological geometric point of the object space has a unique minimal
prime.  That condition in turn follows from Tag 06DU for the pair of étale local rings
`A = 𝒪_{R, e}` and `C = 𝒪_{R ×_{s, U, t} R, (e, e)}`, stated as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.MinimalPrimesSplitAtIdentityArrow`.

Condition (5) of [Stacks Project, Tag 06DK] at the point of an identity arrow quantifies over
*every* geometric point above that point; it reduces to the one geometric point
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrowPoint` because the number of minimal
primes of the étale local ring is the same at every geometric point above a given point
(`AlgebraicGeometry.Space.hasUniqueMinimalPrimeAtGeometricPoints_of_geometricPoint`).

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.extensionTautologicalGeometricPoint`: the
  tautological geometric point of the object space of the restriction of a groupoid over a field
  along an algebraically closed extension of that field.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.MinimalPrimesSplitAtIdentityArrow`: Tag 06DU for
  the étale local rings of the arrow space and of the space of composable pairs, at the identity
  arrow at a geometric point of the object space.

## Main results

* `GroupoidInAlgebraicSpaces.hasUniqueMinimalPrimeAtGeometricPoints_restrictionIdentityArrow`:
  condition (5) of Tag 06DK at the point of the identity arrow of a restriction follows from a
  unique minimal prime in the étale local ring at the single geometric point given by the
  identity arrow at the tautological geometric point of the object space.
* `GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_identityArrowMinimalPrimes`:
  the arrow space of a groupoid over a field is geometrically unibranch as soon as, for every
  algebraically closed extension of that field in the site, the étale local ring of the restricted
  arrow space at that one geometric point has a unique minimal prime.
* `GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_minimalPrimesSplit`:
  the same conclusion from Tag 06DU for the two étale local rings.

## Implementation notes

The restriction produced by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict` has
`objects_eq` and `arrows_eq` equal to `rfl`, so its object space *is* the algebraic space of the
spectrum of the extension field and its arrow space *is*
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows`.

## References

* [Stacks Project, Tag 06E4](https://stacks.math.columbia.edu/tag/06E4)
* [Stacks Project, Tag 06DK](https://stacks.math.columbia.edu/tag/06DK)
* [Stacks Project, Tag 06DU](https://stacks.math.columbia.edu/tag/06DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_unibranchArrowsMinimalPrimePairs
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : AlgebraicGeometry.Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Tag 06DU for the étale local rings at an identity arrow.** Write `A` for the étale local
ring of the arrow space of a groupoid in algebraic spaces at the identity arrow at a geometric
point `z` of the object space, and `C` for the étale local ring of the space of composable pairs
of arrows at the pair of identity arrows.  This says that contracting a minimal prime of `C`
along the two projections is a bijection onto the pairs of minimal primes of `A`, and that each
minimal prime of `C` is the smallest prime containing the images of its two contractions. -/
def MinimalPrimesSplitAtIdentityArrow (G : GroupoidInAlgebraicSpaces C S hS B)
    (z : Space.GeometricPoint C S hS G.objects.obj) : Prop :=
  Set.BijOn
      (fun q : Ideal (Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
          (identityPairPoint G z)) =>
        (q.comap (identityPairLeft G z), q.comap (identityPairRight G z)))
      (minimalPrimes (Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z)))
      (minimalPrimes (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z)) ×ˢ
        minimalPrimes (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))) ∧
    ∀ q ∈ minimalPrimes (Space.etaleLocalRing C S hS
        (pullback G.source.hom G.target.hom) (identityPairPoint G z)),
      ∀ P : Ideal (Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z)), P.IsPrime →
      (q.comap (identityPairLeft G z)).map (identityPairLeft G z) ≤ P →
      (q.comap (identityPairRight G z)).map (identityPairRight G z) ≤ P → q ≤ P

section Restriction

variable (C) (hS) {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))
  (structureMap : Spec (.of k) ⟶ S) (G : GroupoidInAlgebraicSpaces C S hS B)
  (hU : G.objects = Space.fieldSpace C hS hk structureMap)

/-- The tautological geometric point of the object space of the restriction of a groupoid over a
field along an algebraically closed extension field: the identity section of the spectrum of that
extension. -/
def extensionTautologicalGeometricPoint {k' : Type u} [Field k'] (alg' : IsAlgClosed k')
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k') :
    Space.GeometricPoint C S hS
      (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj :=
  ⟨extensionTautologicalPoint C hS hk structureMap G hU hk' i, alg'⟩

/-- **Condition (5) of Tag 06DK at the identity arrow of a restriction, from one geometric
point.** If the étale local ring of the restricted arrow space at the identity arrow at the
tautological geometric point of the object space has a unique minimal prime, then so does the
étale local ring at every geometric point above the point of that identity arrow. -/
theorem hasUniqueMinimalPrimeAtGeometricPoints_restrictionIdentityArrow
    {k' : Type u} [Field k'] (alg' : IsAlgClosed k')
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (h : ∃! q : Ideal (Space.etaleLocalRing C S hS
        (extensionRestriction C hS hk structureMap G hU hk' i).arrows.obj
        (identityArrowPoint (extensionRestriction C hS hk structureMap G hU hk' i)
          (extensionTautologicalGeometricPoint C hS hk structureMap G hU alg' hk' i))),
      q ∈ minimalPrimes _) :
    Space.HasUniqueMinimalPrimeAtGeometricPoints C S hS
      (restrictionArrows G
        (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj
      (restrictionIdentityArrowPoint C hS hk structureMap G hU hk' i) :=
  Space.hasUniqueMinimalPrimeAtGeometricPoints_of_geometricPoint C S hS
    (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).property _
    (identityArrowPoint (extensionRestriction C hS hk structureMap G hU hk' i)
      (extensionTautologicalGeometricPoint C hS hk structureMap G hU alg' hk' i))
    (pointsMap_extensionTautologicalPoint C hS hk structureMap G hU hk' i
      (identityArrow (extensionRestriction C hS hk structureMap G hU hk' i))) h

/-- Let `G` be a groupoid in algebraic spaces whose object space is the spectrum of a field `k`.
Suppose that for every algebraically closed field extension `k'/k` whose spectrum lies in the
site, the étale local ring of the restricted arrow space at the identity arrow at the tautological
geometric point of the object space has a unique minimal prime.  Then the arrow space of `G` is
geometrically unibranch. -/
theorem isGeometricallyUnibranch_arrows_of_identityArrowMinimalPrimes
    (hres : ∀ (k' : Type u) (_ : Field k') (alg' : IsAlgClosed k') (i : k →+* k')
      (hk' : C.Contains (Spec (.of k'))),
      ∃! q : Ideal (Space.etaleLocalRing C S hS
          (extensionRestriction C hS hk structureMap G hU hk' i).arrows.obj
          (identityArrowPoint (extensionRestriction C hS hk structureMap G hU hk' i)
            (extensionTautologicalGeometricPoint C hS hk structureMap G hU alg' hk' i))),
        q ∈ minimalPrimes _) :
    Space.IsGeometricallyUnibranch C S hS G.arrows.obj :=
  isGeometricallyUnibranch_arrows_of_minimalPrimes C hS hk structureMap G hU
    fun k' field' alg' i hk' => hasUniqueMinimalPrimeAtGeometricPoints_restrictionIdentityArrow
      C hS hk structureMap G hU alg' hk' i (hres k' field' alg' i hk')

/-- Let `G` be a groupoid in algebraic spaces whose object space is the spectrum of a field `k`.
Suppose that for every algebraically closed field extension `k'/k` whose spectrum lies in the
site, the étale local rings of the restricted arrow space at the identity arrow and of its space
of composable pairs at the pair of identity arrows satisfy
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.MinimalPrimesSplitAtIdentityArrow`.  Then the arrow
space of `G` is geometrically unibranch. -/
theorem isGeometricallyUnibranch_arrows_of_minimalPrimesSplit
    (h06DU : ∀ (k' : Type u) (_ : Field k') (alg' : IsAlgClosed k') (i : k →+* k')
      (hk' : C.Contains (Spec (.of k'))),
      MinimalPrimesSplitAtIdentityArrow
        (extensionRestriction C hS hk structureMap G hU hk' i)
        (extensionTautologicalGeometricPoint C hS hk structureMap G hU alg' hk' i)) :
    Space.IsGeometricallyUnibranch C S hS G.arrows.obj := by
  refine isGeometricallyUnibranch_arrows_of_identityArrowMinimalPrimes C hS hk structureMap
    G hU fun k' field' alg' i hk' => ?_
  obtain ⟨hbij, hsmallest⟩ := h06DU k' field' alg' i hk'
  let G' := extensionRestriction C hS hk structureMap G hU hk' i
  let z := extensionTautologicalGeometricPoint C hS hk structureMap G hU alg' hk' i
  let _ : IsLocalRing (Space.etaleLocalRing C S hS G'.arrows.obj
      (identityArrowPoint G' z)) :=
    Space.isLocalRing_etaleLocalRing C S hS G'.arrows.obj G'.arrows.property _
  exact existsUnique_minimalPrimes_etaleLocalRing_identityArrow G' z
    (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) hk' rfl
    (fun w => Space.isField_etaleLocalRing_fieldSpace C hS hk'
      (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) w)
    hbij hsmallest

end Restriction

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end

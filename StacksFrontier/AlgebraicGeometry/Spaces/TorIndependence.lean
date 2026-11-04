module

public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.Homology.Tor.Independence

/-!
# Tor independence of algebraic spaces

Two algebraic spaces over a common base are *Tor independent* if their étale
local rings are Tor independent at every compatible pair of geometric points.

## Main definitions

* `AlgebraicGeometry.Space.TorIndependent` is Tor independence over an algebraic space.
* `AlgebraicGeometry.Space.IsEtaleLocalRingMap` characterizes the local-ring map by germs.

## Implementation notes

The induced homomorphisms on étale local rings are specified by their action
on germs of sections in compatible étale charts. At each diagram of geometric
points, the definition asks for such homomorphisms whose algebra structures
satisfy the ring-theoretic Tor-independence condition. This expresses the
definition without choosing maps using an additional existence theorem.

## References

* [Stacks Project, Tag 08IP](https://stacks.math.columbia.edu/tag/08IP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A map of étale local rings is induced by a morphism if it commutes with
the germ maps for compatible diagrams of étale scheme charts. -/
public def IsEtaleLocalRingMap {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (x : GeometricPoint B S hS F)
    (φ : etaleLocalRing B S hS H (geometricPointMap f x) →+*
      etaleLocalRing B S hS F x) : Prop :=
  ∀ (U : SmallEtaleNeighborhood x)
    (V : SmallEtaleNeighborhood (geometricPointMap f x))
    (g : U.chart.obj.left ⟶ V.chart.obj.left),
    U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom → U.point ≫ g = V.point →
    (etaleLocalRingGerm B S hS F x (Opposite.op U)).comp
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom) =
    φ.comp (etaleLocalRingGerm B S hS H (geometricPointMap f x) (Opposite.op V))

/-- **Stacks 08IP.** Two algebraic spaces are Tor independent over a base when the geometric
étale local rings at every compatible pair of points are Tor independent
for the homomorphisms induced on germs by their structure morphisms. -/
@[stacks 08IP]
public def TorIndependent {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : IsAlgebraicSpace B S hS F) (_hG : IsAlgebraicSpace B S hS G)
    (_hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ H) (g : G ⟶ H) : Prop :=
  ∀ (x : GeometricPoint B S hS F)
    (y : GeometricPoint B S hS G)
    (h : geometricPointMap f x = geometricPointMap g y),
    let R := etaleLocalRing B S hS H (geometricPointMap f x)
    let A := etaleLocalRing B S hS F x
    let C := etaleLocalRing B S hS G y
    ∃ (φ : R →+* A) (ψ : etaleLocalRing B S hS H
      (geometricPointMap g y) →+* C),
      IsEtaleLocalRingMap f x φ ∧ IsEtaleLocalRingMap g y ψ ∧
        (letI : Algebra R A := φ.toAlgebra
         letI : Algebra R C := ((eqToHom (congrArg (etaleLocalRing B S hS H) h) ≫
           CommRingCat.ofHom ψ).hom).toAlgebra
         RingTheory.TorIndependence.TorIndependent R A C)

end AlgebraicGeometry.Space

end

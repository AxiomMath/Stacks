module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.SeparableClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# The étale local ring of a scheme, and henselization at a point

At a geometric point `s` of a scheme `S`, the *étale local ring* is the stalk at `s` of the
structure sheaf on the small étale site of `S`; it plays the role for the étale topology that
the ordinary local ring `𝒪_{S,x}` plays for the Zariski topology. At an ordinary point `x` of
`S` the *henselization* of `S` at `x` is the spectrum of the henselization of `𝒪_{S,x}`,
formed from the chosen henselization tower of that local ring over a separable closure of its
residue field.

## Main definitions

* `AlgebraicGeometry.etaleLocalRing` is the étale local ring at a geometric point.
* `AlgebraicGeometry.localHenselizationTower` is the chosen henselization tower of the local
  ring of a scheme at a point.
* `AlgebraicGeometry.henselizationRing` is the henselization of that local ring, and
  `AlgebraicGeometry.henselization` the affine scheme it defines.
* `AlgebraicGeometry.henselizationToBase` is the canonical morphism from the henselization of
  `S` at `x` to `S`.

## Implementation notes

The small étale site carries a size cutoff, so the étale local ring is parameterized by a big
étale site `B` and a proof that `S` is contained in it. It is the ring-valued stalk of the
structure sheaf, i.e. an object of `RingCat`; it is *not* given a `CommRing` instance here,
since commutativity of the stalk is obtained from the identification of the étale local ring
with a strict henselization.

The separable closure used to form the henselization tower is `SeparableClosure` of the
residue field of `𝒪_{S,x}`, so that the tower — and hence the henselization — is a single
chosen object depending only on `S` and `x`. The local-ring and algebra structures of the
tower's henselization are re-exported as instances for `henselizationRing`, so that
`Spec` of it and the canonical map from `𝒪_{S,x}` are available without unfolding the tower.

## References

* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The étale local ring of `S` at a geometric point `s`: the stalk at `s` of the structure
sheaf of the small étale site of `S`. -/
@[stacks 03PS "part (1)",
  sga "7 I 0.0.4" "strict henselization",
  sga "4 VIII 4.3" "strictly local ring"]
public abbrev etaleLocalRing (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) : RingCat.{u} :=
  etaleStalk B S hS s (SmallEtale.structureSheaf B S hS).obj

/-- The chosen henselization tower of the local ring of `S` at a point `x`, taken over the
separable closure of its residue field. -/
public abbrev localHenselizationTower (S : Scheme.{u}) (x : S) :=
  henselizationTower (S.presheaf.stalk x)
    (SeparableClosure (ResidueField (S.presheaf.stalk x)))

/-- The henselization of the local ring of `S` at a point `x`. -/
@[stacks 03PS "part (2)"]
public abbrev henselizationRing (S : Scheme.{u}) (x : S) : Type u :=
  (localHenselizationTower S x).henselization

/-- The henselization of a local ring of a scheme is a commutative ring. -/
public instance henselizationRingCommRing (S : Scheme.{u}) (x : S) :
    CommRing (henselizationRing S x) :=
  HenselizationTower.instCommRingHenselization (localHenselizationTower S x)

/-- The henselization of a local ring of a scheme is local. -/
public instance henselizationRingIsLocalRing (S : Scheme.{u}) (x : S) :
    IsLocalRing (henselizationRing S x) :=
  HenselizationTower.instIsLocalRingHenselization (localHenselizationTower S x)

/-- The henselization of a local ring of a scheme is an algebra over that local ring. -/
public instance henselizationRingAlgebra (S : Scheme.{u}) (x : S) :
    Algebra (S.presheaf.stalk x) (henselizationRing S x) :=
  HenselizationTower.instAlgebraHenselization (localHenselizationTower S x)

/-- The henselization of a scheme at an ordinary point: the spectrum of the henselization of
its local ring. -/
@[stacks 03PS "part (4)"]
public abbrev henselization (S : Scheme.{u}) (x : S) : Scheme.{u} :=
  Spec (.of (henselizationRing S x))

/-- The canonical morphism from the henselization of `S` at `x` to `S`, the spectrum of the
canonical map `𝒪_{S,x} → 𝒪_{S,x}ʰ` followed by the canonical morphism from the local scheme
at `x`. -/
public def henselizationToBase (S : Scheme.{u}) (x : S) : henselization S x ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk x)
    (henselizationRing S x))) ≫ S.fromSpecStalk x

end AlgebraicGeometry

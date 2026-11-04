module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Basic
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksCore.Tactic.StacksAttribute

/-!
# The rational double point situation

A Gorenstein rational surface singularity is a rational double point. This file packages the
standing hypotheses under which such a singularity is studied: a two-dimensional local normal
Nagata domain which defines a rational singularity, whose completion is normal, which is
Gorenstein, and which is not regular.

## Main definitions

* `AlgebraicGeometry.RationalDoublePointSituation` is the standing rational double point
  situation.
* `AlgebraicGeometry.RationalDoublePointSituation.base` and `.closedPoint` are `Spec(A)` and its
  closed point.
* `AlgebraicGeometry.RationalDoublePointSituation.toRationalSingularitySituation` views the
  situation, together with a normal modification of `Spec(A)` and an enumeration of the
  irreducible components of its special fibre, as a rational singularity situation.

## Implementation notes

Normality of the completion is normality of the adic completion of `A` along its maximal ideal,
taken as an abstract ring. The maximal ideal and residue field are the canonical ones attached
to a local ring, and the Noetherian hypothesis is obtained from the Nagata one rather than
recorded as separate data. Non-regularity is recorded for the local ring `A` itself.

## References

* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BGC.** A Nagata local normal domain of dimension two which defines a
rational singularity, whose completion is normal, which is Gorenstein, and which is not
regular. -/
@[stacks 0BGC]
structure RationalDoublePointSituation where
  /-- The local normal Nagata domain. -/
  A : Type u
  /-- The commutative-ring structure on `A`. -/
  [commRing : CommRing A]
  /-- The local-ring hypothesis on `A`. -/
  [localRing : IsLocalRing A]
  /-- The hypothesis that `A` is a normal domain. -/
  [normalDomain : IsNormalDomain A]
  /-- The ring `A` is Nagata. -/
  nagata : IsNagataRing A
  /-- The ring `A` has Krull dimension two. -/
  dimension_two : ringKrullDim A = 2
  /-- The ring `A` defines a rational singularity. -/
  definesRationalSingularity : DefinesRationalSingularity A
  /-- The completion of `A` along its maximal ideal is a normal domain. -/
  completion_normalDomain : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)
  /-- The ring `A` is Gorenstein. -/
  gorenstein :
    letI : IsNoetherianRing A := nagata.isNoetherianRing
    Dualizing.IsGorensteinLocalRing A
  /-- The ring `A` is not regular. -/
  not_isRegularLocalRing : ¬ IsRegularLocalRing A

attribute [instance] RationalDoublePointSituation.commRing
  RationalDoublePointSituation.localRing RationalDoublePointSituation.normalDomain

namespace RationalDoublePointSituation

/-- A Nagata ring is Noetherian. -/
instance noetherian (S : RationalDoublePointSituation) : IsNoetherianRing S.A :=
  S.nagata.isNoetherianRing

/-- The maximal ideal `𝔪` of the local ring. -/
abbrev maximalIdeal (S : RationalDoublePointSituation) : Ideal S.A :=
  IsLocalRing.maximalIdeal S.A

/-- The residue field `𝜅` of the local ring. -/
abbrev residueField (S : RationalDoublePointSituation) : Type u :=
  IsLocalRing.ResidueField S.A

/-- The affine base `Spec(A)`. -/
abbrev base (S : RationalDoublePointSituation) : Scheme.{u} :=
  Spec (.of S.A)

/-- The closed point of the affine local scheme `Spec(A)`. -/
abbrev closedPoint (S : RationalDoublePointSituation) : S.base :=
  IsLocalRing.closedPoint S.A

/-- A rational double point situation, a normal modification of the spectrum of its ring, and an
enumeration of the irreducible components of the special fibre of that modification, together
form a rational singularity situation. -/
def toRationalSingularitySituation (S : RationalDoublePointSituation.{u}) (X : Scheme.{u})
    [IsNormal X] (f : X ⟶ S.base) (hf : IsModification f) (numberOfComponents : ℕ)
    (components : Fin numberOfComponents ≃ {Z : Set (f.fiber S.closedPoint) //
      Z ∈ irreducibleComponents (f.fiber S.closedPoint)}) :
    RationalSingularitySituation.{u} where
  A := S.A
  nagata := S.nagata
  dimension_two := S.dimension_two
  definesRationalSingularity := S.definesRationalSingularity
  X := X
  f := f
  modification := hf
  numberOfComponents := numberOfComponents
  components := components

end RationalDoublePointSituation

end AlgebraicGeometry

end

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import Mathlib.RingTheory.LocalRing.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Glueing rings along a common fraction field

Glueing two rings along a common fraction field is governed by the standing data of a field
`K` together with two subrings `A` and `B` of `K`, each having `K` as its own fraction field.
The fourth corner of the resulting commutative square is the ring `R = A ×_K B = A ∩ B`: the
two descriptions agree because both inclusions into `K` are injective, so a pair of elements
of `A` and `B` with the same image in `K` is the same thing as a single element of `K` lying
in both subrings.

Glueing two one-dimensional rings is governed by this data together with the finiteness and
dimension hypotheses on them. This module also records that data for the case in which the
first ring is Noetherian semilocal of dimension one and the second is a discrete valuation
ring, and constructs the intersection ring and the algebra structures it carries.

## Main definitions

* `Ring.GluingSituation` bundles the common fraction field and its two subrings.
* `Ring.GluingSituation.R` is their intersection inside the common fraction field, the fourth
  corner of the commutative square.
* `Ring.GluingSituation.equivPullback` identifies that intersection with the fibre product
  `A ×_K B`.
* `Ring.SemilocalDVRGluingSituation` bundles the common fraction field, its two subrings, and
  the finiteness and dimension hypotheses.
* `Ring.SemilocalDVRGluingSituation.R` is their intersection inside the common fraction field.
* `Ring.SemilocalDVRGluingSituation.toGluingSituation` forgets those hypotheses.

## Implementation notes

The inclusions into the common field are represented by subrings. Consequently the
fiber-product ring is definitionally their infimum in the lattice of subrings, and the square
commutes by definition. The fibre product itself is Mathlib's `RingHom.pullback`, the subring
of `A × B` cut out by agreement in `K`. Semilocality is expressed by finiteness of the maximal
spectrum.

## References

* [Stacks Project, Section 33.41 (Tag 09MX)](https://stacks.math.columbia.edu/tag/09MX)
* [Stacks Project, Tag 09MY](https://stacks.math.columbia.edu/tag/09MY)
-/

@[expose] public section

universe u

namespace Ring

/-- **Stacks Project, Tag 09MY.** The standing data for glueing two rings along a common
fraction field: a field `K` together with two subrings `A` and `B` of `K`, each of which has
`K` as its fraction field. These fit into a commutative square whose fourth corner is the
ring `R = A ×_K B = A ∩ B`. -/
@[stacks 09MY "the standing data"]
public structure GluingSituation where
  /-- The common fraction field. -/
  K : Type u
  /-- The field structure on the common fraction field. -/
  [fieldK : Field K]
  /-- The first subring of the common fraction field. -/
  A : Subring K
  /-- The second subring of the common fraction field. -/
  B : Subring K
  /-- The common field is the fraction field of `A`. -/
  [isFractionRingA : IsFractionRing A K]
  /-- The common field is the fraction field of `B`. -/
  [isFractionRingB : IsFractionRing B K]

attribute [instance]
  GluingSituation.fieldK
  GluingSituation.isFractionRingA
  GluingSituation.isFractionRingB

namespace GluingSituation

/-- The fourth corner `R = A ×_K B` of the commutative square, realized as the intersection
of `A` and `B` in `K`. -/
@[stacks 09MY "the fourth corner of the square"]
public def R (S : GluingSituation) : Subring S.K := S.A ⊓ S.B

/-- The canonical algebra structure induced by the inclusion `R ⊆ A`. -/
public instance algebraRA (S : GluingSituation) : Algebra S.R S.A :=
  (Subring.inclusion inf_le_left).toAlgebra

/-- The canonical algebra structure induced by the inclusion `R ⊆ B`. -/
public instance algebraRB (S : GluingSituation) : Algebra S.R S.B :=
  (Subring.inclusion inf_le_right).toAlgebra

/-- The inclusions `R ⊆ A ⊆ K` form the canonical scalar tower. -/
public instance isScalarTowerRAK (S : GluingSituation) : IsScalarTower S.R S.A S.K :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The inclusions `R ⊆ B ⊆ K` form the canonical scalar tower. -/
public instance isScalarTowerRBK (S : GluingSituation) : IsScalarTower S.R S.B S.K :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- An element of the common field lies in `R` exactly when it lies in both subrings. -/
public lemma mem_R_iff (S : GluingSituation) {x : S.K} : x ∈ S.R ↔ x ∈ S.A ∧ x ∈ S.B :=
  Subring.mem_inf

/-- The fourth corner of the square is the intersection `A ∩ B` inside the common field. -/
@[stacks 09MY "the identification `R = A ∩ B`"]
public lemma coe_R (S : GluingSituation) : (S.R : Set S.K) = (S.A : Set S.K) ∩ S.B :=
  Subring.coe_inf S.A S.B

/-- The square commutes: the two composites `R → A → K` and `R → B → K` agree. -/
@[stacks 09MY "commutativity of the square"]
public lemma subtype_comp_algebraMap_eq (S : GluingSituation) :
    S.A.subtype.comp (algebraMap S.R S.A) = S.B.subtype.comp (algebraMap S.R S.B) :=
  RingHom.ext fun _ => rfl

/-- The two components of an element of the fibre product have the same image in the common
field. -/
public lemma coe_fst_eq_coe_snd {S : GluingSituation}
    (y : RingHom.pullback S.A.subtype S.B.subtype) :
    ((y : S.A × S.B).1 : S.K) = ((y : S.A × S.B).2 : S.K) :=
  RingHom.mem_eqLocus.mp y.2

/-- The fourth corner of the square is the fibre product `A ×_K B`: the intersection of `A`
and `B` in `K` is canonically isomorphic to the subring of `A × B` of pairs having the same
image in `K`. -/
@[stacks 09MY "the identification `R = A ×_K B`"]
public def equivPullback (S : GluingSituation) :
    S.R ≃+* RingHom.pullback S.A.subtype S.B.subtype where
  toFun x := ⟨(⟨x.1, (S.mem_R_iff.mp x.2).1⟩, ⟨x.1, (S.mem_R_iff.mp x.2).2⟩), rfl⟩
  invFun y :=
    ⟨(y.1.1 : S.K), S.mem_R_iff.mpr ⟨y.1.1.2, (coe_fst_eq_coe_snd y) ▸ y.1.2.2⟩⟩
  left_inv _ := rfl
  right_inv y := Subtype.ext (Prod.ext rfl (Subtype.ext (coe_fst_eq_coe_snd y)))
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The isomorphism onto the fibre product is compatible with the inclusion of `R` into `A`. -/
@[simp]
public lemma coe_equivPullback_fst (S : GluingSituation) (x : S.R) :
    ((S.equivPullback x).1.1 : S.K) = (x : S.K) := rfl

/-- The isomorphism onto the fibre product is compatible with the inclusion of `R` into `B`. -/
@[simp]
public lemma coe_equivPullback_snd (S : GluingSituation) (x : S.R) :
    ((S.equivPullback x).1.2 : S.K) = (x : S.K) := rfl

end GluingSituation

/-- The standing data for the semilocal/DVR gluing argument: two subrings `A` and `B` of
a common fraction field `K`, with `A` a one-dimensional Noetherian semilocal ring and `B`
a discrete valuation ring. -/
public structure SemilocalDVRGluingSituation where
  /-- The common fraction field. -/
  K : Type u
  /-- The field structure on the common fraction field. -/
  [fieldK : Field K]
  /-- The first subring of the common fraction field. -/
  A : Subring K
  /-- The second subring of the common fraction field. -/
  B : Subring K
  /-- The common field is the fraction field of `A`. -/
  [isFractionRingA : IsFractionRing A K]
  /-- The common field is the fraction field of `B`. -/
  [isFractionRingB : IsFractionRing B K]
  /-- The first ring is Noetherian. -/
  [isNoetherianRingA : IsNoetherianRing A]
  /-- The first ring has only finitely many maximal ideals. -/
  [finiteMaximalSpectrumA : Finite (MaximalSpectrum A)]
  /-- The first ring has Krull dimension one. -/
  ringKrullDimA : ringKrullDim A = 1
  /-- The second ring is a discrete valuation ring. -/
  [isDiscreteValuationRingB : IsDiscreteValuationRing B]

attribute [instance]
  SemilocalDVRGluingSituation.fieldK
  SemilocalDVRGluingSituation.isFractionRingA
  SemilocalDVRGluingSituation.isFractionRingB
  SemilocalDVRGluingSituation.isNoetherianRingA
  SemilocalDVRGluingSituation.finiteMaximalSpectrumA
  SemilocalDVRGluingSituation.isDiscreteValuationRingB

namespace SemilocalDVRGluingSituation

/-- The fiber-product ring `A ×_K B`, realized as the intersection of `A` and `B` in `K`. -/
public def R (S : SemilocalDVRGluingSituation) : Subring S.K := S.A ⊓ S.B

/-- The canonical algebra structure induced by the inclusion `R ⊆ A`. -/
public instance algebraRA (S : SemilocalDVRGluingSituation) : Algebra S.R S.A :=
  (Subring.inclusion inf_le_left).toAlgebra

/-- The canonical algebra structure induced by the inclusion `R ⊆ B`. -/
public instance algebraRB (S : SemilocalDVRGluingSituation) : Algebra S.R S.B :=
  (Subring.inclusion inf_le_right).toAlgebra

/-- The inclusions `R ⊆ A ⊆ K` form the canonical scalar tower. -/
public instance isScalarTowerRAK (S : SemilocalDVRGluingSituation) :
    IsScalarTower S.R S.A S.K :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The inclusions `R ⊆ B ⊆ K` form the canonical scalar tower. -/
public instance isScalarTowerRBK (S : SemilocalDVRGluingSituation) :
    IsScalarTower S.R S.B S.K :=
  IsScalarTower.of_algebraMap_eq' rfl

end SemilocalDVRGluingSituation

/-- The semilocal/DVR gluing situation is an instance of the general gluing situation,
obtained by forgetting the finiteness and dimension hypotheses. -/
public def SemilocalDVRGluingSituation.toGluingSituation (S : SemilocalDVRGluingSituation) :
    GluingSituation where
  K := S.K
  A := S.A
  B := S.B

/-- Forgetting the finiteness and dimension hypotheses does not change the intersection
ring. -/
@[simp]
public lemma SemilocalDVRGluingSituation.toGluingSituation_R (S : SemilocalDVRGluingSituation) :
    S.toGluingSituation.R = S.R := rfl

end Ring

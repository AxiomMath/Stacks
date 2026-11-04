module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Completion of the local ring of a locally Noetherian scheme

The completion of the local ring of a locally Noetherian scheme at a point is a Noetherian
complete local ring.  A morphism to the spectrum of a field gives this completion its
canonical algebra structure, and completion does not change the residue field.

## Main definitions

* `AlgebraicGeometry.Scheme.completedLocalRing` is the completion of the stalk at its maximal
  ideal.
* `AlgebraicGeometry.Scheme.completedLocalRingAlgebra` is its canonical algebra structure over
  the ground field.

## Main results

* `AlgebraicGeometry.Scheme.completedLocalRing_isNoetherian` states Noetherianity.
* `AlgebraicGeometry.Scheme.completedLocalRing_isLocal` states locality.
* `AlgebraicGeometry.Scheme.completedLocalRing_isAdicComplete` states completeness at the
  maximal ideal.
* `AlgebraicGeometry.Scheme.completedLocalRing_residueFieldMap_bijective` identifies the
  residue field through the canonical completion map.

## Implementation notes

The local ring is `X.presheaf.stalk x`, and its completion is Mathlib's `AdicCompletion` at
`IsLocalRing.maximalIdeal`.  Completeness is expressed by `IsAdicComplete` at the maximal ideal
of the completed ring.  Rather than choosing an arbitrary residue-field isomorphism, the last
result says that the map on residue fields induced by the completion map is bijective.

## References

* [Stacks Project, Section 10.97](https://stacks.math.columbia.edu/tag/0BNH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- The completion of the local ring of `X` at `x`. -/
abbrev completedLocalRing (X : Scheme.{u}) (x : X) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x)

/-- The canonical algebra structure on the completed local ring of a scheme over a field. -/
@[instance_reducible]
def completedLocalRingAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : Algebra k (completedLocalRing X x) :=
  ((algebraMap (X.presheaf.stalk x) (completedLocalRing X x)).comp
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫ X.presheaf.Γgerm x).hom)).toAlgebra

/-- The four properties of the completed local ring of a locally Noetherian scheme, proved
together and exposed separately below. -/
private theorem completedLocalRing_properties (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) :
    IsNoetherianRing (completedLocalRing X x) ∧
      IsLocalRing (completedLocalRing X x) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (completedLocalRing X x))
        (completedLocalRing X x) ∧
      Function.Bijective
        (IsLocalRing.ResidueField.map
          (algebraMap (X.presheaf.stalk x) (completedLocalRing X x))) :=
  ⟨inferInstance, inferInstance, inferInstance,
    AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)⟩

/-- The completed local ring of a locally Noetherian scheme is Noetherian. -/
theorem completedLocalRing_isNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) : IsNoetherianRing (completedLocalRing X x) :=
  (completedLocalRing_properties X x).1

/-- The completed local ring of a locally Noetherian scheme is local. -/
theorem completedLocalRing_isLocal (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) : IsLocalRing (completedLocalRing X x) :=
  (completedLocalRing_properties X x).2.1

/-- The completed local ring of a locally Noetherian scheme is complete for its
maximal-ideal-adic topology. -/
theorem completedLocalRing_isAdicComplete (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) :
    IsAdicComplete (IsLocalRing.maximalIdeal (completedLocalRing X x))
      (completedLocalRing X x) :=
  (completedLocalRing_properties X x).2.2.1

/-- The completion map of a local ring induces an isomorphism on residue fields. -/
theorem completedLocalRing_residueFieldMap_bijective
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    Function.Bijective
      (IsLocalRing.ResidueField.map
        (algebraMap (X.presheaf.stalk x) (completedLocalRing X x))) :=
  (completedLocalRing_properties X x).2.2.2

end AlgebraicGeometry.Scheme

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points with finite residue field are closed

Let `X` be a scheme locally of finite type over a field `k`. A point `x` of `X` whose residue
field is finite is closed.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_finite_residueField`: a point with finite residue
  field of a scheme locally of finite type over a field is closed.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A point with finite residue field of a scheme locally of finite type over a field is
closed.** -/
@[ega "IV 10.4.11.1" "(i), special case"]
theorem isClosed_singleton_of_finite_residueField {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) [Finite (X.residueField x)] :
    IsClosed ({x} : Set X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [isClosed_singleton_iff_locallyOfFiniteType]
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
    rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    let := φ.hom.toAlgebra
    have : Module.Finite k (X.residueField x) := Module.Finite.of_finite
    exact (inferInstance : Algebra.FiniteType k (X.residueField x))
  exact HasRingHomProperty.of_comp (P := @LocallyOfFiniteType)
    (fun _ _ h => RingHom.FiniteType.of_comp_finiteType h) h

end AlgebraicGeometry

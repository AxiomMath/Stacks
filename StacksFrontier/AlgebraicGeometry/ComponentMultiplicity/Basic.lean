module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Length
public import StacksCore.Tactic.StacksAttribute

/-!
# The local ring at a generic point of a reduced scheme

The local ring of a scheme at a point maximal for the specialization order is Noetherian of
Krull dimension zero; on a reduced scheme it is a field, and so has length one over itself.

## Main results

* `AlgebraicGeometry.isField_stalk_of_isMax`: the local ring at a maximal point of a reduced
  scheme is a field.
* `AlgebraicGeometry.length_stalk_eq_one_of_isMax`: that local ring has length one over itself.

## Implementation notes

A point of a scheme is maximal for the specialization order exactly when the local ring there
has Krull dimension zero, by `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`. On a reduced
scheme every stalk is reduced, and a reduced local ring of Krull dimension zero is a field.

The multiplicity of a one-dimensional irreducible component in Stacks Tag 0AYW is the length of
the local ring at its generic point, so on a reduced scheme every component has multiplicity
one: this is the input to the base case `e = 0` of the induction in that tag, where `X` equals
its own reduction and the component formula reads `deg(ℰ) = 1 · deg(ℰ|_C)`. The statement is
phrased in terms of maximality rather than of membership of the set of generic points of
one-dimensional components, because that set's defining property is not available outside the
module that introduces it.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **The local ring at a maximal point of a reduced scheme is a field.** -/
theorem isField_stalk_of_isMax {X : Scheme.{u}} [IsReduced X] {x : X} (hx : IsMax x) :
    IsField (X.presheaf.stalk x) := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    simpa only [WithBot.coe_zero] using
      congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) (Order.coheight_eq_zero.mpr hx)
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  exact Ring.KrullDimLE.isField_of_isReduced

/-- **The local ring at a maximal point of a reduced scheme has length one over itself.** The
multiplicity of a one-dimensional irreducible component, in the sense of Stacks Tag 0AYW, is
therefore one on a reduced scheme. -/
theorem length_stalk_eq_one_of_isMax {X : Scheme.{u}} [IsReduced X] {x : X} (hx : IsMax x) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) = 1 := by
  have hfield := isField_stalk_of_isMax hx
  have : IsSimpleModule (X.presheaf.stalk x) (X.presheaf.stalk x) :=
    isSimpleModule_self_iff_isUnit.mpr ⟨⟨hfield.exists_pair_ne⟩, fun a ha =>
      (hfield.mul_inv_cancel ha).elim fun b hb => IsUnit.of_mul_eq_one b hb⟩
  exact Module.length_eq_one _ _

end AlgebraicGeometry

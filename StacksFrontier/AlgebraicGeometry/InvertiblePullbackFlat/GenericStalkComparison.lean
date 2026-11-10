module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Stalks

/-!
# The chart square's generic fibre ring inside the function field

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/GenericFibreChart.lean` states the
penultimate paragraph of [Stacks, Tag 0BD7] at a point `x` inside the ring
`Ideal.Fiber ⊥ 𝒪_{X, x}`, the source's `A ⊗_R K`. The meromorphic section the first paragraph
of that proof builds lives instead in the stalk of `ℒ` at the **generic point** of `X`, over the
function field `K(X) = 𝒪_{X, ξ}`. Nothing in the development related the two rings, so no
equation proved in one could be used in the other.

This file supplies the comparison. For a flat `f` and an integral `X` the local ring `𝒪_{Y, f x}`
embeds in `K(X)` — the map `𝒪_{Y, f x} → 𝒪_{X, x}` is faithfully flat, hence injective, and
`𝒪_{X, x} → K(X)` is a fraction-field embedding — so the nonzero elements of `𝒪_{Y, f x}` become
units of the field `K(X)` and the localization
`Ideal.Fiber ⊥ 𝒪_{X, x} = Frac 𝒪_{Y, f x} ⊗ 𝒪_{X, x}` maps to `K(X)`.

## Main results

* `AlgebraicGeometry.injective_algebraMap_functionField_of_flat`: `𝒪_{Y, f x} → K(X)` is
  injective.
* `AlgebraicGeometry.stalkFiberBotToGenericStalk`: the resulting ring homomorphism
  `Ideal.Fiber ⊥ 𝒪_{X, x} → K(X)`.
* `AlgebraicGeometry.stalkFiberBotToGenericStalk_algebraMap_stalk` and
  `AlgebraicGeometry.stalkFiberBotToGenericStalk_algebraMap_base`: its two defining equations,
  on the germs at `x` and on the germs at `f x`, which are the two kinds of element the
  penultimate paragraph's conclusion is built from.

## Implementation notes

The algebra structure `𝒪_{Y, f x} → K(X)` is the composite of the two maps rather than a germ,
and the scalar tower it sits in is `rfl`; stating it any other way makes
`Algebra.TensorProduct.lift` ask for a tower that is not definitionally the one in scope.

No tag attribute: every statement here carries a point of `X`, which [Stacks, Tag 0BD7] does
not.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral X] [IsIntegral Y] (x : X)

omit [IsIntegral Y] in
/-- **The local ring of the base embeds in the function field of the source.** The map
`𝒪_{Y, f x} → 𝒪_{X, x}` is faithfully flat for a flat `f`, hence injective, and
`𝒪_{X, x} → K(X)` is a fraction-field embedding for an integral `X`. -/
theorem injective_algebraMap_functionField_of_flat :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
      ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
        (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
    Function.Injective (algebraMap ↑(Y.presheaf.stalk (f x)) X.functionField) := by
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.FaithfullyFlat ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    Flat.faithfullyFlat_stalkMap f x
  simpa only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp] using
    (IsFractionRing.injective ↑(X.presheaf.stalk x) X.functionField).comp
      (FaithfulSMul.algebraMap_injective ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))

/-- **The chart square's generic fibre ring at `x`, inside the function field of `X`.** The
ring `Ideal.Fiber ⊥ 𝒪_{X, x}` is `Frac 𝒪_{Y, f x} ⊗_{𝒪_{Y, f x}} 𝒪_{X, x}`; the right factor maps
to `K(X)` by `AlgebraicGeometry.stalkFunctionFieldAlgebra` and the left one by the universal
property of a field of fractions, applied to
`AlgebraicGeometry.injective_algebraMap_functionField_of_flat`. -/
def stalkFiberBotToGenericStalk :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    (⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x) →+* X.functionField :=
  letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  letI : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
    ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
      (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
  haveI : IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.lift
    (IsFractionRing.liftAlgHom (A := ↑(Y.presheaf.stalk (f x)))
      (g := Algebra.ofId ↑(Y.presheaf.stalk (f x)) X.functionField)
      (show Function.Injective ⇑(Algebra.ofId ↑(Y.presheaf.stalk (f x)) X.functionField) from
        injective_algebraMap_functionField_of_flat f x))
    (IsScalarTower.toAlgHom ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) X.functionField)
    fun _ _ => Commute.all _ _).toRingHom

/-- **The comparison is the identity on germs at `x`.** -/
theorem stalkFiberBotToGenericStalk_algebraMap_stalk (a : ↑(X.presheaf.stalk x)) :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra ↑(X.presheaf.stalk x)
        ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
      Algebra.TensorProduct.rightAlgebra
    stalkFiberBotToGenericStalk f x
        (algebraMap ↑(X.presheaf.stalk x)
          ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) a) =
      algebraMap ↑(X.presheaf.stalk x) X.functionField a := by
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
    ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
      (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
  have : IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  change (Algebra.TensorProduct.lift _ _ _) (1 ⊗ₜ[↑(Y.presheaf.stalk (f x))] a) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- **The comparison is the identity on germs at `f x`.** -/
theorem stalkFiberBotToGenericStalk_algebraMap_base (b : ↑(Y.presheaf.stalk (f x))) :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
      ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
        (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
    stalkFiberBotToGenericStalk f x
        (algebraMap ↑(Y.presheaf.stalk (f x))
          ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) b) =
      algebraMap ↑(Y.presheaf.stalk (f x)) X.functionField b := by
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
    ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
      (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
  have : IsScalarTower ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  change (Algebra.TensorProduct.lift _ _ _)
    (algebraMap ↑(Y.presheaf.stalk (f x))
      (⊥ : Ideal ↑(Y.presheaf.stalk (f x))).ResidueField b ⊗ₜ[↑(Y.presheaf.stalk (f x))] 1) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  exact IsFractionRing.lift_algebraMap
    (show Function.Injective ⇑(Algebra.ofId ↑(Y.presheaf.stalk (f x)) X.functionField) from
      injective_algebraMap_functionField_of_flat f x) b

end AlgebraicGeometry

end

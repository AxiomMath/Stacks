module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModel

/-!
# The universal property of the local model of an affine bundle

The local model `B[z₁, z₂]/(z₁z₂ - f)` is the `B`-algebra presented by two generators whose
product is `f`. This file records that presentation as a universal property: a `B`-algebra map out
of the local model is the same thing as a pair of elements of the target whose product is the
image of `f`.

## Main definitions

* `Stacks.AffineBundle.lift` — **the `B`-algebra map out of the local model** determined by a pair
  of elements of a `B`-algebra whose product is the image of `f`.

## Main results

* `Stacks.AffineBundle.lift_coord_zero` and `Stacks.AffineBundle.lift_coord_one` — the two
  coordinates are sent to the two chosen elements.
* `Stacks.AffineBundle.algHom_ext` — **two `B`-algebra maps out of the local model agreeing on the
  two coordinates are equal**, so `lift` is the unique such map.
* `Stacks.AffineBundle.lift_comp` — composing `lift` with a `B`-algebra map of targets is `lift` of
  the images.

## Implementation notes

The map is built by `MvPolynomial.aeval` on the pair and descended through the quotient by
`Ideal.Quotient.liftₐ`; the defining relation is in the kernel precisely because the two chosen
elements multiply to the image of `f`. Uniqueness is `MvPolynomial.algHom_ext` composed with the
surjectivity of the quotient map, and is stated as an `ext`-shaped lemma rather than as a
bijection of `Hom` sets so that it applies to algebra maps that were not built by `lift`.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u v

namespace Stacks.AffineBundle

variable (B : Type u) [CommRing B] (f : B)

/-- The pair `(a, b)` read as a map `Fin 2 → T`. -/
def pairFun {T : Type v} (a b : T) : Fin 2 → T := fun i => if i = 0 then a else b

/-- The pair evaluated at the first index. -/
@[simp] theorem pairFun_zero {T : Type v} (a b : T) : pairFun a b 0 = a := rfl

/-- The pair evaluated at the second index. -/
@[simp] theorem pairFun_one {T : Type v} (a b : T) : pairFun a b 1 = b := rfl

variable {T : Type v} [CommRing T] [Algebra B T]

/-- The evaluation of the defining relation at a pair of elements is the difference of their
product and the image of `f`. -/
theorem aeval_localRelation (a b : T) :
    aeval (pairFun a b) (localRelation B f) = a * b - algebraMap B T f := by
  rw [localRelation, map_sub, map_mul, aeval_X, aeval_X, aeval_C, pairFun_zero, pairFun_one]

/-- **The `B`-algebra map out of the local model determined by a pair of elements whose product is
the image of `f`.** It sends the first coordinate `z₁` to `a` and the second `z₂` to `b`. -/
def lift (a b : T) (hab : a * b = algebraMap B T f) : LocalModel B f →ₐ[B] T :=
  Ideal.Quotient.liftₐ (Ideal.span {localRelation B f}) (aeval (pairFun a b)) <| by
    intro x hx
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, aeval_localRelation, hab, sub_self, mul_zero]

/-- `lift` sends the class of a polynomial `p` to the evaluation of `p` at the pair. -/
@[simp] theorem lift_mk (a b : T) (hab : a * b = algebraMap B T f)
    (p : MvPolynomial (Fin 2) B) :
    lift B f a b hab (Ideal.Quotient.mk (Ideal.span {localRelation B f}) p) =
      aeval (pairFun a b) p :=
  rfl

/-- **`lift` sends the first coordinate to the first chosen element.** -/
@[simp] theorem lift_coord_zero (a b : T) (hab : a * b = algebraMap B T f) :
    lift B f a b hab (coord B f 0) = a := by
  rw [coord, lift_mk, aeval_X, pairFun_zero]

/-- **`lift` sends the second coordinate to the second chosen element.** -/
@[simp] theorem lift_coord_one (a b : T) (hab : a * b = algebraMap B T f) :
    lift B f a b hab (coord B f 1) = b := by
  rw [coord, lift_mk, aeval_X, pairFun_one]

/-- **Two `B`-algebra maps out of the local model that agree on the two coordinates are equal.**
Together with `lift_coord_zero` and `lift_coord_one` this says that `lift` is the unique
`B`-algebra map sending the coordinates to a given pair. -/
@[ext] theorem algHom_ext {φ ψ : LocalModel B f →ₐ[B] T}
    (h₀ : φ (coord B f 0) = ψ (coord B f 0)) (h₁ : φ (coord B f 1) = ψ (coord B f 1)) :
    φ = ψ := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {localRelation B f}) x
  have hcomp : φ.comp (Ideal.Quotient.mkₐ B (Ideal.span {localRelation B f})) =
      ψ.comp (Ideal.Quotient.mkₐ B (Ideal.span {localRelation B f})) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    match i with
    | 0 => exact h₀
    | 1 => exact h₁
  exact congrArg (fun k : MvPolynomial (Fin 2) B →ₐ[B] T => k p) hcomp

/-- A `B`-algebra map out of the local model is `lift` of the images of the two coordinates. -/
theorem eq_lift (φ : LocalModel B f →ₐ[B] T) :
    φ = lift B f (φ (coord B f 0)) (φ (coord B f 1))
      (by rw [← map_mul, coord_zero_mul_coord_one, AlgHom.commutes]) :=
  algHom_ext B f (by rw [lift_coord_zero]) (by rw [lift_coord_one])

/-- **Composing `lift` with a `B`-algebra map of targets is `lift` of the images.** -/
theorem lift_comp {T' : Type v} [CommRing T'] [Algebra B T'] (a b : T)
    (hab : a * b = algebraMap B T f) (χ : T →ₐ[B] T') :
    χ.comp (lift B f a b hab) =
      lift B f (χ a) (χ b) (by rw [← map_mul, hab, AlgHom.commutes]) :=
  algHom_ext B f (by simp) (by simp)

/-- The identity is `lift` of the two coordinates. -/
@[simp] theorem lift_coord_coord :
    lift B f (coord B f 0) (coord B f 1) (coord_zero_mul_coord_one B f) = AlgHom.id B _ :=
  (eq_lift B f (AlgHom.id B _)).symm

end Stacks.AffineBundle

end

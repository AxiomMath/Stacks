module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction
public import StacksFrontier.Algebra.DifferentialGraded.TensorProduct

/-!
# The universal property of a tensor product of differential graded algebras

Let `C`, `D` and `E` be differential graded algebras over a commutative ring `R`. A pair of
homomorphisms `f : C → E` and `g : D → E` whose images anticommute by the Koszul sign,
`f(a) g(b) = (-1)^(deg a · deg b) g(b) f(a)` on homogeneous elements, assembles into a single
homomorphism `C ⊗_R D → E`, which on a pure tensor is `a ⊗ b ↦ f(a) g(b)`. Conversely every
homomorphism out of `C ⊗_R D` arises this way from its restrictions along the two inclusions,
so the two inclusions exhibit `C ⊗_R D` as the coproduct of `C` and `D` among differential
graded algebras over `R` with Koszul-anticommuting images.

## Main definitions

* `DifferentialGradedAlgebra.Hom.comp`: the composition of homomorphisms of differential graded
  algebras.
* `DifferentialGradedAlgebra.tensorLift`: the homomorphism `C ⊗_R D → E` determined by a pair of
  Koszul-anticommuting homomorphisms.

## Main results

* `DifferentialGradedAlgebra.d_mul_of_mem`: the Leibniz rule needs a homogeneity hypothesis on
  the left factor only.
* `DifferentialGradedAlgebra.tensorLiftAlgebraHom_tmul`: the value of the lift on a pure tensor.
* `DifferentialGradedAlgebra.tensorLiftAlgebraHom_comp_includeLeft` and
  `DifferentialGradedAlgebra.tensorLiftAlgebraHom_comp_includeRight`: the lift restricts along the
  two inclusions to the two given homomorphisms.
* `DifferentialGradedAlgebra.tensorHom_ext`: two homomorphisms out of `C ⊗_R D` agreeing on both
  inclusions are equal.

## References

* [Stacks Project, Tag 061X](https://stacks.math.columbia.edu/tag/061X)
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The Leibniz rule of a differential graded algebra, with a homogeneity hypothesis on the left
factor only. -/
theorem d_mul_of_mem (E : DifferentialGradedAlgebra R) {p : ℤ} {a : E.A}
    (ha : a ∈ E.grading p) (b : E.A) :
    E.d (a * b) = E.d a * b + (p.negOnePow : ℤ) • (a * E.d b) := by
  induction b using DirectSum.Decomposition.inductionOn E.grading with
  | zero => simp
  | add b c hb hc =>
    simp only [mul_add, map_add, smul_add, hb, hc]
    abel
  | @homogeneous q b => exact E.leibniz p q a b ha b.2

namespace Hom

variable {A B C : DifferentialGradedAlgebra R}

/-- The composition of two homomorphisms of differential graded algebras. -/
def comp (g : B.Hom C) (f : A.Hom B) : A.Hom C where
  toAlgebraHom := g.toAlgebraHom.comp f.toAlgebraHom
  map_grading n a ha := g.map_grading n _ (f.map_grading n a ha)
  map_d a := by
    simp only [AlgHom.comp_apply]
    rw [f.map_d a, g.map_d (f.toAlgebraHom a)]

/-- The underlying algebra homomorphism of a composite is the composite of the underlying algebra
homomorphisms. -/
@[simp]
theorem comp_toAlgebraHom (g : B.Hom C) (f : A.Hom B) :
    (g.comp f).toAlgebraHom = g.toAlgebraHom.comp f.toAlgebraHom := rfl

end Hom

section Lift

variable (C D E : DifferentialGradedAlgebra R)

/-- The Koszul anticommutation hypothesis for a pair of homomorphisms `f : C → E` and
`g : D → E`: the images of homogeneous elements of degrees `i` and `j` commute up to the sign
`(-1)^(i·j)`. -/
def AnticommutesAlong (f : C.Hom E) (g : D.Hom E) : Prop :=
  ∀ (i j : ℤ) (a : C.grading i) (b : D.grading j),
    f.toAlgebraHom a * g.toAlgebraHom b =
      (-1 : ℤˣ) ^ (j * i) • (g.toAlgebraHom b * f.toAlgebraHom a)

variable {C D E}

/-- The underlying algebra homomorphism of the lift of a pair of Koszul-anticommuting
homomorphisms. -/
noncomputable def tensorLiftAlgebraHom {f : C.Hom E} {g : D.Hom E}
    (h : AnticommutesAlong C D E f g) :
    (C.grading ᵍ⊗[R] D.grading) →ₐ[R] E.A :=
  GradedTensorProduct.lift C.grading D.grading f.toAlgebraHom g.toAlgebraHom
    fun {i j} a b => h i j a b

/-- The lift sends a pure tensor `a ⊗ b` to `f(a) g(b)`. -/
@[simp]
theorem tensorLiftAlgebraHom_tmul {f : C.Hom E} {g : D.Hom E} (h : AnticommutesAlong C D E f g)
    (a : C.A) (b : D.A) :
    tensorLiftAlgebraHom h (a ᵍ⊗ₜ[R] b) = f.toAlgebraHom a * g.toAlgebraHom b := rfl

/-- The lift sends the degree `n` part of the total grading of `C ⊗_R D` into the degree `n` part
of `E`. -/
theorem tensorLiftAlgebraHom_mem_grading {f : C.Hom E} {g : D.Hom E}
    (h : AnticommutesAlong C D E f g) (n : ℤ) (x : C.grading ᵍ⊗[R] D.grading)
    (hx : x ∈ tensorProductGrading C D n) :
    tensorLiftAlgebraHom h x ∈ E.grading n := by
  rw [tensorProductGrading] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, a, b, ha, hb, hpq, rfl⟩ := hz
    rw [tensorLiftAlgebraHom_tmul, ← hpq]
    exact SetLike.mul_mem_graded (f.map_grading p a ha) (g.map_grading q b hb)
  | zero => simp
  | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
  | smul r y _ hy => simpa using Submodule.smul_mem _ r hy

/-- The lift commutes with the differentials of `C ⊗_R D` and of `E`. -/
theorem tensorLiftAlgebraHom_map_d {f : C.Hom E} {g : D.Hom E} (h : AnticommutesAlong C D E f g)
    (x : C.grading ᵍ⊗[R] D.grading) :
    tensorLiftAlgebraHom h (tensorProductDifferential C D x) =
      E.d (tensorLiftAlgebraHom h x) := by
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of R C.grading D.grading).surjective x
  induction t using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b =>
    induction a using DirectSum.Decomposition.inductionOn C.grading with
    | zero => simp
    | add a a' ha ha' =>
      simp only [TensorProduct.add_tmul, map_add] at ha' ha ⊢
      rw [ha, ha']
    | @homogeneous p a =>
      rw [tensorProductDifferential_tmul_aux C D p a b, map_add, map_zsmul,
        tensorLiftAlgebraHom_tmul, tensorLiftAlgebraHom_tmul,
        tensorLiftAlgebraHom_tmul, f.map_d, g.map_d,
        d_mul_of_mem E (f.map_grading p a a.2) (g.toAlgebraHom b)]

/-- **The universal property of the tensor product of differential graded algebras.** A pair of
homomorphisms `f : C → E` and `g : D → E` whose images anticommute by the Koszul sign assembles
into a homomorphism `C ⊗_R D → E` sending `a ⊗ b` to `f(a) g(b)`. -/
noncomputable def tensorLift {f : C.Hom E} {g : D.Hom E} (h : AnticommutesAlong C D E f g) :
    (tensorProduct C D).Hom E where
  toAlgebraHom := tensorLiftAlgebraHom h
  map_grading := tensorLiftAlgebraHom_mem_grading h
  map_d := tensorLiftAlgebraHom_map_d h

/-- The underlying algebra homomorphism of `tensorLift h` is `tensorLiftAlgebraHom h`. -/
@[simp]
theorem tensorLift_toAlgebraHom {f : C.Hom E} {g : D.Hom E} (h : AnticommutesAlong C D E f g) :
    (tensorLift h).toAlgebraHom = tensorLiftAlgebraHom h := rfl

/-- The lift restricts to `f` along the inclusion `a ↦ a ⊗ 1` of the left factor. -/
theorem tensorLiftAlgebraHom_comp_includeLeft {f : C.Hom E} {g : D.Hom E}
    (h : AnticommutesAlong C D E f g) :
    (tensorLiftAlgebraHom h).comp (GradedTensorProduct.includeLeft C.grading D.grading) =
      f.toAlgebraHom :=
  AlgHom.ext fun a => by
    change tensorLiftAlgebraHom h (a ᵍ⊗ₜ[R] (1 : D.A)) = f.toAlgebraHom a
    rw [tensorLiftAlgebraHom_tmul, map_one, mul_one]

/-- The lift restricts to `g` along the inclusion `b ↦ 1 ⊗ b` of the right factor. -/
theorem tensorLiftAlgebraHom_comp_includeRight {f : C.Hom E} {g : D.Hom E}
    (h : AnticommutesAlong C D E f g) :
    (tensorLiftAlgebraHom h).comp (GradedTensorProduct.includeRight C.grading D.grading) =
      g.toAlgebraHom :=
  AlgHom.ext fun b => by
    change tensorLiftAlgebraHom h ((1 : C.A) ᵍ⊗ₜ[R] b) = g.toAlgebraHom b
    rw [tensorLiftAlgebraHom_tmul, map_one, one_mul]

/-- Two homomorphisms out of `C ⊗_R D` that agree on both inclusions are equal. -/
theorem tensorHom_ext {u v : (tensorProduct C D).Hom E}
    (hl : u.toAlgebraHom.comp (GradedTensorProduct.includeLeft C.grading D.grading) =
      v.toAlgebraHom.comp (GradedTensorProduct.includeLeft C.grading D.grading))
    (hr : u.toAlgebraHom.comp (GradedTensorProduct.includeRight C.grading D.grading) =
      v.toAlgebraHom.comp (GradedTensorProduct.includeRight C.grading D.grading)) :
    u.toAlgebraHom = v.toAlgebraHom :=
  GradedTensorProduct.algHom_ext C.grading D.grading hl hr

end Lift

end DifferentialGradedAlgebra

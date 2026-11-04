module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence

/-!
# The ideal sheaves of the powers of an ideal sheaf, as a graded algebra

Let `I` be an ideal sheaf on a scheme `X`. Two parts of the library multiply the ideal sheaves of
the powers of `I`, and they do not know about each other:

* `Stacks.Divisors.idealTensorMul`, the morphism `ℐ_I ⊗ ℐ_J ⟶ ℐ_{I · J}` out of the tensor
  product sheaf, which for effective Cartier `J` is an isomorphism
  (`Stacks.Divisors.idealTensorMulIso`). It is the identification that the short exact sequence
  of [Stacks, Tag 0C4T] runs on. It has **no** associativity lemma, no compatibility with the
  monoidal associator and no unit lemma.
* `Stacks.Blowup.reesMultiplication`, the bilinear map on local sections which makes
  `⨁_{n ≥ 0} ℐ_{Iⁿ}` a sheaf of graded algebras, `Stacks.Blowup.reesGradedAlgebra`. That one is
  **fully associative and unital**, `Stacks.Blowup.reesMultiplication_assoc` and the `one_mul`
  and `mul_one` fields of the graded algebra.

This file records that the two are the same multiplication of the same sheaves. The pieces agree
definitionally, and so do the maps that read a local section of a piece as a section of `𝒪_X`;
the two multiplications then agree because each of them computes, on a local pure tensor, to the
product of the two ambient sections.

## Why this matters

A monomial symbol system on the formal neighbourhood of an exceptional curve — the one
undischarged input of [Stacks, Tag 0C2K], see
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveFormalNeighborhood.lean` — needs a family
of identifications of the graded pieces that is compatible with multiplication *across all pairs
of degrees*. Building one by iterating `idealTensorMulIso` requires knowing that iterating it is
unambiguous, i.e. an associativity statement about it, and there is none. The module docstring of
that file accordingly recorded associativity of `idealTensorMul` as absent. It is absent *at that
spelling*: the content exists, at the Rees spelling, and this file is the identification that
carries it across.

## Main results

* `Stacks.Divisors.reesPiece_eq_negativeTwist` and `idealPowerKernel_eq_negativeTwist` — the
  degree-`n` piece of the Rees algebra of `I` *is* the ideal sheaf `ℐ_{Iⁿ}`.
* `Stacks.Divisors.reesPieceAmbient_eq_idealSheafSection` — and the two readings of a local
  section of it as a section of `𝒪_X` agree.
* `Stacks.Divisors.idealSheafSection_reesMultiplication_eq_idealTensorMul` — **the two
  multiplications agree**, on a local pure tensor, read inside `𝒪_X`.

## What this does not yet give

The agreement above is at the level of *local sections*. Associativity of `idealTensorMul` as an
equation between two morphisms out of `(ℐ_I ⊗ ℐ_J) ⊗ ℐ_K` is not stated here, and
`Stacks.Divisors.tensorSheaf_hom_ext_affine` is not enough to reach it: it determines a morphism
out of a *twofold* tensor product by its values on pure tensors over affine opens, and applying
it to the outer tensor leaves a map out of `ℐ_I ⊗ ℐ_J` with one argument fixed, which is not a
morphism of sheaves and so cannot be fed back in.

The threefold principle that this calls for is nevertheless already in the library, so it is not
the next piece of work. `PresheafOfModules.tensorSheaf_hom_ext₂` determines a morphism out of a
twice-iterated tensor product sheaf by its values on triple pure tensors, handling the inner
level by local surjectivity of `tensorSheafUnit` rather than by fixing an argument. And it has
already been used for exactly this promotion one layer up:
`Stacks.TensorSheafWorld.mulSheaf_assoc` turns the associativity that a
`SheafOfModules.GradedAlgebra` carries as an `HEq` between values at arbitrary local sections
into an equality of morphisms out of `(A_i ⊗ A_j) ⊗ A_k`.

**The Rees algebra of an ideal sheaf is built twice in this library, under two namespaces, with
two multiplications**, and the two halves of the argument sit on opposite copies:

* `SheafOfModules.reesPiece` (`Algebra/Category/ModuleCat/Sheaf/IdealSheafPowers.lean:402`) with
  `SheafOfModules.reesMul` (`:459`), one uniform bilinear map taking a commutativity assumption,
  packaged as `SheafOfModules.reesGradedAlgebra` (`:498`).
* `Stacks.Blowup.reesPiece` (`AlgebraicGeometry/Blowup/ReesAlgebraSheaf.lean:84`) with
  `Stacks.Blowup.reesMultiplication` (`:596`), which is built by *case analysis on the signs of
  the two integer degrees* and so has no single defining equation. This is the copy
  `idealSheafSection_reesMultiplication_eq_idealTensorMul` below is about, and the copy
  `reesPiece_eq_negativeTwist` above identifies with the ideal sheaves.

The two are now related, in `StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebraCopies.lean`: the
index types are matched by `Stacks.Blowup.unitSubmodule_pow`, the pieces by
`Stacks.Blowup.reesPieceIso` and the multiplications by
`Stacks.Blowup.reesPieceIso_hom_reesMul`, giving the isomorphism of sheaves of graded algebras
`Stacks.Blowup.reesGradedAlgebraIso`.

**The morphism-level identification does not depend on that relation, and this file was wrong to
say it did.** `SheafOfModules.GradedAlgebra.mulSheaf` and
`Stacks.TensorSheafWorld.mulSheaf_assoc` are statements about an *arbitrary* sheaf of graded
algebras over a ring sheaf of the form `CategoryTheory.Sheaf.toRingCat J O♯`, taking the graded
algebra as a variable; `X.ringCatSheaf` is of that form, being definitionally
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`. So they apply to
`Stacks.Blowup.reesGradedAlgebra` — the copy the sectionwise bridge below is about — with no
comparison of copies at all, and `Stacks.Blowup.reesMulSheaf` and
`Stacks.Blowup.reesMulSheaf_assoc` record that. Neither copy is privileged here:
`SheafOfModules.reesGradedAlgebra` is stated over a bare `Sheaf J RingCat` and has to be re-seated
on a `toRingCat` ring sheaf, which is `SheafOfModules.reesGradedAlgebraOfRingedSite`, before
`mulSheaf` reaches it either.

What the promotion still wants is therefore spelling: the target asks for
`I ^ m * I ^ n = I ^ (m + n)` transported, while the two tensor products of sheaves of modules
need no transport at all, agreeing by `rfl`
(`Stacks.TensorSheafWorld.tensorSheafBifunctor_obj_eq`).

## References

* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The degree-`n` piece of the Rees algebra of `I` is the ideal sheaf of `Iⁿ`.** Both are the
kernel of `𝒪_X ⟶ (ι_{Iⁿ})_* 𝒪_{V(Iⁿ)}`, so this holds definitionally; it is stated because the
two names belong to parts of the library that do not otherwise meet. -/
public theorem idealPowerKernel_eq_negativeTwist (n : ℕ) :
    Stacks.Blowup.idealPowerKernel I n = negativeTwist (I ^ n) := rfl

/-- **The degree-`n` piece of the Rees algebra of `I` is the ideal sheaf of `Iⁿ`**, for the
integer-graded `Stacks.Blowup.reesPiece` at a nonnegative degree. -/
public theorem reesPiece_eq_negativeTwist (n : ℕ) :
    Stacks.Blowup.reesPiece I (n : ℤ) = negativeTwist (I ^ n) := rfl

/-- **The two readings of a local section of `ℐ_{Iⁿ}` as a section of `𝒪_X` agree.** The Rees
algebra reads it with `Stacks.Blowup.idealPowerKernelAmbient` and the divisor library with
`Stacks.Divisors.idealSheafSection`; both are the kernel inclusion evaluated at the open. -/
public theorem idealPowerKernelAmbient_eq_idealSheafSection (n : ℕ) (U : X.Opens)
    (x : (Stacks.Blowup.idealPowerKernel I n).val.obj (op U)) :
    Stacks.Blowup.idealPowerKernelAmbient I n U x = idealSheafSection (I ^ n) x := rfl

/-- **The two readings of a local section of `ℐ_{Iⁿ}` as a section of `𝒪_X` agree**, for
`Stacks.Blowup.reesPieceAmbient` at a nonnegative degree. -/
public theorem reesPieceAmbient_eq_idealSheafSection (n : ℕ) (U : X.Opens)
    (x : (Stacks.Blowup.reesPiece I (n : ℤ)).val.obj (op U)) :
    Stacks.Blowup.reesPieceAmbient I (n : ℤ) U x = idealSheafSection (I ^ n) x := rfl

/-- **The multiplication of the Rees algebra and `idealTensorMul` are the same
multiplication.** On a local pure tensor of a section of `ℐ_{Iᵐ}` with one of `ℐ_{Iⁿ}`, the two
agree once read inside `𝒪_X`: each of them is the product of the two ambient sections, by
`Stacks.Blowup.reesMultiplication_ambient` on one side and by
`Stacks.Divisors.idealSheafSection_idealTensorMul` together with
`Stacks.Divisors.idealTensorToUnit_app_tmul` on the other.

Reading inside `𝒪_X` loses nothing: the inclusion of an ideal sheaf is injective on sections,
`Stacks.Divisors.idealSheafSection_injective`. So this is the identification of the two
multiplications, and it is what carries `Stacks.Blowup.reesMultiplication_assoc` over to
`Stacks.Divisors.idealTensorMul`.

The action of `(idealTensorMul _ _).val.app (op U)` on a section is written through
`ModuleCat.Hom.hom`, which is how `Stacks.Divisors.idealSheafSection_idealTensorMul` and
`Stacks.Divisors.idealTensorToUnit_app_tmul` write it; applying the morphism directly spells the
same function through `CategoryTheory.ConcreteCategory.hom`, definitionally equal but a different
pattern.

The two lemmas are composed at explicit arguments rather than rewritten with, because this
statement straddles two spellings of one ring sheaf. `Stacks.Divisors.idealTensorMul` is typed
over `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, whose site is
`Opens.grothendieckTopology ↥X`, while `Stacks.Blowup.reesMultiplication` is typed over
`AlgebraicGeometry.Scheme.ringCatSheaf`, whose site is the opens of `X.toPresheafedSpace`. The
two agree definitionally — `Stacks.Divisors.reesPiece_eq_negativeTwist` and
`Stacks.Divisors.reesPieceAmbient_eq_idealSheafSection` above are both `rfl` — so the statement
elaborates and `Eq.trans` crosses between them at default transparency, but it is not
type-correct at `implicit` transparency, which is the level a rewrite forms its motive at; both
`rw` and `conv_rhs => rw` fail on it for that reason. -/
public theorem idealSheafSection_reesMultiplication_eq_idealTensorMul (m n : ℕ) (U : X.Opens)
    (y : (idealSheafOfModules (I ^ m)).val.obj (op U))
    (z : (idealSheafOfModules (I ^ n)).val.obj (op U)) :
    idealSheafSection (I ^ (m + n))
        ((Stacks.Blowup.reesMultiplication I (m : ℤ) (n : ℤ)).app (op U) y z) =
      idealSheafSection (I ^ m * I ^ n)
        (((idealTensorMul (I ^ m) (I ^ n)).val.app (op U)).hom
          (toTensorSheafSection X.toRingedSpace (idealSheafOfModules (I ^ m))
            (idealSheafOfModules (I ^ n)) (op U) (y ⊗ₜ z))) := by
  have hprod : idealSheafSection (I ^ m * I ^ n)
        (((idealTensorMul (I ^ m) (I ^ n)).val.app (op U)).hom
          (toTensorSheafSection X.toRingedSpace (idealSheafOfModules (I ^ m))
            (idealSheafOfModules (I ^ n)) (op U) (y ⊗ₜ z))) =
      idealSheafSection (I ^ m) y * idealSheafSection (I ^ n) z :=
    (idealSheafSection_idealTensorMul (I ^ m) (I ^ n) U
          (toTensorSheafSection X.toRingedSpace (idealSheafOfModules (I ^ m))
            (idealSheafOfModules (I ^ n)) (op U) (y ⊗ₜ z))).trans
      (idealTensorToUnit_app_tmul (I ^ m) (I ^ n) U y z)
  exact (Stacks.Blowup.reesMultiplication_ambient I (m : ℤ) (n : ℤ) U y z).trans hprod.symm

end Stacks.Divisors

end

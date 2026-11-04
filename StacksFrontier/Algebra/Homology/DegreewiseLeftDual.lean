module

public import Mathlib.Algebra.Homology.Monoidal
public import StacksCore.CategoryTheory.GradedObject.Monoidal.Dual
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# Degreewise duals of a dual pair of cochain complexes

Let `C` be a monoidal preadditive category with the coproducts that make both
`GradedObject ℤ C` and `CochainComplex C ℤ` monoidal, the tensor product of complexes being
the total complex of the degreewise tensor product. If a complex `L` is a left dual of a
complex `K`, then in each degree `n` the term `L^{-n}` is a left dual of `K^n`, and the
pairing of that pair is the degree-`n` component of the pairing of `K` and `L`.

This is the step that turns a duality hypothesis on a complex into one on each of its terms,
and it is the converse of the assembly of [Stacks, Tag 0FP9]: there degreewise duals are
summed into a graded dual, here a dual of a complex is read degree by degree. In particular
it is what makes [Stacks, Tag 0FNW] — a module with a left dual is locally a direct summand
of a finite free module — applicable to the terms of a complex of modules with a left dual.

## Main definitions

* `CochainComplex.exactPairingX`: the underlying graded objects of a dual pair of complexes
  are themselves a dual pair.
* `CochainComplex.exactPairingXApply`: the dual pair `(K^n, L^{-n})` in degree `n`.

## Main results

* `CochainComplex.exactPairingXApply_coevaluation` and
  `CochainComplex.exactPairingXApply_evaluation`: the degreewise pairing is the degree-`n`
  component `ηₙ`, `εₙ` of the pairing of the complexes.
* `CochainComplex.isZero_X_of_coevApply_eq_zero`: a term whose degreewise coevaluation
  vanishes is a zero object.

## Implementation notes

Mathlib's monoidal structure on `CochainComplex C ℤ` is induced along the forgetful functor
to graded objects, which therefore is monoidal; `CategoryTheory.ExactPairing.map` transports
the pairing along it, and `CategoryTheory.GradedObject.Monoidal.exactPairingApply` reads the
transported pairing degree by degree. The differential plays no part: both triangle
identities for the terms already hold for the underlying graded objects.

The unit of the monoidal structure on complexes is the unit of `C` in degree zero, which is
only isomorphic — not equal — to the unit of the graded monoidal structure; that isomorphism
is the unit structure map of the forgetful functor, and it is the reason the transported
coevaluation and evaluation are conjugated by it rather than being the original ones.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNW](https://stacks.math.columbia.edu/tag/0FNW)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject
open CategoryTheory.GradedObject.Monoidal

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The forgetful functor from cochain complexes to graded objects is monoidal, the monoidal
structure on complexes being the one it induces. -/
@[instance_reducible]
noncomputable def forgetMonoidal : (HomologicalComplex.forget C (ComplexShape.up ℤ)).Monoidal :=
  Monoidal.fromInducedMonoidal _
    (HomologicalComplex.Monoidal.inducingFunctorData C (ComplexShape.up ℤ))

/-- The underlying graded object of a cochain complex. -/
abbrev toGradedObject (K : CochainComplex C ℤ) : GradedObject ℤ C := K.X

variable (K L : CochainComplex C ℤ) [ExactPairing K L]

/-- **The underlying graded objects of a dual pair of complexes are a dual pair.** The
coevaluation and evaluation are those of the complexes, read through the identification of
the two units. -/
@[instance_reducible]
noncomputable def exactPairingX : ExactPairing (toGradedObject K) (toGradedObject L) :=
  letI := forgetMonoidal (C := C)
  ExactPairing.map (HomologicalComplex.forget C (ComplexShape.up ℤ)) K L

/-- **The degreewise duals of a dual pair of complexes.** If `L` is a left dual of `K`, then
in every degree `n` the term `L^{-n}` is a left dual of the term `K^n`. -/
@[instance_reducible]
noncomputable def exactPairingXApply (n : ℤ) : ExactPairing (K.X n) (L.X (-n)) :=
  letI := exactPairingX K L
  exactPairingApply (toGradedObject K) (toGradedObject L) n

attribute [local instance] exactPairingX exactPairingXApply

/-- The coevaluation of the degreewise dual pair is the degree-`n` component `ηₙ` of the
coevaluation of the complexes. -/
theorem exactPairingXApply_coevaluation (n : ℤ) :
    η_ (K.X n) (L.X (-n)) = coevApply (toGradedObject K) (toGradedObject L) n :=
  rfl

/-- The evaluation of the degreewise dual pair is the degree-`n` component `εₙ` of the
evaluation of the complexes. -/
theorem exactPairingXApply_evaluation (n : ℤ) :
    ε_ (K.X n) (L.X (-n)) = evalApply (toGradedObject K) (toGradedObject L) n :=
  rfl

/-- A term of a complex with a left dual is a zero object as soon as the degreewise
coevaluation in that degree vanishes. -/
theorem isZero_X_of_coevApply_eq_zero (n : ℤ)
    (h : coevApply (toGradedObject K) (toGradedObject L) n = 0) :
    IsZero (K.X n) :=
  isZero_of_coevaluation_eq_zero (X := K.X n) (Y := L.X (-n))
    ((exactPairingXApply_coevaluation K L n).trans h)

end CochainComplex

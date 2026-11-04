module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
public import StacksFrontier.AlgebraicGeometry.TensorPowerCongrMul.Successor

/-!
# Tag 01CU's congruence of integral tensor powers is the Laurent one, and is multiplicative

There are two comparisons `L^{⊗ n} ≅ L'^{⊗ n}` of the integral tensor powers of
[Stacks, Tag 01CU] induced by an isomorphism `e : L ≅ L'` of invertible modules:

* `Stacks.SheafOfModules.TensorPower.tensorPowerCongr`, transported through the iterates of the
  two tensoring autoequivalences;
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso`, built by recursion on
  the degree, which is multiplicative in every integral bidegree
  (`...LaurentCongr.congrIso_mul`).

Identifying them needs the successor law for `powIntertwineObj` for every integer exponent, which
is `Stacks.Equivalence.powIntertwineObj_succIso`. With it, this file shows that the two
comparisons agree in every integer degree, so that Tag 01CU's own congruence inherits the
multiplicativity of the Laurent one.

## Main definitions

* `...LaurentCongr.congrCmpTP`: `Stacks.SheafOfModules.TensorPower.tensorPowerCongr`, with its
  type ascribed to the homogeneous pieces of the Laurent algebra. The two spellings are equal by
  definition; naming the ascription is what lets the statements below be compared with
  `congrIso`'s.

## Main results

* `...LaurentCongr.congrSucc_congrCmpTP`: `tensorPowerCongr` satisfies the recursion `congrIso`
  is defined by. This is `Stacks.SheafOfModules.TensorPower.tensorPowerCongr_succIso` with the
  degree-one comparison rewritten as a left whiskering.
* `...LaurentCongr.congrCmpTP_eq_congrIso`: **the two comparisons agree, in every integer
  degree.**
* `...LaurentCongr.congrCmpTP_mul`: **Tag 01CU's congruence of integral tensor powers is
  multiplicative in every integral bidegree** — it intertwines the coherent multiplication
  `Stacks.SheafOfModules.TensorPower.coherentMulIso` on `L` with the one on `L'`.

## Implementation notes

The induction is the one `congrIso` is built by, and runs in both directions out of the degree
zero: upwards by the recursion itself, downwards by `...LaurentCongr.congrPred_congrSucc`, since
the raising step is invertible. The downward step is `congrCmpTP_eq_of_succ`, stated with the
degree `n + 1` in the hypothesis rather than with a subtraction so that the `Int.induction_on`
branch can supply it after a single `rw` on the exponent, as `congrIso_mul` does.

Three spelling crossings occur and all three are handled by `exact` rather than `rw`:
`Y.Modules` against `SheafOfModules (structureRingSheaf T.toRingedSpace)` against
`SheafOfModules (TensorSheafification.structureSheaf T.toRingedSpace.presheaf _)` are equal by
definition but not syntactically, so a `rw` whose pattern names one of them does not see the
others.

The same crossing makes one instance unreachable by search. The hypothesis of
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr_succIso` is that right tensoring by the
module is an equivalence, at the native spelling
`(Tensor.sheafTensor ⟨T.toRingedSpace.presheaf, _⟩).flip.obj L`, and the instance supplying it,
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor`, carries its module over
`TensorSheafification.structureSheaf`, which the variables here spell `structureRingSheaf`.
Neither spelling unfolds at the transparency instance search runs at, so the instance is named
explicitly, for `L` and for `L'`, exactly as `congrCmpTP` already does.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T : Scheme.{u}}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
  (e : L ≅ L')

/-- **Tag 01CU's own congruence of integral tensor powers**,
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr`, with its type ascribed to the homogeneous
pieces of the Laurent algebras of `L` and `L'`. The ascription is definitional; it exists so that
the statements below live at the same spelling as `congrIso`'s and can be compared with them. -/
abbrev congrCmpTP (n : ℤ) : CongrCmp e n :=
  letI := isEquivalence_tensorRightFunctor T.toRingedSpace.presheaf (isSheafStruct T) L
  letI := isEquivalence_tensorRightFunctor T.toRingedSpace.presheaf (isSheafStruct T) L'
  tensorPowerCongr T.toRingedSpace.presheaf (isSheafStruct T) e n

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L'] in
/-- The degree-one comparison that `tensorPowerCongr` is transported along is a left whiskering
by the isomorphism. This is `...LaurentPullback.bridge_tensorIso_left`: the tensor product sheaf
of an identity with `e` is the monoidal left whiskering by `e`. -/
theorem tensorRightFunctorObjCongr_hom_eq_whiskerLeft
    (X : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
        (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).obj X).mapIso e).hom =
      X ◁ e.hom :=
  (Stacks.SheafOfModules.whiskerLeft_eq_sheafify_map
    T.toRingedSpace.presheaf (isSheafStruct T) X e.hom).symm

/-- **`tensorPowerCongr` satisfies the recursion `congrIso` is defined by.** Raising the degree
of `tensorPowerCongr` at `n` by `...LaurentCongr.congrSucc` gives `tensorPowerCongr` at `n + 1`.

This is `Stacks.SheafOfModules.TensorPower.tensorPowerCongr_succIso` with its degree-one
comparison rewritten as a left whiskering and with the successor comparison on the `L` side
cancelled off the front. -/
theorem congrSucc_congrCmpTP (n : ℤ) :
    congrSucc e n (congrCmpTP e n) = congrCmpTP e (n + 1) := by
  refine Iso.ext ((cancel_epi (succIso L n).hom).mp ?_)
  have hcs : (congrSucc e n (congrCmpTP e n)).hom =
      ((succIso L n).inv ≫ ((laurent L).piece n ◁ e.hom)) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
            (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').map
            (congrCmpTP e n).hom ≫ (succIso L' n).hom) := rfl
  rw [hcs]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  let := isEquivalence_tensorRightFunctor T.toRingedSpace.presheaf (isSheafStruct T) L
  let := isEquivalence_tensorRightFunctor T.toRingedSpace.presheaf (isSheafStruct T) L'
  rw [← tensorRightFunctorObjCongr_hom_eq_whiskerLeft e]
  exact (tensorPowerCongr_succIso T.toRingedSpace.presheaf (isSheafStruct T) e n).symm

/-- **The downward step of the identification.** If the two comparisons agree in the degree
`n + 1` then they agree in the degree `n`: the lowering step `...LaurentCongr.congrPred` inverts
the raising step, and both families satisfy the raising recursion. -/
theorem congrCmpTP_eq_of_succ {n : ℤ}
    (h : congrCmpTP e (n + 1) = congrIso e (n + 1)) :
    congrCmpTP e n = congrIso e n := by
  have h2 : congrPred e n (congrCmpTP e (n + 1)) = congrCmpTP e n := by
    rw [← congrSucc_congrCmpTP e n]
    exact congrPred_congrSucc e n (congrCmpTP e n)
  rw [← h2, h, ← congrIso_pred]

/-- **The two comparisons of the integral tensor powers agree, in every integer degree.**
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr` and
`...LaurentCongr.congrIso` are the same isomorphism.

Both are the identity in the degree zero and both satisfy the raising recursion
`...LaurentCongr.congrSucc` — for `congrIso` by construction, for `tensorPowerCongr` by
`congrSucc_congrCmpTP` — and that recursion is invertible, so the two families agree
everywhere. -/
theorem congrCmpTP_eq_congrIso (n : ℤ) : congrCmpTP e n = congrIso e n := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [congrIso_succ, ← ih, congrSucc_congrCmpTP]
  | pred i ih => exact congrCmpTP_eq_of_succ e (by rwa [sub_add_cancel])

/-- **Tag 01CU's congruence of integral tensor powers is multiplicative in every integral
bidegree.** The coherent multiplication
`Stacks.SheafOfModules.TensorPower.coherentMulIso` of `L` followed by the comparison in the
degree `n + m` is the comparisons in the degrees `n` and `m` on the two factors followed by the
coherent multiplication of `L'`. Both degrees are arbitrary integers.

This is `...LaurentCongr.congrIso_mul` transported along `congrCmpTP_eq_congrIso`. -/
theorem congrCmpTP_mul (n m : ℤ) :
    (mulIso L n m).hom ≫ (congrCmpTP e (n + m)).hom =
      ((congrCmpTP e n).hom ⊗ₘ (congrCmpTP e m).hom) ≫ (mulIso L' n m).hom := by
  rw [congrCmpTP_eq_congrIso e (n + m), congrCmpTP_eq_congrIso e n, congrCmpTP_eq_congrIso e m]
  exact congrIso_mul e n m

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria

/-!
# Tensor powers of a tensor power of an invertible sheaf of modules

Let `L` be an invertible sheaf of modules on a ringed site and let `n, m` be integers. The
tensor power `L^{⊗ n}` of Tag 01CU is again invertible, and this file constructs the
comparison

`(L^{⊗ n})^{⊗ m} ≅ L^{⊗ n m}`.

The integer tensor powers are the images of the structure sheaf under the integer powers of the
autoequivalence `e = - ⊗ L`, so the comparison is an instance of a statement about
autoequivalences alone: if `f` is an autoequivalence whose functor is isomorphic to that of
`e ^ n`, then the functor of `f ^ m` is isomorphic to that of `e ^ (n m)`. Tensoring on the
right by `L^{⊗ n}` is such an `f`, by `Stacks.SheafOfModules.TensorPower.powFunctorIsoTensorRight`.

## Main definitions

* `CategoryTheory.Equivalence.powPowFunctorIso`: for autoequivalences `e` and `f` with
  `f.functor ≅ (e ^ n).functor`, the isomorphism `(f ^ m).functor ≅ (e ^ (n * m)).functor`.
* `Stacks.SheafOfModules.Invertible.tensorPowerTensorPowerIso`: the comparison
  `(L^{⊗ n})^{⊗ m} ≅ L^{⊗ (n * m)}`.

## Implementation notes

For `m < 0` the power `f ^ m` applies a chosen quasi-inverse of `f`, so it has no description in
terms of objects. The negative half of `CategoryTheory.Equivalence.powPowFunctorIso` is therefore
built by descending recursion, each step cancelling the equivalence `f` on the right
(`Stacks.SheafOfModules.TensorPower.cancelRightEquivalence`), exactly as the comparison of the
iterates of `- ⊗ L` with tensoring by `L^{⊗ m}` is built.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C]

/-- The comparison `(f ^ k).functor ≅ (e ^ (n * k)).functor` for a natural number `k`, by
ascending recursion on `k`. -/
def powPowNat (e f : C ≌ C) (n : ℤ) (α : f.functor ≅ (e ^ n).functor) :
    (k : ℕ) → ((f ^ (k : ℤ)).functor ≅ (e ^ (n * k)).functor)
  | 0 => eqToIso (by rw [Nat.cast_zero, mul_zero]; rfl)
  | k + 1 =>
      (powSucc f (k : ℤ) ((k + 1 : ℕ) : ℤ) (by push_cast; rfl)).symm ≪≫
        Functor.isoWhiskerRight (powPowNat e f n α k) f.functor ≪≫
        Functor.isoWhiskerLeft (e ^ (n * k)).functor α ≪≫
        powAdd e (n * k) n (n * ((k + 1 : ℕ) : ℤ)) (by push_cast; ring)

/-- The comparison `(f ^ (-k)).functor ≅ (e ^ (n * (-k))).functor` for a natural number `k`, by
descending recursion, each step cancelling `f` on the right. -/
def powPowNeg (e f : C ≌ C) (n : ℤ) (α : f.functor ≅ (e ^ n).functor) :
    (k : ℕ) → ((f ^ (-(k : ℤ))).functor ≅ (e ^ (n * -(k : ℤ))).functor)
  | 0 => eqToIso (by rw [Nat.cast_zero, neg_zero, mul_zero]; rfl)
  | k + 1 =>
      Stacks.SheafOfModules.TensorPower.cancelRightEquivalence f
        (powSucc f (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ)) (by push_cast; ring) ≪≫
          powPowNeg e f n α k ≪≫
          (powAdd e (n * -((k + 1 : ℕ) : ℤ)) n (n * -(k : ℤ)) (by push_cast; ring)).symm ≪≫
          Functor.isoWhiskerLeft (e ^ (n * -((k + 1 : ℕ) : ℤ))).functor α.symm)

/-- **Powers of a power of an autoequivalence.** If the functor of the autoequivalence `f` is
isomorphic to that of `e ^ n`, then for every integer `m` the functor of `f ^ m` is isomorphic
to that of `e ^ (n * m)`. -/
def powPowFunctorIso (e f : C ≌ C) (n : ℤ) (α : f.functor ≅ (e ^ n).functor) :
    (m : ℤ) → ((f ^ m).functor ≅ (e ^ (n * m)).functor)
  | Int.ofNat k => powPowNat e f n α k
  | Int.negSucc k =>
      eqToIso (congrArg (fun p : ℤ => (f ^ p).functor)
          (show Int.negSucc k = -((k + 1 : ℕ) : ℤ) from rfl)) ≪≫
        powPowNeg e f n α (k + 1) ≪≫
        eqToIso (congrArg (fun p : ℤ => (e ^ (n * p)).functor)
          (show -((k + 1 : ℕ) : ℤ) = Int.negSucc k from rfl))

end CategoryTheory.Equivalence

namespace Stacks.SheafOfModules.Invertible

open AlgebraicGeometry.SheafOfModules (IsInvertible)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Tensor powers of a tensor power.** For an invertible sheaf of modules `L` and integers
`n` and `m`, the `m`-th tensor power of the invertible sheaf `L^{⊗ n}` is `L^{⊗ (n * m)}`. -/
def tensorPowerTensorPowerIso
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ) :
    letI := tensorPower_isInvertible O hO L n
    tensorPower O hO (tensorPower O hO L n) m ≅ tensorPower O hO L (n * m) :=
  letI := tensorPower_isInvertible O hO L n
  (Equivalence.powPowFunctorIso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L n)).asEquivalence n
    (Stacks.SheafOfModules.TensorPower.powFunctorIsoTensorRight O hO L n).symm m).app
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

end Stacks.SheafOfModules.Invertible

end

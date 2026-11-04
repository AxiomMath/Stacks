module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge

/-!
# The step maps of the two integer tensor powers agree

There are two developments of the integer tensor power `L^{⊗ n}` of an invertible sheaf of
modules on a ringed site: `Stacks.SheafOfModules.Invertible.tensorPower` assumes
`AlgebraicGeometry.SheafOfModules.IsInvertible`, while
`Stacks.SheafOfModules.TensorPower.tensorPower` assumes that tensoring on the right by `L` is an
equivalence, and the two powers are the same sheaf of modules
(`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower`). Each development builds its step
map `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` from its own copy of the successor comparison for integer
iterates of an autoequivalence, `Stacks.SheafOfModules.Invertible.powSuccIso` and
`Stacks.Equivalence.powSuccIso`. This file proves that the two copies agree, and hence that the
two step maps agree.

## Main results

* `Stacks.SheafOfModules.Invertible.powNatSuccIso_eq`,
  `Stacks.SheafOfModules.Invertible.powNatInverseSuccIso_eq` and
  `Stacks.SheafOfModules.Invertible.powSuccIso_eq`: the two copies of the successor comparison
  for iterates of an autoequivalence are the same isomorphism, for non-negative iterates, for
  inverse iterates, and for integer iterates respectively.
* `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_eq` and
  `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_hom_eq`: the two step maps
  `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` are the same isomorphism, and have the same underlying
  morphism.
* `Stacks.SheafOfModules.Invertible.tensorPowerOneIso_eq` and
  `Stacks.SheafOfModules.Invertible.tensorPowerReindex_eq`: the degree-one identification and
  the reindexing isomorphism also agree.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.SheafOfModules.Invertible

section Iterates

variable {A : Type u} [Category.{v} A]

/-- The two copies of the successor comparison for non-negative iterates of an autoequivalence
are the same isomorphism. -/
theorem powNatSuccIso_eq (e : A ≌ A) :
    (n : ℕ) → (M : A) → powNatSuccIso e n M = Stacks.Equivalence.powNatSuccIso e n M
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, M => powNatSuccIso_eq e (n + 1) (e.functor.obj M)

/-- The two copies of the cancellation comparison for inverse iterates of an autoequivalence
are the same isomorphism. -/
theorem powNatInverseSuccIso_eq (e : A ≌ A) :
    (n : ℕ) → (M : A) →
      powNatInverseSuccIso e n M = Stacks.Equivalence.powNatInverseSuccIso e n M
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, M => powNatInverseSuccIso_eq e (n + 1) (e.inverse.obj M)

/-- The two copies of the successor comparison
`e.functor.obj ((e ^ n).functor.obj M) ≅ (e ^ (n + 1)).functor.obj M` for integer iterates of an
autoequivalence are the same isomorphism. -/
theorem powSuccIso_eq (e : A ≌ A) (n : ℤ) (M : A) :
    powSuccIso e n M = Stacks.Equivalence.powSuccIso e n M := by
  match n with
  | Int.ofNat k => exact powNatSuccIso_eq e k M
  | Int.negSucc 0 => rfl
  | Int.negSucc (k + 1) => exact powNatInverseSuccIso_eq e (k + 1) M

end Iterates

section Sheaves

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The step maps `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` of the two integer tensor powers agree. -/
theorem tensorPowerSuccIso_eq
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] (n : ℤ) :
    tensorPowerSuccIso O hO L n =
      Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso O hO L n :=
  powSuccIso_eq _ n _

/-- The underlying morphisms of the two step maps agree. -/
theorem tensorPowerSuccIso_hom_eq
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] (n : ℤ) :
    (tensorPowerSuccIso O hO L n).hom =
      (Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso O hO L n).hom :=
  congrArg Iso.hom (tensorPowerSuccIso_eq O hO L n)

/-- The two developments' identifications of the first tensor power with `L` agree. -/
theorem tensorPowerOneIso_eq
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    tensorPowerOneIso O hO L = Stacks.SheafOfModules.TensorPower.tensorPowerOneIso O hO L :=
  rfl

/-- The two developments' reindexing isomorphisms along an equality of exponents agree. -/
theorem tensorPowerReindex_eq
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] {n m : ℤ} (h : n = m) :
    tensorPowerReindex O hO L h =
      Stacks.SheafOfModules.TensorPower.tensorPowerReindex O hO L h := by
  subst h
  rfl

end Sheaves

end Stacks.SheafOfModules.Invertible

end

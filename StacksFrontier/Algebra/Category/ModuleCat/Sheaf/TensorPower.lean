module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedSymmetry
public import StacksCore.Tactic.StacksAttribute

/-!
# Integer tensor powers of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site and let `L` be a sheaf of `O`-modules which
is invertible, in the sense that tensoring by `L` is an autoequivalence of the category of
sheaves of `O`-modules. The `n`th tensor power `L^{⊗ n}`, for `n : ℤ`, is the image of the
structure sheaf under the `n`th power of that autoequivalence; negative powers use its
quasi-inverse, which is what makes the definition available for all integers.

The arithmetic of these powers rests on a comparison between an iterated autoequivalence and
one further application of it, and this file provides that comparison for an arbitrary
autoequivalence of an arbitrary category, together with its naturality. Mathlib defines
`CategoryTheory.Equivalence.powNat` and the integer power `e ^ n` but proves nothing about
them beyond the three values `e ^ 0`, `e ^ 1` and `e ^ (-1)`, so the comparison and its
naturality are built here from scratch.

## Main definitions

The general statements about iterated autoequivalences live in `Stacks.Equivalence`, the
sheaf-theoretic ones in `Stacks.SheafOfModules.TensorPower`.

* `powNatSuccIso`, `powNatInverseSuccIso` and `powSuccIso`: for an autoequivalence `e` of a
  category, the comparison `e.functor.obj ((e ^ n).functor.obj M) ≅ (e ^ (n + 1)).functor.obj M`
  between an iterate and its successor, for `n : ℕ`, for negative iterates, and for `n : ℤ`
  respectively.
* `tensorRightFunctor` and `tensorLeftFunctor`: tensoring on the right, respectively on the
  left, by a sheaf of modules.
* `tensorPowerEquivalence`: the `n`th power of the autoequivalence given by tensoring on the
  right by `L`.
* `tensorPower`: the `n`th tensor power of `L`, for `n : ℤ`.
* `tensorPowerSuccIso`: the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`.
* `tensorPowerReindex`: reindexing of tensor powers along an equality of integers.

## Main results

* `powSuccIso_naturality`: the successor comparison is natural in the object the iterated
  autoequivalence is applied to. Its sheaf-theoretic instance is `tensorPowerSuccIso_natural`.
* `tensorPower_zero`: the zeroth tensor power is the structure sheaf.
* `tensorPowerOneIso`: the first tensor power is `L`.
* `isEquivalence_tensorRightFunctor_iff`: tensoring on the right by `L` is an equivalence
  exactly when tensoring on the left by `L` is, so the hypothesis used here is the usual
  notion of invertibility.

## Implementation notes

Invertibility of `L` is taken to mean that the native sheaf tensor bifunctor, flipped and
evaluated at `L`, is an equivalence. `isEquivalence_tensorRightFunctor_iff` relates its two
variables through the native braiding, without a separate tensor-functor implementation.

The tensor product of sheaves of modules used here is the sheafification of the objectwise
tensor product of the underlying presheaves of modules, so that
the native tensor bifunctor and its flip have the same object at `(M, L)` by definition;
this is what lets `tensorPowerSuccIso` be stated in terms of the tensor product while being
constructed from the iteration.

The successor comparison is not a single formula. For non-negative exponents the iteration
`e ^ (n + 1) = e.trans (e ^ n)` already applies `e` once more, so the comparison is an identity
after reassociating the recursion; for negative exponents the extra application of `e` cancels
one inverse iterate, and the comparison is the counit of the equivalence. Both cases are
defined by the recursion that `Equivalence.powNat` itself uses, whose base cases are `0` and
`1`, and naturality is proved by the same recursion.

This file does not construct the canonical multiplication isomorphisms
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` and their coherence. Those need two inputs which are not
available: a symmetric monoidal structure on sheaves of modules, whose associativity and unit
constraints the coherence laws are stated against, and the rank-one local structure of an
invertible sheaf, without which the commutativity constraint fails to be provable — a
commutativity constraint forces the braiding of `L^{⊗ n}` with itself to be the identity,
which is a genuine property of invertible modules and not a formal consequence of the
monoidal axioms.

The site universes `u`, `v` are independent of the section universe `w`; the rings and the
modules share the universe `w`, as Mathlib's monoidal structure on presheaves of modules
requires.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks

namespace Equivalence

variable {A : Type u} [Category.{v} A]

/-- Iteration of an autoequivalence commutes with applying it once more: the comparison is the
identity after reassociating the recursion defining `Equivalence.powNat`. -/
noncomputable def powNatSuccIso (e : A ≌ A) :
    (n : ℕ) → (M : A) →
      e.functor.obj ((e.powNat n).functor.obj M) ≅ (e.powNat (n + 1)).functor.obj M
  | 0, _ => Iso.refl _
  | 1, _ => Iso.refl _
  | n + 2, M => powNatSuccIso e (n + 1) (e.functor.obj M)

/-- The successor comparison for non-negative iterates is natural in the object. -/
theorem powNatSuccIso_naturality (e : A ≌ A) :
    (n : ℕ) → (M N : A) → (f : M ⟶ N) →
      e.functor.map ((e.powNat n).functor.map f) ≫ (powNatSuccIso e n N).hom =
        (powNatSuccIso e n M).hom ≫ (e.powNat (n + 1)).functor.map f
  | 0, _, _, _ | 1, _, _, _ => (Category.comp_id _).trans (Category.id_comp _).symm
  | n + 2, M, N, f =>
      powNatSuccIso_naturality e (n + 1) (e.functor.obj M) (e.functor.obj N) (e.functor.map f)

/-- Applying an autoequivalence cancels the first of its inverse iterates. -/
noncomputable def powNatInverseSuccIso (e : A ≌ A) :
    (n : ℕ) → (M : A) →
      e.functor.obj ((e.symm.powNat (n + 1)).functor.obj M) ≅ (e.symm.powNat n).functor.obj M
  | 0, M => e.counitIso.app M
  | 1, M => e.counitIso.app (e.inverse.obj M)
  | n + 2, M => powNatInverseSuccIso e (n + 1) (e.inverse.obj M)

/-- The cancellation comparison for inverse iterates is natural in the object. -/
theorem powNatInverseSuccIso_naturality (e : A ≌ A) :
    (n : ℕ) → (M N : A) → (f : M ⟶ N) →
      e.functor.map ((e.symm.powNat (n + 1)).functor.map f) ≫
          (powNatInverseSuccIso e n N).hom =
        (powNatInverseSuccIso e n M).hom ≫ (e.symm.powNat n).functor.map f
  | 0, _, _, f => e.counitIso.hom.naturality f
  | 1, _, _, f => e.counitIso.hom.naturality (e.inverse.map f)
  | n + 2, M, N, f =>
      powNatInverseSuccIso_naturality e (n + 1) (e.inverse.obj M) (e.inverse.obj N)
        (e.inverse.map f)

/-- The successor comparison for the integer iterates of an autoequivalence. For negative
exponents the extra application of `e` cancels an inverse iterate, so the comparison is the
counit of the equivalence. -/
noncomputable def powSuccIso (e : A ≌ A) :
    (n : ℤ) → (M : A) →
      e.functor.obj ((e ^ n).functor.obj M) ≅ (e ^ (n + 1)).functor.obj M
  | Int.ofNat k, M => powNatSuccIso e k M
  | Int.negSucc 0, M => e.counitIso.app M
  | Int.negSucc (k + 1), M => powNatInverseSuccIso e (k + 1) M

/-- The successor comparison for integer iterates is natural in the object the iterated
autoequivalence is applied to. -/
theorem powSuccIso_naturality (e : A ≌ A) (n : ℤ) {M N : A} (f : M ⟶ N) :
    e.functor.map ((e ^ n).functor.map f) ≫ (powSuccIso e n N).hom =
      (powSuccIso e n M).hom ≫ (e ^ (n + 1)).functor.map f := by
  match n with
  | Int.ofNat k => exact powNatSuccIso_naturality e k M N f
  | Int.negSucc 0 => exact e.counitIso.hom.naturality f
  | Int.negSucc (k + 1) => exact powNatInverseSuccIso_naturality e (k + 1) M N f

end Equivalence

namespace SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Symmetry of the tensor product identifies tensoring on the left by `L` with tensoring on
the right by `L`. -/
noncomputable def tensorLeftIsoTensorRight
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L) := by
  letI := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  exact (Stacks.SheafOfModules.TensorRaised.tensorRightRaisedIso.{u, v, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩ L).symm

/-- Tensoring on the right by `L` is an equivalence exactly when tensoring on the left by `L`
is: the two functors are isomorphic. -/
theorem isEquivalence_tensorRightFunctor_iff
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence ↔
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).obj L)).IsEquivalence :=
  ⟨fun _ ↦ Functor.isEquivalence_of_iso (tensorLeftIsoTensorRight O hO L).symm,
    fun _ ↦ Functor.isEquivalence_of_iso (tensorLeftIsoTensorRight O hO L)⟩

/-- The autoequivalence obtained by tensoring on the right by `L` an integer number of times.
Negative powers use the chosen quasi-inverse. -/
@[implicit_reducible]
noncomputable def tensorPowerEquivalence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] (n : ℤ) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).asEquivalence ^ n

/-- The `n`th tensor power of an invertible sheaf of modules `L`, for `n : ℤ`: the image of the
structure sheaf under the `n`th power of the autoequivalence given by tensoring by `L`. -/
@[stacks 01CU]
noncomputable def tensorPower
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] (n : ℤ) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  (tensorPowerEquivalence O hO L n).functor.obj
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- The zeroth tensor power is the structure sheaf. -/
@[simp]
theorem tensorPower_zero
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] :
    tensorPower O hO L 0 = SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) := rfl

/-- The first tensor power is `L`: the left unit constraint of the tensor product of presheaves
of modules, followed by the counit of sheafification. -/
noncomputable def tensorPowerOneIso
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] :
    tensorPower O hO L 1 ≅ L := by
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        := by
    change MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  letI : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit := by
    change IsIso
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit
    infer_instance
  change (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
      ((SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val ⊗
        L.val) ≅ L
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (λ_ L.val) ≪≫
    (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit).app L

/-- The successor comparison for tensor powers: tensoring the `n`th power by `L` once more
gives the `(n + 1)`st power. -/
noncomputable def tensorPowerSuccIso
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
        (tensorPower O hO L n)).obj L ≅
      tensorPower O hO L (n + 1) :=
  Equivalence.powSuccIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).asEquivalence n
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- Reindexing tensor powers along an equality of integers. -/
noncomputable def tensorPowerReindex
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] {n m : ℤ} (h : n = m) :
    tensorPower O hO L n ≅ tensorPower O hO L m := by
  subst h
  exact Iso.refl _

/-- Reindexing along a reflexive equality is the identity. -/
@[simp]
theorem tensorPowerReindex_rfl
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] {n : ℤ} (h : n = n) :
    tensorPowerReindex O hO L h = Iso.refl _ := rfl

/-- The successor comparison of the iteration defining the tensor powers is natural in the
sheaf of modules the iterated autoequivalence is applied to. -/
theorem tensorPowerSuccIso_natural
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).IsEquivalence] (n : ℤ)
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f :
      M ⟶ N) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).map ((tensorPowerEquivalence O hO L n).functor.map f) ≫
        (Equivalence.powSuccIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).asEquivalence n N).hom =
      (Equivalence.powSuccIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).asEquivalence n M).hom ≫
        (tensorPowerEquivalence O hO L (n + 1)).functor.map f :=
  Equivalence.powSuccIso_naturality (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
        hO⟩).flip.obj L)).asEquivalence n f

end SheafOfModules.TensorPower

end Stacks

end

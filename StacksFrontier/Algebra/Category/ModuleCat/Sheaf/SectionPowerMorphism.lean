module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-!
# Powers of a global section of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site and let `L` be a sheaf of `O`-modules whose
tensor functor is an equivalence, so that the integer tensor powers `L^{⊗ n}` of Tag 01CU are
available. A global section of `L^{⊗ n}` is the same thing as a morphism
`O ⟶ L^{⊗ n}` out of the structure sheaf, and among those morphisms the `n`-th power `sⁿ` of a
global section `s` of `L` is cut out by the two rules `s⁰ = 𝟙` and `sⁿ⁺¹ = sⁿ ⊗ s`. This file
defines those rules, the predicate they cut out, and multiplication by such a power: the
morphism `F ⟶ F ⊗ L^{⊗ n}` by which a power of `s` acts on an arbitrary sheaf of modules `F`,
and hence on anything functorial in `F`.

## Main definitions

* `Stacks.SheafOfModules.sectionPowerSucc` adjoins one copy of `s` to a morphism representing
  a tensor power, raising its exponent by one.
* `Stacks.SheafOfModules.IsSectionPowerHom` is the predicate singling out the morphisms
  `O ⟶ L^{⊗ n}` that represent a power of `s`, by the unit and successor rules.
* `Stacks.SheafOfModules.sectionPowerHom` is the morphism representing `sⁿ` for a natural
  number exponent, defined by that recursion.
* `Stacks.SheafOfModules.sectionPowerAction` is multiplication by a power of `s`, the morphism
  `F ⟶ F ⊗ L^{⊗ n}` attached to a morphism `O ⟶ L^{⊗ n}`.

## Main results

* `Stacks.SheafOfModules.isSectionPowerHom_sectionPowerHom`: the recursive construction does
  represent a power of the section, so the predicate is satisfied in every nonnegative degree.
* `Stacks.SheafOfModules.IsSectionPowerHom.nonneg`: no morphism represents a power of a section
  in a negative degree.
* `Stacks.SheafOfModules.IsSectionPowerHom.unique`: in a fixed degree the representing morphism
  is unique, so the predicate determines `sⁿ` and not merely constrains it.

## Implementation notes

The exponent is an integer, because the tensor powers are, while the recursion defining a power
of a section runs over the natural numbers. The predicate is what bridges the two: a statement
indexed by an integer can require its data to represent `sⁿ` without the integer being known to
be a cast, and `IsSectionPowerHom.unique` then identifies that data with the recursive
construction wherever the exponent is a natural number.

Multiplication by `sⁿ` is the right unit constraint of the tensor product sheaf followed by
tensoring the given morphism on the left by `F`, which is the same recipe as the successor rule
with `F` in place of `L^{⊗ n}`; the two are kept separate because the successor rule composes
with the comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` and multiplication does not.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      L).IsEquivalence]

/-- Adjoin one copy of the global section `s` to a morphism `t : O ⟶ L^{⊗ n}`: tensor `t` on the
right by `s` and compare `L^{⊗ n} ⊗ L` with `L^{⊗ (n + 1)}`. -/
def sectionPowerSucc (s : L.sections) (n : ℤ)
    (t : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n) :
    SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L (n + 1) :=
  t ≫ ((tensorLeftFunctorObjUnitIso O hO (TensorPower.tensorPower O hO L n)).inv ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (TensorPower.tensorPower O hO L n)).map
        (L.unitHomEquiv.symm s)) ≫
    (TensorPower.tensorPowerSuccIso O hO L n).hom

/-- A morphism `O ⟶ L^{⊗ n}` *represents the `n`-th power of the global section `s`* when it is
obtained from the identity of the structure sheaf by adjoining `n` copies of `s`. -/
inductive IsSectionPowerHom (s : L.sections) : (n : ℤ) →
    (SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n) → Prop
  | zero : IsSectionPowerHom s 0 (𝟙 _)
  | succ {n : ℤ} {t} : IsSectionPowerHom s n t →
      IsSectionPowerHom s (n + 1) (sectionPowerSucc O hO L s n t)

/-- The morphism `O ⟶ L^{⊗ n}` representing the `n`-th power of a global section, for a natural
number exponent, by the recursion that `IsSectionPowerHom` describes. -/
def sectionPowerHom (s : L.sections) : (n : ℕ) →
    (SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n)
  | 0 => 𝟙 _
  | n + 1 => sectionPowerSucc O hO L s n (sectionPowerHom s n)

/-- The recursive construction does represent a power of the section. -/
theorem isSectionPowerHom_sectionPowerHom (s : L.sections) (n : ℕ) :
    IsSectionPowerHom O hO L s n (sectionPowerHom O hO L s n) := by
  induction n with
  | zero => exact .zero
  | succ n ih => simpa [sectionPowerHom] using IsSectionPowerHom.succ ih

/-- Multiplication by the power of a section represented by `t : O ⟶ L^{⊗ n}`: the morphism
`F ⟶ F ⊗ L^{⊗ n}` obtained by writing `F` as `F ⊗ O` and tensoring `t` on the left by `F`. -/
def sectionPowerAction
    (F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) (n : ℤ)
    (t : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n) :
    F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F)).obj ((TensorPower.tensorPower O hO L n))) :=
  (tensorLeftFunctorObjUnitIso O hO F).inv ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F).map t

/-- A morphism can only represent a power of a section in a nonnegative degree. -/
theorem IsSectionPowerHom.nonneg {s : L.sections} {n : ℤ}
    {t : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n}
    (h : IsSectionPowerHom O hO L s n t) : 0 ≤ n := by
  induction h with
  | zero => exact le_refl 0
  | succ _ ih => omega

/-- Two morphisms representing powers of the same section in the same degree are heterogeneously
equal. The degrees are kept separate so that the induction on the two derivations does not need
dependent elimination on the integer index. -/
private theorem isSectionPowerHom_heq {s : L.sections} :
    ∀ {n : ℤ} {t : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
        TensorPower.tensorPower O hO L n}, IsSectionPowerHom O hO L s n t →
      ∀ {m : ℤ} {t' : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
        TensorPower.tensorPower O hO L m}, IsSectionPowerHom O hO L s m t' →
      n = m → HEq t t' := by
  intro n t h
  induction h with
  | zero =>
      intro m t' h'
      induction h' with
      | zero => intro _; rfl
      | @succ k u' hu' _ =>
          intro hnm
          have := hu'.nonneg
          omega
  | @succ j u hu ih =>
      intro m t' h'
      induction h' with
      | zero =>
          intro hnm
          have := hu.nonneg
          omega
      | @succ k u' hu' _ =>
          intro hnm
          have hjk : j = k := by omega
          subst hjk
          have heq : u = u' := eq_of_heq (ih hu' rfl)
          subst heq
          rfl

/-- The morphism representing the `n`-th power of a global section is unique. -/
theorem IsSectionPowerHom.unique {s : L.sections} {n : ℤ}
    {t t' : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n}
    (h : IsSectionPowerHom O hO L s n t) (h' : IsSectionPowerHom O hO L s n t') :
    t = t' :=
  eq_of_heq (isSectionPowerHom_heq O hO L h h' rfl)

end Stacks.SheafOfModules

end

module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Basic
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Preadditive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded ring of sections of an invertible sheaf

This file assembles the graded ring

  `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})`

of Tag 01CV out of the two halves proved elsewhere: the graded *monoid* of
`StacksFrontier.AlgebraicGeometry.GradedSectionRing.Basic` (multiplication, associativity and
the two unit laws, all formal consequences of the monoidal structure) and the *distributive*
laws, which are `CategoryTheory.MonoidalPreadditive` for the tensor product of sheaves of
modules, proved as `Stacks.SheafOfModules.monoidalPreadditive`.

As there, the construction is done twice: abstractly for a `Stacks.Monoidal.PowerSystem` in a
preadditive monoidal category whose tensor product is biadditive, and then concretely for the
non-negative tensor powers of an invertible sheaf of modules.

## Main definitions

* `Stacks.Monoidal.PowerSystem.gradedRing`: the `DirectSum.GRing` structure on
  `n ↦ (𝟙_ C ⟶ S.obj n)`. **Unconditional.**
* `Stacks.Monoidal.PowerSystem.gradedCommRing`: the `DirectSum.GCommRing` structure on the same
  family, given the commutativity constraint of Tag 01CU as a hypothesis.
* `Stacks.SheafOfModules.Invertible.homGradedRing` and
  `Stacks.SheafOfModules.Invertible.homGradedCommRing`: the same two for the non-negative tensor
  powers of an invertible sheaf of modules, so that `⨁ n : ℕ, (𝟙_ ⟶ L^{⊗ n})` is a ring, and a
  commutative ring under the constraint.

## Main results

* `Stacks.Monoidal.PowerSystem.sectionMul_add`, `add_sectionMul`, `sectionMul_zero` and
  `zero_sectionMul`: **the multiplication of global sections is biadditive.** These are the four
  distributive laws of Tag 01CV, and they are exactly the four fields of
  `CategoryTheory.MonoidalPreadditive` read through `sectionTensor`.
* `Stacks.SheafOfModules.Invertible.homToSection_sectionMul` and
  `Stacks.SheafOfModules.Invertible.sectionToHom_sectionMul`: the multiplication of the graded
  ring agrees with `Stacks.SheafOfModules.Invertible.sectionMul`, the multiplication on Mathlib's
  `SheafOfModules.sections`. This is what makes the ring built here the ring of global sections.

## Implementation notes

**The grading is indexed by morphisms out of the tensor unit, not by
`PresheafOfModules.sections`.** Tag 01CV's summands are the global sections `Γ(X, L^{⊗ n})`, and
in this repository those are spelled two ways: as `(tensorPower O hO L n).sections`, Mathlib's
`PresheafOfModules.sections`, and as morphisms `𝟙_ ⟶ tensorPower O hO L n` out of the tensor
unit, the two being identified by `SheafOfModules.unitHomEquiv`. The graded ring is stated for
the second spelling because `DirectSum.GRing` needs an `AddCommGroup` on every summand and
`PresheafOfModules.sections` is a bare subtype of a product with no additive structure at all,
whereas a morphism group of a preadditive category has one for free. The alternative —
transporting an `AddCommGroup` onto `sections` along `unitHomEquiv` — would have coined a second,
non-canonical additive structure on a Mathlib type owned by another part of the development, and
would have left the additivity of `SheafOfModules.sectionsMap` to be proved separately; here the
four distributive laws are literally the four fields of `MonoidalPreadditive`. Nothing is lost:
`unitHomEquiv` is a bijection, the tensor unit *is* `SheafOfModules.unit` on the nose
(`Stacks.SheafOfModules.tensorUnit_eq`), and `homToSection_sectionMul` identifies the
multiplication of the ring with the multiplication already defined on `sections`.

The commutativity constraint of Tag 01CU is **not** a formal consequence of the symmetric monoidal
axioms (in a general symmetric monoidal category an invertible object only satisfies `β ≫ β = 𝟙`,
and the odd line in super vector spaces has `β = -𝟙`), so `gradedCommRing` and `homGradedCommRing`
carry it as an explicit hypothesis, in exactly the form
`Stacks.Monoidal.PowerSystem.sectionMul_comm` uses; and `gradedRing` is unconditional, which is
everything Tag 01CV's first clause asserts except commutativity.

`natCast` and `intCast` are `n • 1`, the only choice: `DirectSum.GSemiring.natCast_zero` and
`natCast_succ` force them.

Like `Stacks.SheafOfModules.monoidalCategory` and `Stacks.SheafOfModules.monoidalPreadditive`,
the sheaf-level results here need both of those activated as local instances together.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-! ### Biadditivity of the product of global sections -/

/-- The tensor product of a global section with the zero section is zero. -/
@[simp]
theorem sectionTensor_zero_right {M N : C} (s : 𝟙_ C ⟶ M) :
    sectionTensor s (0 : 𝟙_ C ⟶ N) = 0 := by
  simp [sectionTensor]

/-- The tensor product of the zero section with a global section is zero. -/
@[simp]
theorem zero_sectionTensor {M N : C} (t : 𝟙_ C ⟶ N) :
    sectionTensor (0 : 𝟙_ C ⟶ M) t = 0 := by
  simp [sectionTensor]

/-- The tensor product of global sections is additive in the second factor. -/
@[simp]
theorem sectionTensor_add_right {M N : C} (s : 𝟙_ C ⟶ M) (t t' : 𝟙_ C ⟶ N) :
    sectionTensor s (t + t') = sectionTensor s t + sectionTensor s t' := by
  simp [sectionTensor, MonoidalPreadditive.tensor_add]

/-- The tensor product of global sections is additive in the first factor. -/
@[simp]
theorem add_sectionTensor {M N : C} (s s' : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N) :
    sectionTensor (s + s') t = sectionTensor s t + sectionTensor s' t := by
  simp [sectionTensor, MonoidalPreadditive.add_tensor]

namespace PowerSystem

variable (S : PowerSystem C)

/-- The product of a global section with the zero section is zero. -/
@[simp]
theorem sectionMul_zero {a b : ℕ} (s : 𝟙_ C ⟶ S.obj a) :
    S.sectionMul s (0 : 𝟙_ C ⟶ S.obj b) = 0 := by
  simp [sectionMul]

/-- The product of the zero section with a global section is zero. -/
@[simp]
theorem zero_sectionMul {a b : ℕ} (t : 𝟙_ C ⟶ S.obj b) :
    S.sectionMul (0 : 𝟙_ C ⟶ S.obj a) t = 0 := by
  simp [sectionMul]

/-- The product of global sections distributes over addition in the second factor. -/
@[simp]
theorem sectionMul_add {a b : ℕ} (s : 𝟙_ C ⟶ S.obj a) (t t' : 𝟙_ C ⟶ S.obj b) :
    S.sectionMul s (t + t') = S.sectionMul s t + S.sectionMul s t' := by
  simp [sectionMul, Preadditive.add_comp]

/-- The product of global sections distributes over addition in the first factor. -/
@[simp]
theorem add_sectionMul {a b : ℕ} (s s' : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ S.obj b) :
    S.sectionMul (s + s') t = S.sectionMul s t + S.sectionMul s' t := by
  simp [sectionMul, Preadditive.add_comp]

/-! ### The graded ring of global sections -/

/-- **The global sections of the tensor powers form an `ℕ`-graded ring** under the
multiplication of sections. Beyond the graded monoid of
`Stacks.Monoidal.PowerSystem.gradedMonoid` this adds the two distributive laws, which are the
biadditivity of the tensor product. Unconditional: it is everything Tag 01CV asserts except
commutativity. -/
@[instance_reducible]
noncomputable def gradedRing :
    DirectSum.GRing (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := by
  let : GradedMonoid.GOne (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionOne⟩
  let : GradedMonoid.GMul (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionMul⟩
  exact { S.gradedMonoid with
    mul_zero := fun s => S.sectionMul_zero s
    zero_mul := fun t => S.zero_sectionMul t
    mul_add := fun s t t' => S.sectionMul_add s t t'
    add_mul := fun s s' t => S.add_sectionMul s s' t
    natCast := fun n => n • S.sectionOne
    natCast_zero := by simp
    natCast_succ := fun n => succ_nsmul _ _
    intCast := fun n => n • S.sectionOne
    intCast_ofNat := by simp
    intCast_negSucc_ofNat := by simp }

/-- **The graded ring of global sections is commutative**, *given* the commutativity constraint
of Tag 01CU for the multiplication isomorphisms. That constraint is not a formal consequence of
the symmetric monoidal axioms; see the implementation notes. -/
@[instance_reducible]
noncomputable def gradedCommRing [BraidedCategory C]
    (hβ : ∀ a b : ℕ, (β_ (S.obj a) (S.obj b)).hom ≫ (S.mulIso b a).hom
      = (S.mulIso a b).hom ≫ eqToHom (congrArg S.obj (Nat.add_comm a b))) :
    DirectSum.GCommRing (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := by
  let : GradedMonoid.GOne (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionOne⟩
  let : GradedMonoid.GMul (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionMul⟩
  exact { S.gradedRing with
    mul_comm := fun ⟨n, a⟩ ⟨m, b⟩ => Sigma.ext (add_comm n m)
      ((heq_of_eq (S.sectionMul_comm hβ a b)).trans (comp_eqToHom_heq _ _)) }

end PowerSystem

end Stacks.Monoidal

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.monoidalPreadditive Stacks.SheafOfModules.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]

/-- Reading the product of two morphisms out of the tensor unit as a global section gives the
product of global sections: the graded multiplication of `homGradedRing` is the multiplication
`Stacks.SheafOfModules.Invertible.sectionMul` of Tag 01CV. -/
theorem homToSection_sectionMul {a b : ℕ}
    (f : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
      ⟶ tensorPower O hO L (a : ℤ))
    (g : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
      ⟶ tensorPower O hO L (b : ℤ)) :
    homToSection O hO L ((tensorPowerSystem O hO L).sectionMul f g)
      = sectionMul O hO L (homToSection O hO L f) (homToSection O hO L g) := by
  rw [sectionMul, sectionToHom_homToSection, sectionToHom_homToSection]

/-- The same identification read the other way: the multiplication
`Stacks.SheafOfModules.Invertible.sectionMul` of Tag 01CV on `SheafOfModules.sections` is the
homogeneous multiplication of `homGradedRing`, which is `(tensorPowerSystem O hO L).sectionMul`
by definition. -/
theorem sectionToHom_sectionMul {a b : ℕ} (s : (tensorPower O hO L (a : ℤ)).sections)
    (t : (tensorPower O hO L (b : ℤ)).sections) :
    sectionToHom O hO L (sectionMul O hO L s t)
      = (tensorPowerSystem O hO L).sectionMul
          (sectionToHom O hO L s) (sectionToHom O hO L t) := by
  rw [sectionMul, sectionToHom_homToSection]

/-- **The global sections of the tensor powers of an invertible sheaf of modules form an
`ℕ`-graded ring**: all of Tag 01CV except commutativity. The summands are the morphisms out of
the tensor unit, which `SheafOfModules.unitHomEquiv` identifies with
`(tensorPower O hO L n).sections`; see the implementation notes for why the grading is indexed
that way. -/
@[instance_reducible,
  ega "II 4.5.1" "S graded ring",
  ega "III 2.1.1" "(2.1.1.1)",
  ega "II 2.6.1" "graded ring Γ_•(O_X)", ega "0 5.4.6" "graded ring Γ•(L)"]
noncomputable def homGradedRing :
    DirectSum.GRing (fun n : ℕ =>
      𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))
        ⟶ tensorPower O hO L (n : ℤ)) :=
  (tensorPowerSystem O hO L).gradedRing

/-- **The graded ring of global sections of the tensor powers of an invertible sheaf of modules
is commutative**, *given* the commutativity constraint of Tag 01CU for the multiplication
isomorphisms `tensorPowerMulIso`. -/
@[instance_reducible]
noncomputable def homGradedCommRing
    (hβ : ∀ a b : ℕ, (β_ (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ))).hom
        ≫ (tensorPowerMulIso O hO L b a).hom
      = (tensorPowerMulIso O hO L a b).hom
        ≫ eqToHom (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ)) (Nat.add_comm a b))) :
    DirectSum.GCommRing (fun n : ℕ =>
      𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))
        ⟶ tensorPower O hO L (n : ℤ)) :=
  (tensorPowerSystem O hO L).gradedCommRing hβ

end Stacks.SheafOfModules.Invertible

end

module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Integer
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Basic
public import StacksFrontier.AlgebraicGeometry.SelfBraidingInvertible.Basic

/-!
# The coherence of the multiplication on the tensor powers of an invertible sheaf of modules

`StacksFrontier/AlgebraicGeometry/TensorPowers/Basic.lean` defines the integer tensor powers
`AlgebraicGeometry.SheafOfModules.tensorPow` of an invertible sheaf of modules and their
addition law `AlgebraicGeometry.SheafOfModules.tensorPowAddIso`. Stacks Tag 01CU asserts the
commutativity and associativity constraints for that multiplication, omitting their
formulation.

This file proves them in nonnegative degree, by transport along
`Stacks.TensorPowers.TensorInverse.addIso_natCast`: the addition law is
`Stacks.GradedSections.powAddIso` there, and that family's coherence is
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/Basic.lean`. The constraints are stated
against the unitors, associator and braiding of the monoidal structure
`Stacks.SheafInternalHom.monoidalCategory` on sheaves of modules itself, which is the structure
`tensorPow` is defined in, so no auxiliary choice of constraint enters.

## Main results

* `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_natCast`: in nonnegative degree the addition
  law is `Stacks.GradedSections.powAddIso`. This is the single transport every other result here
  goes through.
* `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_assoc_natCast`: **the associativity
  constraint.**
* `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_right_natCast` and
  `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_left_natCast`: the two unit
  constraints, namely that multiplication by `L ^⊗ 0` is the right, respectively left, unitor.
* `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_one_right_natCast`: **the normalisation.**
  Multiplication by `L ^⊗ 1` is `tensorPowOneIso` whiskered in, which identifies the
  multiplication with one more step of the iteration defining the powers and so leaves no
  cocycle ambiguity.
* `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_comm_natCast`: **the commutativity
  constraint.**
* `AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf_natCast`: the same transport for the
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling of the addition law, the one
  whose statement needs no monoidal instance in scope.

## Implementation notes

**Everything is `exact`, not `rw`.** `tensorPow 𝒪 h𝒪 L (a : ℤ)` and
`Stacks.TensorPowers.natTensorPow L a` are the same term by `rfl`
(`AlgebraicGeometry.SheafOfModules.tensorPow_natCast`), and `tensorPowAddIso` is
`Stacks.TensorPowers.TensorInverse.addIso` of the chosen inverse by `rfl`. So each statement
here is definitionally the corresponding statement of the sibling file, and `exact` discharges
it; the spellings differ only for the reader's benefit. Writing them with `rw` would fail on
exactly those spellings, which is the hazard the sibling file documents.

**The monoidal and braided structures are local instances**, as in
`StacksFrontier/AlgebraicGeometry/TensorPowers/Basic.lean` and for the reason given there: they
are `def`s so that they cannot collide with a structure deduced from chosen finite products.
Consumers of any statement here mentioning `⊗`, `α_`, `λ_`, `ρ_` or `β_` need them in scope.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## Remarks

Negative degrees are not treated. The commutativity constraint has one mathematical input beyond
the transport: the braiding of `L` with itself is the identity
(`Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding`). This holds for an invertible sheaf of
modules but is not a formal consequence of the symmetric monoidal axioms: the odd line in super
vector spaces is invertible with self-braiding `-𝟙`.
-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory BraidedCategory Stacks.SheafOfModules.TensorSheafification
  Stacks.TensorPowers
open Stacks.GradedSections

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- The transport of a tensor power along an equality of nonnegative degrees. -/
noncomputable abbrev tensorPowNatCongrIso {a b : ℕ} (hab : a = b) :
    tensorPow 𝒪 h𝒪 L (a : ℤ) ≅ tensorPow 𝒪 h𝒪 L (b : ℤ) :=
  powCongrIso L hab

/-- **In nonnegative degree the addition law on tensor powers is
`Stacks.GradedSections.powAddIso`**, whose coherence is proved in
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/Basic.lean`. Every constraint below is this
transport followed by the corresponding law there. -/
theorem tensorPowAddIso_natCast (a b : ℕ) :
    tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) (b : ℤ) = powAddIso L a b :=
  TensorInverse.addIso_natCast _ a b

/-- The right unit constraint: multiplication by `L ^⊗ 0` on the right is the right unitor. -/
@[stacks 01CU "canonical multiplication and coherence"]
theorem tensorPowAddIso_zero_right_natCast (a : ℕ) :
    tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) ((0 : ℕ) : ℤ) = ρ_ (tensorPow 𝒪 h𝒪 L (a : ℤ)) :=
  TensorInverse.addIso_zero_right_natCast _ a

/-- The left unit constraint: multiplication by `L ^⊗ 0` on the left is the left unitor. -/
@[stacks 01CU "canonical multiplication and coherence"]
theorem tensorPowAddIso_zero_left_natCast (b : ℕ) :
    tensorPowAddIso 𝒪 h𝒪 L ((0 : ℕ) : ℤ) (b : ℤ) ≪≫
        tensorPowNatCongrIso 𝒪 h𝒪 L (Nat.zero_add b) =
      λ_ (tensorPow 𝒪 h𝒪 L (b : ℤ)) :=
  TensorInverse.addIso_zero_left_natCast _ b

/-- **The normalisation in degree one.** Multiplication by the first tensor power is
`AlgebraicGeometry.SheafOfModules.tensorPowOneIso` whiskered into `L ^⊗ a`, followed by the
successor step `L ^⊗ a ⊗ L = L ^⊗ (a + 1)` of the iteration which defines the powers; in
nonnegative degree that step is the identity. This is what pins the canonical multiplication
down: an associative family of multiplication isomorphisms is determined by its degree-`(a, 1)`
value. -/
@[stacks 01CU "canonical multiplication and coherence"]
theorem tensorPowAddIso_one_right_natCast (a : ℕ) :
    tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) ((1 : ℕ) : ℤ) =
      whiskerLeftIso (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPowOneIso 𝒪 h𝒪 L) :=
  TensorInverse.addIso_one_right_natCast _ a

/-- **The associativity constraint on the multiplication of tensor powers**, which Stacks Tag
01CU asserts with the formulation omitted, in nonnegative degree and against the associator of
the monoidal structure on sheaves of modules itself. -/
@[stacks 01CU "canonical multiplication and coherence"]
theorem tensorPowAddIso_assoc_natCast (a b c : ℕ) :
    whiskerRightIso (tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) (b : ℤ)) (tensorPow 𝒪 h𝒪 L (c : ℤ)) ≪≫
        tensorPowAddIso 𝒪 h𝒪 L ((a + b : ℕ) : ℤ) (c : ℤ) =
      α_ (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPow 𝒪 h𝒪 L (b : ℤ)) (tensorPow 𝒪 h𝒪 L (c : ℤ)) ≪≫
        whiskerLeftIso (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPowAddIso 𝒪 h𝒪 L (b : ℤ) (c : ℤ)) ≪≫
          tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) ((b + c : ℕ) : ℤ) ≪≫
            tensorPowNatCongrIso 𝒪 h𝒪 L (Nat.add_assoc a b c).symm :=
  TensorInverse.addIso_assoc_natCast _ a b c

/-- **The commutativity constraint on the multiplication of tensor powers**, in nonnegative
degree.

At degrees `(1, 1)` the constraint *is* the triviality of the self-braiding of `L`, which holds
for every invertible `L` by the instance `Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding`. -/
@[stacks 01CU "canonical multiplication and coherence"]
theorem tensorPowAddIso_comm_natCast (a b : ℕ) :
    β_ (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPow 𝒪 h𝒪 L (b : ℤ)) ≪≫
        tensorPowAddIso 𝒪 h𝒪 L (b : ℤ) (a : ℤ) =
      tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) (b : ℤ) ≪≫
        tensorPowNatCongrIso 𝒪 h𝒪 L (Nat.add_comm a b) :=
  TensorInverse.addIso_comm_natCast _ a b

/-- The transport for the `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling of the
addition law, the one whose statement needs no monoidal instance in scope. -/
theorem tensorPowAddIsoSheaf_natCast (a b : ℕ) :
    tensorPowAddIsoSheaf 𝒪 h𝒪 L (a : ℤ) (b : ℤ) =
      (tensorIso 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPow 𝒪 h𝒪 L (b : ℤ))).symm ≪≫
        powAddIso L a b := by
  show (tensorIso 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPow 𝒪 h𝒪 L (b : ℤ))).symm ≪≫
    tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) (b : ℤ) = _
  rw [tensorPowAddIso_natCast]
  rfl

end AlgebraicGeometry.SheafOfModules

end

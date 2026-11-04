module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The multiplication of an invertible sheaf against its inverse tensor power

Let `L` be an invertible sheaf of modules on a site with a sheaf of rings. The integer tensor
powers `L^{⊗ n}` of [Stacks, Tag 01CU] carry a coherent multiplication
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}`, and that coherent structure is *not* available in this
development: Tag 01CU's `TensorPowerCoherence` is not proved in this development, and
the multiplication that is available
(`Stacks.SheafOfModules.Invertible.tensorPowerMulIso` of
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean`) is indexed by **natural** numbers
only.

This file supplies the one pair of *negative* exponents that the Picard-group arguments of
Chapter 33 need, `(1, -1)`, and supplies it unconditionally — no coherence structure, no
sorried input:

`L^{⊗ 1} ⊗ L^{⊗ -1} ≅ 𝒪`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorPowerMulIsoNegOne`: the multiplication isomorphism at
  the exponent pair `(1, -1)`.
* `Stacks.SheafOfModules.Invertible.sectionMulNegOne`: its value on a pair of sections over an
  object of the site — the product of a section of `L` and a section of `L^{⊗ -1}`, a section of
  the structure sheaf.
* `Stacks.SheafOfModules.Invertible.globalSectionsMulNegOne`: the same on global sections
  of a scheme.

## Implementation notes

**Why this needs no coherence, and why it is nevertheless the coherent multiplication.** The
iso is the composite

`L^{⊗ 1} ⊗ L^{⊗ -1} ≅ L^{⊗ -1} ⊗ L^{⊗ 1} ≅ L^{⊗ -1} ⊗ L ≅ L^{⊗ (-1 + 1)} = L^{⊗ 0} = 𝒪`,

whose three steps are the braiding of the sheaf tensor product
(`Stacks.SheafOfModules.Invertible.tensorProductBraiding`), the identification of the first
tensor power with `L` (`tensorPowerOneIso`), and one step of the defining integer iteration
(`tensorPowerSuccIso` at `n = -1`). All three are proved, and the last is where
the negative exponent is absorbed: `tensorPowerSuccIso` is stated for every `n : ℤ`, the
negative part of the iteration using the counit of the tensoring autoequivalence.

That composite is not merely *a* trivializing pairing, it is *the* multiplication: Tag 01CU's
coherence structure pins `mulIso 1 (-1)` down to exactly this composite by two of its own
fields, with no freedom left. `mul_comm 1 (-1)` says
`mulIso 1 (-1) = braiding ≪≫ mulIso (-1) 1 ≪≫ reindex`, and `mul_one_right (-1)` says
`mulIso (-1) 1 = tensorProductIso (Iso.refl _) tensorPowerOneIso ≪≫ tensorPowerSuccIso L (-1)`.
Substituting the second into the first gives the definition below. So a statement written with
`tensorPowerMulIsoNegOne` asserts what a statement written with the coherent `mulIso 1 (-1)`
asserts; it does not weaken it to an unspecified isomorphism.

**What this unblocks.** [Stacks, Tag 0CDX] asserts that the canonical multiplication
`H⁰(X, L) ⊗_{H⁰(X, 𝒪_X)} H⁰(X, L^{⊗ -1}) ⟶ H⁰(X, 𝒪_X)` is an isomorphism, and its statement is
therefore unwritable without a name for that multiplication at the exponent pair `(1, -1)`.
`globalSectionsMulNegOne` is that name, in the spelling the Chapter 33 decomposition uses
(sheafification unit applied to a pure tensor, then the multiplication isomorphism). Tag 0CDY
consumes the same multiplication, through the unit `s t ∈ H⁰(X, 𝒪_X)`.

The remaining input Tag 0CDX needs is unrelated to this file and is recorded in
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/Basic.lean`: degree-zero flat base change
for a *quasi-coherent module*, `Γ(X, L) ⊗_A B ≅ Γ(X_B, L_B)`.

**Which `IsInvertible`.** `AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`, which is the class the whole Tag 01CU
tensor-power development is stated in. The repository also carries
`Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, with the same body;
nothing here identifies the two.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 0CDY](https://stacks.math.columbia.edu/tag/0CDY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The multiplication isomorphism `L^{⊗ 1} ⊗ L^{⊗ -1} ≅ 𝒪`** of Tag 01CU, at the one pair of
exponents with a negative member that the Picard-group arguments need, and built without the
coherence structure Tag 01CU leaves unproved.

The composite is the braiding, the identification `L^{⊗ 1} ≅ L`, and one step of the integer
iteration. Tag 01CU's own `mul_comm` and `mul_one_right` fields force the coherent
multiplication at `(1, -1)` to be this composite; see the implementation notes. -/
@[ega "0 5.4.4" "opposite-power case (1"]
def tensorPowerMulIsoNegOne (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((tensorPower O hO L 1))).obj ((tensorPower O hO L (-1)))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  tensorProductBraiding O hO _ _ ≪≫
    tensorProductIso O hO (Iso.refl (tensorPower O hO L (-1))) (tensorPowerOneIso O hO L) ≪≫
    tensorPowerSuccIso O hO L (-1) ≪≫
    tensorPowerReindex O hO L (by ring : (-1 : ℤ) + 1 = 0)

/-- **The product of a section of `L` and a section of `L^{⊗ -1}`**, a section of the structure
sheaf over the same object of the site.

The pure tensor of the two sections is a section of the *presheaf* tensor product; the
sheafification unit carries it into `L^{⊗ 1} ⊗ L^{⊗ -1}`, where `tensorPowerMulIsoNegOne`
evaluates it. Specifying the multiplication this way, rather than as some isomorphism of
modules, is what makes a statement about it a statement about multiplication. -/
def sectionMulNegOne (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (U : Cᵒᵖ)
    (s : L.val.obj U) (t : (tensorPower O hO L (-1)).val.obj U) :
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val.obj U
      :=
  ((tensorPowerMulIsoNegOne O hO L).hom.val.app U).hom
    (((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
      ((PresheafOfModules.tensorObj (O := O) ((tensorPower O hO L 1).val)
        ((tensorPower O hO L (-1)).val)))).app U).hom
      ((((tensorPowerOneIso O hO L).inv.val.app U).hom s) ⊗ₜ t))

/-- The product of a global section of an invertible module sheaf on a scheme and a global
section of its inverse tensor power, a global function. This is the shape in which Tag 0CDX
states its multiplication clause. -/
def globalSectionsMulNegOne {X : AlgebraicGeometry.Scheme.{w}} (L : X.Modules)
    [IsInvertible X.presheaf X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    (t : (tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤)) :
    Γ(X, ⊤) :=
  sectionMulNegOne X.presheaf X.ringCatSheaf.property L (.op ⊤) s t

end Stacks.SheafOfModules.Invertible

end

module

public import StacksFrontier.AlgebraicGeometry.TensorPowers.Basic

/-!
# The canonical pairing of an invertible module with its inverse

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and `L` an invertible sheaf of
`𝒪`-modules. Stacks Tag 01CY, in its "inverse section" clause, pairs a section of `L` with a
section of `L ^⊗ (-1)` and asks that the result be `1`. The pairing it uses is the degree
`(1, -1)` case of the addition isomorphism of Stacks Tag 01CU, read in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling and valued in the sections of the structure
sheaf. This file assembles that pairing as a single isomorphism, together with the reindexing
isomorphism it is built from.

## Main definitions

* `Stacks.InverseSection.tensorPowReindexIso`: transport of a tensor power along an equality of
  exponents; the form of `Stacks.TensorPowers.reindex` for
  `AlgebraicGeometry.SheafOfModules.tensorPow`, which needs only the category structure.
* `Stacks.InverseSection.tensorPowPairingIso`: the canonical pairing, an isomorphism
  `L ^⊗ 1 ⊗ L ^⊗ (-1) ≅ 𝒪`, with the tensor product spelled by
  `Stacks.SheafOfModules.Tensor.sheafTensor` and the structure sheaf by `SheafOfModules.unit`.

## Implementation notes

The three factors of `tensorPowPairingIso` are the addition law
`AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf` in degrees `1` and `-1`, the reindexing
along `1 + (-1) = 0`, and `AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`. The last is
needed because the zeroth tensor power is the monoidal unit of
`Stacks.SheafInternalHom.monoidalCategory`, which is the *sheafified* unit and not
`SheafOfModules.unit`. The statement of every declaration here is free of `⊗` and `𝟙_`, so no
monoidal instance is needed to use them; this is why `tensorPowAddIsoSheaf` is used rather than
`tensorPowAddIso`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u w

open CategoryTheory Opposite Stacks.SheafOfModules.TensorSheafification
open AlgebraicGeometry.SheafOfModules (IsInvertible)

namespace Stacks.InverseSection

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

open AlgebraicGeometry.SheafOfModules

/-- Equal exponents give equal tensor powers, hence an isomorphism between them. -/
@[reducible] noncomputable def tensorPowReindexIso {n m : ℤ} (h : n = m) :
    tensorPow 𝒪 h𝒪 L n ≅ tensorPow 𝒪 h𝒪 L m :=
  eqToIso (by rw [h])

/-- The canonical pairing of an invertible sheaf of modules with its inverse: the tensor product
of the first and the `(-1)`-st tensor powers is isomorphic to the structure sheaf, via the
addition law in degrees `1` and `-1`, the reindexing along `1 + (-1) = 0`, and the
identification of the zeroth power with `SheafOfModules.unit`. -/
noncomputable def tensorPowPairingIso :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        ((tensorPow 𝒪 h𝒪 L 1))).obj ((tensorPow 𝒪 h𝒪 L (-1)))) ≅
      SheafOfModules.unit (structureSheaf 𝒪 h𝒪) :=
  tensorPowAddIsoSheaf 𝒪 h𝒪 L 1 (-1) ≪≫
    tensorPowReindexIso 𝒪 h𝒪 L (show (1 : ℤ) + -1 = 0 by omega) ≪≫ tensorPowZeroIso 𝒪 h𝒪 L

end Site

end Stacks.InverseSection

end

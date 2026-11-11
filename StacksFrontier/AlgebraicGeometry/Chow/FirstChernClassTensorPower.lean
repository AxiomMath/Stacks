module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries

/-!
# The first Chern class of a tensor power

[Stacks, Tag 02SP] gives additivity of the cap product with the first Chern class in the
invertible module, `c₁(ℒ) ∩ α + c₁(𝒩) ∩ α = c₁(ℒ ⊗ 𝒩) ∩ α`, and its vanishing on the structure
sheaf. Iterating the first along the second is the statement that a tensor power multiplies the
first Chern class:

  `c₁(ℒ^{⊗ m}) ∩ α = m • (c₁(ℒ) ∩ α)`.

This file proves it, for both of the two library spellings of the tensor powers of an invertible
module on a scheme: `AlgebraicGeometry.tensorPowSucc`, the iterated tensor product of
[Stacks, Tag 01CA], and `Stacks.Ample.tensorPowModule`, the `ℤ`-indexed family of
[Stacks, Tag 01CU] the ampleness theory is written against.

## Main results

* `Stacks.Chow.firstChernClassCapOfInvertible_tensorPowSucc`: the identity for
  `AlgebraicGeometry.tensorPowSucc`, by induction on the exponent.
* `Stacks.Chow.firstChernClassCapOfInvertible_tensorPowModule`: the identity for
  `Stacks.Ample.tensorPowModule` in nonnegative degree.
* `Stacks.Chow.firstChernClassCapFundamental_tensorPowModule`: the identity for the Weil divisor
  class `c₁(ℒ) ∩ [X]` of [Stacks, Tag 02SJ] (2) on an integral scheme.

## Implementation notes

The induction is run on `AlgebraicGeometry.tensorPowSucc` because there the recursion is the
tensor product on the nose — `tensorPowSucc L (m + 1)` is literally `tensorPowSucc L m ⊗ L` in
the spelling `AlgebraicGeometry.Scheme.Modules.tensorObj` that [Stacks, Tag 02SP] is stated in —
so the step is one rewrite with no comparison isomorphism. The result is then carried to
`Stacks.Ample.tensorPowModule` by `AlgebraicGeometry.tensorPowSuccIsoTensorPowModule` and the
isomorphism invariance of the cap product; the two families are not definitionally equal, since
the ampleness theory's tensor product is a sheafification that does not reduce to `tensorSheaf`.

Everything is stated at the cycle level, against `Stacks.Chow.firstChernClassCapOfInvertible`
rather than the descended operation `Stacks.Chow.firstChernClassCapOnChow` of
[Stacks, Tag 02TI]: the identity holds already on cycles and needs no factorisation through
rational equivalence.

No `@[stacks 02SP]` attribute is carried here. The tag's two assertions are the additivity and
the vanishing, both proved in
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor`; the tensor-power identity is a
consequence of them, not a further clause of the tag.

## References

* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The cap product with the first Chern class of a tensor power is a multiple of the cap
product with the first Chern class**: `c₁(ℒ^{⊗ m}) ∩ α = m • (c₁(ℒ) ∩ α)` in `A_k(X)`, for the
tensor powers `AlgebraicGeometry.tensorPowSucc` of [Stacks, Tag 01CA].

Induction on `m`. The zeroth power is `𝒪_X`, whose cap product vanishes
(`Stacks.Chow.firstChernClassCapOfInvertible_unit`); the step is
`tensorPowSucc L (m + 1) = tensorPowSucc L m ⊗ ℒ` and the additivity of [Stacks, Tag 02SP]. -/
theorem firstChernClassCapOfInvertible_tensorPowSucc (m : ℕ) (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k (tensorPowSucc L m) α =
      m • firstChernClassCapOfInvertible C p k L α := by
  induction m with
  | zero =>
    rw [zero_nsmul]
    exact firstChernClassCapOfInvertible_unit C p k α
  | succ m ih =>
    have h := firstChernClassCapOfInvertible_tensorObj C p k (tensorPowSucc L m) L α
    rw [ih] at h
    rw [succ_nsmul]
    exact h.symm

/-- **The tensor powers of the ampleness theory are invertible in the spelling of chapter 42.**
`Stacks.Ample.isInvertibleModule_tensorPowModule` is the same statement with the structure
presheaf and its sheaf condition supplied as `X.presheaf` and
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X` rather than as `X.sheaf.obj` and
`X.ringCatSheaf.property`; the two are definitionally equal, but instance search does not cross
between them. -/
instance isInvertible_tensorPowModule [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule X L n) :=
  Stacks.Ample.isInvertibleModule_tensorPowModule X L n

/-- **The cap product with the first Chern class of a tensor power is a multiple of the cap
product with the first Chern class**, for the `ℤ`-indexed tensor powers
`Stacks.Ample.tensorPowModule` of [Stacks, Tag 01CU] in nonnegative degree:
`c₁(ℒ^{⊗ m}) ∩ α = m • (c₁(ℒ) ∩ α)` in `A_k(X)`. -/
theorem firstChernClassCapOfInvertible_tensorPowModule
    [Stacks.Ample.IsInvertibleModule X L] (m : ℕ) (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k (Stacks.Ample.tensorPowModule X L (m : ℤ)) α =
      m • firstChernClassCapOfInvertible C p k L α :=
  (firstChernClassCapOfInvertible_congr C p k (tensorPowSucc L m)
        (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (tensorPowSuccIsoTensorPowModule L m) α).symm.trans
    (firstChernClassCapOfInvertible_tensorPowSucc C p k L m α)

/-! ### The Weil divisor class of a tensor power -/

/-- **The Weil divisor class of a tensor power is a multiple of the Weil divisor class**:
`c₁(ℒ^{⊗ m}) ∩ [X] = m • (c₁(ℒ) ∩ [X])` in `CH_{n-1}(X)`, for `X` integral of delta-dimension
`n` locally of finite type over the base.

This is the form the divisibility arguments of chapter 45 use. Since
`Stacks.Chow.firstChernClassCapFundamental` is defined by a choice of regular meromorphic
section, the comparison runs through
`Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental`,
which identifies it with the cap product of [Stacks, Tag 02SO] at the fundamental cycle. -/
theorem firstChernClassCapFundamental_tensorPowModule [IsIntegral X] (d : ℤ)
    (hd : schemeDeltaDimension C p = (d : EInt)) [Stacks.Ample.IsInvertibleModule X L] (m : ℕ) :
    firstChernClassCapFundamental C p d hd (Stacks.Ample.tensorPowModule X L (m : ℤ)) =
      m • firstChernClassCapFundamental C p d hd L :=
  (firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental C p d hd
        (Stacks.Ample.tensorPowModule X L (m : ℤ))).symm.trans
    ((firstChernClassCapOfInvertible_tensorPowModule C p (d - 1) L m _).trans
      (congrArg (fun c => m • c)
        (firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental
          C p d hd L)))

end Stacks.Chow

end

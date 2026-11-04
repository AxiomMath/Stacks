module

public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.GeometricallyReduced.Separable
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct

/-!
# Separability of a field extension in a tower with separable algebraic top step

Separability of a possibly transcendental field extension is `Algebra.IsSeparableExtension`, the
notion of Stacks 030O(2). This file records the three facts about it that a tower
`k ⊆ κ ⊆ L` with `L/κ` separable algebraic needs, none of which is in the library: that a
separable algebraic extension is separable in this sense, that separability is inherited by `L/k`
from `κ/k`, and that it transports along an isomorphism of `k`-extensions.

All three go through geometric reducedness, which is the pivot `Algebra.isSeparableExtension_tfae`
(Stacks 030W) provides: `K/k` is separable exactly when `K ⊗_k \bar k` is reduced. The transitivity
is then the computation
`L ⊗_k \bar k = L ⊗_κ (κ ⊗_k \bar k)`
(`Algebra.TensorProduct.cancelBaseChange`) combined with Stacks 030U
(`Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated`) applied twice:
once over `k` to see that `κ ⊗_k \bar k` is a reduced `κ`-algebra, and once over `κ` to see that
tensoring that with the separable extension `L` stays reduced.

## Main definitions

There are no definitions.

## Main results

* `Algebra.IsSeparableExtension.of_isSeparable` — a separable algebraic extension is separable.
* `Algebra.IsSeparableExtension.trans_of_isSeparable` — separability of `κ/k` and separable
  algebraicity of `L/κ` give separability of `L/k`.
* `Algebra.IsSeparableExtension.of_algEquiv` — separability transports along an isomorphism of
  extensions.

## Implementation notes

These are general statements about field extensions, with no reference to curves; their natural
home is `StacksFrontier/FieldTheory/Separable/`, and they are kept here only because that directory
is being edited concurrently.

No `@[stacks]` tag is carried here; the tagged statement of the characterization these rest on is
`Algebra.isSeparableExtension_tfae` (Stacks 030W).

## References

* [Stacks Project, Tag 030O](https://stacks.math.columbia.edu/tag/030O)
* [Stacks Project, Tag 030U](https://stacks.math.columbia.edu/tag/030U)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.IsSeparableExtension

/-- A geometrically reduced field extension is separable (Stacks 030W, `(4) ⇒ (1)`). -/
private theorem of_isGeometricallyReduced (k L : Type*) [Field k] [Field L] [Algebra k L]
    [Algebra.IsGeometricallyReduced k L] : Algebra.IsSeparableExtension k L :=
  ((Algebra.isSeparableExtension_tfae k L (ringExpChar k)).out 4 1).mp ‹_›

/-- **A separable algebraic field extension is separable** in the sense of Stacks 030O(2). Such
an extension is geometrically reduced, which is one of the equivalent conditions. -/
public theorem of_isSeparable (k L : Type*) [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] : Algebra.IsSeparableExtension k L := by
  have : Algebra.IsGeometricallyReduced k L := .of_isSeparable k L
  exact of_isGeometricallyReduced k L

/-- **Separability of a field extension passes through a separable algebraic step.** If `κ/k` is
separable and `L/κ` is separable algebraic, then `L/k` is separable. The base change
`L ⊗_k \bar k` is `L ⊗_κ (κ ⊗_k \bar k)`, a separable extension of `κ` tensored with a reduced
`κ`-algebra, hence reduced. -/
public theorem trans_of_isSeparable (k κ L : Type*) [Field k] [Field κ] [Field L] [Algebra k κ]
    [Algebra κ L] [Algebra k L] [IsScalarTower k κ L] [Algebra.IsSeparableExtension k κ]
    [Algebra.IsSeparable κ L] : Algebra.IsSeparableExtension k L := by
  have hbase : IsReduced (κ ⊗[k] AlgebraicClosure k) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated (.inl ‹_›)
  have htop : IsReduced (L ⊗[κ] (κ ⊗[k] AlgebraicClosure k)) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
      (.inl (of_isSeparable κ L))
  have e : (L ⊗[κ] (κ ⊗[k] AlgebraicClosure k)) ≃+* (AlgebraicClosure k ⊗[k] L) :=
    (Algebra.TensorProduct.cancelBaseChange k κ L L (AlgebraicClosure k)).toRingEquiv.trans
      (Algebra.TensorProduct.comm k L (AlgebraicClosure k)).toRingEquiv
  have : IsReduced (AlgebraicClosure k ⊗[k] L) :=
    isReduced_of_injective e.symm.toRingHom e.symm.injective
  have : Algebra.IsGeometricallyReduced k L :=
    (Algebra.isGeometricallyReduced_field_iff k L).mpr ‹_›
  exact of_isGeometricallyReduced k L

/-- **Separability of a field extension transports along an isomorphism of extensions.** -/
public theorem of_algEquiv {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [Algebra.IsSeparableExtension k K] (e : K ≃ₐ[k] L) :
    Algebra.IsSeparableExtension k L := by
  have hK : Algebra.IsGeometricallyReduced k K :=
    ((Algebra.isSeparableExtension_tfae k K (ringExpChar k)).out 1 4).mp ‹_›
  have : Algebra.IsGeometricallyReduced k L :=
    .of_injective e.symm.toAlgHom e.symm.injective
  exact of_isGeometricallyReduced k L

end Algebra.IsSeparableExtension

end

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Tensoring with `ℤ/2` does not preserve injectivity

Multiplication by `2` is an injective map of `ℤ`-modules `ℤ → ℤ`. After tensoring it with
`N = ℤ/2` the resulting map `ℤ ⊗[ℤ] ℤ/2 → ℤ ⊗[ℤ] ℤ/2` is the zero map, because on a pure tensor
`(2 ⊗ 1)(x ⊗ y) = 2x ⊗ y = x ⊗ 2y = x ⊗ 0 = 0`, while `ℤ ⊗[ℤ] ℤ/2` is not the zero module. So the
induced map is not injective: the functor `- ⊗[ℤ] ℤ/2`, right exact by Lemma 00DG, is not left
exact, which is Remark 00DH, and `ℤ/2` is not a flat `ℤ`-module in the sense of Remark 00DJ.

This is Example 00DI, the standard witness that tensoring does not preserve exactness.

## Main results

* `TensorProduct.not_injective_rTensor_zmod_two_lsmul_two`: multiplication by `2` on `ℤ` is
  injective, its tensor product with the identity of `ℤ/2` is the zero map, and that map is
  therefore not injective.

## Implementation notes

Multiplication by `2` is spelled `LinearMap.lsmul ℤ ℤ 2`, Mathlib's name for the `R`-linear map
`x ↦ r • x`, and the map it induces is `LinearMap.rTensor (ZMod 2)`, Mathlib's `f ⊗ id` on
`- ⊗[ℤ] ℤ/2`, characterised on pure tensors by `LinearMap.rTensor_tmul`; this is the source's
`2 ⊗ 1` and not merely a map of the same shape.

The vanishing is supplied by the private helper `rTensor_lsmul_eq_zero`, which records the
displayed computation at exactly the generality it uses: over a commutative semiring `R`, if
`r : R` annihilates `N`, then multiplication by `r` on an arbitrary `M` becomes the zero map
`M ⊗[R] N → M ⊗[R] N`. Equivalently, `r` annihilates `M ⊗[R] N`; Mathlib carries neither form. The
example is the case `R = M = ℤ`, `r = 2`, `N = ℤ/2`, where `2` annihilates `ℤ/2` because `ℤ/2` has
characteristic `2`. Injectivity of multiplication by `2` on `ℤ` is `LinearMap.lsmul_injective`, `ℤ`
being torsion-free, and non-injectivity of the induced map is `LinearMap.ne_zero_of_injective` read
contrapositively.

The source's two intermediate assertions are both recorded, and both are stronger than the bare
failure of injectivity: that the induced map *vanishes*, and — the remaining ingredient, which is
`inferInstance` here rather than a conjunct — that `Nontrivial (ℤ ⊗[ℤ] ZMod 2)`. Non-injectivity is
kept as a conjunct even though it follows from those two, because it is the assertion the tag
makes.

*The general mechanism is deliberately not what is stated.* For a commutative ring `R` and `r : R`
which is a non-zerodivisor and not a unit, `LinearMap.lsmul R R r` is injective while its tensor
product with the identity of `R ⧸ Ideal.span {r}` vanishes on a nonzero module, by the same
computation. That generalisation has hypotheses, and an example whose content is that the
phenomenon *occurs* is not witnessed by a conditional statement; the concrete instance `R = ℤ`,
`r = 2` is the mathematics of this tag. The general form is the natural companion lemma for
Remark 00DJ, where non-flatness, not a witness, is the subject.

Faithfulness to [StacksProject 00DI]. (1) There is no hypothesis at all, hence no dead one: the
statement is closed, about the source's `ℤ`, `2` and `ℤ/2`. (2) The scalars and base are the
source's: `ℤ` is the base of both tensor products, the map tensored is `ℤ`-linear, and `ℤ/2` is
viewed as a `ℤ`-module, not as a ring changing the base. (3) The canonical map the source names is
pinned rather than asserted to exist: it is `(LinearMap.lsmul ℤ ℤ 2).rTensor (ZMod 2)`, whose
values on pure tensors are the source's, and the second conjunct pins its value, `0`. (4) The
instantiation is not degenerate: `ℤ ⊗[ℤ] ZMod 2` is nontrivial (it is `ZMod 2` up to
`TensorProduct.lid`), so the vanishing of the induced map is a genuine failure of injectivity, and
the map tensored is injective by the first conjunct, so the failure is created by tensoring.

## References

* [StacksProject 00DI](https://stacks.math.columbia.edu/tag/00DI)
-/

@[expose] public section

open TensorProduct

/-- A scalar annihilating `N` kills multiplication by it after tensoring with `N`: on a pure
tensor, `(r • x) ⊗ y = x ⊗ (r • y) = x ⊗ 0 = 0`. -/
private theorem rTensor_lsmul_eq_zero {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {r : R} (h : Module.IsTorsionBy R N r) :
    (LinearMap.lsmul R M r).rTensor N = 0 :=
  TensorProduct.ext' fun x y => by simp [TensorProduct.smul_tmul, h]

/-- **Stacks 00DI**.
Multiplication by `2` is an injective map of `ℤ`-modules `ℤ → ℤ`, but the induced map
`ℤ ⊗[ℤ] ℤ/2 → ℤ ⊗[ℤ] ℤ/2` is the zero map and hence not injective, `ℤ ⊗[ℤ] ℤ/2` being nonzero.
So tensoring does not preserve injectivity. -/
@[stacks 00DI]
public theorem TensorProduct.not_injective_rTensor_zmod_two_lsmul_two :
    Function.Injective (LinearMap.lsmul ℤ ℤ (2 : ℤ)) ∧
      (LinearMap.lsmul ℤ ℤ (2 : ℤ)).rTensor (ZMod 2) = 0 ∧
      ¬ Function.Injective ((LinearMap.lsmul ℤ ℤ (2 : ℤ)).rTensor (ZMod 2)) :=
  have hzero := rTensor_lsmul_eq_zero (M := ℤ) (N := ZMod 2) fun {_} => by
    rw [zsmul_eq_mul, (CharP.intCast_eq_zero_iff (ZMod 2) 2 2).2 dvd_rfl, zero_mul]
  ⟨LinearMap.lsmul_injective two_ne_zero, hzero, fun h => LinearMap.ne_zero_of_injective h hzero⟩

end

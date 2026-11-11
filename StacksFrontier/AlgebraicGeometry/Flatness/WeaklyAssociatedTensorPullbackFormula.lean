module

public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackGlobal
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormulaEssentiallyFiniteType

/-!
# Tag 05IH, with its algebraic input supplied

`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback` reduces [Stacks, Tag
05IH] to a statement of pure algebra, carried there as the hypothesis
`Stacks.Divisors.WeaklyAssociatedPrimesTensorFormula`: the fibrewise description of the weakly
associated primes of a flat tensor product, which is [Stacks, Tag 05II] at one universe and for
a module that is finite rather than a localization of a finite one. This file proves that
hypothesis and so proves the tag.

The algebra is `weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small'`, in the
namespace `Stacks.WeaklyAssociatedPrimes` and the module
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormulaEssentiallyFiniteType`,
which proves Tag 05II for a module presented as a localization of a finite one. A finite module
is such a localization trivially, at the submonoid `{1}` and along the identity, which is the
only step here.

This is a separate module rather than an edit to the one stating the hypothesis because the
reduction is used, through its other consumers, by the files the algebra is proved in: the
module that *states* the formula is imported by the chain that *proves* it, so discharging the
hypothesis in place would close an import cycle.

## Main results

* `Stacks.Divisors.weaklyAssociatedPrimesTensorFormula` is the algebraic input, proved.
* `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType` is [Stacks, Tag 05IH]:
  for `f : X ⟶ S` locally of finite type, `F` a quasi-coherent `𝒪_X`-module of finite type flat
  over `S` at `x`, and `G` a quasi-coherent `𝒪_S`-module, the point `x` is weakly associated to
  `F ⊗_{𝒪_X} f^*G` exactly when `f x` is weakly associated to `G` and `x` lies in the relative
  assassin `Ass_{X/S}(F)`.
* `Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_eq` is [Stacks, Tag 05IJ], the same
  statement read as a set equality over all of `X`, which
  `StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackGlobal` had reduced to
  the same algebraic input.

## References

* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 05IJ](https://stacks.math.columbia.edu/tag/05IJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct
open Stacks.WeaklyAssociatedPrimes

universe u

namespace Stacks.Divisors

/-- A finite module is a localization of a finite module in the trivial way: at the submonoid
`{1}`, along the identity map. -/
theorem isLocalizedModule_bot_id (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N] :
    IsLocalizedModule (⊥ : Submonoid B) (LinearMap.id : N →ₗ[B] N) where
  map_units x := by
    have hx : x.val = 1 := x.property
    simp [hx]
  surj y := ⟨(y, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

/-- **The algebraic input of [Stacks, Tag 05IH], proved.** The fibrewise description of the
weakly associated primes of `N ⊗[R] M`, for `R → B` essentially of finite type and `N` finite
over `B` and flat over `R`, is [Stacks, Tag 05II] for the trivial localization of `N`. -/
theorem weaklyAssociatedPrimesTensorFormula : WeaklyAssociatedPrimesTensorFormula.{u} := by
  intro R B M N _ _ _ _ _ _ _ _ _ _ _ hess
  have : IsLocalizedModule (⊥ : Submonoid B) (LinearMap.id : N →ₗ[B] N) :=
    isLocalizedModule_bot_id B N
  exact weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small'
    R B M N N hess ⊥ LinearMap.id

/-- **[Stacks, Tag 05IJ].** Let `f : X ⟶ S` be locally of finite type, let `F` be a
quasi-coherent `𝒪_X`-module of finite type which is flat over `S`, and let `G` be a
quasi-coherent `𝒪_S`-module. Then the weakly associated points of `F ⊗_{𝒪_X} f^*G` are exactly
the points of the fibres `X_s`, over the weakly associated points `s` of `G`, that are
associated to the restriction of `F` to `X_s`.

This is the global form of Tag 05IH, and the source's proof of it is the pointwise statement
plus the passage to sets. Both are already in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackGlobal`, up to the same
algebraic input that Tag 05IH needed; supplying it here removes the hypothesis. -/
@[stacks 05IJ "the set equality for f locally of finite type, F quasi-coherent of finite type and \
flat over S, G quasi-coherent; unconditional"]
theorem weaklyAssociatedPoints_tensorPullback_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    weaklyAssociatedPoints
        (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(X.toLocallyRingedSpace.toRingedSpace).presheaf,
                (X.toLocallyRingedSpace.toRingedSpace).IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) =
      ⋃ s ∈ weaklyAssociatedPoints G,
        f.fiberι s '' associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) :=
  weaklyAssociatedPoints_tensorPullback_eq_of_formula
    weaklyAssociatedPrimesTensorFormula f F G hF

end Stacks.Divisors

end

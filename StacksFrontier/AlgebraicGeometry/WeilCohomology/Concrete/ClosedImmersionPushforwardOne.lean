module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionZeroPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoheightOfEquidimensional
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupRelationGeneral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupPushforwardOne
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionZeroOpen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExtendableConormalReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPushforwardGrassmannian
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumIndependence

/-!
# The two pullbacks of `K₀(Vect)`

The library has two pullbacks `K₀(Vect(Y)) ⟶ K₀(Vect(X))` along a morphism of schemes: the
additive `VectorBundleKZero.pullback` and the ring homomorphism
`VectorBundleKZero.pullbackRingHom`. They agree
(`AlgebraicGeometry.VectorBundleKZero.pullback_apply_eq_pullbackRingHom`). This is used in the
proof of Tag 0FIT to read the hypothesis of Lemma 0FIR, stated with `pullbackRingHom`, as the
hypothesis of Lemma 0FIH, stated with `pullback`.

The imports collect the inputs of the key case of the proof of Tag 0FIT
(`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPushforwardGlobalSections`).

## Main results

* `AlgebraicGeometry.VectorBundleKZero.pullback_apply_eq_pullbackRingHom`

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero
  Stacks.Chow

universe u w

namespace AlgebraicGeometry.VectorBundleKZero

/-- The two pullbacks `K₀(Vect(Y)) ⟶ K₀(Vect(X))` of the library agree. -/
theorem pullback_apply_eq_pullbackRingHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : VectorBundleKZero Y) : VectorBundleKZero.pullback f x = pullbackRingHom f x := by
  have h : VectorBundleKZero.pullback f = (pullbackRingHom f).toAddMonoidHom := by
    refine addHom_ext fun M hM ↦ ?_
    rw [pullback_classOf]
    exact (pullbackAddHom_classOf f M hM).symm
  exact DFunLike.congr_fun h x

end AlgebraicGeometry.VectorBundleKZero

end

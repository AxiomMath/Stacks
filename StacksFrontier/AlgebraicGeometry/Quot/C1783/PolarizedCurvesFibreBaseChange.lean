module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverEssentiallySmall

/-!
# The base change of `PolarizedCurves ⟶ 𝒞urves` along a scheme point

Stacks 0D5C: *the left vertical arrow `PolarizedCurves ⟶ 𝒞urves` is algebraic, as base change of
the arrow in Lemma 0D41*. The arrow is the second projection of the 2-fibre product
`PolarizedCurves = 𝒫olarized ×_{𝒮paces'_{fp,flat,proper}} 𝒞urves`, so its base change along a
scheme point `z : (Sch/Z) ⟶ 𝒞urves` is the base change of the forgetful 1-morphism
`𝒫olarized ⟶ 𝒮paces'_{fp,flat,proper}` of Stacks 0D41 along the composite point
`(Sch/Z) ⟶ 𝒞urves ⟶ 𝒮paces'_{fp,flat,proper}`:

```text
(Sch/Z) ×_{𝒞urves} (𝒫olarized ×_{𝒮paces'} 𝒞urves)  ≃  (Sch/Z) ×_{𝒮paces'} 𝒫olarized
```

over the site. This is Stacks 02XD (`CategoryTheory.TwoFibreProductOver.cancelSnd`), conjugated by
the exchange of the two factors (`CategoryTheory.TwoFibreProductOver.swapEquivalenceOver`), and
algebraicity transports along it (Stacks 03YQ,
`AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver`).

Nothing here is registered.

## Main results

* `AlgebraicGeometry.C1783.equivalenceOver_baseChange_polarizedCurves`:
  the equivalence over the site.
* `AlgebraicGeometry.C1783.isAlgebraicStack_baseChange_polarizedCurves_of`:
  the base change of `PolarizedCurves ⟶ 𝒞urves` is algebraic when that of
  `𝒫olarized ⟶ 𝒮paces'` along the composite point is.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.C1783

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)
  (Z : BigFppfOver B integerBase hZ)
  (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
  (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map Z.hom)

/-- The base change of `PolarizedCurves ⟶ 𝒞urves` along the scheme point `z`, as a category over
the site. -/
abbrev baseChangeProjection :
    TwoFibreProductOver (Over.map Z.hom)
      (polarizedCurvesSquare B hZ h3Z).pt.val.p (curvesFiberedCategory B hZ).val.p z
      (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd) ⥤
      BigFppfOver B integerBase hZ :=
  TwoFibreProductOver.structureFunctor (Over.map Z.hom)
    (polarizedCurvesSquare B hZ h3Z).pt.val.p (curvesFiberedCategory B hZ).val.p z
    (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd)

/-- The base change of the forgetful 1-morphism `𝒫olarized ⟶ 𝒮paces'_{fp,flat,proper}` along
the composite point `z ⋙ (𝒞urves ⟶ 𝒮paces')`, as a category over the site. -/
abbrev forgetBaseChangeProjection :
    TwoFibreProductOver (Over.map Z.hom) (polarizedFiberedCategory B hZ h3Z).val.p
      (cartesianProperFlatFiberedCategory B integerBase hZ).val.p
      (z ⋙ CatFiberedInGroupoids.homFunctor (curvesToCartesianProperFlatHom B hZ))
      (CatFiberedInGroupoids.homFunctor (polarizedToCartesianProperFlatHom B hZ h3Z)) ⥤
      BigFppfOver B integerBase hZ :=
  TwoFibreProductOver.structureFunctor (Over.map Z.hom) (polarizedFiberedCategory B hZ h3Z).val.p
    (cartesianProperFlatFiberedCategory B integerBase hZ).val.p
    (z ⋙ CatFiberedInGroupoids.homFunctor (curvesToCartesianProperFlatHom B hZ))
    (CatFiberedInGroupoids.homFunctor (polarizedToCartesianProperFlatHom B hZ h3Z))

include hz in
/-- **Stacks 02XD for PolarizedCurves.** The base change of `PolarizedCurves ⟶ 𝒞urves` along `z`
is equivalent over the site to the base change of `𝒫olarized ⟶ 𝒮paces'_{fp,flat,proper}` along
`z ⋙ (𝒞urves ⟶ 𝒮paces')`. -/
theorem equivalenceOver_baseChange_polarizedCurves :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (forgetBaseChangeProjection B hZ h3Z Z z) (baseChangeProjection B hZ h3Z Z z)) := by
  have hz' : (z ⋙ CatFiberedInGroupoids.homFunctor (curvesToCartesianProperFlatHom B hZ)) ⋙
      (cartesianProperFlatFiberedCategory B integerBase hZ).val.p = Over.map Z.hom := by
    rwa [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p]
  obtain ⟨e₂⟩ := TwoFibreProductOver.nonempty_equivalenceOver_cancelSnd
    (polarizedFiberedCategory B hZ h3Z).val.p (curvesFiberedCategory B hZ).val.p
    (cartesianProperFlatFiberedCategory B integerBase hZ).val.p (Over.map Z.hom)
    (CatFiberedInGroupoids.homFunctor (polarizedToCartesianProperFlatHom B hZ h3Z))
    (CatFiberedInGroupoids.homFunctor (curvesToCartesianProperFlatHom B hZ)) z
    (z ⋙ CatFiberedInGroupoids.homFunctor (curvesToCartesianProperFlatHom B hZ))
    (CatFiberedInGroupoids.homFunctor_comp_p _) hz (Iso.refl _)
    (fun u => IsHomLift.id (Functor.congr_obj hz' u))
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (polarizedCurvesSquare B hZ h3Z).pt.property (Stack.schemeSlice B integerBase hZ Z).property
      (curvesFiberedCategory B hZ).property TwoFibreProductOver.snd_comp_eq hz)
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (polarizedFiberedCategory B hZ h3Z).property (Stack.schemeSlice B integerBase hZ Z).property
      (cartesianProperFlatFiberedCategory B integerBase hZ).property
      (CatFiberedInGroupoids.homFunctor_comp_p _) hz')
  exact ⟨((TwoFibreProductOver.swapEquivalenceOver _ _ _ _ _).trans e₂.symm).trans
    (TwoFibreProductOver.swapEquivalenceOver _ _ _ _ _)⟩

include hz in
/-- **Stacks 0D5C: PolarizedCurves ⟶ 𝒞urves is algebraic as a base change of the arrow of
Stacks 0D41.** If the base change of the forgetful 1-morphism `𝒫olarized ⟶ 𝒮paces'` along the
composite point `z ⋙ (𝒞urves ⟶ 𝒮paces')` is an algebraic stack, so is the base change of
`PolarizedCurves ⟶ 𝒞urves` along `z` (Stacks 02XD and 03YQ). -/
theorem isAlgebraicStack_baseChange_polarizedCurves_of
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (BasedCategory.ofFunctor (forgetBaseChangeProjection B hZ h3Z Z z))) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (BasedCategory.ofFunctor (baseChangeProjection B hZ h3Z Z z)) :=
  let ⟨e⟩ := equivalenceOver_baseChange_polarizedCurves B hZ h3Z Z z hz
  Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ e h

end AlgebraicGeometry.C1783

module

public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesFibreBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The base change of `𝒫olarized ⟶ 𝒮paces'` with morphisms lifted, and without

The 2-fibre product square of PolarizedCurves (`AlgebraicGeometry.polarizedCurvesSquare`) uses the
form `AlgebraicGeometry.polarizedFiberedCategory` of `𝒫olarized` whose morphisms are lifted one
universe up. Stacks 0D41 is naturally stated for the category of polarized families itself, over
the site through `polarizedProjection ⋙ schemeOverIntegers`. The two base changes along a scheme
point of `𝒮paces'_{fp, flat, proper}` are equivalent over the site (change of the second factor
along the equivalence `ULiftHom.down`, `CategoryTheory.TwoFibreProductOver.precomposeSnd`), so
algebraicity passes from the second to the first.

Nothing here is registered.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.C1783

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)

include h3Z in
/-- **The base changes of `𝒫olarized ⟶ 𝒮paces'` with morphisms lifted, and without.** The base
change along a scheme point `y` of the lifted form `polarizedToCartesianProperFlatHom` of the
forgetful functor `𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}` is equivalent over the site to the base
change of the forgetful functor itself: change the second factor along the equivalence
`ULiftHom.down` (`CategoryTheory.TwoFibreProductOver.precomposeSnd`). -/
theorem nonempty_equivalenceOver_baseChange_polarizedUp (Z : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B Z.left.1 Z.left.2 ⥤ CartesianProperFlatSpaces B integerBase hZ)
    (hy : y ⋙ cartesianProperFlatProjection B integerBase hZ = Over.map Z.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
        (polarizedProjectionOver B hZ) (cartesianProperFlatProjection B integerBase hZ) y
        (forgetPolarizationUp B hZ))
      (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
        (polarizedProjection B ⋙ schemeOverIntegers B)
        (cartesianProperFlatProjection B integerBase hZ) y (forgetPolarization B))) := by
  have hU : (Over.map Z.hom).IsFiberedInGroupoids := Functor.IsFiberedInGroupoids.over_map Z.hom
  have hpol := isFiberedInGroupoids_polarizedProjectionOver B hZ h3Z
  have hsp := cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ
  let a : PolarizedFamilyUp B ⥤ PolarizedFamily B := ULiftHom.down
  have : a.IsEquivalence := (ULiftHom.equiv (C := PolarizedFamily B)).isEquivalence_inverse
  have hA : a ⋙ (polarizedProjection B ⋙ schemeOverIntegers B) = polarizedProjectionOver B hZ :=
    rfl
  have hF : forgetPolarization B ⋙ cartesianProperFlatProjection B integerBase hZ =
      polarizedProjection B ⋙ schemeOverIntegers B := rfl
  have hK := TwoFibreProductOver.isEquivalence_precomposeSnd (pT := Over.map Z.hom)
    (pℬ := cartesianProperFlatProjection B integerBase hZ) (G := y)
    (F := forgetPolarization B) (a := a) hU hpol h3Z hA hF
  exact StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hU hpol hsp hy
      (forgetPolarizationUp_comp B hZ))
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hU h3Z hsp hy hF)
    (TwoFibreProductOver.precomposeSnd (pT := Over.map Z.hom)
      (pℬ := cartesianProperFlatProjection B integerBase hZ) y (forgetPolarization B) a hA)
    (TwoFibreProductOver.precomposeSnd_comp_structureFunctor _ _ _ _) hK

include h3Z in
/-- **Stacks 0D41 read on the lifted form of `𝒫olarized`.** If the base change of the forgetful
functor `𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}` along a scheme point `y` is algebraic, so is the
base change of its lifted form `polarizedToCartesianProperFlatHom` along `y`. -/
private theorem isAlgebraicStack_baseChange_polarizedUp_of (Z : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B Z.left.1 Z.left.2 ⥤ CartesianProperFlatSpaces B integerBase hZ)
    (hy : y ⋙ cartesianProperFlatProjection B integerBase hZ = Over.map Z.hom)
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
        (polarizedProjection B ⋙ schemeOverIntegers B)
        (cartesianProperFlatProjection B integerBase hZ) y (forgetPolarization B)))) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
        (polarizedProjectionOver B hZ) (cartesianProperFlatProjection B integerBase hZ) y
        (forgetPolarizationUp B hZ))) :=
  let ⟨e⟩ := nonempty_equivalenceOver_baseChange_polarizedUp B hZ h3Z Z y hy
  Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ e.symm h

include h3Z in
/-- **PolarizedCurves ⟶ 𝒞urves is algebraic, from Stacks 0D41** in the form "the base change of
`𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}` along every scheme point is algebraic": the base change
along `z` of `PolarizedCurves ⟶ 𝒞urves` is the base change of `𝒫olarized ⟶ 𝒮paces'` along the
composite point (Stacks 02XD). -/
theorem isAlgebraicStack_baseChange_polarizedCurves_of_forget
    (h0D41 : ∀ (Z : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B Z.left.1 Z.left.2 ⥤ CartesianProperFlatSpaces B integerBase hZ)
      (_hy : y ⋙ cartesianProperFlatProjection B integerBase hZ = Over.map Z.hom),
      Stack.IsAlgebraicStack.{u, w} B integerBase hZ
        (BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
          (polarizedProjection B ⋙ schemeOverIntegers B)
          (cartesianProperFlatProjection B integerBase hZ) y (forgetPolarization B))))
    (Z : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map Z.hom) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (BasedCategory.ofFunctor (baseChangeProjection B hZ h3Z Z z)) :=
  isAlgebraicStack_baseChange_polarizedCurves_of B hZ h3Z Z z hz
    (isAlgebraicStack_baseChange_polarizedUp_of B hZ h3Z Z (z ⋙ curvesToCartesianProperFlat B hZ)
      hz (h0D41 Z _ hz))

end AlgebraicGeometry.C1783

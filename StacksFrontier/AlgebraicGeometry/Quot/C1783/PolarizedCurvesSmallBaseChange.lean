module

public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesFibreBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesAlgebraic
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Base changes of the small model of `PolarizedCurves ⟶ 𝒞urves`

The base change of the small model `PolarizedCurves_s ⟶ 𝒞urves_s` along a scheme point
`z : (Sch/Z) ⟶ 𝒞urves_s` is equivalent over the site to the base change of
`PolarizedCurves ⟶ 𝒞urves` along the corresponding point of `𝒞urves`: change the target along the
fully faithful comparison `𝒞urves_s ⟶ 𝒞urves`
(`CategoryTheory.TwoFibreProductOver.mapBase`) and the second factor along the equivalence
`PolarizedCurves_s ⟶ PolarizedCurves` (`CategoryTheory.TwoFibreProductOver.precomposeSnd`). So
algebraicity of the base changes (Stacks 0D5C: the 1-morphism is algebraic) may be
proved for `PolarizedCurves ⟶ 𝒞urves` itself, where Stacks 02XD reduces it to Stacks 0D41
(`AlgebraicGeometry.C1783.isAlgebraicStack_baseChange_polarizedCurves_of`).

Nothing here is registered.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.C1783

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)

/-- The comparison `𝒞urves_s ⥤ 𝒞urves` out of the small model. -/
noncomputable abbrev curvesSmallInverse :
    (curvesSmall B hZ).val.obj ⥤ (curvesFiberedCategory B hZ).val.obj :=
  letI := locallySmall_curveFamily B hZ
  ShrinkHoms.inverse.{u} (CurveFamily B hZ)

omit hZ h3Z in
/-- Algebraicity of a 2-fibre product over the site depends on its second leg only through that
leg. -/
private theorem isAlgebraicStack_structureFunctor_of_eq {T 𝒜 ℬ : Type*} [Category T]
    [Category 𝒜] [Category ℬ] {S : Scheme.{u}} {hS : B.Contains S} {pT : T ⥤ BigFppfOver B S hS}
    {p𝒜 : 𝒜 ⥤ BigFppfOver B S hS} {pℬ : ℬ ⥤ BigFppfOver B S hS} {G : T ⥤ ℬ}
    {F₁ F₂ : 𝒜 ⥤ ℬ} (h : F₁ = F₂)
    (H : Stack.IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F₂))) :
    Stack.IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F₁)) := by
  subst h
  exact H

/-- **Algebraicity of the base changes of the small model of `PolarizedCurves ⟶ 𝒞urves`**, from
that of the base changes of `PolarizedCurves ⟶ 𝒞urves` itself. -/
theorem isAlgebraicStack_baseChange_polarizedCurvesSmall_of (Z : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesSmall B hZ).val.obj)
    (hz : z ⋙ (curvesSmall B hZ).val.p = Over.map Z.hom)
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (BasedCategory.ofFunctor (baseChangeProjection B hZ h3Z Z (z ⋙ curvesSmallInverse B hZ)))) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).pt.val := by
  let := locallySmall_polarizedCurves B hZ h3Z
  let := locallySmall_curveFamily B hZ
  let : LocallySmall.{u} (curvesFiberedCategory B hZ).val.obj := locallySmall_curveFamily B hZ
  have hU : (Over.map Z.hom).IsFiberedInGroupoids := Functor.IsFiberedInGroupoids.over_map Z.hom
  have hPC := (polarizedCurvesFiberedCategory B hZ h3Z).property
  have hPCs := (polarizedCurvesSmall B hZ h3Z).property
  have hC := (curvesFiberedCategory B hZ).property
  have hCs := (curvesSmall B hZ).property
  let b := curvesSmallInverse B hZ
  let a :
      (polarizedCurvesSmall B hZ h3Z).val.obj ⥤ (polarizedCurvesFiberedCategory B hZ h3Z).val.obj :=
    ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj
  let snd := CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd
  let Fs := CatFiberedInGroupoids.homFunctor (polarizedCurvesSmallToCurvesSmall B hZ h3Z)
  have hb : b ⋙ (curvesFiberedCategory B hZ).val.p = (curvesSmall B hZ).val.p := rfl
  have hA : a ⋙ (polarizedCurvesFiberedCategory B hZ h3Z).val.p =
      (polarizedCurvesSmall B hZ h3Z).val.p :=
    rfl
  have hz' : (z ⋙ b) ⋙ (curvesFiberedCategory B hZ).val.p = Over.map Z.hom := hz
  have hsnd : snd ⋙ (curvesFiberedCategory B hZ).val.p =
      (polarizedCurvesFiberedCategory B hZ h3Z).val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p _
  have hrt := BasedCategory.shrinkHoms_functor_comp_inverse.{u} (curvesFiberedCategory B hZ).val
  -- the second leg after changing the target, read as a precomposition
  let F' :
      (polarizedCurvesFiberedCategory B hZ h3Z).val.obj ⥤ (curvesFiberedCategory B hZ).val.obj :=
    snd ⋙ ShrinkHoms.functor.{u} (curvesFiberedCategory B hZ).val.obj ⋙
      ShrinkHoms.inverse.{u} (curvesFiberedCategory B hZ).val.obj
  have hF' : F' = snd := (congrArg (fun G => snd ⋙ G) hrt).trans rfl
  have hF'p : F' ⋙ (curvesFiberedCategory B hZ).val.p =
      (polarizedCurvesFiberedCategory B hZ h3Z).val.p :=
    hF' ▸ hsnd
  -- step 1: change the second factor along the equivalence `a`
  have : a.IsEquivalence :=
    (ShrinkHoms.equivalence.{u}
      (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).isEquivalence_inverse
  have h₁ : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor (Over.map Z.hom) (polarizedCurvesSmall B hZ h3Z).val.p
        (curvesFiberedCategory B hZ).val.p (z ⋙ b) (a ⋙ F'))) := by
    have hK := TwoFibreProductOver.isEquivalence_precomposeSnd (pT := Over.map Z.hom)
      (pℬ := (curvesFiberedCategory B hZ).val.p) (G := z ⋙ b) (F := F') (a := a) hU hPCs hPC hA
      hF'p
    obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
      (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hU hPCs hC hz'
        ((congrArg (a ⋙ ·) hF'p).trans hA))
      (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hU hPC hC hz' hF'p)
      (TwoFibreProductOver.precomposeSnd (pT := Over.map Z.hom)
        (pℬ := (curvesFiberedCategory B hZ).val.p) (z ⋙ b) F' a hA)
      (TwoFibreProductOver.precomposeSnd_comp_structureFunctor _ _ _ _) hK
    exact Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ e.symm
      (isAlgebraicStack_structureFunctor_of_eq B hF' h)
  -- step 2: change the target along the fully faithful `b`
  have : b.IsEquivalence := (ShrinkHoms.equivalence.{u} (CurveFamily B hZ)).isEquivalence_inverse
  have hK := TwoFibreProductOver.isEquivalence_mapBase (pT := Over.map Z.hom)
    (p𝒜 := (polarizedCurvesSmall B hZ h3Z).val.p) (G := z) (F := Fs) (b := b) hb
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hU hPCs hCs hz
      (CatFiberedInGroupoids.homFunctor_comp_p _))
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hU hPCs hC hz'
      ((congrArg (Fs ⋙ ·) hb).trans (CatFiberedInGroupoids.homFunctor_comp_p _)))
    (TwoFibreProductOver.mapBase (pT := Over.map Z.hom)
      (p𝒜 := (polarizedCurvesSmall B hZ h3Z).val.p) z Fs b hb)
    (TwoFibreProductOver.mapBase_comp_structureFunctor _ _ _ _) hK
  exact Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ e.symm h₁

end AlgebraicGeometry.C1783

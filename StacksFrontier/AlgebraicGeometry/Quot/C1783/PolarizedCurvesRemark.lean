module

public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesForgetBridge
public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesSmallBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesSmoothLimit
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesSurjective
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedForgetAlgebraicMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackOfSmoothAlgebraicCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackHomUniverse
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomStack

/-!
# The stack of polarized curves and the algebraicity of `𝒞urves` (Stacks 0D5C)

Remark 0D5C of the Quot chapter considers the 2-fibre product

```text
  PolarizedCurves = 𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized
```

and asserts:

1. it parametrizes polarized curves, i.e. families of curves endowed with a relatively ample
   invertible sheaf;
2. the left vertical arrow `PolarizedCurves ⟶ 𝒞urves` is algebraic, as base change of the arrow
   `𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}` of Stacks 0D41;
3. it is smooth (there are no obstructions to deforming invertible sheaves on curves);
4. it is surjective (every point is in the image);
5. PolarizedCurves is an open and closed substack of the algebraic stack `𝒫olarized`
   (Stacks 0D5B, Stacks 0D4X);
6. this gives another approach to the algebraicity of `𝒞urves`: a stack in groupoids which is the
   target of a smooth (surjective) algebraic morphism from an algebraic stack is algebraic.

All of them are clauses of the single conjunction
`AlgebraicGeometry.polarizedCurvesToCurves_isAlgebraic_smooth_surjective`.

The ingredients from the library are: the equivalence of PolarizedCurves with the polarized curves
(`AlgebraicGeometry.polarizedCurvesToIsPolarizedCurve`), the open and closed immersion
`PolarizedCurves ⟶ 𝒫olarized`
(`AlgebraicGeometry.polarizedCurvesToPolarized_isOpenImmersion_and_isClosedImmersion`),
Stacks 0D4X (`AlgebraicGeometry.isAlgebraicStack_polarizedStack`), Stacks 0D41
(`AlgebraicGeometry.isAlgebraicMorphism_forgetPolarizationOneMorphism`), surjectivity on objects
(`AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesToCurves`) and its form between the
hom-shrunk models (`AlgebraicGeometry.isSurjective_polarizedCurvesToCurvesAlgebraic_of`), and the
general statement on targets of smooth surjective algebraic 1-morphisms
(`AlgebraicGeometry.Stack.isAlgebraicStack_of_smooth_surjective_algebraicMorphism`). The
identification of the base changes with those of 0D41 is
`StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesFibreBaseChange` and
`StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesForgetBridge`; smoothness is
`StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesSmoothLimit`.

The 1-morphism `PolarizedCurves ⟶ 𝒞urves` is read, for the assertions about its base changes and
for surjectivity, between the hom-shrunk models `AlgebraicGeometry.polarizedCurvesSmall` and
`AlgebraicGeometry.curvesSmall`, whose morphisms lie in the universe of the site, as the
2-category of algebraic stacks requires; they are equivalent over the site to PolarizedCurves and
`𝒞urves`. Algebraic and smooth are in the sense of Stacks 06CF and Stacks 075U: every base change
along a scheme-valued point is an algebraic stack, smooth over that scheme.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D5B](https://stacks.math.columbia.edu/tag/0D5B)
* [Stacks Project, Tag 0D58](https://stacks.math.columbia.edu/tag/0D58)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace C1783

/-- The form `AlgebraicGeometry.polarizedFiberedCategory` of `𝒫olarized` in the square defining
PolarizedCurves, whose morphisms are lifted one universe up, is an algebraic stack: it is
equivalent over the site to `AlgebraicGeometry.polarizedStackUnconditional` (Stacks 03YQ), which
is algebraic by Stacks 0D4X. -/
private theorem isAlgebraicStack_polarizedFiberedCategory :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (polarizedFiberedCategory B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val := by
  have h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (BasedCategory.ofFunctor (polarizedProjection B ⋙ schemeOverIntegers B)) := by
    rw [← polarizedSliceProjection_eq B]
    exact (isAlgebraicStack_polarizedStack.{u, w} B).1
  exact Stack.isAlgebraicStack_of_equivalenceOver B _ hZ
    (Functor.equivalenceOver_uliftHom.{u, u + 1, u, u + 1, u + 1}
      (polarizedProjection B ⋙ schemeOverIntegers B)) h

/-- PolarizedCurves is an algebraic stack: its projection to `𝒫olarized` is representable by
algebraic spaces (Stacks 0D5B), so Stacks 05UM applies. -/
private theorem isAlgebraicStack_polarizedCurvesUnconditional :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (polarizedCurvesUnconditional B hZ).val :=
  Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse B integerBase hZ _
    (polarizedCurvesToPolarized_isOpenImmersion_and_isClosedImmersion B hZ).1
    (isAlgebraicStack_polarizedFiberedCategory B hZ)

/-- The base change of `PolarizedCurves ⟶ 𝒞urves` along a scheme point is equivalent over the
site to the base change of the forgetful 1-morphism of Stacks 0D41 along the composite point. -/
private theorem nonempty_equivalenceOver_baseChange_forgetPolarization
    (Z : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map Z.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
        (polarizedProjection B ⋙ schemeOverIntegers B)
        (cartesianProperFlatProjection B integerBase hZ)
        (z ⋙ curvesToCartesianProperFlat B hZ) (forgetPolarization B))
      (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
        (polarizedCurvesUnconditional B hZ).val.p (curvesFiberedCategory B hZ).val.p z
        (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).snd))) :=
  let ⟨e₁⟩ := nonempty_equivalenceOver_baseChange_polarizedUp B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B) Z
    (z ⋙ curvesToCartesianProperFlat B hZ) hz
  let ⟨e₂⟩ := equivalenceOver_baseChange_polarizedCurves B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B) Z z hz
  ⟨e₁.symm.trans e₂⟩

/-- The base changes of the small model of `PolarizedCurves ⟶ 𝒞urves` along scheme points are
algebraic: they are base changes of the forgetful 1-morphism of Stacks 0D41. -/
private theorem isAlgebraicStack_baseChange_polarizedCurvesSmallToCurvesSmall
    (Z : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesSmall B hZ).val.obj)
    (hz : z ⋙ (curvesSmall B hZ).val.p = Over.map Z.hom) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B))).pt.val :=
  isAlgebraicStack_baseChange_polarizedCurvesSmall_of B hZ _ Z z hz
    (isAlgebraicStack_baseChange_polarizedCurves_of_forget B hZ _
      (fun Z' y hy => isAlgebraicMorphism_forgetPolarizationOneMorphism.{w, u} B Z' y hy)
      Z (z ⋙ curvesSmallInverse B hZ) hz)

end C1783

open C1783 in
/-- **Stacks 0D5C.** Let `PolarizedCurves = 𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized`
(`AlgebraicGeometry.polarizedCurvesUnconditional`), over the big fppf site of `Spec ℤ`.

1. PolarizedCurves parametrizes polarized curves: its first projection is an equivalence onto the
   category of polarized families of relative dimension at most one, i.e. of families of curves
   endowed with a relatively ample invertible sheaf.
2. PolarizedCurves is an open and closed substack of the algebraic stack `𝒫olarized`: `𝒫olarized`
   is an algebraic stack, the projection `PolarizedCurves ⟶ 𝒫olarized` is representable by
   algebraic spaces, an open immersion and a closed immersion, and PolarizedCurves is an algebraic
   stack.
3. `PolarizedCurves ⟶ 𝒞urves` is a base change of the arrow `𝒫olarized ⟶ 𝒮paces'_{fp,flat,proper}`
   of Stacks 0D41: its base change along every scheme point `z` of `𝒞urves` is equivalent over the
   site to the base change of the forgetful 1-morphism of Stacks 0D41 along the image of `z` in
   `𝒮paces'_{fp, flat, proper}`.
4. `PolarizedCurves ⟶ 𝒞urves` is algebraic (Stacks 06CF): its base change along every scheme point
   of `𝒞urves` is an algebraic stack.
5. `PolarizedCurves ⟶ 𝒞urves` is smooth: each of these base changes is smooth over the scheme
   (Stacks 075U).
6. `PolarizedCurves ⟶ 𝒞urves` is surjective: every point of `𝒞urves` is in the image
   (surjectivity on objects, Stacks 06D4), and the 1-morphism of algebraic stacks is surjective on
   points (Stacks 04ZS).
7. Another approach to the algebraicity of `𝒞urves`: `𝒞urves` is an algebraic stack, as the
   target of the smooth, surjective, algebraic 1-morphism `PolarizedCurves ⟶ 𝒞urves` from the
   algebraic stack PolarizedCurves.

Clauses 4–6 are stated for the hom-shrunk models `AlgebraicGeometry.polarizedCurvesSmall` and
`AlgebraicGeometry.curvesSmall`, equivalent over the site to PolarizedCurves and `𝒞urves`, with
the projection `AlgebraicGeometry.polarizedCurvesSmallToCurvesSmall`; surjectivity on objects in
clause 6 is also stated for PolarizedCurves itself. -/
@[stacks 0D5C]
theorem polarizedCurvesToCurves_isAlgebraic_smooth_surjective :
    -- (1) PolarizedCurves parametrizes polarized curves
    (polarizedCurvesToIsPolarizedCurve B hZ).IsEquivalence ∧
    -- (2) PolarizedCurves is an open and closed substack of the algebraic stack `𝒫olarized`
    (Stack.IsAlgebraicStack.{u, w} B integerBase hZ (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (polarizedCurvesToPolarizedUnconditional B hZ).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (polarizedCurvesToPolarizedUnconditional B hZ) ∧
      Stack.IsClosedImmersion B integerBase hZ (polarizedCurvesToPolarizedUnconditional B hZ) ∧
      Stack.IsAlgebraicStack.{u, w} B integerBase hZ (polarizedCurvesUnconditional B hZ).val) ∧
    -- (3) `PolarizedCurves ⟶ 𝒞urves` is a base change of the arrow of Stacks 0D41
    (∀ (Z : BigFppfOver B integerBase hZ)
      (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj),
      z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map Z.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
          (polarizedProjection B ⋙ schemeOverIntegers B)
          (cartesianProperFlatProjection B integerBase hZ)
          (z ⋙ curvesToCartesianProperFlat B hZ) (forgetPolarization B))
        (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
          (polarizedCurvesUnconditional B hZ).val.p (curvesFiberedCategory B hZ).val.p z
          (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ
            (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).snd)))) ∧
    -- (4) `PolarizedCurves ⟶ 𝒞urves` is algebraic
    (∀ (Z : BigFppfOver B integerBase hZ)
      (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesSmall B hZ).val.obj)
      (hz : z ⋙ (curvesSmall B hZ).val.p = Over.map Z.hom),
      Stack.IsAlgebraicStack.{u, w} B integerBase hZ
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (Stack.schemeSliceMap B integerBase hZ Z z hz)
          (polarizedCurvesSmallToCurvesSmall B hZ
            (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B))).pt.val) ∧
    -- (5) `PolarizedCurves ⟶ 𝒞urves` is smooth
    (∀ (Z : BigFppfOver B integerBase hZ)
      (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesSmall B hZ).val.obj)
      (hz : z ⋙ (curvesSmall B hZ).val.p = Over.map Z.hom),
      Stack.HasPropertyOnSomeSmoothDiagram B integerBase hZ
        (fun _ _ h => Space.IsSmooth B integerBase hZ h)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (Stack.schemeSliceMap B integerBase hZ Z z hz)
          (polarizedCurvesSmallToCurvesSmall B hZ
            (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B))).fst) ∧
    -- (6) `PolarizedCurves ⟶ 𝒞urves` is surjective
    (Stack.IsSurjectiveOnObjects B integerBase hZ
        (polarizedCurvesUnconditional B hZ).val.p (curvesFiberedCategory B hZ).val.p
        (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).snd) ∧
      Stack.IsSurjectiveOnObjects B integerBase hZ
        (polarizedCurvesSmall B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val.p
        (curvesSmall B hZ).val.p
        (CatFiberedInGroupoids.homFunctor (polarizedCurvesSmallToCurvesSmall B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B))) ∧
      ∃ (hX : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
          (polarizedCurvesUnconditional B hZ).val)
        (hY : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val),
        Stack.IsSurjective B integerBase hZ (polarizedCurvesToCurvesAlgebraic B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B) hX hY)) ∧
    -- (7) `𝒞urves` is an algebraic stack
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val := by
  have hS := fun (Z : BigFppfOver B integerBase hZ) z hz =>
    hasPropertyOnSomeSmoothDiagram_baseChange_polarizedCurvesSmall B hZ _ Z z hz
      (isAlgebraicStack_baseChange_polarizedCurvesSmallToCurvesSmall.{w} B hZ Z z hz)
  -- (7), the remark's approach: `𝒞urves` is the target of the smooth, surjective, algebraic
  -- 1-morphism `PolarizedCurves ⟶ 𝒞urves` (on the hom-shrunk models) from the algebraic stack
  -- PolarizedCurves (Stacks 0D5C, last sentence)
  have hC : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val := by
    have h𝒳 : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (polarizedCurvesSmall B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val :=
      (isAlgebraicStack_polarizedCurvesSmall_iff B hZ _).2
        (isAlgebraicStack_polarizedCurvesUnconditional B hZ)
    have h𝒴 : (curvesSmall B hZ).val.p.IsStack (BigFppfOver.topology B integerBase hZ) :=
      (BasedCategory.isStack_iff_of_equivalence
        (curvesSmallEquivalenceOver B hZ).toBasedEquivalence
        (BigFppfOver.topology B integerBase hZ)).1 (curvesProjectionOver_isStack B hZ)
    exact (isAlgebraicStack_curvesSmall_iff B hZ).1
      (Stack.isAlgebraicStack_of_smooth_surjective_algebraicMorphism B integerBase hZ
        (polarizedCurvesSmallToCurvesSmall B hZ _) h𝒳 h𝒴
        (isAlgebraicStack_baseChange_polarizedCurvesSmallToCurvesSmall B hZ)
        hS
        (isSurjectiveOnObjects_polarizedCurvesSmallToCurvesSmall B hZ _))
  exact ⟨inferInstance,
    ⟨isAlgebraicStack_polarizedFiberedCategory B hZ,
      (polarizedCurvesToPolarized_isOpenImmersion_and_isClosedImmersion B hZ).1,
      (polarizedCurvesToPolarized_isOpenImmersion_and_isClosedImmersion B hZ).2.1,
      (polarizedCurvesToPolarized_isOpenImmersion_and_isClosedImmersion B hZ).2.2,
      isAlgebraicStack_polarizedCurvesUnconditional B hZ⟩,
    nonempty_equivalenceOver_baseChange_forgetPolarization B hZ,
    isAlgebraicStack_baseChange_polarizedCurvesSmallToCurvesSmall B hZ,
    hS,
    ⟨isSurjectiveOnObjects_polarizedCurvesToCurves B hZ,
      isSurjectiveOnObjects_polarizedCurvesSmallToCurvesSmall B hZ _,
      isAlgebraicStack_polarizedCurvesUnconditional B hZ, hC,
      isSurjective_polarizedCurvesToCurvesAlgebraic_of B hZ _ _ _⟩,
    hC⟩

end AlgebraicGeometry

end

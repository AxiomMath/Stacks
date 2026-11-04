module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlusSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation

/-!
# Smoothness results on the stack of curves from its limit preservation

The statements of Stacks 0DZU, 0DZX (1), 0E00 and 0E79 in
`StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothLocusDeformation` and
`StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlusSmooth` take `hlfp`, the local finite
presentation of `Curves → Spec(ℤ)` (the second clause of Stacks 0DSS). That clause is
`AlgebraicGeometry.isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack`, from the
limit preservation of the stack of curves (Stacks 0D55). The results below are those statements
with `hlfp` discharged in this way, so that what remains is `h`, the algebraicity of the stack of
curves (Stacks 0D5A), and `hlim`, its limit preservation (Stacks 0D55); these declarations are
therefore unregistered.

## Main results

* `AlgebraicGeometry.smoothLocus_property_curvesSmallPoint_iff_of_isLimitPreserving`: Stacks 0DZU.
* `AlgebraicGeometry.smoothLocus_property_curvesSmallPoint_iff_of_isCohenRing_of_isLimitPreserving`
  is Stacks 0DZU over a Cohen ring.
* `AlgebraicGeometry.isSmoothOverIntegers_lciPlus_of_isLimitPreserving`: Stacks 0DZX (1).
* `AlgebraicGeometry.isSmoothOverIntegers_nodal_of_isLimitPreserving`: Stacks 0E00.
* `AlgebraicGeometry.isSmoothOverIntegers_stable_of_isLimitPreserving` and
  `AlgebraicGeometry.isSmoothOverIntegers_stableOfGenus_of_isLimitPreserving`: Stacks 0E79.

## References

* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0DZU](https://stacks.math.columbia.edu/tag/0DZU)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0E79](https://stacks.math.columbia.edu/tag/0E79)
-/

@[expose] public section

open CategoryTheory Deformation Deformation.Examples

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DZU on the stack of curves, from limit preservation.** Let `X` be a proper scheme of
dimension at most one over a field `k` and `Λ` a Noetherian local ring, separated in its
`𝔪`-adic topology, flat over `ℤ`, with a surjection `Λ → k`. With `h` the algebraicity of the
stack of curves (Stacks 0D5A) and `hlim` its limit preservation (Stacks 0D55), the point
classifying `X` lies in the open substack where `Curves → Spec ℤ` is smooth exactly when `Def_X`
over `𝒞_Λ` is unobstructed. -/
theorem smoothLocus_property_curvesSmallPoint_iff_of_isLimitPreserving
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
    (hdim : topologicalKrullDim X.left ≤ 1)
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    {W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)}
    (hW : Stack.IsSmoothLocus B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W)
    [IsLocalRing Λ] [IsNoetherianRing Λ] [IsHausdorff (IsLocalRing.maximalIdeal Λ) Λ]
    (hsurj : Function.Surjective (algebraMap Λ k))
    (hflat : ∀ f : Spec (.of Λ) ⟶ integerBase, Flat f) :
    W.property (curvesSmallPoint B hZ X hk hdim) ↔
      IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) X)) :=
  smoothLocus_property_curvesSmallPoint_iff B hZ X hk hdim h
    (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim) hW hsurj
    hflat

/-- **Stacks 0DZU over a Cohen ring, on the stack of curves, from limit preservation.** With `h`
the algebraicity of the stack of curves (Stacks 0D5A) and `hlim` its limit preservation
(Stacks 0D55), for `Λ` a Cohen ring for `k` the point classifying `X` lies in the open substack
where `Curves → Spec ℤ` is smooth exactly when `Def_X` over `𝒞_Λ` is unobstructed. -/
theorem smoothLocus_property_curvesSmallPoint_iff_of_isCohenRing_of_isLimitPreserving
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
    (hdim : topologicalKrullDim X.left ≤ 1)
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    {W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)}
    (hW : Stack.IsSmoothLocus B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W)
    [IsDomain Λ] [IsCohenRing Λ] (hsurj : Function.Surjective (algebraMap Λ k)) :
    W.property (curvesSmallPoint B hZ X hk hdim) ↔
      IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) X)) :=
  smoothLocus_property_curvesSmallPoint_iff_of_isCohenRing B hZ X hk hdim h
    (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim) hW hsurj

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Stacks 0DZX, part (1), on the stack of curves, from limit preservation**: with `h` the
algebraicity of the stack of curves (Stacks 0D5A) and `hlim` its limit preservation
(Stacks 0D55), `Curves^{lci+} → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_lciPlus_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ)) :
    IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_lciPlus B hZ) :=
  isSmoothOverIntegers_lciPlus B hZ h
    (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim)

/-- **Stacks 0E00 on the stack of curves, from limit preservation**: with `h` the algebraicity of
the stack of curves (Stacks 0D5A) and `hlim` its limit preservation (Stacks 0D55),
`Curves^{nodal} → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_nodal_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ)) :
    IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_isAtWorstNodal B hZ) :=
  isSmoothOverIntegers_nodal B hZ h
    (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim)

/-- **Stacks 0E79 for `𝓜̄`, on the stack of curves, from limit preservation**: with `h` the
algebraicity of the stack of curves (Stacks 0D5A) and `hlim` its limit preservation
(Stacks 0D55), for the open substack `𝓜̄ = Curves^{stable}` (`hst`, Stacks 0E76),
`𝓜̄ → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_stable_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ)) :
    IsSmoothOverIntegers B hZ h hst :=
  isSmoothOverIntegers_stable B hZ h
    (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim) hst

/-- **Stacks 0E79 for `𝓜̄_g`, on the stack of curves, from limit preservation**: with `h` the
algebraicity of the stack of curves (Stacks 0D5A) and `hlim` its limit preservation
(Stacks 0D55), for the open substack `𝓜̄_g` of stable curves of genus `g` (`hst`, Stacks 0E78),
`𝓜̄_g → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_stableOfGenus_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ)) (g : ℕ)
    (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g)) :
    IsSmoothOverIntegers B hZ h hst :=
  isSmoothOverIntegers_stableOfGenus B hZ h
    (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim) g hst

end AlgebraicGeometry

end

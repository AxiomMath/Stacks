module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationThickening
public import StacksFrontier.Deformation.Artin.Predeformation.Transport
public import StacksFrontier.Deformation.Smooth.UnobstructedEquivalenceOver
public import StacksFrontier.AlgebraicGeometry.Size.CompleteLocalRing
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PredeformationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingSmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationBaseChange

/-!
# The smooth locus of the stack of curves and deformations of a curve (Stacks 0DZU)

Let `k` be a field, `X` a proper scheme of dimension at most one over `k` and `Λ → k` a ring map
(in Stacks 0DZU a Cohen ring of `k`). The proof of Stacks 0DZU compares the deformation category
`Def_X` of flat deformations of `X` over `𝒞_Λ` with the predeformation category
`𝓕_{Curves, k, x₀}` of the point `x₀ : Spec k ⟶ Curves` classifying `X`.

`Deformation.Examples.isSmooth_baseProjection_schemeDeformation_iff_curves` reads that comparison
on the presentation `AlgebraicGeometry.CurveFamily` of the stack of curves. This file transports
it to the small model `AlgebraicGeometry.curvesSmall`, the presentation at which the stack of
curves is an object of the 2-category of algebraic stacks, along the equivalence over the site
`AlgebraicGeometry.curvesSmallEquivalenceOver`.

## Main results

* `AlgebraicGeometry.isSmooth_baseProjection_curvesSmall_iff_schemeDeformation`: `Def_X` is
  unobstructed exactly when `𝓕_{Curves, k, x₀}`, computed on the small model, is.
* `AlgebraicGeometry.smoothLocus_property_curvesSmallPoint_iff` and
  `AlgebraicGeometry.smoothLocus_property_curvesSmallPoint_iff_of_isCohenRing`: the equivalence of
  Stacks 0DZU, from the algebraicity of the stack of curves (Stacks 0D5A) and its local finite
  presentation over `Spec ℤ` (Stacks 0DSS); not registered until those are available.

## References

* [Stacks Project, Tag 0DZU](https://stacks.math.columbia.edu/tag/0DZU)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin Deformation.Examples

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (X : Over (Spec (.of k))) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
  (hdim : topologicalKrullDim X.left ≤ 1) (iΛ : Spec (.of Λ) ⟶ integerBase)

/-- The point `x₀ : Spec k ⟶ Curves` classifying `X`, as an object of the small model of the stack
of curves. -/
abbrev curvesSmallPoint : (curvesSmallBased B hZ).obj :=
  (curvesSmallEquivalenceOver B hZ).hom.functor.obj (curveFamilyOfScheme X B hZ hk hdim)

/-- The point classifying `X` lies over `Spec k`, read over `Spec ℤ` through `Spec Λ`. -/
theorem curvesSmallPoint_lies_over :
    ((curvesSmallBased B hZ).p ⋙ Over.post B.inclusion).obj (curvesSmallPoint B hZ X hk hdim) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  (transport_obj_eq B hZ (curvesFiberedCategory B hZ).val.p (curvesSmallBased B hZ).p _
    (curvesSmallEquivalenceOver B hZ).hom.w _).trans
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)

/-- **`Def_X` is unobstructed exactly when `𝓕_{Curves, k, x₀}` is, on the small model.** The
predeformation category of the point classifying `X` in `AlgebraicGeometry.curvesSmall` is
equivalent over `𝒞_Λ` to the one in `AlgebraicGeometry.CurveFamily`
(`Deformation.Artin.predeformationEquivalenceOfEquivalenceOver`), which is unobstructed exactly
when `Def_X` is (`Deformation.Examples.isSmooth_baseProjection_schemeDeformation_iff_curves`). -/
theorem isSmooth_baseProjection_curvesSmall_iff_schemeDeformation :
    letI := (predeformationCategory iΛ ((curvesSmallBased B hZ).p ⋙ Over.post B.inclusion)
      (curvesSmallPoint B hZ X hk hdim) (curvesSmallPoint_lies_over B hZ X hk hdim iΛ)).category
    IsSmooth (baseProjection (predeformationCategory iΛ
        ((curvesSmallBased B hZ).p ⋙ Over.post B.inclusion) (curvesSmallPoint B hZ X hk hdim)
        (curvesSmallPoint_lies_over B hZ X hk hdim iΛ)).projection) ↔
      IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) X)) := by
  let := (predeformationCategory iΛ ((curvesSmallBased B hZ).p ⋙ Over.post B.inclusion)
    (curvesSmallPoint B hZ X hk hdim) (curvesSmallPoint_lies_over B hZ X hk hdim iΛ)).category
  let := (predeformationCategory iΛ
    ((curvesFiberedCategory B hZ).val.p ⋙ Over.post B.inclusion)
    (curveFamilyOfScheme X B hZ hk hdim)
    (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)).category
  have hpX : (curvesFiberedCategory B hZ).val.p.IsFiberedInGroupoids :=
    (curvesFiberedCategory B hZ).property
  exact ((isSmooth_baseProjection_iff_of_equivalenceOver
    (predeformationEquivalenceOfEquivalenceOver B hZ iΛ (curvesFiberedCategory B hZ).val.p
      (curvesSmallBased B hZ).p (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ) hpX
      (isFiberedInGroupoids_curvesSmall B hZ) (curvesSmallEquivalenceOver B hZ))).symm).trans
    (isSmooth_baseProjection_schemeDeformation_iff_curves B hZ X hk hdim iΛ).symm

/-- **The smooth locus of the stack of curves and deformations of a curve** (the equivalence of
Stacks 0DZU, over a general coefficient ring). Let `X` be a proper scheme of dimension at most one
over a field `k`, and let `Λ` be a Noetherian local ring, separated in its `𝔪`-adic topology, flat
over `ℤ`, with a surjection `Λ → k`. With `h` the algebraicity of the stack of curves (Stacks 0D5A)
and `hlfp` its local finite presentation over `Spec ℤ` (Stacks 0DSS), the point
`x₀ : Spec k ⟶ Curves` classifying `X` lies in the open substack where `Curves → Spec ℤ` is smooth
exactly when the deformation category `Def_X` over `𝒞_Λ` is unobstructed. -/
theorem smoothLocus_property_curvesSmallPoint_iff
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    {W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)}
    (hW : Stack.IsSmoothLocus B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W)
    [IsLocalRing Λ] [IsNoetherianRing Λ] [IsHausdorff (IsLocalRing.maximalIdeal Λ) Λ]
    (hsurj : Function.Surjective (algebraMap Λ k))
    (hflat : ∀ f : Spec (.of Λ) ⟶ integerBase, Flat f) :
    W.property (curvesSmallPoint B hZ X hk hdim) ↔
      IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) X)) := by
  classical
  have hΛ : B.Contains (Spec (.of Λ)) := BigFppfSite.contains_spec_of_isHausdorff B hsurj hk
  let g : B.obj hΛ ⟶ B.obj hZ := ObjectProperty.homMk (specULiftZIsTerminal.from _)
  let 𝒳 := curvesAlgebraicStack B hZ h
  let P := Stack.algebraicStackBaseChangeSquare B (Spec (.of Λ)) integerBase hΛ hZ g 𝒳
  let 𝒳Λ := Stack.algebraicStackBaseChange B (Spec (.of Λ)) integerBase hΛ hZ g 𝒳
  let T : Over (Spec (.of Λ)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)))
  have hT : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj (curvesSmallPoint B hZ X hk hdim) =
      (Over.map (B.inclusion.map g)).obj T :=
    curvesSmallPoint_lies_over B hZ X hk hdim (B.inclusion.map g)
  let φ₀ := Stack.algebraicStackBaseChangeFactor B (Spec (.of Λ)) integerBase hΛ hZ g 𝒳 _ T hT
  let x₀' := Stack.algebraicStackBaseChangeLift B (Spec (.of Λ)) integerBase hΛ hZ g 𝒳 _ φ₀
  have hx₀' : (𝒳Λ.val.val.p ⋙ Over.post B.inclusion).obj x₀' =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ 𝟙 _) := by
    rw [Category.comp_id]
    exact Stack.algebraicStackBaseChangeLift_factor_post B (Spec (.of Λ)) integerBase hΛ hZ g 𝒳 _
      T hT
  obtain ⟨W', hW', -⟩ := (Stack.smoothLocus B integerBase hZ P.fst).1
  have h4 := (Stack.smoothLocus B integerBase hZ (Stack.structureMorphism B integerBase hZ 𝒳)).2.2.2
    hlfp _ _ P (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B integerBase hZ _ _)
    (Stack.isFlat_structureMorphism_schemeStack.{u, w} B integerBase hZ (Over.mk g) (hflat _))
    W W' hW hW'
  obtain ⟨W'', hW''eq, hW''⟩ :=
    Stack.exists_isSmoothLocus_changeBaseStructureMorphism_algebraicStackBaseChange B
      (Spec (.of Λ)) integerBase hΛ hZ g 𝒳 W' hW'
  obtain ⟨WΛ, hWΛ, -⟩ :=
    (Stack.smoothLocus B (Spec (.of Λ)) hΛ (Stack.structureMorphism B (Spec (.of Λ)) hΛ 𝒳Λ)).1
  have hloc : WΛ.property x₀' ↔ W.property (curvesSmallPoint B hZ X hk hdim) := by
    rw [Stack.IsSmoothLocus.property_eq_changeBase B (Spec (.of Λ)) integerBase hΛ hZ g hWΛ hW'',
      hW''eq, h4]
    rfl
  let D : Stack.VersalSituation.{u, w} :=
    { B := B, S := Spec (.of Λ), hS := hΛ, 𝒳 := 𝒳Λ
      locallyFiniteType := Stack.isLocallyOfFiniteType_structureMorphism_algebraicStackConstructionB
        B (Spec (.of Λ)) integerBase hΛ hZ g _
        (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase
          hZ (Stack.AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B integerBase hZ _ _ P
            (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B integerBase hZ _ _)
            hlfp)) }
  have : Module.Finite Λ k := module_finite_of_surjective_algebraMap hsurj
  have hfin := locallyOfFiniteType_and_quasiCompact_spec_map_of_surjective hsurj
  obtain ⟨A, hA⟩ := Stack.exists_isVersalRingAt D (𝟙 _) inferInstance x₀' hx₀' hfin
  exact hloc.symm.trans (((Stack.tfae_smoothLocus_formallySmooth_unobstructed D hWΛ (𝟙 _)
    inferInstance x₀' hx₀' hfin A hA).out 1 3).trans
    ((Stack.isSmooth_baseProjection_algebraicStackBaseChange_iff B (Spec (.of Λ)) integerBase
      hΛ hZ g 𝒳 (𝟙 _) _ φ₀ hx₀'
      (curvesSmallPoint_lies_over B hZ X hk hdim (𝟙 _ ≫ B.inclusion.map g))).trans
      (isSmooth_baseProjection_curvesSmall_iff_schemeDeformation B hZ X hk hdim _)))

/-- **The smooth locus of the stack of curves and deformations of a curve, over a Cohen ring**
(the equivalence of Stacks 0DZU). Let `X` be a proper scheme of dimension at most one over a field
`k` and `Λ` a Cohen ring for `k`. With `h` the algebraicity of the stack of curves (Stacks 0D5A)
and `hlfp` its local finite presentation over `Spec ℤ` (Stacks 0DSS), the classifying morphism
`Spec k ⟶ Curves` of `X` factors through the open substack where `Curves → Spec ℤ` is smooth
exactly when the deformation category `Def_X` over `𝒞_Λ` is unobstructed. -/
theorem smoothLocus_property_curvesSmallPoint_iff_of_isCohenRing
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    {W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)}
    (hW : Stack.IsSmoothLocus B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W)
    [IsDomain Λ] [IsCohenRing Λ] (hsurj : Function.Surjective (algebraMap Λ k)) :
    W.property (curvesSmallPoint B hZ X hk hdim) ↔
      IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) X)) :=
  smoothLocus_property_curvesSmallPoint_iff B hZ X hk hdim h hlfp hW hsurj
    flat_of_isCohenRing

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ModuliStableCurvesOfGenus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StabilizationMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelExists
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelGlue
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelUniqueHom

/-!
# The stabilization morphism `Curves^{prestable}_g → 𝓜̄_g` (Stacks 0E8B)

Let `g ≥ 2`. Stacks 0E8B constructs a morphism of algebraic stacks over `ℤ`
$$stabilization : Curves^{prestable}_g → \overline{\mathcal M}_g$$
sending a prestable family of curves `X → S` of genus `g` to the stable family `Y → S` associated
to it in Stacks 0E8A: the target of the unique morphism `c : X → Y` over `S` with
`𝒪_Y = c_*𝒪_X`, `R¹c_*𝒪_X = 0` universally, inducing on every fibre the contraction of rational
tails and bridges.

## Main definitions

* `AlgebraicGeometry.stabilizationMorphism`: the stabilization 1-morphism
  `Curves^{prestable}_g ⟶ 𝓜̄_g`.

## Main results

* `AlgebraicGeometry.stabilizationMorphism_obj`: it sends a prestable family `X` of genus `g` to
  a stable model of `X` in the sense of Stacks 0E8A, over the base of `X`.

## Implementation notes

The construction of Stacks 0E8A is compatible with base change
(`AlgebraicGeometry.C1590Private.IsStableModel.of_hom`) and unique up to unique isomorphism, so in
the language of Properties of Stacks, Section 04XA it defines a morphism of stacks: this is
`AlgebraicGeometry.C1590Private.modelFunctor`.

The existence of the stable model is `AlgebraicGeometry.C1590Private.exists_isStableModel` (Stacks
0E8A), whose inputs are the étale local scheme charts of families of curves (Stacks 0E6F,
`AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts`) and the openness of the stable locus
(Stacks 0E76, `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily`).

The source and target are the substacks `Curves^{prestable}_g` (Stacks 0E6V) and `𝓜̄_g`
(Stacks 0E78) of the stack of curves, as categories fibred in groupoids over the big fppf site of
`Spec(ℤ)`; a morphism of algebraic stacks over `ℤ` is a 1-morphism of these (Stacks 04XA, 026O).
Both are open substacks of `Curves`, which is algebraic by Stacks 0D5A, and so are algebraic; that
algebraicity is a property of the source and target and not part of the morphism, and is not
restated here.

## References

* [Stacks Project, Tag 0E8B](https://stacks.math.columbia.edu/tag/0E8B)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 04XA](https://stacks.math.columbia.edu/tag/04XA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace C1590Private

/-- Stable models of prestable families of genus `g ≥ 2` form a model relation (Stacks 0E8A,
uniqueness). -/
theorem isModelRelation_stabilization (g : ℕ) (hg : 2 ≤ g) :
    IsModelRelation (fun X Y (b : X.base ⟶ Y.base) c =>
      IsPrestableCurveFamily B hZ X ∧ IsStableModel B hZ g b c) :=
  isModelRelation_isStableModel_of_exists_hom
    fun hX h₁ h₂ => IsStableModel.exists_hom (hasEtaleLocalSchemeCharts B hZ) hX hg h₁ h₂

/-- A prestable family of genus `g ≥ 2` has a stable model (Stacks 0E8A, existence). -/
theorem exists_stabilization (g : ℕ) (hg : 2 ≤ g) (X : CurveFamily B hZ)
    (hX : IsPrestableCurveFamilyOfFibreGenus B hZ g X) :
    ∃ (Y : CurveFamily B hZ) (b : X.base ⟶ Y.base) (c : X.total ⟶ Y.total),
      IsPrestableCurveFamily B hZ X ∧ IsStableModel B hZ g b c := by
  obtain ⟨Y, b, c, h⟩ := exists_isStableModel (hasEtaleLocalSchemeCharts B hZ)
    (isOpenCurvesLocus_isStableCurveFamily B hZ) hg hX.1 hX.2
  exact ⟨Y, b, c, hX.1, h⟩

/-- The target of a stable model of genus `g` is a stable family of genus `g`. -/
theorem isStableCurveFamilyOfFibreGenus_of_stabilization (g : ℕ) {X Y : CurveFamily B hZ}
    {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total}
    (h : IsPrestableCurveFamily B hZ X ∧ IsStableModel B hZ g b c) :
    IsStableCurveFamilyOfFibreGenus B hZ g Y :=
  ⟨h.2.isStable, h.2.hasFibresOfGenus⟩

end C1590Private

/-- For `g ≥ 2`, the stabilization morphism `Curves^{prestable}_g ⟶ 𝓜̄_g` of stacks over `ℤ`, a
1-morphism of categories fibred in groupoids over the big fppf site of `Spec(ℤ)`. It sends a
prestable family of curves `X → S` of genus `g` to the stable family `Y → S` of Stacks 0E8A
(`AlgebraicGeometry.stabilizationMorphism_obj`). -/
@[stacks 0E8B "the stabilization morphism Curves^{prestable}_g → Mbar_g"]
def stabilizationMorphism (g : ℕ) (hg : 2 ≤ g) :
    curvesPrestableOfGenus B hZ g ⟶ moduliStableCurvesOfGenus B hZ g :=
  modelFunctor (isPrestableCurveFamilyOfFibreGenus_of_hom B hZ g)
    (isStableCurveFamilyOfFibreGenus_of_hom B hZ g) (isModelRelation_stabilization B hZ g hg)
    (exists_stabilization B hZ g hg) (isStableCurveFamilyOfFibreGenus_of_stabilization B hZ g)

/-- The stabilization morphism sends a prestable family of curves `X → S` of genus `g ≥ 2` to a
stable family `Y → S` over the same base together with a morphism `c : X → Y` over `S` which is the
stable model of Stacks 0E8A: `Y` is stable with fibres of genus `g`, `𝒪_Y = c_*𝒪_X` and
`R¹c_*𝒪_X = 0` after every base change, and on every fibre `c` is the contraction of rational tails
and bridges. -/
@[stacks 0E8B "it sends a prestable family X → S of genus g to its stable model Y → S of 0E8A"]
theorem stabilizationMorphism_obj (g : ℕ) (hg : 2 ≤ g)
    (X : (curvesPrestableOfGenus B hZ g).val.obj) :
    ∃ (h : ((stabilizationMorphism B hZ g hg).hom.obj X).obj.base = X.obj.base)
      (c : X.obj.total ⟶ ((stabilizationMorphism B hZ g hg).hom.obj X).obj.total),
      IsStableModel B hZ g (eqToHom h.symm) c :=
  (modelFunctor_obj (isPrestableCurveFamilyOfFibreGenus_of_hom B hZ g)
    (isStableCurveFamilyOfFibreGenus_of_hom B hZ g) (isModelRelation_stabilization B hZ g hg)
    (exists_stabilization B hZ g hg) (isStableCurveFamilyOfFibreGenus_of_stabilization B hZ g)
    X).imp fun _ ⟨c, hc⟩ => ⟨c, hc.2⟩

end AlgebraicGeometry

end

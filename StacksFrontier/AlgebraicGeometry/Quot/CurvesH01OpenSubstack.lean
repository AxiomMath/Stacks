module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayDimOne
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01BettiInput
public import StacksFrontier.AlgebraicGeometry.Quot.H0FibreRankSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiZeroGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The open substack `Curves^{h0,1}` of the stack of curves (Stacks 0E6I)

This file proves Stacks 0E6I: the families of curves `f : X → S` with `f_*𝒪_X = 𝒪_S` universally
and fibres of dimension `1` form an open substack `Curves^{h0,1} ⊂ Curves`, the classifying
morphism of a family of curves factors through it exactly when the family has these properties, and
for a scheme `X` proper over a field `k` with `dim(X) ≤ 1` the classifying morphism
`Spec k → Curves` of `X` factors through it exactly when `H⁰(X, 𝒪_X) = k` and `dim(X) = 1`.

## Main results

* `AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff`:
  **Stacks 0E6I**, the open substack together with its parts (1) and (2).

## Implementation notes

Part (2) assumes of `X ⟶ Spec k` only what the source does: properness and `dim(X) ≤ 1`. The
remaining conditions that `AlgebraicGeometry.curveFamilyOfSchemeMorphism` needs in order to read
the morphism as a family of curves are consequences of those and are supplied here rather than
assumed — flatness and local finite presentation because the base is the spectrum of a field
(`AlgebraicGeometry.flat_of_eq_spec_field`,
`AlgebraicGeometry.locallyOfFinitePresentation_of_eq_spec_field`), and the space-level
quasi-compactness, separatedness and quasi-separatedness because they are those of the proper
morphism of schemes (`AlgebraicGeometry.Space.isQuasiCompact_yoneda_map`,
`AlgebraicGeometry.Space.isSeparated_yoneda_map_iff`,
`AlgebraicGeometry.Space.isQuasiSeparated_yoneda_map_iff`).

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- There is an open substack `Curves^{h0,1} ⊂ Curves` of the stack of curves — the strictly full
subcategory of families with `f_*𝒪_X = 𝒪_S` universally and fibres of dimension `1` is invariant
under isomorphism and its inclusion is representable by algebraic spaces and an open immersion —
such that
1. the classifying morphism of a family of curves `f : X → S` factors through `Curves^{h0,1}`
   exactly when `f_*𝒪_X = 𝒪_S`, this holds after arbitrary base change, and the fibres of `f`
   have dimension `1`;
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
   `Spec k → Curves` of `X` factors through `Curves^{h0,1}` exactly when `H⁰(X, 𝒪_X) = k` and
   `dim(X) = 1`. -/
@[stacks 0E6I]
theorem curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily (B := B) (hZ := hZ)).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily (B := B) (hZ := hZ)).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        IsH01CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅
        curveFamilyOfSchemeMorphism B hZ g (flat_of_eq_spec_field _ k hW) hproper
          (locallyOfFinitePresentation_of_eq_spec_field _ k hW)
          (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
          ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
          ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1)) :=
  have h := curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_betti
    (B := B) (hZ := hZ) fun f hf hfl hfp =>
      Space.exists_upperSemicontinuous_h0FibreRank f hf hfl hfp
  ⟨h.1, h.2.1, fun g k _ hW hproper hdim U y hy e =>
    h.2.2 g k hW _ hproper _ _ _ _ hdim U y hy e⟩

end AlgebraicGeometry

end

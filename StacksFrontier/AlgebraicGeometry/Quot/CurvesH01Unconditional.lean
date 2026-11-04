module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01BettiInput
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodalOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiZeroGlobalFunctions

/-!
# The open substack `Curves^{h0,1}` (Stacks 0E6I)

This file states and proves Stacks 0E6I with no hypotheses beyond the source's. There is an open
substack `Curves^{h0,1} ⊂ Curves` such that
1. the classifying morphism of a family of curves `f : X → S` factors through it if and only if
   `f_*𝒪_X = 𝒪_S`, this holds after arbitrary base change, and the fibres of `f` have
   dimension `1`;
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
   `Spec(k) → Curves` factors through it if and only if `H⁰(X, 𝒪_X) = k` and `dim(X) = 1`.

## Main results

* `AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_properOverField_iff`:
  Stacks 0E6I, parts (1) and (2).

## Implementation notes

The `Spec(k)`-family of part (2) is
`AlgebraicGeometry.curveFamilyOfProperOverFieldEqSpec`, which asks only that `X → Spec(k)` be
proper and `dim(X) ≤ 1`: flatness, finite presentation and the space-level quasi-compactness and
(quasi-)separatedness are discharged there. `H⁰(X, 𝒪_X) = k` is the bijectivity of the composite
`k ≅ Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0D4R](https://stacks.math.columbia.edu/tag/0D4R)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- `Curves^{h0,1}`, the strictly full subcategory of `Curves` of families of curves `f : X → S`
with `f_*𝒪_X = 𝒪_S`, this holding after arbitrary base change, and whose fibres have dimension `1`
(`AlgebraicGeometry.IsH01CurveFamily`), is an open substack of `Curves`: it is closed under
isomorphisms and its inclusion `curvesSubstackInclusion` is representable by algebraic spaces and
an open immersion. Moreover
1. for a family of curves over a scheme `S = U`, classified by `y` (a morphism over `U` from the
   site of `U` to `Curves`), the classifying morphism factors through `Curves^{h0,1}` if and only
   if the family `y(U)` has `f_*𝒪_X = 𝒪_S`, universally, and fibres of dimension `1`;
2. for a scheme `X = T` proper over a field `k` (the scheme of `W` being `Spec k`) with
   `dim(X) ≤ 1`, and `y` a classifying morphism `Spec(k) → Curves` of the attached family of
   curves, `y` factors through `Curves^{h0,1}` if and only if `k ⟶ H⁰(X, 𝒪_X)` is bijective and
   `dim(X) = 1`. -/
@[stacks 0E6I "the open substack Curves^{h0,1} of Curves (closed under isomorphisms, inclusion \
representable by algebraic spaces and an open immersion), with (1) for a family of curves \
f : X → S, the classifying morphism factors through it iff f_*O_X = O_S, universally, and the \
fibres have dimension 1, and (2) for a scheme X proper over a field k with dim(X) ≤ 1, the \
classifying morphism Spec(k) → Curves factors through it iff H^0(X, O_X) = k and dim(X) = 1. \
Unconditional: 0E0R at i = 0 and 0E6B (a) are proved, not assumed"]
theorem curvesH01_isOpenSubstack_and_factors_iff_and_properOverField_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          CurveFamily.isOpenCurvesLocus_isH01CurveFamily.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          CurveFamily.isOpenCurvesLocus_isH01CurveFamily.prop_of_hom)) ∧
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
      (y : BigFppfOver B W.left.1 W.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map W.hom →
      (y.obj (Over.mk (𝟙 W.left)) ≅ curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) →
      ((∃ z : BigFppfOver B W.left.1 W.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1)) := by
  have hP := CurveFamily.isOpenCurvesLocus_isH01CurveFamily (B := B) (hZ := hZ)
  have hpush : ∀ X : CurveFamily B hZ,
      CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
        HasUniversallyBijectiveGlobalFunctions B hZ X := fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      (Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ) hX
  refine ⟨isOpenImmersion_curvesSubstackInclusion hP,
    fun U y hy => factors_curvesSubstack_iff hP U y hy,
    fun {T W} g k _ hW hproper hdim y hy e => ?_⟩
  have := hproper
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g) :=
    inferInstance
  have hk : Function.Bijective ⇑(Scheme.ΓSpecIso (.of k)).inv :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hcomp : ⇑((Scheme.ΓSpecIso (.of k)).inv ≫
      ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop) =
      ⇑((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∘
        ⇑(Scheme.ΓSpecIso (.of k)).inv := by
    funext x
    exact ConcreteCategory.comp_apply _ _ x
  rw [hcomp, Function.Bijective.of_comp_iff _ hk]
  exact (factors_curvesSubstack_iff_of_iso hP W y hy _ e).trans
    (CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW _ hproper _ _ _
      _ hdim)

end AlgebraicGeometry

end

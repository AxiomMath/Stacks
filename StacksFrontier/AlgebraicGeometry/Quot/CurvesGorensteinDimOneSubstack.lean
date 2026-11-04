module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGorenstein
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGorensteinDimOne
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackOfAlgebraicStack

/-!
# The open substack of Gorenstein curves of relative dimension one (Stacks 0E6M)

The property of a family of curves `X → S` that `X → S` be Gorenstein (Tag 0E14) and have
relative dimension one (Tag 06LR) satisfies condition (o) of Section 0E0E: a Gorenstein morphism
is Cohen–Macaulay (Tag 0C06), so the property is that of `Curves^{Gorenstein}` (Tag 0E1M)
intersected with the locus of relative dimension one, which is open over a Cohen–Macaulay family
(Tag 0E1F). So by Stacks 0E0E the families of curves having it form a strictly full subcategory
`Curves^{Gorenstein,1}` of the category fibred in groupoids `Curves` of families of curves whose
inclusion is representable by algebraic spaces and an open immersion, and:

1. given a family of curves `X → S`, the classifying morphism `S → Curves` factors through
   `Curves^{Gorenstein,1}` if and only if `X → S` is Gorenstein and has relative dimension one;
2. given a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
   `Spec(k) → Curves` factors through `Curves^{Gorenstein,1}` if and only if `X` is Gorenstein
   and equidimensional of dimension one.

The same property cuts an open substack, in the sense of Stacks 04YM, out of every algebraic
stack `𝒳` equipped with a `1`-morphism to `Curves`, with the same two characterizations.

## Main definitions

* `AlgebraicGeometry.curvesGorensteinDimOneOpenSubstack`: the open substack of an algebraic stack
  over the category of curves cut out by the families which are Gorenstein of relative dimension
  one.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff`: Stacks 0E1M in
  the form taken by `AlgebraicGeometry.isOpenCurvesLocus_isGorensteinDimOneFamily`, condition (o)
  of Section 0E0E for Gorenstein families together with its reading over a field.
* `AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion_gorensteinDimOne`:
  **Stacks 0E6M**, the inclusion `Curves^{Gorenstein,1} ⊂ Curves` is representable by algebraic
  spaces and an open immersion.
* `AlgebraicGeometry.factorsThrough_curvesSubstack_gorensteinDimOne_iff`: **Stacks 0E6M**,
  part (1).
* `AlgebraicGeometry.factorsThrough_curvesSubstack_gorensteinDimOne_over_field_iff`:
  **Stacks 0E6M**, part (2).
* `AlgebraicGeometry.factorsThrough_curvesGorensteinDimOneOpenSubstack_iff` and
  `AlgebraicGeometry.factorsThrough_curvesGorensteinDimOneOpenSubstack_over_field_iff`: the two
  characterizations for the open substack of an algebraic stack over the category of curves.

## Implementation notes

`Curves` is the category fibred in groupoids `AlgebraicGeometry.curvesFiberedCategory` of
Situation 0D4Z, and the open-immersion conclusion is that of Stacks 04XB, which needs no
algebraicity. An open substack in the sense of Stacks 04YM is a strictly full subcategory of an
*algebraic* stack which is itself algebraic: for `Curves^{Gorenstein,1} ⊂ Curves` that is the
algebraicity of the stack of curves (Stacks 0D5A), at which
`AlgebraicGeometry.curvesGorensteinDimOneOpenSubstack` applies to the small model of `Curves`
with its comparison functor to families of curves.

A classifying morphism of a family `X → S` is a scheme-valued point `z : (Sch/S) → Curves`
together with an isomorphism `z(S) ≅ X`, a classifying morphism being determined only up to
2-isomorphism. In part (2) the family of curves of `X → Spec(k)` is
`AlgebraicGeometry.curveFamilyOfSchemeMorphism`, all of whose hypotheses hold for a proper
scheme of dimension at most one over a field. "Equidimensional of dimension one" is read as in
Tag 0058: all irreducible components have the same dimension, and that dimension is one; so the
empty scheme, which is Gorenstein of relative dimension one, is included.

## References

* [Stacks Project, Tag 0E6M](https://stacks.math.columbia.edu/tag/0E6M)
* [Stacks Project, Tag 0E1M](https://stacks.math.columbia.edu/tag/0E1M)
* [Stacks Project, Tag 0E1F](https://stacks.math.columbia.edu/tag/0E1F)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0C06](https://stacks.math.columbia.edu/tag/0C06)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 0058](https://stacks.math.columbia.edu/tag/0058)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0E1M, in the form of `AlgebraicGeometry.isOpenCurvesLocus_isGorensteinDimOneFamily`.**
Condition (o) of Section 0E0E for Gorenstein families of curves, together with its reading on
the family of curves of a proper scheme of dimension at most one over a field: that family is
Gorenstein exactly when the scheme is. -/
theorem isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff :
    IsOpenCurvesLocus B hZ (fun X : CurveFamily B hZ => Space.IsGorenstein B integerBase hZ
        X.toBase.hom) ∧
      ∀ {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
        (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
        (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
        (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
        (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
        (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
        (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
        (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
        (k : Type u) [Field k],
        (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k) →
        (Space.IsGorenstein B integerBase hZ
            (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase.hom ↔
          IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T)) :=
  ⟨isOpenCurvesLocus_isGorensteinFamily B hZ, fun g _ hproper _ _ _ _ hdim k _ hU =>
    isGorensteinFamily_curveFamilyOfSchemeMorphism_iff B hZ g k hU hproper hdim⟩

/-- **`Curves^{Gorenstein,1}` is open in `Curves`.** The inclusion into the category fibred in
groupoids of families of curves of the full subcategory `Curves^{Gorenstein,1}` of the families
which are Gorenstein of relative dimension one is representable by algebraic spaces and an open
immersion. -/
@[stacks 0E6M "the inclusion of Curves^{Gorenstein,1} into Curves is representable by algebraic \
spaces and an open immersion"]
theorem isOpenImmersion_curvesSubstackInclusion_gorensteinDimOne :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGorensteinDimOneFamily B hZ)
          (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ
            (isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff B hZ)).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGorensteinDimOneFamily B hZ)
          (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ
            (isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff B hZ)).prop_of_hom) :=
  (curvesGorensteinDimOne_isOpenSubstack B hZ
    (isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff B hZ)).2

/-- Gorenstein families of relative dimension one form an open locus of curves. -/
private theorem isOpenCurvesLocus_gorensteinDimOneFamily :
    IsOpenCurvesLocus B hZ (IsGorensteinDimOneFamily B hZ) :=
  isOpenCurvesLocus_isGorensteinDimOneFamily B hZ
    (isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff B hZ)

/-- Let `X → S` be a family of curves and `z : (Sch/S) → Curves` a classifying morphism for it, a
scheme-valued point together with an isomorphism `z(S) ≅ X`. Then `z` factors through
`Curves^{Gorenstein,1}`, over the site and up to a 2-isomorphism, if and only if `X → S` is
Gorenstein and has relative dimension one. -/
@[stacks 0E6M "part (1)"]
theorem factorsThrough_curvesSubstack_gorensteinDimOne_iff
    (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : z.obj (Over.mk (𝟙 S.left)) ≅ X) :
    (∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
          Stack.objectPropertySubcategory B integerBase hZ (curvesFiberedCategory B hZ).val
            (IsGorensteinDimOneFamily B hZ),
        Nonempty (g.comp (Stack.objectPropertyInclusion B integerBase hZ
          (curvesFiberedCategory B hZ).val (IsGorensteinDimOneFamily B hZ)) ≅
            { toFunctor := z, w := hz })) ↔
      Space.IsGorenstein B integerBase hZ X.toBase.hom ∧
        Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom :=
  factorsThrough_curvesSubstack_iff (isOpenCurvesLocus_gorensteinDimOneFamily B hZ) S z hz X ξ

/-- Let `g : T ⟶ W` be a morphism of the big fppf site of the integers whose target scheme is the
spectrum of a field `k`, whose underlying morphism of schemes is proper, and whose source scheme
`X` has dimension at most one, and let `z : (Sch/Spec(k)) → Curves` classify the family of curves
of `g`. Then `z` factors through `Curves^{Gorenstein,1}` if and only if `X` is Gorenstein and
equidimensional of dimension one, every irreducible component of it having dimension one. -/
@[stacks 0E6M "part (2)"]
theorem factorsThrough_curvesSubstack_gorensteinDimOne_over_field_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map W.hom)
    (ξ : z.obj (Over.mk (𝟙 W.left)) ≅ curveFamilyOfSchemeMorphism B hZ g
      (flat_of_eq_spec_field _ k hW) hproper
      (locallyOfFinitePresentation_of_eq_spec_field _ k hW)
      (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
      ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
      ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) :
    (∃ q : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
          Stack.objectPropertySubcategory B integerBase hZ (curvesFiberedCategory B hZ).val
            (IsGorensteinDimOneFamily B hZ),
        Nonempty (q.comp (Stack.objectPropertyInclusion B integerBase hZ
          (curvesFiberedCategory B hZ).val (IsGorensteinDimOneFamily B hZ)) ≅
            { toFunctor := z, w := hz })) ↔
      (IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        TopologicalSpace.Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        ∀ C ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
          topologicalKrullDim C = (1 : WithBot ℕ∞)) :=
  (factorsThrough_curvesSubstack_over_field_iff (isOpenCurvesLocus_gorensteinDimOneFamily B hZ)
    g k hW hproper hdim z hz ξ).trans
    (isGorensteinDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ
      (isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff B hZ) g _ hproper _ _ _ _ hdim k hW)

/-! ### Over an algebraic stack with a `1`-morphism to the category of curves -/

variable {B hZ} {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
  (F : 𝒳.val.val ⥤ᵇ (curvesFiberedCategory B hZ).val)

/-- **The open substack of Gorenstein curves of relative dimension one.** For an algebraic stack
`𝒳` with a `1`-morphism `F` to the category of curves, the full subcategory of `𝒳` on the objects
whose family of curves is Gorenstein of relative dimension one is an open substack of `𝒳`. At the
stack of curves this is `Curves^{Gorenstein,1} ⊂ Curves`. -/
def curvesGorensteinDimOneOpenSubstack : Stack.OpenSubstack 𝒳 :=
  curvesOpenSubstack F (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ
    (isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff B hZ))

/-- The objects of the open substack of Gorenstein curves of relative dimension one are those
whose family of curves is Gorenstein of relative dimension one. -/
@[simp]
theorem curvesGorensteinDimOneOpenSubstack_property (x : 𝒳.val.val.obj) :
    (curvesGorensteinDimOneOpenSubstack F).property x ↔
      IsGorensteinDimOneFamily B hZ (F.obj x) :=
  Iff.rfl

/-- **The first characterization of the open substack.** A scheme-valued point of `𝒳` with values
in `S` classifying a family of curves `X → S`, in the sense that `F` sends its value at `S` to a
family isomorphic to `X`, factors through the open substack of Gorenstein curves of relative
dimension one if and only if `X → S` is Gorenstein and has relative dimension one. -/
theorem factorsThrough_curvesGorensteinDimOneOpenSubstack_iff (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : F.obj (z.obj (Over.mk (𝟙 S.left))) ≅ X) :
    (∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
          Stack.fullSubcategoryBased 𝒳 (curvesGorensteinDimOneOpenSubstack F).property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳
          (curvesGorensteinDimOneOpenSubstack F).property) ≅ { toFunctor := z, w := hz })) ↔
      Space.IsGorenstein B integerBase hZ X.toBase.hom ∧
        Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom :=
  factorsThrough_curvesOpenSubstack_iff F (isOpenCurvesLocus_gorensteinDimOneFamily B hZ) S z hz X ξ

/-- **The second characterization of the open substack.** A scheme-valued point of `𝒳` with
values in the spectrum of a field `k` classifying the family of curves of a proper scheme `X`
over `k` with `dim(X) ≤ 1` factors through the open substack of Gorenstein curves of relative
dimension one if and only if `X` is Gorenstein and equidimensional of dimension one. -/
theorem factorsThrough_curvesGorensteinDimOneOpenSubstack_over_field_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map W.hom)
    (ξ : F.obj (z.obj (Over.mk (𝟙 W.left))) ≅ curveFamilyOfSchemeMorphism B hZ g
      (flat_of_eq_spec_field _ k hW) hproper
      (locallyOfFinitePresentation_of_eq_spec_field _ k hW)
      (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
      ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
      ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) :
    (∃ q : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
          Stack.fullSubcategoryBased 𝒳 (curvesGorensteinDimOneOpenSubstack F).property,
        Nonempty (q.comp (Stack.fullSubcategoryBasedInclusion 𝒳
          (curvesGorensteinDimOneOpenSubstack F).property) ≅ { toFunctor := z, w := hz })) ↔
      (IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        TopologicalSpace.Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        ∀ C ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
          topologicalKrullDim C = (1 : WithBot ℕ∞)) :=
  (factorsThrough_curvesOpenSubstack_iff F (isOpenCurvesLocus_gorensteinDimOneFamily B hZ) W z hz
    _ ξ).trans
    (isGorensteinDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ
      (isOpenCurvesLocus_isGorensteinFamily_and_over_field_iff B hZ) g _ hproper _ _ _ _ hdim k hW)

end AlgebraicGeometry

end

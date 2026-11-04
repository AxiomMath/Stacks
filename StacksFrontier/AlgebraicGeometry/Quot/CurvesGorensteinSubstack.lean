module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGorenstein
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackOfAlgebraicStack

/-!
# The open substack of Gorenstein curves (Stacks 0E1M)

The property of a family of curves `X → S` that `X → S` be Gorenstein (Tag 0E14) satisfies
condition (o) of Section 0E0E (`AlgebraicGeometry.isOpenCurvesLocus_isGorensteinFamily`): by
Tag 0E19 the Gorenstein locus of `X` is open and commutes with base change, and properness of
`X → S` carries it to an open of `S` with the same property. So by Stacks 0E0E the families of
curves having it form a strictly full subcategory `Curves^{Gorenstein}` of the category fibred in
groupoids `Curves` of families of curves whose inclusion is representable by algebraic spaces and
an open immersion, and:

1. given a family of curves `X → S`, the classifying morphism `S → Curves` factors through
   `Curves^{Gorenstein}` if and only if `X → S` is Gorenstein;
2. given a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
   `Spec(k) → Curves` factors through `Curves^{Gorenstein}` if and only if `X` is Gorenstein.

The same property cuts an open substack, in the sense of Stacks 04YM, out of every algebraic
stack `𝒳` equipped with a `1`-morphism to `Curves`, with the same two characterizations.

## Main definitions

* `AlgebraicGeometry.curvesGorensteinOpenSubstack`: the open substack of an algebraic stack over
  the category of curves cut out by the Gorenstein families.

## Main results

* `AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion_gorenstein`: **Stacks 0E1M**, the
  inclusion `Curves^{Gorenstein} ⊂ Curves` is representable by algebraic spaces and an open
  immersion.
* `AlgebraicGeometry.factorsThrough_curvesSubstack_gorenstein_iff`: **Stacks 0E1M**, part (1).
* `AlgebraicGeometry.factorsThrough_curvesSubstack_gorenstein_over_field_iff`: **Stacks 0E1M**,
  part (2).
* `AlgebraicGeometry.factorsThrough_curvesGorensteinOpenSubstack_iff` and
  `AlgebraicGeometry.factorsThrough_curvesGorensteinOpenSubstack_over_field_iff`: the two
  characterizations for the open substack of an algebraic stack over the category of curves.

## Implementation notes

`Curves` is the category fibred in groupoids `AlgebraicGeometry.curvesFiberedCategory` of
Situation 0D4Z, and the open-immersion conclusion is that of Stacks 04XB, which needs no
algebraicity. An open substack in the sense of Stacks 04YM is a strictly full subcategory of an
*algebraic* stack which is itself algebraic: for `Curves^{Gorenstein} ⊂ Curves` that is the
algebraicity of the stack of curves (Stacks 0D5A), at which
`AlgebraicGeometry.curvesGorensteinOpenSubstack` applies to the small model of `Curves` with its
comparison functor to families of curves.

A classifying morphism of a family `X → S` is a scheme-valued point `z : (Sch/S) → Curves`
together with an isomorphism `z(S) ≅ X`, a classifying morphism being determined only up to
2-isomorphism. In part (2) the family of curves of `X → Spec(k)` is
`AlgebraicGeometry.curveFamilyOfSchemeMorphism`, all of whose hypotheses hold for a proper
scheme of dimension at most one over a field.

## References

* [Stacks Project, Tag 0E1M](https://stacks.math.columbia.edu/tag/0E1M)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E19](https://stacks.math.columbia.edu/tag/0E19)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0E1M, `Curves^{Gorenstein}` is open in `Curves`.** The inclusion into the category
fibred in groupoids of families of curves of the full subcategory `Curves^{Gorenstein}` of the
Gorenstein families is representable by algebraic spaces and an open immersion. -/
@[stacks 0E1M "the inclusion of Curves^{Gorenstein} into Curves is representable by algebraic \
spaces and an open immersion"]
theorem isOpenImmersion_curvesSubstackInclusion_gorenstein :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGorensteinFamily B hZ)
          (isOpenCurvesLocus_isGorensteinFamily B hZ).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGorensteinFamily B hZ)
          (isOpenCurvesLocus_isGorensteinFamily B hZ).prop_of_hom) :=
  (isOpenImmersion_curvesSubstackInclusion (isOpenCurvesLocus_isGorensteinFamily B hZ)).2

/-- **Stacks 0E1M, part (1).** Let `X → S` be a family of curves and `z : (Sch/S) → Curves` a
classifying morphism for it, a scheme-valued point together with an isomorphism `z(S) ≅ X`.
Then `z` factors through `Curves^{Gorenstein}`, over the site and up to a 2-isomorphism, if and
only if `X → S` is Gorenstein. -/
@[stacks 0E1M "part (1)"]
theorem factorsThrough_curvesSubstack_gorenstein_iff
    (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : z.obj (Over.mk (𝟙 S.left)) ≅ X) :
    (∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
          Stack.objectPropertySubcategory B integerBase hZ (curvesFiberedCategory B hZ).val
            (IsGorensteinFamily B hZ),
        Nonempty (g.comp (Stack.objectPropertyInclusion B integerBase hZ
          (curvesFiberedCategory B hZ).val (IsGorensteinFamily B hZ)) ≅
            { toFunctor := z, w := hz })) ↔
      Space.IsGorenstein B integerBase hZ X.toBase.hom :=
  factorsThrough_curvesSubstack_iff (isOpenCurvesLocus_isGorensteinFamily B hZ) S z hz X ξ

/-- **Stacks 0E1M, part (2).** Let `g : T ⟶ W` be a morphism of the big fppf site of the integers
whose target scheme is the spectrum of a field `k`, whose underlying morphism of schemes is
proper, and whose source scheme `X` has dimension at most one, and let `z : (Sch/Spec(k)) →
Curves` classify the family of curves of `g`. Then `z` factors through `Curves^{Gorenstein}` if
and only if `X` is Gorenstein. -/
@[stacks 0E1M "part (2)"]
theorem factorsThrough_curvesSubstack_gorenstein_over_field_iff
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
            (IsGorensteinFamily B hZ),
        Nonempty (q.comp (Stack.objectPropertyInclusion B integerBase hZ
          (curvesFiberedCategory B hZ).val (IsGorensteinFamily B hZ)) ≅
            { toFunctor := z, w := hz })) ↔
      IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
  (factorsThrough_curvesSubstack_over_field_iff (isOpenCurvesLocus_isGorensteinFamily B hZ)
    g k hW hproper hdim z hz ξ).trans
    (isGorensteinFamily_curveFamilyOfSchemeMorphism_iff B hZ g k hW hproper hdim)

/-! ### Over an algebraic stack with a `1`-morphism to the category of curves -/

variable {B hZ} {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
  (F : 𝒳.val.val ⥤ᵇ (curvesFiberedCategory B hZ).val)

/-- **The open substack of Gorenstein curves.** For an algebraic stack `𝒳` with a `1`-morphism
`F` to the category of curves, the full subcategory of `𝒳` on the objects whose family of curves
is Gorenstein is an open substack of `𝒳`. At the stack of curves this is
`Curves^{Gorenstein} ⊂ Curves`. -/
def curvesGorensteinOpenSubstack : Stack.OpenSubstack 𝒳 :=
  curvesOpenSubstack F (isOpenCurvesLocus_isGorensteinFamily B hZ)

/-- The objects of the open substack of Gorenstein curves are those whose family of curves is
Gorenstein. -/
@[simp]
theorem curvesGorensteinOpenSubstack_property (x : 𝒳.val.val.obj) :
    (curvesGorensteinOpenSubstack F).property x ↔ IsGorensteinFamily B hZ (F.obj x) :=
  Iff.rfl

/-- **The first characterization of the open substack.** A scheme-valued point of `𝒳` with values
in `S` classifying a family of curves `X → S`, in the sense that `F` sends its value at `S` to a
family isomorphic to `X`, factors through the open substack of Gorenstein curves if and only if
`X → S` is Gorenstein. -/
theorem factorsThrough_curvesGorensteinOpenSubstack_iff (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : F.obj (z.obj (Over.mk (𝟙 S.left))) ≅ X) :
    (∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
          Stack.fullSubcategoryBased 𝒳 (curvesGorensteinOpenSubstack F).property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳
          (curvesGorensteinOpenSubstack F).property) ≅ { toFunctor := z, w := hz })) ↔
      Space.IsGorenstein B integerBase hZ X.toBase.hom :=
  factorsThrough_curvesOpenSubstack_iff F (isOpenCurvesLocus_isGorensteinFamily B hZ)
    S z hz X ξ

/-- **The second characterization of the open substack.** A scheme-valued point of `𝒳` with
values in the spectrum of a field `k` classifying the family of curves of a proper scheme `X`
over `k` with `dim(X) ≤ 1` factors through the open substack of Gorenstein curves if and only if
`X` is Gorenstein. -/
theorem factorsThrough_curvesGorensteinOpenSubstack_over_field_iff
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
          Stack.fullSubcategoryBased 𝒳 (curvesGorensteinOpenSubstack F).property,
        Nonempty (q.comp (Stack.fullSubcategoryBasedInclusion 𝒳
          (curvesGorensteinOpenSubstack F).property) ≅ { toFunctor := z, w := hz })) ↔
      IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
  (factorsThrough_curvesOpenSubstack_iff F (isOpenCurvesLocus_isGorensteinFamily B hZ)
    W z hz _ ξ).trans
    (isGorensteinFamily_curveFamilyOfSchemeMorphism_iff B hZ g k hW hproper hdim)

end AlgebraicGeometry

end

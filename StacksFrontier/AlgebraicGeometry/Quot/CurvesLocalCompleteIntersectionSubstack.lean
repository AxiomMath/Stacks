module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayDimOne
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackOfAlgebraicStack

/-!
# The open substack of local complete intersection curves (Stacks 0DZV)

The local complete intersection property of the structure morphism of a family of curves
satisfies condition (o) of Section 0E0E: its locus in the base is open and its formation commutes
with arbitrary base change (`AlgebraicGeometry.isOpenCurvesLocus_isLciFamily`). So by Stacks 0E0E
the families of curves having it form a strictly full subcategory `Curves^{lci}` of the category
fibred in groupoids `Curves` of families of curves whose inclusion is representable by algebraic
spaces and an open immersion, and:

1. given a family of curves `X → S` with a classifying morphism `S → Curves`, the following are
   equivalent: (a) the classifying morphism factors through `Curves^{lci}`, (b) `X → S` is a
   local complete intersection morphism, (c) `X → S` is syntomic;
2. given a proper scheme `X` of dimension at most one over a field `k`, the classifying morphism
   `Spec(k) → Curves` factors through `Curves^{lci}` if and only if `X` is a local complete
   intersection over `k`.

The same property cuts an open substack, in the sense of Stacks 04YM, out of every algebraic
stack `𝒳` equipped with a `1`-morphism `F : 𝒳 → Curves`, with the same two characterizations.

## Main definitions

* `AlgebraicGeometry.curvesLciOpenSubstack`: the open substack `𝒳^{lci}` of an algebraic stack
  over the category of curves.

## Main results

* `AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion_lci`: **Stacks 0DZV**, the
  inclusion `Curves^{lci} ⊂ Curves` is representable by algebraic spaces and an open immersion.
* `AlgebraicGeometry.factorsThrough_curvesSubstack_lci_tfae`: **Stacks 0DZV**, part (1), the
  equivalence of (a), (b) and (c).
* `AlgebraicGeometry.factorsThrough_curvesSubstack_lci_over_field_iff`: **Stacks 0DZV**,
  part (2), the equivalence of (a) and (b).
* `AlgebraicGeometry.factorsThrough_curvesLciOpenSubstack_tfae` and
  `AlgebraicGeometry.factorsThrough_curvesLciOpenSubstack_over_field_iff`: the two
  characterizations for the open substack of an algebraic stack over the category of curves.

## Implementation notes

`Curves` is the category fibred in groupoids `AlgebraicGeometry.curvesFiberedCategory` of
Situation 0D4Z, and the open-immersion conclusion is that of Stacks 04XB, which needs no
algebraicity. An open substack in the sense of Stacks 04YM is a strictly full subcategory of an
*algebraic* stack which is itself algebraic: for `Curves^{lci} ⊂ Curves` that is the
algebraicity of the stack of curves (Stacks 0D5A), at which
`AlgebraicGeometry.curvesLciOpenSubstack` applies to the small model of `Curves` with its
comparison functor to families of curves.

A classifying morphism of a family `X → S` is a scheme-valued point `z : (Sch/S) → Curves`
together with an isomorphism `z(S) ≅ X`, a classifying morphism being determined only up to
2-isomorphism. Over an algebraic stack `𝒳` with `F : 𝒳 → Curves` it is a scheme-valued point of
`𝒳` with values in `S` whose value at `S` is sent by `F` to a family isomorphic to `X`.

In part (2) the family of curves of the proper scheme `X → Spec(k)` is
`AlgebraicGeometry.curveFamilyOfSchemeMorphism`, its flatness and finite presentation discharged
over the field by `AlgebraicGeometry.flat_of_eq_spec_field` and
`AlgebraicGeometry.locallyOfFinitePresentation_of_eq_spec_field`, and its quasi-compactness,
separatedness and quasi-separatedness as a morphism of algebraic spaces read off from the
scheme-level properties of the proper morphism by Stacks 03KY.

## References

* [Stacks Project, Tag 0DZV](https://stacks.math.columbia.edu/tag/0DZV)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 06C9](https://stacks.math.columbia.edu/tag/06C9)
* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-! ### The open subcategory `Curves^{lci}` of the category of curves -/

section CurvesLci

variable (B hZ)

/-- **Stacks 0DZV, `Curves^{lci}` is open in `Curves`.** The inclusion into the category fibred
in groupoids of families of curves of the full subcategory `Curves^{lci}` of the families whose
structure morphism is a local complete intersection morphism is representable by algebraic spaces
and an open immersion. -/
@[stacks 0DZV "the inclusion of Curves^{lci} into Curves is representable by algebraic spaces \
and an open immersion"]
theorem isOpenImmersion_curvesSubstackInclusion_lci :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsLciFamily B hZ)
          (isOpenCurvesLocus_isLciFamily B hZ).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsLciFamily B hZ)
          (isOpenCurvesLocus_isLciFamily B hZ).prop_of_hom) :=
  (isOpenImmersion_curvesSubstackInclusion (isOpenCurvesLocus_isLciFamily B hZ)).2

/-- **Stacks 0DZV, part (1).** Let `X → S` be a family of curves and `z : (Sch/S) → Curves` a
classifying morphism for it, a scheme-valued point together with an isomorphism `z(S) ≅ X`.
Then the following are equivalent:

* (a) `z` factors through `Curves^{lci}`, over the site and up to a 2-isomorphism;
* (b) `X → S` is a local complete intersection morphism;
* (c) `X → S` is syntomic. -/
@[stacks 0DZV "part (1)"]
theorem factorsThrough_curvesSubstack_lci_tfae (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : z.obj (Over.mk (𝟙 S.left)) ≅ X) :
    List.TFAE
      [∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
            Stack.objectPropertySubcategory B integerBase hZ
              (curvesFiberedCategory B hZ).val (IsLciFamily B hZ),
          Nonempty (g.comp (Stack.objectPropertyInclusion B integerBase hZ
            (curvesFiberedCategory B hZ).val (IsLciFamily B hZ)) ≅ { toFunctor := z, w := hz }),
        Space.IsLocalCompleteIntersection B integerBase hZ X.toBase.hom,
        Space.IsSyntomic B integerBase hZ X.toBase.hom] := by
  tfae_have 1 ↔ 2 := factorsThrough_curvesSubstack_iff
    (isOpenCurvesLocus_isLciFamily B hZ) S z hz X ξ
  tfae_have 2 ↔ 3 := isLciFamily_iff_isSyntomicFamily B hZ X
  tfae_finish

/-- **Stacks 0DZV, part (2).** Let `g : T ⟶ W` be a morphism of the big fppf site of the integers
whose target scheme is the spectrum of a field `k`, whose underlying morphism of schemes is
proper, and whose source scheme `X` has dimension at most one, and let `z : (Sch/Spec(k)) →
Curves` classify the family of curves of `g`. Then `z` factors through `Curves^{lci}` if and only
if `X` is a local complete intersection over `k`, that is, `g` is a local complete intersection
morphism. -/
@[stacks 0DZV "part (2)"]
theorem factorsThrough_curvesSubstack_lci_over_field_iff
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
          Stack.objectPropertySubcategory B integerBase hZ
            (curvesFiberedCategory B hZ).val (IsLciFamily B hZ),
        Nonempty (q.comp (Stack.objectPropertyInclusion B integerBase hZ
          (curvesFiberedCategory B hZ).val (IsLciFamily B hZ)) ≅
            { toFunctor := z, w := hz })) ↔
      IsLocalCompleteIntersectionMorphism ((BigFppfOver.toScheme B integerBase hZ).map g) :=
  (factorsThrough_curvesSubstack_over_field_iff (isOpenCurvesLocus_isLciFamily B hZ)
    g k hW hproper hdim z hz ξ).trans
    (isLciFamily_curveFamilyOfSchemeMorphism_iff B hZ g _ hproper _ _ _ _ hdim)

end CurvesLci

/-! ### Over an algebraic stack with a `1`-morphism to the category of curves -/

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
  (F : 𝒳.val.val ⥤ᵇ (curvesFiberedCategory B hZ).val)

/-- **The local complete intersection open substack.** For an algebraic stack `𝒳` with a
`1`-morphism `F` to the category of curves, the full subcategory of `𝒳` on the objects whose
family of curves has a local complete intersection structure morphism is an open substack of
`𝒳`. At the stack of curves this is `Curves^{lci} ⊂ Curves`. -/
def curvesLciOpenSubstack : Stack.OpenSubstack 𝒳 :=
  curvesOpenSubstack F (isOpenCurvesLocus_isLciFamily B hZ)

/-- The objects of the local complete intersection open substack are those whose family of
curves has a local complete intersection structure morphism. -/
@[simp]
theorem curvesLciOpenSubstack_property (x : 𝒳.val.val.obj) :
    (curvesLciOpenSubstack F).property x ↔ IsLciFamily B hZ (F.obj x) :=
  Iff.rfl

/-- **Part (1) of the characterization of the local complete intersection open substack.** Let
`z` be a scheme-valued point of `𝒳` with values in `S` classifying a family of curves `X → S`,
in the sense that `F` sends its value at `S` to a family isomorphic to `X`. Then the following
are equivalent:

* `z` factors through the local complete intersection open substack;
* `X → S` is a local complete intersection morphism;
* `X → S` is syntomic. -/
theorem factorsThrough_curvesLciOpenSubstack_tfae (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : F.obj (z.obj (Over.mk (𝟙 S.left))) ≅ X) :
    List.TFAE
      [∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
            Stack.fullSubcategoryBased 𝒳 (curvesLciOpenSubstack F).property,
          Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳
            (curvesLciOpenSubstack F).property) ≅ { toFunctor := z, w := hz }),
        Space.IsLocalCompleteIntersection B integerBase hZ X.toBase.hom,
        Space.IsSyntomic B integerBase hZ X.toBase.hom] := by
  tfae_have 1 ↔ 2 := factorsThrough_curvesOpenSubstack_iff F
    (isOpenCurvesLocus_isLciFamily B hZ) S z hz X ξ
  tfae_have 2 ↔ 3 := isLciFamily_iff_isSyntomicFamily B hZ X
  tfae_finish

/-- **Part (2) of the characterization of the local complete intersection open substack.** Let
`g : T ⟶ W` be a morphism of the big fppf site of the integers whose target scheme is the
spectrum of a field `k`, whose underlying morphism of schemes is proper, and whose source scheme
has dimension at most one, and let `z` be a scheme-valued point of `𝒳` with values in `W`
classifying the family of curves of `g`. Then `z` factors through the local complete
intersection open substack if and only if the source of `g` is a local complete intersection over
`k`, that is, `g` is a local complete intersection morphism. -/
theorem factorsThrough_curvesLciOpenSubstack_over_field_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hk : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map W.hom)
    (ξ : F.obj (z.obj (Over.mk (𝟙 W.left))) ≅
      curveFamilyOfSchemeMorphism B hZ g (flat_of_eq_spec_field _ k hk) hproper
        (locallyOfFinitePresentation_of_eq_spec_field _ k hk)
        (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
        ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
        ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) :
    (∃ q : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
          Stack.fullSubcategoryBased 𝒳 (curvesLciOpenSubstack F).property,
        Nonempty (q.comp (Stack.fullSubcategoryBasedInclusion 𝒳
          (curvesLciOpenSubstack F).property) ≅ { toFunctor := z, w := hz })) ↔
      IsLocalCompleteIntersectionMorphism ((BigFppfOver.toScheme B integerBase hZ).map g) :=
  (factorsThrough_curvesOpenSubstack_iff F (isOpenCurvesLocus_isLciFamily B hZ) W z hz _
    ξ).trans (isLciFamily_curveFamilyOfSchemeMorphism_iff B hZ g _ hproper _ _ _ _ hdim)

end AlgebraicGeometry

end

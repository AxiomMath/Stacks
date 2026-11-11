module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack

/-!
# The open substack `Curves^{lci}` of the algebraic stack of curves (Stacks 0DZV)

The stack of curves is algebraic (Stacks 0D5A,
`AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack`), and its small model
`AlgebraicGeometry.curvesAlgebraicStack` is an object of `AlgebraicGeometry.Stack.AlgebraicStacks`
equivalent over the site to the category of families of curves. The local complete intersection
property of the structure morphism of a family of curves satisfies condition (o) of Section 0E0E
(`AlgebraicGeometry.isOpenCurvesLocus_isLciFamily`, from the openness and base-change
compatibility of the local complete intersection locus on the base, Stacks 06CE), so it cuts an
open substack `Curves^{lci} ⊂ Curves` out of the algebraic stack of curves, in the sense of
Stacks 04YM, and:

1. given a family of curves `X → S` with a classifying morphism `S → Curves`, the following are
   equivalent: (a) the classifying morphism factors through `Curves^{lci}`, (b) `X → S` is a
   local complete intersection morphism, (c) `X → S` is syntomic;
2. given a proper scheme `X` of dimension at most one over a field `k`, the classifying morphism
   `Spec(k) → Curves` factors through `Curves^{lci}` if and only if `X` is a local complete
   intersection over `k`.

Nothing is assumed: neither the algebraicity of the stack of curves nor the openness of the
local complete intersection locus.

## Main definitions

* `AlgebraicGeometry.curvesLci`: the open substack `Curves^{lci}` of the algebraic stack of
  curves.

## Main results

* `AlgebraicGeometry.curvesLci_property_iff`: an object of the stack of curves lies in
  `Curves^{lci}` exactly when the family of curves it classifies is a local complete
  intersection morphism.
* `AlgebraicGeometry.factorsThrough_curvesLci_tfae`: **Stacks 0DZV**, part (1).
* `AlgebraicGeometry.factorsThrough_curvesLci_over_field_iff`: **Stacks 0DZV**, part (2).
* `AlgebraicGeometry.exists_openSubstack_curvesLci`: **Stacks 0DZV**, the whole statement: there
  is an open substack of the algebraic stack of curves with properties (1) and (2).

## Implementation notes

`Curves` is the small model `AlgebraicGeometry.curvesAlgebraicStack` at the algebraicity proof
`AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack`, and `Curves^{lci}` is the open
substack `AlgebraicGeometry.curvesSmallOpenSubstack` of the method of Section 0E0E for the local
complete intersection condition. A classifying morphism of a family `X → S` is a scheme-valued
point `z : (Sch/S) → Curves` together with an isomorphism between `X` and the family of curves
classified by its value at `S`, a classifying morphism being determined only up to
2-isomorphism; it factors through `Curves^{lci}` when it does over the site and up to a
2-isomorphism. By Stacks 0507 that is the condition that every value of `z` lies in
`Curves^{lci}`, and every value maps to the value at `S`.

In part (2) the family of curves of the proper scheme `X → Spec(k)` is
`AlgebraicGeometry.curveFamilyOfSchemeMorphism`, its flatness and finite presentation discharged
over the field, and its quasi-compactness, separatedness and quasi-separatedness as a morphism of
algebraic spaces read off from the proper morphism of schemes by Stacks 03KY, exactly as in
`AlgebraicGeometry.factorsThrough_curvesSubstack_lci_over_field_iff`.

## References

* [Stacks Project, Tag 0DZV](https://stacks.math.columbia.edu/tag/0DZV)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 06C9](https://stacks.math.columbia.edu/tag/06C9)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DZV, the open substack `Curves^{lci}`.** The open substack of the algebraic stack of
curves (Stacks 0D5A) of the families of curves whose structure morphism is a local complete
intersection morphism, cut out by the method of Section 0E0E. -/
@[stacks 0DZV "the open substack Curves^{lci} of the algebraic stack of curves"]
abbrev curvesLci :
    Stack.OpenSubstack
      (curvesAlgebraicStack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)) :=
  curvesSmallOpenSubstack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)
    (isOpenCurvesLocus_isLciFamily B hZ)

/-- An object of the stack of curves lies in `Curves^{lci}` exactly when the family of curves it
classifies has a local complete intersection structure morphism. -/
theorem curvesLci_property_iff
    (x : (curvesAlgebraicStack B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.obj) :
    (curvesLci.{u, w} B hZ).property x ↔
      IsLciFamily B hZ
        ((curvesSmallEquivalence B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).inverse.obj x) :=
  curvesOpenSubstackOfIsOpenCurvesLocus_property_iff_inverse B hZ
    (isOpenCurvesLocus_isLciFamily B hZ) _ _ _ x

/-- A classifying morphism of a family of curves factors through `Curves^{lci}` exactly when the
family has a local complete intersection structure morphism: the condition (a) ⇔ (b) of both
parts of Stacks 0DZV. -/
theorem factorsThrough_curvesLci_iff (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤
      (curvesAlgebraicStack B hZ
        (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.obj)
    (hz : z ⋙ (curvesAlgebraicStack B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.p = Over.map S.hom)
    (X : CurveFamily B hZ)
    (ξ : (curvesSmallEquivalence B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).inverse.obj
        (z.obj (Over.mk (𝟙 S.left))) ≅ X) :
    (∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
          Stack.fullSubcategoryBased _ (curvesLci.{u, w} B hZ).property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion _
          (curvesLci.{u, w} B hZ).property) ≅ { toFunctor := z, w := hz })) ↔
      IsLciFamily B hZ X := by
  have := (curvesLci.{u, w} B hZ).strictlyFull
  have hP := isOpenCurvesLocus_isLciFamily B hZ
  let E := curvesSmallEquivalence B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)
  rw [Stack.exists_based_factorization_iff]
  refine ⟨fun hall => hP.prop_of_hom ξ.inv
      ((curvesLci_property_iff B hZ _).mp (hall (Over.mk (𝟙 S.left)))), fun hX T => ?_⟩
  exact (curvesLci_property_iff B hZ _).mpr
    (hP.prop_of_hom (E.inverse.map (z.map (Over.mkIdTerminal.from T))) (hP.prop_of_hom ξ.hom hX))

/-- **Stacks 0DZV, part (1).** Let `X → S` be a family of curves and `z : (Sch/S) → Curves` a
classifying morphism for it, a scheme-valued point of the algebraic stack of curves together with
an isomorphism between the family it classifies at `S` and `X`. Then the following are
equivalent:

* (a) `z` factors through `Curves^{lci}`, over the site and up to a 2-isomorphism;
* (b) `X → S` is a local complete intersection morphism;
* (c) `X → S` is syntomic. -/
@[stacks 0DZV "part (1), on the open substack Curves^{lci} of the algebraic stack of curves"]
theorem factorsThrough_curvesLci_tfae (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤
      (curvesAlgebraicStack B hZ
        (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.obj)
    (hz : z ⋙ (curvesAlgebraicStack B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.p = Over.map S.hom)
    (X : CurveFamily B hZ)
    (ξ : (curvesSmallEquivalence B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).inverse.obj
        (z.obj (Over.mk (𝟙 S.left))) ≅ X) :
    List.TFAE
      [∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
            Stack.fullSubcategoryBased _ (curvesLci.{u, w} B hZ).property,
          Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion _
            (curvesLci.{u, w} B hZ).property) ≅ { toFunctor := z, w := hz }),
        Space.IsLocalCompleteIntersection B integerBase hZ X.toBase.hom,
        Space.IsSyntomic B integerBase hZ X.toBase.hom] := by
  tfae_have 1 ↔ 2 := factorsThrough_curvesLci_iff B hZ S z hz X ξ
  tfae_have 2 ↔ 3 := isLciFamily_iff_isSyntomicFamily B hZ X
  tfae_finish

/-- **Stacks 0DZV, part (2).** Let `g : T ⟶ W` be a morphism of the big fppf site of the integers
whose target scheme is the spectrum of a field `k`, whose underlying morphism of schemes is
proper, and whose source scheme `X` has dimension at most one, and let `z : (Sch/Spec(k)) →
Curves` classify the family of curves of `g`. Then `z` factors through `Curves^{lci}` if and only
if `X` is a local complete intersection over `k`, that is, `g` is a local complete intersection
morphism. -/
@[stacks 0DZV "part (2), on the open substack Curves^{lci} of the algebraic stack of curves"]
theorem factorsThrough_curvesLci_over_field_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (z : BigFppfOver B W.left.1 W.left.2 ⥤
      (curvesAlgebraicStack B hZ
        (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.obj)
    (hz : z ⋙ (curvesAlgebraicStack B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.p = Over.map W.hom)
    (ξ : (curvesSmallEquivalence B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).inverse.obj
        (z.obj (Over.mk (𝟙 W.left))) ≅
      curveFamilyOfSchemeMorphism B hZ g (flat_of_eq_spec_field _ k hW) hproper
        (locallyOfFinitePresentation_of_eq_spec_field _ k hW)
        (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
        ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
        ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) :
    (∃ q : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
          Stack.fullSubcategoryBased _ (curvesLci.{u, w} B hZ).property,
        Nonempty (q.comp (Stack.fullSubcategoryBasedInclusion _
          (curvesLci.{u, w} B hZ).property) ≅ { toFunctor := z, w := hz })) ↔
      IsLocalCompleteIntersectionMorphism ((BigFppfOver.toScheme B integerBase hZ).map g) :=
  (factorsThrough_curvesLci_iff B hZ W z hz _ ξ).trans
    (isLciFamily_curveFamilyOfSchemeMorphism_iff B hZ g _ hproper _ _ _ _ hdim)

/-- **Stacks 0DZV.** There is an open substack `Curves^{lci}` of the algebraic stack of curves
such that

1. for a family of curves `X → S` with classifying morphism `z : (Sch/S) → Curves`, the following
   are equivalent: (a) `z` factors through `Curves^{lci}`, (b) `X → S` is a local complete
   intersection morphism, (c) `X → S` is syntomic;
2. for a proper scheme `X` of dimension at most one over a field `k` (a morphism `g` of the site
   to `Spec(k)`) with classifying morphism `z : (Sch/Spec(k)) → Curves`, `z` factors through
   `Curves^{lci}` if and only if `X` is a local complete intersection over `k`.

The open substack is `AlgebraicGeometry.curvesLci`. -/
@[stacks 0DZV]
theorem exists_openSubstack_curvesLci :
    ∃ U : Stack.OpenSubstack
        (curvesAlgebraicStack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)),
      (∀ (S : BigFppfOver B integerBase hZ)
        (z : BigFppfOver B S.left.1 S.left.2 ⥤
          (curvesAlgebraicStack B hZ
            (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.obj)
        (hz : z ⋙ (curvesAlgebraicStack B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.p = Over.map S.hom)
        (X : CurveFamily B hZ)
        (_ : (curvesSmallEquivalence B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).inverse.obj
            (z.obj (Over.mk (𝟙 S.left))) ≅ X),
        List.TFAE
          [∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
                Stack.fullSubcategoryBased _ U.property,
              Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion _ U.property) ≅
                { toFunctor := z, w := hz }),
            Space.IsLocalCompleteIntersection B integerBase hZ X.toBase.hom,
            Space.IsSyntomic B integerBase hZ X.toBase.hom]) ∧
      ∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
        (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
        (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
        (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
        (z : BigFppfOver B W.left.1 W.left.2 ⥤
          (curvesAlgebraicStack B hZ
            (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.obj)
        (hz : z ⋙ (curvesAlgebraicStack B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).val.val.p = Over.map W.hom)
        (_ : (curvesSmallEquivalence B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).inverse.obj
            (z.obj (Over.mk (𝟙 W.left))) ≅
          curveFamilyOfSchemeMorphism B hZ g (flat_of_eq_spec_field _ k hW) hproper
            (locallyOfFinitePresentation_of_eq_spec_field _ k hW)
            (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
            ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
            ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim),
        (∃ q : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
              Stack.fullSubcategoryBased _ U.property,
            Nonempty (q.comp (Stack.fullSubcategoryBasedInclusion _ U.property) ≅
              { toFunctor := z, w := hz })) ↔
          IsLocalCompleteIntersectionMorphism ((BigFppfOver.toScheme B integerBase hZ).map g) :=
  ⟨curvesLci.{u, w} B hZ, fun S z hz X ξ => factorsThrough_curvesLci_tfae B hZ S z hz X ξ,
    fun g k _ hW hproper hdim z hz ξ =>
      factorsThrough_curvesLci_over_field_iff B hZ g k hW hproper hdim z hz ξ⟩

end AlgebraicGeometry

end

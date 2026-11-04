module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesSmallHoms
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackOfRepresentableInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation

/-!
# `Curves⁺` as an open substack of the algebraic stack of curves (Stacks 0DZW)

Granted that the stack of curves is algebraic (Stacks 0D5A, supplied as the statement
`Stack.IsAlgebraicStack B integerBase hZ (curvesFiberedCategory B hZ).val`), this file produces
`Curves⁺` as an `AlgebraicGeometry.Stack.OpenSubstack` — the library's object of Stacks 04YM,
part (1): a strictly full subcategory which is an algebraic stack and whose inclusion is an open
immersion — of the algebraic stack of curves, and proves parts (1) and (2) of Stacks 0DZW for it.

## Main results

* `AlgebraicGeometry.exists_openSubstack_curvesPlus`: if the stack of curves is algebraic, then
  `Curves⁺` is an open substack of it satisfying parts (1) and (2) of Stacks 0DZW.

## Implementation notes

The 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` consists of categories fibred in
groupoids with morphism universe `u`, while families of curves have morphism universe `u + 1`; the
algebraic stack of curves is therefore its model with small hom-sets,
`AlgebraicGeometry.curvesShrinkHomsAlgebraicStack`, which has the same objects and is equivalent
over the site to `AlgebraicGeometry.curvesFiberedCategory`
(`AlgebraicGeometry.curvesShrinkHomsEquivalenceOver`).

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves⁺` on the small-hom model of the stack of curves. -/
abbrev curvesPlusSmallProperty : ObjectProperty (ShrinkHoms (CurveFamily B hZ)) :=
  fun x => IsFiniteNonSmoothLocus B hZ (ShrinkHoms.fromShrinkHoms x)

/-- The defining condition of `Curves⁺` on the small-hom model is stable under pullback. -/
theorem curvesPlusSmallProperty_of_hom {x y : ShrinkHoms (CurveFamily B hZ)} (f : x ⟶ y) :
    curvesPlusSmallProperty B hZ y → curvesPlusSmallProperty B hZ x :=
  fun h => CurveFamily.isFiniteNonSmoothLocus_of_hom B hZ ((ShrinkHoms.inverse _).map f) h

/-- Over a scheme-valued point of the small-hom model of the stack of curves, the families in
`Curves⁺` are those over an open subscheme of the base. -/
theorem exists_open_over_curvesSmall (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ ShrinkHoms (CurveFamily B hZ))
    (hy : y ⋙ curvesSmallProjection B hZ = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map V.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        curvesPlusSmallProperty B hZ (y.obj T) ↔ Nonempty (T ⟶ V) :=
  exists_open_over_iff_of_exists_isOpenSubspace B hZ (IsFiniteNonSmoothLocus B hZ)
    (CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus B hZ) U
    (y ⋙ ShrinkHoms.inverse _) hy

/-- **Stacks 0DZW.** Let the stack of curves be algebraic (Stacks 0D5A). Then `Curves⁺` is an open
substack of the algebraic stack of curves in the sense of Stacks 04YM — a strictly full
subcategory which is an algebraic stack and whose inclusion is an open immersion — whose objects
are the families of curves with finite singular locus, and

1. for every family of curves `X → S` and every classifying morphism `S → Curves`, the classifying
   morphism factors through `Curves⁺` iff the singular locus with some closed subspace structure
   is finite over `S`, iff it is finite over `S` with every closed subspace structure;
2. for every proper scheme `X` of dimension at most one over a field `k` and every classifying
   morphism `Spec(k) → Curves` of it, that morphism factors through `Curves⁺` iff `X → Spec(k)`
   is smooth except at finitely many points. -/
theorem exists_openSubstack_curvesPlus
    (hCurvesAlgebraic : Stack.IsAlgebraicStack.{u, u + 1, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ).val) :
    ∃ V : Stack.OpenSubstack (curvesShrinkHomsAlgebraicStack B hZ hCurvesAlgebraic),
      (∀ X : CurveFamily B hZ,
        V.property (ShrinkHoms.toShrinkHoms X) ↔ IsFiniteNonSmoothLocus B hZ X) ∧
      (∀ (X : CurveFamily B hZ)
        (y : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
          (curvesShrinkHomsAlgebraicStack B hZ hCurvesAlgebraic).val.val),
        Nonempty (y.obj (Over.mk (𝟙 X.base.left)) ≅ ShrinkHoms.toShrinkHoms X) →
          ((∃ g : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
                Stack.fullSubcategoryBased (curvesShrinkHomsAlgebraicStack B hZ hCurvesAlgebraic)
                  V.property,
              Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion _ V.property) ≅ y)) ↔
            ∃ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z ∧
              Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
                CurveFamily.nonSmoothLocus B hZ X ∧
              Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)) ∧
          ((∃ g : BasedCategory.ofFunctor (Over.map X.base.hom) ⥤ᵇ
                Stack.fullSubcategoryBased (curvesShrinkHomsAlgebraicStack B hZ hCurvesAlgebraic)
                  V.property,
              Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion _ V.property) ≅ y)) ↔
            ∀ Z : Subfunctor X.total.1, Space.IsClosedSubspace B integerBase hZ Z →
              Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
                CurveFamily.nonSmoothLocus B hZ X →
              Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom))) ∧
      (∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
        (e : (BigFppfOver.toScheme B integerBase hZ).obj W ≅ Spec (.of k))
        (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
        (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
        (y : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
          (curvesShrinkHomsAlgebraicStack B hZ hCurvesAlgebraic).val.val),
        Nonempty (y.obj (Over.mk (𝟙 W.left)) ≅
          ShrinkHoms.toShrinkHoms (curveFamilyOfProperOverField B hZ k g e hproper hdim)) →
          ((∃ g' : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
                Stack.fullSubcategoryBased (curvesShrinkHomsAlgebraicStack B hZ hCurvesAlgebraic)
                  V.property,
              Nonempty (g'.comp (Stack.fullSubcategoryBasedInclusion _ V.property) ≅ y)) ↔
            {x : (BigFppfOver.toScheme B integerBase hZ).obj T |
              ¬ InfinitesimalLifting.SmoothAt
                ((BigFppfOver.toScheme B integerBase hZ).map g) x}.Finite)) := by
  set 𝒳 := curvesShrinkHomsAlgebraicStack B hZ hCurvesAlgebraic
  let P : ObjectProperty 𝒳.val.val.obj := curvesPlusSmallProperty B hZ
  have hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a := curvesPlusSmallProperty_of_hom B hZ
  have hrep : Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (Stack.fullSubcategoryBasedInclusion 𝒳 P) := by
    intro U
    dsimp only
    intro y hy
    obtain ⟨V, hV, hchar⟩ := exists_open_over_curvesSmall B hZ U y hy
    exact ⟨yoneda.obj V, isAlgebraicSpace_yoneda B U.left.1 U.left.2 V,
      nonempty_equivalenceOver_baseChange_of_open (curvesSmallProjection B hZ) P hP
        (curvesSmallProjection_isFiberedInGroupoids B hZ) U y hy V hV hchar⟩
  have hopen : Stack.IsOpenImmersion B integerBase hZ
      (Stack.fullSubcategoryFiberedInclusion 𝒳 hP) := by
    intro U y hy F hF he
    obtain ⟨V, hV, hchar⟩ := exists_open_over_curvesSmall B hZ U y hy
    exact isOpenImmersion_of_baseChange_of_open (curvesSmallProjection B hZ) P hP
      (curvesSmallProjection_isFiberedInGroupoids B hZ) U y hy V hV hchar F hF he.some
  obtain ⟨V, hVP⟩ := Stack.exists_openSubstack_of_isOpenImmersion 𝒳 P hP hrep hopen
  have := V.strictlyFull
  have hfactor : ∀ {U : BigFppfOver B integerBase hZ} (X : CurveFamily B hZ)
      (y : BasedCategory.ofFunctor (Over.map U.hom) ⥤ᵇ 𝒳.val.val),
      Nonempty (y.obj (Over.mk (𝟙 U.left)) ≅ ShrinkHoms.toShrinkHoms X) →
      ((∃ g : BasedCategory.ofFunctor (Over.map U.hom) ⥤ᵇ Stack.fullSubcategoryBased 𝒳 V.property,
          Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 V.property) ≅ y)) ↔
        IsFiniteNonSmoothLocus B hZ X) := by
    intro U X y ⟨e⟩
    rw [Stack.exists_based_factorization_iff y, hVP]
    exact ⟨fun h => hP e.inv (h (Over.mk (𝟙 U.left))),
      fun h T => hP (y.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 U.left))) (hP e.hom h)⟩
  refine ⟨V, fun X => by rw [hVP]; rfl, fun X y hy => ⟨?_, ?_⟩, ?_⟩
  · exact (hfactor X y hy).trans
      (CurveFamily.isFiniteNonSmoothLocus_iff_exists_isClosedSubspace B hZ X)
  · exact (hfactor X y hy).trans
      (CurveFamily.isFiniteNonSmoothLocus_iff_forall_isClosedSubspace B hZ X)
  · intro k _ T W g e hproper hdim y hy
    exact (hfactor _ y hy).trans
      (isFiniteNonSmoothLocus_curveFamilyOfProperOverField_iff B hZ k g e hproper hdim)

end AlgebraicGeometry

end

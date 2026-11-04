module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.LefschetzMotive
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointSummands
public import StacksCore.Tactic.StacksAttribute

/-!
# The two summands of the motive of the projective line

Let `k` be a field, `X = P¹_k` and `x ∈ X` a `k`-rational point. Example 0FG6 attaches to `x`
the orthogonal idempotents `c₀ = [x × X]` and `c₂ = [X × x]` of `Corr⁰(X, X)`
(`Stacks.WeilCohomology.projectiveLinePointFibreCorr`,
`Stacks.WeilCohomology.projectiveLineFibrePointCorr`). Lemma 0FGD identifies the two motives they
cut out, in the category `M_k = ChowMotiveCat k` of Chow motives:

1. `(X, c₀, 0) ≅ 1 = (Spec k, 1, 0)`;
2. `(X, c₂, 0) ≅ 1(-1) = (Spec k, 1, -1)`, the motive `(X, c₂, 0)` being
   `Stacks.WeilCohomology.ChowMotiveCat.lefschetzMotive`.

This is the case `X = P¹_k`, `d = 1` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointSummands`, where the proof of
the source is carried out for any smooth projective `X` of constant dimension `d` with a rational
point. What remains here is to identify Example 0FG6's `c₀` and `c₂` with the correspondences of
that file: `c₀` is the graph class of the constant morphism `X → x → X`, and `c₂` is the class of
the fibre `X × x`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.projectiveLinePointFibreMotiveIso`: **Stacks 0FGD (1)**.
* `Stacks.WeilCohomology.ChowMotiveCat.projectiveLineFibrePointMotiveIso`: **Stacks 0FGD (2)**.

## References

* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

namespace ChowMotiveCat

variable {k : Type u} [Field k]
  (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
    𝟙 (fieldChowSituation k).S)

/-- A rational point of `P¹_k`, as a morphism from the monoidal unit `Spec k` of smooth projective
schemes over `k`. -/
def projectiveLinePoint : 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⟶ projectiveLineObj k :=
  ObjectProperty.homMk (Over.homMk x hx)

/-- The motive `(X, p, m)` depends on the projector `p` only. -/
theorem mk'_congr {X : (SmoothProjectiveScheme k).FullSubcategory}
    {p q : SmoothProjectiveCorr X X 0} (h : p = q)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p)
    (hq : (canonicalCorrespondenceCompositionData k).comp q q = q) (m : ℤ) :
    mk' X p hp m = mk' X q hq m := by
  subst h
  rfl

/-- `c₀` is the graph class of the constant morphism through the rational point. -/
theorem projectiveLinePointFibreCorr_eq_constantGraphCorr :
    projectiveLinePointFibreCorr x hx = constantGraphCorr (projectiveLinePoint x hx) := by
  rw [projectiveLinePointFibreCorr_eq_graph, constantGraphCorr]
  congr 1

attribute [local instance] isClosedImmersion_graphMorphism isClosedImmersion_constantFibreEmbedding

/-- `c₂` is the class of the fibre `X × x`. -/
theorem projectiveLineFibrePointCorr_eq_fibreClassCorr :
    projectiveLineFibrePointCorr x hx =
      fibreClassCorr (relativeDimension_projectiveLine k) (projectiveLinePoint x hx) := by
  have hι : graphMorphism _ _ _ (constantMorphism_comp_base _ x hx) ≫
      (pullbackSymmetry _ _).hom =
        constantFibreEmbedding k _ (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (projectiveLinePoint x hx).hom.left (Over.w (projectiveLinePoint x hx).hom) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, graphMorphism_snd]
      exact (pullback.lift_fst (f := (projectiveLineObj k).obj.hom)
        (g := (projectiveLineObj k).obj.hom) _ _ _).symm
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, graphMorphism_fst]
      refine Eq.trans ?_ (pullback.lift_snd (f := (projectiveLineObj k).obj.hom)
        (g := (projectiveLineObj k).obj.hom) _ _ _).symm
      have hinv : inv (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom = 𝟙 _ :=
        IsIso.inv_eq_of_hom_inv_id (by rw [Category.comp_id]; rfl)
      rw [hinv, Category.id_comp]
      rfl
  have hcyc := (cycle_fibrePoint_imageι x hx (1 - 0)).trans
    (cycleAssociatedToClosedSubscheme_congr _ _ _ _ hι _)
  rw [projectiveLineFibrePointCorr, fibrePointCorrespondence, hcyc]
  rfl

/-- `c₀ ∘ c₀ = c₀` in `Corr⁰(P¹_k, P¹_k)`, read off from the splitting of `c₀` through `Spec k`. -/
theorem projectiveLinePointFibreCorr_comp_self :
    (canonicalCorrespondenceCompositionData k).comp (projectiveLinePointFibreCorr x hx)
      (projectiveLinePointFibreCorr x hx) = projectiveLinePointFibreCorr x hx := by
  rw [projectiveLinePointFibreCorr_eq_constantGraphCorr]
  exact constantGraphCorr_comp_self _

/-- **Stacks Project, Tag 0FGD (1).** For a rational point `x` of `X = P¹_k`, the motive
`(X, c₀, 0)`, with `c₀ = [x × X]`, is isomorphic to `1 = (Spec k, 1, 0)`. The mutually inverse
morphisms are the graph classes of the structure morphism `X → Spec k` and of the point
`x : Spec k → X`. -/
@[stacks 0FGD "part (1): the motive (P¹_k, c₀, 0) is isomorphic to 1 = (Spec k, 1, 0), in the
category of Chow motives built on the actual composition of correspondences"]
def projectiveLinePointFibreMotiveIso :
    mk' (projectiveLineObj k) (projectiveLinePointFibreCorr x hx)
      (projectiveLinePointFibreCorr_comp_self x hx) 0 ≅ tate k 0 :=
  eqToIso (mk'_congr (projectiveLinePointFibreCorr_eq_constantGraphCorr x hx) _
      (constantGraphCorr_comp_self _) 0) ≪≫
    pointGraphMotiveIso (projectiveLinePoint x hx)

/-- **Stacks Project, Tag 0FGD (2).** For a rational point `x` of `X = P¹_k`, the motive
`(X, c₂, 0)`, with `c₂ = [X × x]`, is isomorphic to `1(-1) = (Spec k, 1, -1)`. The mutually
inverse morphisms are the class `a' ∈ Corr¹(Spec k, X)` of the point `x` and the fundamental class
`b' ∈ Corr^{-1}(X, Spec k)`, whose compositions `b' ∘ a' = 1` and `a' ∘ b' = c₂` are computed by
intersecting cycles. -/
@[stacks 0FGD "part (2): the motive (P¹_k, c₂, 0) is isomorphic to 1(-1) = (Spec k, 1, -1), with
b' ∘ a' = 1 and a' ∘ b' = c₂ proved by intersecting the actual cycles"]
def projectiveLineFibrePointMotiveIso : lefschetzMotive x hx ≅ tate k (-1) :=
  eqToIso (mk'_congr (projectiveLineFibrePointCorr_eq_fibreClassCorr x hx) _
      (fibreClassCorr_comp_self _ _) 0) ≪≫
    pointFibreMotiveIso (relativeDimension_projectiveLine k) (projectiveLinePoint x hx)

end ChowMotiveCat

end Stacks.WeilCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.SectionPairFibreCycle
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 at an arbitrary pair of distinct closed points of the projective line

This file states and proves the whole of Tag 0B07 under the source's own hypotheses: `X` is a
nonsingular variety over an algebraically closed field `Kf`, `a` and `b` are distinct closed
points of `ℙ¹`, and `k` is an integer. The four clauses — (1)(a), (1)(b), (2) and (3) — are
proved as a single statement, `Stacks.Chow.tag_0B07`.

The closed points enter as closed points of the topological space of `ℙ¹_S`, and the closed
subscheme `X × a` as the image of the section of the family attached to such a point by
`Stacks.Chow.closedPointSection`. That the section at a closed point is
`Stacks.Chow.pointSection` at a global function on the base or `Stacks.Chow.infinitySection` is
`Stacks.Chow.exists_closedPointSection_eq_pointSection_or_eq_infinitySection`, and the clauses
of the tag at a section of either shape are the statements of
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.SectionPairFibreCycle` and
`...SectionPairFibreIntersectionDifference`. Nothing mathematical is reproved here: this file is
the assembly.

## Main results

* `Stacks.Chow.tag_0B07` — **Tag 0B07, whole, at an arbitrary pair of distinct closed points.**

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

/-- **Stacks Project, Tag 0B07.** Let `X` be a nonsingular variety over an algebraically closed
field, let `a ≠ b` be closed points of `ℙ¹` and let `k` be an integer. Writing `X × a` for the
image of the section of `X ×_S ℙ¹_S ⟶ X` at `a`:

0. that section is constant at `a` — its second projection sends every point of `X` to `a` — so
   `X × a` is the fibre of `X ×_S ℙ¹_S ⟶ ℙ¹_S` over `a`, and likewise at `b`;
1. if `W ⊆ X ×_S ℙ¹_S` is a closed subvariety of delta-dimension `k + 1` meeting `X × a`
   properly, then (a) `[W_a]_k = W · (X × a)` as cycles on `X ×_S ℙ¹_S`, and (b)
   `[W_a]_k = pr_{X,*}(W · X × a)` as cycles on `X`;
2. for every `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` meeting `X × a` and `X × b` properly,
   `pr_{X,*}(α · X × a - α · X × b)` is rationally equivalent to zero;
3. conversely, every `k`-cycle rationally equivalent to zero is of that form.

The intersection products are the Section 43.14 products of Tag 0AZR, read on cycles by the Tag
0B08 product; rational equivalence is `Stacks.Chow.rationalEquivalences`, the group of Tag 02RW;
and "of that form" is `Stacks.Chow.PointCycle.IsSectionPairFibreIntersectionDifference`, which
spells out the conclusion of (2). Nothing is assumed about the ambient family `X ×_S ℙ¹_S`. -/
@[stacks 0B07 "the whole tag, at an ARBITRARY pair of distinct closed points `a`, `b` of `P^1` \
over an algebraically closed field: (1)(a) `[W_a]_k = W · X × a` as cycles on `X × P^1`, \
(1)(b) `[W_a]_k = pr_{X,*}(W · X × a)` as cycles on `X`, (2) `pr_{X,*}(α · X × a - α · X × b)` \
is rationally equivalent to zero for every `(k + 1)`-cycle `α` meeting the two fibres properly, \
and (3) the converse, that every `k`-cycle rationally equivalent to zero is of that form. The \
hypotheses are the source's own and concern `X`, `a`, `b` and `W` (resp. `α`, `β`) alone: `X` is \
nonsingular (`hX`) and a variety over an algebraically closed field `Kf`, and `a`, `b` are \
distinct closed points of the projective line (`ha`, `hb`, `hab`); `k` is an arbitrary integer, \
the source's `k ≥ 0` being unnecessary. `X × a` is the image of the section of the family at \
`a`, which is `Stacks.Chow.closedPointSection`, built from Mathlib's \
`AlgebraicGeometry.pointOfClosedPoint`: over an algebraically closed field the residue field at \
a closed point of a scheme locally of finite type is the field itself, so a closed point of \
`P^1` is a rational point. The first clause of the conclusion records that the second projection \
of each of the two sections is constant at its point, so that `X × a` and `X × b` are the fibres \
of `X × P^1` over `a` and over `b`. That this section is `Stacks.Chow.pointSection` at a global \
function on the base, or `Stacks.Chow.infinitySection`, is \
`Stacks.Chow.exists_closedPointSection_eq_pointSection_or_eq_infinitySection`, proved from the \
chart dichotomy `Stacks.Chow.compl_range_affineChart` together with the classification of the \
`S`-points of the affine chart, `Stacks.Chow.eq_affineLineSection_of_comp_eq`. The products are \
the honest Section 43.14 products of Tag 0AZR and the Tag 0B08 products \
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` assembled from them; \
`rationally equivalent to zero` is `Stacks.Chow.rationalEquivalences`, the group of Tag 02RW; \
`of that form` in (3) is `Stacks.Chow.PointCycle.IsSectionPairFibreIntersectionDifference`, \
which spells out the conclusion of (2) at the two sections. Proper intersection is the \
delta-dimension idiom of chapter 42 (`hWD`, for `dim (W ∩ X × a) ≤ k`) in (1) and the form \
Section 43.8 and Tag 02S4 part (2) use in (2) — no component of `α` is contained in the \
section. Nothing is assumed about the ambient `X × P^1`: its regularity is \
`Stacks.Chow.isRegular_projectiveLineProduct_of_eq`, derived from nonsingularity of `X`; the \
pointwise readings of (1)(a) are `Stacks.Chow.localConditions_ker_pointSection` and its \
infinity twin; the delta-dimension bounds on the supports of the Tor sheaves are \
`AlgebraicGeometry.TorFormula.schemeDeltaDimension_reducedSupport_torSheaf_le`; and the bound \
on the Krull dimension of the family that makes the alternating Tor sum finite is \
`Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le`. Tag 0B2U, the \
2-transitivity of the automorphism group of `P^1`, is not invoked: each clause is proved at the \
pair of points themselves."]
theorem tag_0B07 (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (Kf : Type u) [Field Kf] [IsAlgClosed Kf]
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
    [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)] (hX : IsRegular X) (k : ℤ)
    (a b : relativeProjectiveLine C.S) (ha : IsClosed {a}) (hb : IsClosed {b}) (hab : a ≠ b) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    ((∀ x : X, (closedPointSection Kf hC a ha p ≫
            pullback.snd p (relativeProjectiveLine C.S ↘ C.S)) x = a) ∧
        ∀ x : X, (closedPointSection Kf hC b hb p ≫
          pullback.snd p (relativeProjectiveLine C.S ↘ C.S)) x = b) ∧
      (∀ W : (projectiveLineProduct p).IdealSheafData, IsIntegral W.subscheme →
        (∀ ξ : genericPoints W.subscheme,
          relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1) →
        ∀ hWD : schemeDeltaDimension C
            ((W ⊔ (closedPointSection Kf hC a ha p).ker).subschemeι ≫
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt),
          (cycleAssociatedToClosedSubscheme C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (W ⊔ (closedPointSection Kf hC a ha p).ker).subschemeι k).1 =
            intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX)
              (subschemeStructureSheaf W)
              (subschemeStructureSheaf (closedPointSection Kf hC a ha p).ker)
              (isCoherent_subschemeStructureSheaf W)
              (isCoherent_subschemeStructureSheaf (closedPointSection Kf hC a ha p).ker) k
              (schemeDeltaDimension_reducedSupport_torSheaf_le C
                (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
                (isRegular_projectiveLineProduct_of_eq p hC hX) W
                (closedPointSection Kf hC a ha p).ker k hWD) ∧
          properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
              ⟨intersectionProductCycle C
                  (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
                  (isRegular_projectiveLineProduct_of_eq p hC hX)
                  (subschemeStructureSheaf W)
                  (subschemeStructureSheaf (closedPointSection Kf hC a ha p).ker)
                  (isCoherent_subschemeStructureSheaf W)
                  (isCoherent_subschemeStructureSheaf (closedPointSection Kf hC a ha p).ker) k
                  (schemeDeltaDimension_reducedSupport_torSheaf_le C
                    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
                    (isRegular_projectiveLineProduct_of_eq p hC hX) W
                    (closedPointSection Kf hC a ha p).ker k hWD),
                intersectionProductCycle_mem_cyclesOfDimension C
                  (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
                  (isRegular_projectiveLineProduct_of_eq p hC hX) W
                  (closedPointSection Kf hC a ha p).ker k hWD⟩ =
            cycleAssociatedToClosedSubscheme C p
              (W.comap (closedPointSection Kf hC a ha p)).subschemeι k) ∧
      (∀ α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1),
          ∀ hT₁ : ∀ x ∈ Function.support α.1, ¬ Set.range (integralComponentAt x).subschemeι ⊆
            Set.range (closedPointSection Kf hC a ha p),
          ∀ hT₂ : ∀ x ∈ Function.support α.1, ¬ Set.range (integralComponentAt x).subschemeι ⊆
            Set.range (closedPointSection Kf hC b hb p),
            properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
                (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
                ⟨torFormulaCycleIntersectionProduct C
                    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
                    (isRegular_projectiveLineProduct_of_eq p hC hX) k α.1
                    (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                      (Classical.decEq _) _
                      ((closedPointSection Kf hC a ha p) (genericPoint X)) (1 : ℤ)),
                  torFormulaCycleIntersectionProduct_section_mem_cyclesOfDimension C p Kf hC
                    (isRegular_projectiveLineProduct_of_eq p hC hX) k
                    (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC a ha p)
                    α hT₁⟩ -
              properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
                (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
                ⟨torFormulaCycleIntersectionProduct C
                    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
                    (isRegular_projectiveLineProduct_of_eq p hC hX) k α.1
                    (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                      (Classical.decEq _) _
                      ((closedPointSection Kf hC b hb p) (genericPoint X)) (1 : ℤ)),
                  torFormulaCycleIntersectionProduct_section_mem_cyclesOfDimension C p Kf hC
                    (isRegular_projectiveLineProduct_of_eq p hC hX) k
                    (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC b hb p)
                    α hT₂⟩ ∈
            rationalEquivalences C p k) ∧
      (∀ β : CycleGroup C p k, β ∈ rationalEquivalences C p k →
        PointCycle.IsSectionPairFibreIntersectionDifference C p
          (isRegular_projectiveLineProduct_of_eq p hC hX) k
          (closedPointSection Kf hC a ha p) (closedPointSection Kf hC b hb p) β) := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have hpt : ∀ (z : relativeProjectiveLine C.S) (hz : IsClosed {z}) (x : X),
      (closedPointSection Kf hC z hz p ≫
        pullback.snd p (relativeProjectiveLine C.S ↘ C.S)) x = z := by
    intro z hz x
    rw [closedPointSection_comp_snd, Scheme.Hom.comp_apply, closedPointLineSection_apply]
  refine ⟨⟨hpt a ha, hpt b hb⟩, fun W hW hDim hWD => ?_, fun α hT₁ hT₂ => ?_, fun β hβ => ?_⟩
  · have := hW
    exact ⟨cycleAssociatedToClosedSubscheme_sup_sectionKer_eq_intersectionProductCycle C p Kf hC
        (isRegular_projectiveLineProduct_of_eq p hC hX) k
        (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC a ha p) W hDim hWD,
      properPushforward_intersectionProductCycle_eq_sectionFiberCycle C p Kf hC
        (isRegular_projectiveLineProduct_of_eq p hC hX) k
        (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC a ha p) W hDim hWD⟩
  · exact sub_properPushforward_torFormulaCycleProduct_sectionPair_mem_rationalEquivalences
      C p Kf hC (isRegular_projectiveLineProduct_of_eq p hC hX) k
      (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC a ha p)
      (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC b hb p) α hT₁ hT₂
  · exact PointCycle.isSectionPairFibreIntersectionDifference_of_mem_rationalEquivalences C p
      (isRegular_projectiveLineProduct_of_eq p hC hX) k Kf hC
      (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC a ha p)
      (exists_closedPointSection_eq_pointSection_or_eq_infinitySection Kf hC b hb p)
      (closedPointSection_ne Kf hC a ha p b hb hab) β hβ

end Stacks.Chow

end

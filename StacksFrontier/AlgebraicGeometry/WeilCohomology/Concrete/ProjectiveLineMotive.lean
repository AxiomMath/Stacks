module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineSummands
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiBiproduct

/-!
# The motive of the projective line

Let `k` be a field and `X = P¹_k`. Lemma 0FGG of the Stacks Project: in the category `M_k` of
Chow motives,

  `h(P¹_k) ≅ 1 ⊕ 1(-1)`.

The proof is the one of the source, "this follows from Example 0FG6 and Lemma 0FGD". For a
`k`-rational point `x` of `X`, Example 0FG6 provides the correspondences `c₀ = [x × X]` and
`c₂ = [X × x]` in `Corr⁰(X, X)` with `[Δ] = c₀ + c₂` and `c₀ ∘ c₀ = c₀`, `c₀ ∘ c₂ = 0`,
`c₂ ∘ c₀ = 0`, `c₂ ∘ c₂ = c₂`
(`Stacks.WeilCohomology.projectiveLine_id_eq_add` and the four composition rules). Two orthogonal
idempotents summing to the identity `[Δ]` of `h(X) = (X, [Δ], 0)` split it as the direct sum of
the motives `(X, c₀, 0)` and `(X, c₂, 0)` they cut out
(`CategoryTheory.GradedCategory.TwistedKaroubi.ofObjBiproductData`), and Lemma 0FGD identifies
these with `1 = (Spec k, 1, 0)` and `1(-1) = (Spec k, 1, -1)`
(`Stacks.WeilCohomology.ChowMotiveCat.projectiveLinePointFibreMotiveIso` and
`Stacks.WeilCohomology.ChowMotiveCat.projectiveLineFibrePointMotiveIso`).

Everything is about the actual objects: `P¹_k` is `Stacks.WeilCohomology.projectiveLineObj k`,
the correspondences are composed by `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` with the canonical
Gysin classes of the diagonals, and `M_k` is `Stacks.WeilCohomology.ChowMotiveCat k`.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.projectiveLineSummandsBiproductData`: `h(P¹_k)` is the
  direct sum of `(P¹_k, c₀, 0)` and the Lefschetz motive `(P¹_k, c₂, 0)`.
* `Stacks.WeilCohomology.ChowMotiveCat.projectiveLineMotiveBiproductData`: **Stacks 0FGG**,
  `h(P¹_k)` is the direct sum of `1` and `1(-1)`: a bilimit bicone over `1` and `1(-1)` with point
  `h(P¹_k)`.
* `Stacks.WeilCohomology.ChowMotiveCat.projectiveLineMotiveIso`: **Stacks 0FGG**, the
  isomorphism `h(P¹_k) ≅ 1 ⊞ 1(-1)`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.hasBinaryBiproduct_tate_zero_tate_neg_one`: the direct
  sum `1 ⊕ 1(-1)` exists in `M_k`.

## References

* [Stacks Project, Tag 0FGG](https://stacks.math.columbia.edu/tag/0FGG)
* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.GradedCategory
  Stacks.Chow

universe u

namespace Stacks.WeilCohomology.ChowMotiveCat

variable {k : Type u} [Field k]
  (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
    𝟙 (fieldChowSituation k).S)

/-! ### The projectors `c₀`, `c₂` as endomorphisms of `P¹_k` -/

/-- `c₂ ∘ c₀ = 0`, for `c₀` and `c₂` as homogeneous morphisms of degree zero. -/
theorem homOf_projectiveLinePointFibreCorr_comp_homOf_projectiveLineFibrePointCorr :
    homOf (X := projectiveLineObj k) (Y := projectiveLineObj k) 0
        (projectiveLinePointFibreCorr x hx) ≫ homOf 0 (projectiveLineFibrePointCorr x hx) = 0 := by
  rw [homOf, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  exact projectiveLine_pointFibre_comp_fibrePoint x hx

/-- `c₀ ∘ c₂ = 0`, for `c₀` and `c₂` as homogeneous morphisms of degree zero. -/
theorem homOf_projectiveLineFibrePointCorr_comp_homOf_projectiveLinePointFibreCorr :
    homOf (X := projectiveLineObj k) (Y := projectiveLineObj k) 0
        (projectiveLineFibrePointCorr x hx) ≫ homOf 0 (projectiveLinePointFibreCorr x hx) = 0 := by
  rw [homOf, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  exact projectiveLine_fibrePoint_comp_pointFibre x hx

/-- `c₀ + c₂ = [Δ] = 1`, for `c₀` and `c₂` as homogeneous morphisms of degree zero. -/
theorem homOf_projectiveLinePointFibreCorr_add_homOf_projectiveLineFibrePointCorr :
    homOf (X := projectiveLineObj k) (Y := projectiveLineObj k) 0
        (projectiveLinePointFibreCorr x hx) + homOf 0 (projectiveLineFibrePointCorr x hx) =
      𝟙 (GradedCompositionData.Obj.mk (projectiveLineObj k) :
        (canonicalCorrespondenceCompositionData k).Obj) := by
  rw [homOf, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  exact (projectiveLine_id_eq_add x hx).symm

/-! ### The decomposition of `h(P¹_k)` -/

/-- The motive `h(P¹_k) = (P¹_k, [Δ], 0)` is the direct sum of `(P¹_k, c₀, 0)` and the Lefschetz
motive `(P¹_k, c₂, 0)`, for `c₀ = [x × P¹_k]` and `c₂ = [P¹_k × x]` the projectors of
Example 0FG6 attached to a `k`-rational point `x`: these are orthogonal idempotents with
`c₀ + c₂ = [Δ]`. The point of the bicone is `h(P¹_k)`, see
`Stacks.WeilCohomology.ChowMotiveCat.projectiveLineSummandsBiproductData_bicone_pt`. -/
def projectiveLineSummandsBiproductData :
    BinaryBiproductData
      (mk' (projectiveLineObj k) (projectiveLinePointFibreCorr x hx)
        (projectiveLinePointFibreCorr_comp_self x hx) 0) (lefschetzMotive x hx) :=
  TwistedKaroubi.ofObjBiproductData _ (homOf_mem_grade _) (homOf_mem_grade _)
    (mk' (projectiveLineObj k) (projectiveLinePointFibreCorr x hx)
      (projectiveLinePointFibreCorr_comp_self x hx) 0).idem
    (lefschetzMotive x hx).idem
    (homOf_projectiveLinePointFibreCorr_comp_homOf_projectiveLineFibrePointCorr x hx)
    (homOf_projectiveLineFibrePointCorr_comp_homOf_projectiveLinePointFibreCorr x hx)
    (homOf_projectiveLinePointFibreCorr_add_homOf_projectiveLineFibrePointCorr x hx)

/-- The point of the bicone of `projectiveLineSummandsBiproductData x hx` is the motive
`h(P¹_k)`. -/
@[simp]
theorem projectiveLineSummandsBiproductData_bicone_pt :
    (projectiveLineSummandsBiproductData x hx).bicone.pt =
      (h k).obj (Opposite.op (projectiveLineObj k)) :=
  rfl

/-- **Stacks Project, Tag 0FGG.** In `M_k` the motive `h(P¹_k)` is the direct sum of
`1 = (Spec k, 1, 0)` and `1(-1) = (Spec k, 1, -1)`: a bilimit binary bicone over `1` and `1(-1)`
whose point is `h(P¹_k)`, see
`Stacks.WeilCohomology.ChowMotiveCat.projectiveLineMotiveBiproductData_bicone_pt`.

It is obtained from the splitting `h(P¹_k) = (P¹_k, c₀, 0) ⊕ (P¹_k, c₂, 0)` by the projectors of
Example 0FG6 attached to the `k`-rational point `x`, followed by the two isomorphisms
`(P¹_k, c₀, 0) ≅ 1` and `(P¹_k, c₂, 0) ≅ 1(-1)` of Lemma 0FGD. -/
@[stacks 0FGG "h(P^1_k) is the direct sum of 1 and 1(-1) in M_k: a bilimit bicone over 1 and
1(-1) with point h(P^1_k), for the actual P^1_k and the actual category of Chow motives"]
def projectiveLineMotiveBiproductData : BinaryBiproductData (tate k 0) (tate k (-1)) :=
  (projectiveLineSummandsBiproductData x hx).ofIso (projectiveLinePointFibreMotiveIso x hx)
    (projectiveLineFibrePointMotiveIso x hx)

/-- The point of the bicone of `projectiveLineMotiveBiproductData x hx` is the motive `h(P¹_k)`. -/
@[simp]
theorem projectiveLineMotiveBiproductData_bicone_pt :
    (projectiveLineMotiveBiproductData x hx).bicone.pt =
      (h k).obj (Opposite.op (projectiveLineObj k)) :=
  rfl

variable (k) in
/-- The direct sum `1 ⊕ 1(-1)` exists in `M_k`: `h(P¹_k)` is one, by
`Stacks.WeilCohomology.ChowMotiveCat.projectiveLineMotiveBiproductData` at the rational point
`∞` of `P¹_k`. -/
instance hasBinaryBiproduct_tate_zero_tate_neg_one :
    HasBinaryBiproduct (tate k 0) (tate k (-1)) :=
  .mk (projectiveLineMotiveBiproductData (lineInfinitySection _) (lineInfinitySection_comp _))

variable (k) in
/-- **Stacks Project, Tag 0FGG.** In `M_k` we have `h(P¹_k) ≅ 1 ⊕ 1(-1)`.

This is `Stacks.WeilCohomology.ChowMotiveCat.projectiveLineMotiveBiproductData`, at the rational
point `∞` of `P¹_k`, compared with the chosen direct sum `1 ⊞ 1(-1)`. -/
@[stacks 0FGG "in M_k we have h(P^1_k) iso 1 + 1(-1), for the actual P^1_k and the actual category
of Chow motives"]
def projectiveLineMotiveIso :
    (h k).obj (Opposite.op (projectiveLineObj k)) ≅ tate k 0 ⊞ tate k (-1) :=
  biprod.uniqueUpToIso _ _ (projectiveLineMotiveBiproductData (lineInfinitySection _)
    (lineInfinitySection_comp _)).isBilimit

end Stacks.WeilCohomology.ChowMotiveCat

end

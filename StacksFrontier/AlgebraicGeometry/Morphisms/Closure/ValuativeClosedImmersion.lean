module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The valuative test for closedness of a quasi-compact immersion

Let `j : Z ⟶ S` be a quasi-compact immersion (a quasi-compact preimmersion suffices). Its image
is closed as soon as it is stable under specialization along valuation rings: whenever `A` is a
valuation ring with fraction field `K` and `h : Spec A ⟶ S` is a morphism whose restriction to
`Spec K` factors through `j`, the closed point of `Spec A` maps into the image of `j`. A
preimmersion with closed image is a closed immersion.

The proof is the valuative diagram of [Stacks, Tag 02JQ]: the closure of the image of a
quasi-compact morphism is the support of its scheme-theoretic image, and every point of that
support is the image of the closed point of a valuation ring whose generic point comes from the
source. This is the reduction with which the proof of
[Stacks, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0) begins.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_valuationRing`: the valuative test.

## References

* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
* [Stacks Project, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The valuative test for closedness of a quasi-compact preimmersion.** Let `j : Z ⟶ S` be a
quasi-compact preimmersion. Suppose that whenever `A` is a valuation ring with fraction field `K`
and `h : Spec A ⟶ S` is a morphism whose restriction `g` to `Spec K` factors through `j`, the
closed point of `Spec A` maps into the image of `j`. Then `j` is a closed immersion.

The closure of the image of `j` is the support of its scheme-theoretic image, and by the
valuative diagram of [Stacks, Tag 02JQ] each point of that support is the image of the closed
point of such an `h`. -/
theorem isClosedImmersion_of_valuationRing
    {Z S : Scheme.{u}} (j : Z ⟶ S) [IsPreimmersion j] [QuasiCompact j]
    (H : ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
      (g : Spec (.of K) ⟶ Z) (h : Spec (.of A) ⟶ S),
      g ≫ j = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h →
        h (closedPoint A) ∈ Set.range j) :
    IsClosedImmersion j := by
  refine .of_isPreimmersion j (closure_subset_iff_isClosed.1 ?_)
  intro y hy
  rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι] at hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨A, _, _, _, K, _, _, _, g, h, hcomm, hclosed⟩ :=
    exists_valuationRing_of_image_point j z
  have hfac : g ≫ j = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ (h ≫ j.imageι) := by
    calc g ≫ j = g ≫ j.toImage ≫ j.imageι := by rw [Scheme.Hom.toImage_imageι]
      _ = (g ≫ j.toImage) ≫ j.imageι := (Category.assoc _ _ _).symm
      _ = _ := by rw [hcomm, Category.assoc]
  have hmem := H A K g (h ≫ j.imageι) hfac
  have hval : (h ≫ j.imageι) (closedPoint A) = j.imageι z :=
    (Scheme.Hom.comp_apply h j.imageι _).trans (congrArg j.imageι hclosed)
  exact hval ▸ hmem

end AlgebraicGeometry

end

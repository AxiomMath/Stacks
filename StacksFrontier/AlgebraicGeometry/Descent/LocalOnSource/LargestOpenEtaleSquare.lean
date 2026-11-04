module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.LargestOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale invariance of the largest open locus in a commutative square

For a property of scheme morphisms which is étale local on the source and target, the largest
open locus of the property is preserved at corresponding points of a commutative square whose
two vertical morphisms are étale at those points.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.mem_largestOpen_iff_of_etaleAt` gives the pointwise equivalence.

## Implementation notes

The points of the lower-left and upper-right schemes are the images of the chosen point of the
upper-left scheme, so only that one point is given; commutativity then determines the point of
the lower-right scheme.

Étaleness at a point is only a condition on some affine neighbourhood, so the first step is to
replace each of the two étale-at-a-point hypotheses by an open neighbourhood on which the
corresponding vertical morphism is genuinely étale after restriction to the source. Intersecting
the neighbourhood of the point with the inverse image of the neighbourhood upstairs gives a
single open `A` of `X'` on which both hold, and over it the square becomes a square of honest
étale morphisms; that case is `mem_largestOpen_iff_of_etale_square`, which is the composite of
`AlgebraicGeometry.preimage_largestOpen_etale` with the observation that postcomposing with an
étale morphism does not change the largest open locus. The equivalence for the original square is
recovered by identifying the two sides over `A` with the two sides over `X'`, again by
`AlgebraicGeometry.preimage_largestOpen_etale` on the source and by the postcomposition
invariance on the target.

That postcomposition invariance, `largestOpen_postcomp_etale`, is where the two cancellation
halves of Tag 04R0 enter: one inclusion is
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.of_comp_etale` and the other is
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.postcomp_of_etale`. Locality on the source for
the étale precoverage, which `AlgebraicGeometry.preimage_largestOpen_etale` takes as an instance
hypothesis, is supplied from `hP` by
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.isLocalAtSource_etalePrecoverage`.

## References

* [Stacks Project, Tag 0CEZ](https://stacks.math.columbia.edu/tag/0CEZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An affine-local étale ring map restricts to an étale morphism of schemes. -/
private alias etale_resLE_of_etale_appLE := etale_resLE_of_appLE_etale

/-- A morphism étale at a point is étale after restricting its source to a suitable open
neighbourhood of that point. -/
private lemma exists_etale_open_neighborhood {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (h : EtaleAt f x) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨U, hU, hxU, V, hV, e, happ⟩ := h
  have hres : Etale (f.resLE V U e) :=
    etale_resLE_of_etale_appLE f U hU V hV e happ
  refine ⟨U, hxU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  infer_instance

/-- Postcomposing with an étale morphism does not change the largest open locus of a property
étale local on the source and target. -/
private lemma largestOpen_postcomp_etale {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : Etale g) :
    largestOpen P (f ≫ g) = largestOpen P f := by
  unfold largestOpen
  congr 1
  ext U
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h ↦ IsEtaleLocalOnSourceAndTarget.of_comp_etale hP (U.ι ≫ f) g hg
      (by simpa only [Category.assoc] using h),
    fun h ↦ IsEtaleLocalOnSourceAndTarget.postcomp_of_etale P hP (U.ι ≫ f) h g hg⟩

/-- The case of Tag 0CEZ in which both vertical morphisms of the square are étale, not merely
étale at the two points. -/
private lemma mem_largestOpen_iff_of_etale_square
    {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y A B : Scheme.{u}} (f : X ⟶ Y) (h : A ⟶ B)
    (a : A ⟶ X) (b : B ⟶ Y) (ha : Etale a) (hb : Etale b)
    (hcomm : a ≫ f = h ≫ b) (z : A) :
    a.base z ∈ largestOpen P f ↔ z ∈ largestOpen P h := by
  let : P.IsLocalAtSource Scheme.etalePrecoverage :=
    IsEtaleLocalOnSourceAndTarget.isLocalAtSource_etalePrecoverage P hP
  show z ∈ a ⁻¹ᵁ largestOpen P f ↔ _
  rw [preimage_largestOpen_etale P a f, hcomm, largestOpen_postcomp_etale hP h b hb]

/-- **Stacks Project, Tag 0CEZ.** Étale morphisms on both sides of a commutative square preserve
membership in the largest open locus of a property étale local on the source and target. -/
@[stacks 0CEZ]
public theorem mem_largestOpen_iff_of_etaleAt
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X' X Y' Y : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (hcomm : g' ≫ f = f' ≫ g) (x' : X')
    (hg' : EtaleAt g' x')
    (hg : EtaleAt g (f'.base x')) :
    g'.base x' ∈ largestOpen P f ↔ x' ∈ largestOpen P f' := by
  obtain ⟨U, hxU, hU⟩ := exists_etale_open_neighborhood g' x' hg'
  obtain ⟨V, hxV, hV⟩ := exists_etale_open_neighborhood g (f'.base x') hg
  let A : X'.Opens := U ⊓ f' ⁻¹ᵁ V
  have hxA : x' ∈ A := ⟨hxU, hxV⟩
  let i : A.toScheme ⟶ X' := A.ι
  let a : A.toScheme ⟶ X := A.ι ≫ g'
  let b : V.toScheme ⟶ Y := V.ι ≫ g
  have hAV : A ≤ f' ⁻¹ᵁ V := inf_le_right
  let h : A.toScheme ⟶ V.toScheme := f'.resLE V A hAV
  have ha : Etale a := by
    show Etale (A.ι ≫ g')
    rw [← Scheme.homOfLE_ι X' (inf_le_left : A ≤ U), Category.assoc]
    let : Etale (U.ι ≫ g') := hU
    infer_instance
  have hb : Etale b := hV
  have hSquare : a ≫ f = h ≫ b := by
    calc
      a ≫ f = A.ι ≫ (g' ≫ f) := by simp [a, Category.assoc]
      _ = A.ι ≫ (f' ≫ g) := by rw [hcomm]
      _ = h ≫ b := by simp [h, b]
  let z : A.toScheme := ⟨x', hxA⟩
  have hrestr : i ≫ f' = h ≫ V.ι := (Scheme.Hom.resLE_comp_ι f' hAV).symm
  show a.base z ∈ largestOpen P f ↔ i.base z ∈ largestOpen P f'
  exact (mem_largestOpen_iff_of_etale_square hP f h a b ha hb hSquare z).trans
    (mem_largestOpen_iff_of_etale_square hP f' h i V.ι inferInstance inferInstance
      hrestr z).symm

end AlgebraicGeometry

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence

/-!
# Independence of the smooth scheme an immersion is Koszul-regular into

Let `U`, `P` and `P'` be schemes over `S` with `P` and `P'` smooth over `S`, and let
`i : U ⟶ P` and `i' : U ⟶ P'` be immersions over `S`. Near a point of `U` the immersion `i` is
Koszul-regular exactly when `i'` is: the two are compared through the immersion
`(i, i') : U ⟶ P ×_S P'`, whose two projections are smooth.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_opens_isKoszulRegularImmersion_comp_iff`
  is Stacks 069E.

## Implementation notes

"Koszul-regular in a neighbourhood of `u`" is an open `V` of the source containing `u` whose
restriction `V.ι ≫ i` is a Koszul-regular immersion, the form in which the condition enters
Stacks 069F. That both immersions are over `S` is recorded by the equalities `i ≫ p = f` and
`i' ≫ p' = f`.

## References

* [Stacks Project, Tag 069E](https://stacks.math.columbia.edu/tag/069E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- Koszul-regularity transports along an equality of immersions. The instance argument of
`IsKoszulRegularImmersion` makes the corresponding rewrite fail on the motive. -/
private theorem isKoszulRegularImmersion_congr' {Y X : Scheme.{u}} {i j : Y ⟶ X}
    [IsImmersion i] [IsImmersion j] (h : i = j) (hi : IsKoszulRegularImmersion i) :
    IsKoszulRegularImmersion j := by
  subst h
  exact hi

/-- One implication of Stacks 069E. The immersion `(i, i') : V ⟶ P ×_S P'` is Koszul-regular
because its composite with the smooth first projection is, and composing it with the smooth
second projection returns `i'`. -/
private theorem exists_opens_isKoszulRegularImmersion_comp_of
    {S U P P' : Scheme.{u}} (f : U ⟶ S) (p : P ⟶ S) (p' : P' ⟶ S)
    (i : U ⟶ P) (i' : U ⟶ P') [IsImmersion i] [IsImmersion i'] [Smooth p] [Smooth p']
    (hi : i ≫ p = f) (hi' : i' ≫ p' = f) (u : U)
    (h : ∃ V : U.Opens, u ∈ V ∧ IsKoszulRegularImmersion (V.ι ≫ i)) :
    ∃ V : U.Opens, u ∈ V ∧ IsKoszulRegularImmersion (V.ι ≫ i') := by
  obtain ⟨V, huV, hreg⟩ := h
  refine ⟨V, huV, ?_⟩
  have hcomm : (V.ι ≫ i) ≫ p = (V.ι ≫ i') ≫ p' := by
    rw [Category.assoc, Category.assoc, hi, hi']
  let j : V.toScheme ⟶ pullback p p' := pullback.lift (V.ι ≫ i) (V.ι ≫ i') hcomm
  have hjfst : j ≫ pullback.fst p p' = V.ι ≫ i := pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd p p' = V.ι ≫ i' := pullback.lift_snd _ _ _
  have hfst : IsImmersion (j ≫ pullback.fst p p') := by
    rw [hjfst]
    infer_instance
  have hsnd : IsImmersion (j ≫ pullback.snd p p') := by
    rw [hjsnd]
    infer_instance
  have hjim : IsImmersion j := IsImmersion.of_comp j (pullback.fst p p')
  exact isKoszulRegularImmersion_congr' hjsnd
    (isKoszulRegularImmersion_comp_of_smooth j (pullback.snd p p')
      (isKoszulRegularImmersion_of_comp_of_smooth j (pullback.fst p p')
        (isKoszulRegularImmersion_congr' hjfst.symm hreg)))

/-- **Stacks 069E.** Let `i : U ⟶ P` and `i' : U ⟶ P'` be immersions over `S` of schemes smooth
over `S`. Then `i` is a Koszul-regular immersion in a neighbourhood of `u : U` if and only if
`i'` is. -/
@[stacks 069E]
theorem exists_opens_isKoszulRegularImmersion_comp_iff
    {S U P P' : Scheme.{u}} (f : U ⟶ S) (p : P ⟶ S) (p' : P' ⟶ S)
    (i : U ⟶ P) (i' : U ⟶ P') [IsImmersion i] [IsImmersion i'] [Smooth p] [Smooth p']
    (hi : i ≫ p = f) (hi' : i' ≫ p' = f) (u : U) :
    (∃ V : U.Opens, u ∈ V ∧ IsKoszulRegularImmersion (V.ι ≫ i)) ↔
      ∃ V : U.Opens, u ∈ V ∧ IsKoszulRegularImmersion (V.ι ≫ i') :=
  ⟨exists_opens_isKoszulRegularImmersion_comp_of f p p' i i' hi hi' u,
    exists_opens_isKoszulRegularImmersion_comp_of f p' p i' i hi' hi u⟩

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Common standard open neighbourhoods in two affine schemes

If a scheme admits open immersions into two affine schemes, every point has an affine open
neighbourhood whose images in both affine schemes are standard opens.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_mapped_to_basicOpens` gives a common affine open
  neighbourhood that maps to a basic open in each of two affine schemes.

## Implementation notes

The image of an open subscheme under an open immersion is represented by
`Scheme.Hom.opensFunctor`. Mathlib calls standard opens `Scheme.basicOpen`.

## References

* [Stacks Project, Tag 0H9B](https://stacks.math.columbia.edu/tag/0H9B)
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If `U` is affine and `i : W ⟶ U` is an open immersion whose range contains `D(a)`, then the
image of a basic open of `i ⁻¹ᵁ D(a)` is a basic open of `U`. -/
private theorem image_basicOpen_eq_basicOpen {U W : Scheme.{u}} [IsAffine U] (i : W ⟶ U)
    [IsOpenImmersion i] {a : Γ(U, ⊤)} (ha : U.basicOpen a ≤ i.opensRange)
    (r : Γ(W, i ⁻¹ᵁ U.basicOpen a)) : ∃ f : Γ(U, ⊤), i ''ᵁ W.basicOpen r = U.basicOpen f := by
  have hiA : i ''ᵁ (i ⁻¹ᵁ U.basicOpen a) = U.basicOpen a := by
    simp only [i.image_preimage_eq_opensRange_inf, inf_eq_right.mpr ha]
  obtain ⟨f, hf⟩ := (isAffineOpen_top U).basicOpen_basicOpen_is_basicOpen a
    (U.presheaf.map (eqToHom hiA.symm).op ((i.appIso _).inv r))
  exact ⟨f, ((Scheme.image_basicOpen i r).trans
    (Scheme.basicOpen_res_eq U ((i.appIso _).inv r) (eqToHom hiA.symm).op).symm).trans hf.symm⟩

/-- A point of a scheme admitting open immersions into two affine schemes has an affine open
neighbourhood whose image in each scheme is a basic open. -/
@[stacks 0H9B]
theorem exists_isAffineOpen_mapped_to_basicOpens
    (U V W : Scheme.{u}) [IsAffine U] [IsAffine V]
    (i : W ⟶ U) (j : W ⟶ V) [IsOpenImmersion i] [IsOpenImmersion j] (w : W) :
    ∃ (W' : W.Opens) (f : Γ(U, ⊤)) (g : Γ(V, ⊤)),
      IsAffineOpen W' ∧ w ∈ W' ∧
        i.opensFunctor.obj W' = U.basicOpen f ∧
        j.opensFunctor.obj W' = V.basicOpen g := by
  obtain ⟨a, ha, hwa⟩ := (isAffineOpen_top U).exists_basicOpen_le
    (⟨i w, ⟨w, rfl⟩⟩ : i.opensRange) (Set.mem_univ _)
  obtain ⟨b, hb, hwb⟩ := (isAffineOpen_top V).exists_basicOpen_le
    (⟨j w, ⟨w, rfl⟩⟩ : j.opensRange) (Set.mem_univ _)
  let A := i ⁻¹ᵁ U.basicOpen a
  let B := j ⁻¹ᵁ V.basicOpen b
  have hA : IsAffineOpen A :=
    ((isAffineOpen_top U).basicOpen a).preimage_of_isOpenImmersion i ha
  have hB : IsAffineOpen B :=
    ((isAffineOpen_top V).basicOpen b).preimage_of_isOpenImmersion j hb
  obtain ⟨r, s, hrs, hwr⟩ := exists_basicOpen_le_affine_inter hA hB w ⟨hwa, hwb⟩
  obtain ⟨f, hf⟩ := image_basicOpen_eq_basicOpen i ha r
  obtain ⟨g, hg⟩ := image_basicOpen_eq_basicOpen j hb s
  refine ⟨W.basicOpen r, f, g, hA.basicOpen r, hwr, hf, ?_⟩
  simpa only [hrs] using hg

end AlgebraicGeometry

end

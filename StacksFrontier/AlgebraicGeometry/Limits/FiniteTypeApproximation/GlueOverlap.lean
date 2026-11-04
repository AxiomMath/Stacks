module

public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.GluePair
/-!
# The overlap of the two legs of a glueing

For open immersions `f : W ⟶ X` and `g : W ⟶ Y`, the two legs of
`AlgebraicGeometry.Scheme.gluePair f g` cover it
(`AlgebraicGeometry.Scheme.gluePair_opensRange_sup`) and meet exactly in the image of `W`.  This
file records the second statement, in the form in which the one-affine-open step of Stacks 07RN
uses it: the inverse image of the image of one leg under the other leg is the image of the
corresponding morphism out of `W`.

Together with the covering statement this is what reduces a question about the glueing — the
inverse image of an open of a later stage, the affineness of a transition morphism — to the
same question on `X` and on `Y` separately.

## Main results

* `AlgebraicGeometry.Scheme.preimage_opensRange_gluePairInl` and
  `AlgebraicGeometry.Scheme.preimage_opensRange_gluePairInr`: the two legs of a glueing meet
  exactly in the image of the common open subscheme.
* `AlgebraicGeometry.opens_ext_of_opensRange_sup`: two opens of a scheme covered by the images
  of two morphisms agree as soon as their inverse images under both agree.

## Implementation notes

`AlgebraicGeometry.Scheme.gluePair` is the colimit of
`AlgebraicGeometry.Scheme.gluePairDiagram`, the wide span over
`CategoryTheory.Limits.WidePushoutShape CategoryTheory.Limits.WalkingPair`, so the computation
is Mathlib's `AlgebraicGeometry.Scheme.IsLocallyDirected.ι_eq_ι_iff`: a point of the colimit
lying in the images of two objects is already identified over a third object mapping to both.
The shape has *no* morphism between its two outer objects, so that third object is the centre,
whose structure morphisms are `f` and `g`.  This is the same argument as
`AlgebraicGeometry.opensRange_pushout_inl_inf_inr` runs for
`CategoryTheory.Limits.WalkingSpan`.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Two opens of a scheme whose underlying space is covered by the images of two morphisms agree
as soon as their inverse images under both morphisms agree. -/
lemma opens_ext_of_opensRange_sup {S A C : Scheme.{u}} (i₁ : A ⟶ S) (i₂ : C ⟶ S)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (hcov : i₁.opensRange ⊔ i₂.opensRange = ⊤) {U V : S.Opens}
    (h₁ : i₁ ⁻¹ᵁ U = i₁ ⁻¹ᵁ V) (h₂ : i₂ ⁻¹ᵁ U = i₂ ⁻¹ᵁ V) : U = V := by
  refine Opens.ext (Set.ext fun x ↦ ?_)
  have hx : x ∈ (i₁.opensRange ⊔ i₂.opensRange : S.Opens) := by rw [hcov]; trivial
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := Opens.mem_sup.mp hx
  · exact ⟨fun hy ↦ (congrArg (fun T ↦ y ∈ T) h₁ ▸ hy : y ∈ i₁ ⁻¹ᵁ V),
      fun hy ↦ (congrArg (fun T ↦ y ∈ T) h₁.symm ▸ hy : y ∈ i₁ ⁻¹ᵁ U)⟩
  · exact ⟨fun hy ↦ (congrArg (fun T ↦ y ∈ T) h₂ ▸ hy : y ∈ i₂ ⁻¹ᵁ V),
      fun hy ↦ (congrArg (fun T ↦ y ∈ T) h₂.symm ▸ hy : y ∈ i₂ ⁻¹ᵁ U)⟩

namespace Scheme

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

/-- Points of two distinct outer objects of the glueing diagram that become equal in the colimit
come from a common point of the centre. -/
private lemma exists_map_init_eq_of_ι_eq_ι {i j : WalkingPair} (hij : i ≠ j) {x y}
    (h : colimit.ι (gluePairDiagram f g) (some i) x = colimit.ι (gluePairDiagram f g) (some j) y) :
    ∃ z, (gluePairDiagram f g).map (WidePushoutShape.Hom.init i) z = x := by
  obtain ⟨k, fi, fj, z, hzi, -⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (gluePairDiagram f g)).mp h
  match k, fi, fj with
  | none, WidePushoutShape.Hom.init _, _ => exact ⟨z, hzi⟩
  | some _, fi, fj => cases fi; cases fj; exact (hij rfl).elim

/-- **The two legs of a glueing meet in the image of the common open subscheme.**  The inverse
image of the first leg under the second is the image of `g`. -/
lemma preimage_opensRange_gluePairInl :
    gluePairInr f g ⁻¹ᵁ (gluePairInl f g).opensRange = g.opensRange := by
  apply Opens.ext
  apply Set.Subset.antisymm
  · rintro x ⟨y, hxy⟩
    exact exists_map_init_eq_of_ι_eq_ι f g (by simp) hxy.symm
  · rintro x ⟨z, rfl⟩
    exact ⟨f z, by rw [← Scheme.Hom.comp_apply, gluePair_condition, Scheme.Hom.comp_apply]⟩

/-- **The two legs of a glueing meet in the image of the common open subscheme.**  The inverse
image of the second leg under the first is the image of `f`. -/
lemma preimage_opensRange_gluePairInr :
    gluePairInl f g ⁻¹ᵁ (gluePairInr f g).opensRange = f.opensRange := by
  apply Opens.ext
  apply Set.Subset.antisymm
  · rintro x ⟨y, hxy⟩
    exact exists_map_init_eq_of_ι_eq_ι f g (by simp) hxy.symm
  · rintro x ⟨z, rfl⟩
    exact ⟨g z, by rw [← Scheme.Hom.comp_apply, ← gluePair_condition, Scheme.Hom.comp_apply]⟩

end Scheme

end AlgebraicGeometry

end

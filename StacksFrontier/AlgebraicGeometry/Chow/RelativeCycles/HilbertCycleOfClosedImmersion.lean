module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassFacet

/-!
# A member of `Hilb(X/S, r)` presented by a closed immersion

A member of `Hilb(X/S, r)` (Section [0H6V](https://stacks.math.columbia.edu/tag/0H6V)) is a closed
subscheme `Z ⊆ X`, flat, of finite presentation and of relative dimension at most `r` over `S`.
In `Stacks.Chow.HilbertCycleDatum` the closed subscheme is recorded by its ideal sheaf. This file
produces the datum from an arbitrary closed immersion `w : W ⟶ X` with the three properties, and
identifies its cycle class with the family `[W/X/S]_r` of Example 0H4S.

## Main definitions

* `Stacks.Chow.HilbertCycleDatum.ofClosedImmersion` — the member of `Hilb(X/S, r)` cut out by the
  kernel ideal sheaf of a closed immersion `w : W ⟶ X` which is flat, locally of finite
  presentation, quasi-compact and of relative dimension at most `r` over `S`.

## Main results

* `Stacks.Chow.HilbertCycleDatum.cycleFamily_ofClosedImmersion` — its cycle class is
  `[W/X/S]_r`.

## Implementation notes

The closed subscheme cut out by the kernel of `w` is the scheme-theoretic image of `w`, and `w`
is an isomorphism onto it (`AlgebraicGeometry.Scheme.Hom.toImage`); the three morphism
properties and the dimension bound are transported along that isomorphism.

## References

* [Stacks Project, Section 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
* [Stacks Project, Example 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.HilbertCycleDatum

variable {X S W : Scheme.{u}} (f : X ⟶ S) (r : ℕ) (w : W ⟶ X) [IsClosedImmersion w]

/-- A closed immersion is an isomorphism onto the closed subscheme cut out by its kernel. -/
def kerSubschemeIso : W ≅ w.ker.subscheme :=
  asIso w.toImage

/-- The isomorphism `kerSubschemeIso w` followed by the inclusion of the closed subscheme cut out
by the kernel of `w` is `w`. -/
@[reassoc]
theorem kerSubschemeIso_hom_subschemeι : (kerSubschemeIso w).hom ≫ w.ker.subschemeι = w :=
  w.toImage_imageι

/-- The inverse of `kerSubschemeIso w` followed by `w` is the inclusion of the closed subscheme
cut out by the kernel of `w`. -/
@[reassoc]
theorem kerSubschemeIso_inv_comp : (kerSubschemeIso w).inv ≫ w = w.ker.subschemeι := by
  rw [Iso.inv_comp_eq, kerSubschemeIso_hom_subschemeι]

/-- The structure morphism of the closed subscheme cut out by the kernel of `w`, read through
the isomorphism with `W`. -/
theorem ker_subschemeι_comp : w.ker.subschemeι ≫ f = (kerSubschemeIso w).inv ≫ w ≫ f := by
  rw [kerSubschemeIso_inv_comp_assoc]

/-- **The member of `Hilb(X/S, r)` presented by a closed immersion.** Let `w : W ⟶ X` be a closed
immersion such that `W ⟶ S` is flat, locally of finite presentation, quasi-compact and of
relative dimension at most `r`. The closed subscheme it cuts out, recorded by the kernel ideal
sheaf of `w`, is a member of `Hilb(X/S, r)`. -/
def ofClosedImmersion [Flat (w ≫ f)] [LocallyOfFinitePresentation (w ≫ f)]
    [QuasiCompact (w ≫ f)] (hdim : RelativeDimensionLE (w ≫ f) r) : HilbertCycleDatum f r where
  ideal := w.ker
  flat := by
    rw [ker_subschemeι_comp]
    infer_instance
  locallyFinitePresentation := by
    rw [ker_subschemeι_comp]
    infer_instance
  quasiCompact := by
    rw [ker_subschemeι_comp]
    infer_instance
  relativeDimensionLE := by
    have hsq : IsPullback (kerSubschemeIso w).inv (w.ker.subschemeι ≫ f) (w ≫ f) (𝟙 S) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ker_subschemeι_comp]⟩
    exact RelativeDimensionLE.of_isPullback hsq hdim

/-- The ideal sheaf of `ofClosedImmersion f r w hdim` is the kernel of `w`. -/
@[simp]
theorem ofClosedImmersion_ideal [Flat (w ≫ f)] [LocallyOfFinitePresentation (w ≫ f)]
    [QuasiCompact (w ≫ f)] (hdim : RelativeDimensionLE (w ≫ f) r) :
    (ofClosedImmersion f r w hdim).ideal = w.ker :=
  rfl

/-- **The cycle class of the member of `Hilb(X/S, r)` presented by a closed immersion** is the
family `[W/X/S]_r` of Example 0H4S. -/
theorem cycleFamily_ofClosedImmersion [LocallyOfFinitePresentation f] [Flat (w ≫ f)]
    [LocallyOfFinitePresentation (w ≫ f)] [QuasiCompact (w ≫ f)]
    (hdim : RelativeDimensionLE (w ≫ f) r) :
    (ofClosedImmersion f r w hdim).cycleFamily f = familyAssociatedToClosedSubscheme f w r := by
  rw [cycleFamily_eq_familyAssociatedToClosedSubscheme]
  exact familyAssociatedToClosedSubscheme_eq_of_iso f w.ker.subschemeι w
    (kerSubschemeIso w).symm (kerSubschemeIso_inv_comp w) r

end Stacks.Chow.HilbertCycleDatum

end

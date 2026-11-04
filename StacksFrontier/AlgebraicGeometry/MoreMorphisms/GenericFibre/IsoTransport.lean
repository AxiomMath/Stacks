module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Transporting a morphism property along a pullback square with isomorphic base

In a pullback square whose lower horizontal morphism is an isomorphism, so is the upper one, and
the two vertical morphisms are therefore isomorphic as arrows. Any morphism property which
respects isomorphisms holds for one if and only if it holds for the other.

Two instances of this are used in the reduction step of Stacks Tag 0559, both coming from
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`:

* an isomorphism of the target does not change the fibres, because the residue field map of an
  isomorphism is an isomorphism;
* the fibre of `f ∣_ V` at a point of an open `V` of the target is the fibre of `f` at the
  corresponding point of the target, because the residue field map of an open immersion is an
  isomorphism.

## Main results

* `AlgebraicGeometry.morphismProperty_iff_of_isPullback_of_isIso`
* `AlgebraicGeometry.prop_fiberToSpecResidueField_comp_iso_iff`
* `AlgebraicGeometry.prop_fiberToSpecResidueField_of_morphismRestrict`

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The spectrum of an isomorphism of rings is an isomorphism of schemes. -/
private instance isIso_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsIso φ] :
    IsIso (Spec.map φ) :=
  (Scheme.Spec.mapIso (asIso φ).op).isIso_hom

/-- In a pullback square whose lower horizontal morphism is an isomorphism, the two vertical
morphisms satisfy the same isomorphism invariant morphism properties. -/
theorem morphismProperty_iff_of_isPullback_of_isIso {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {A B C D : Scheme.{u}} {m : A ⟶ B} {n : A ⟶ C} {p : B ⟶ D} {q : C ⟶ D}
    (hsq : IsPullback m n p q) [IsIso q] : P n ↔ P p := by
  have hm : IsIso m := hsq.isIso_fst_of_isIso
  have hn : n = m ≫ p ≫ inv q := by
    rw [← Category.assoc, hsq.w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hn, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]

/-- Composing with an isomorphism of the target does not change the fibres: the fibre of
`f ≫ e.hom` at `e.hom y` satisfies an isomorphism invariant morphism property if and only if the
fibre of `f` at `y` does. -/
theorem prop_fiberToSpecResidueField_comp_iso_iff {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) (y : Y) :
    P ((f ≫ e.hom).fiberToSpecResidueField (e.hom y)) ↔ P (f.fiberToSpecResidueField y) := by
  have hsq : IsPullback (𝟙 X) f (f ≫ e.hom) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (morphismProperty_iff_of_isPullback_of_isIso (P := P)
    (isPullback_fiberToSpecResidueField_of_isPullback hsq y)).symm

/-- The fibre of `f ∣_ V` at a point `v` of an open subscheme `V` of the target satisfies an
isomorphism invariant morphism property if and only if the fibre of `f` at the image of `v`
does. -/
theorem prop_fiberToSpecResidueField_of_morphismRestrict {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (v : V.toScheme) :
    P ((f ∣_ V).fiberToSpecResidueField v) ↔ P (f.fiberToSpecResidueField (V.ι v)) :=
  morphismProperty_iff_of_isPullback_of_isIso (P := P)
    (isPullback_fiberToSpecResidueField_of_isPullback (isPullback_morphismRestrict f V).flip v)

end AlgebraicGeometry

end

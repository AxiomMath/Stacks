module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionFull

/-!
# Lifting sections along a morphism which is an isomorphism over a subfunctor

Let `g : F ⟶ W` be a morphism of presheaves on the big fppf site of `S` and let `W₀` be a
subfunctor of `W` such that the restriction `g⁻¹W₀ ⟶ W₀` of `g` is an isomorphism. Then `g`
is bijective on the sections lying over `W₀`: injectivity is
`AlgebraicGeometry.Space.eq_of_app_eq_of_mem`, and surjectivity is proved here.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_snd_of_isIso_fromPreimage`: the converse of
  `AlgebraicGeometry.Space.isIso_fromPreimage_of_isIso_pullback_snd`, so that the two shapes
  of "is an isomorphism over a subfunctor" — invertibility of
  `CategoryTheory.Limits.pullback.snd`, which is what the definition of a modification uses,
  and invertibility of `CategoryTheory.Subfunctor.fromPreimage`, which is what is usable on
  sections — are interchangeable.
* `AlgebraicGeometry.Space.exists_app_eq_of_mem`: every section lying in the subfunctor lifts.

## Implementation notes

Both statements are about an arbitrary morphism of presheaves and an arbitrary subfunctor; no
algebraicity, openness or closedness is used. They are separated from their application so
that the rigidity computation of Stacks 0BGY, which consumes them, does not have to reprove
them.

`AlgebraicGeometry.Space.exists_app_eq_of_mem` is the existence counterpart of the uniqueness
statement `AlgebraicGeometry.Space.eq_of_app_eq_of_mem`; together they say that
`CategoryTheory.Subfunctor.fromPreimage` being invertible is exactly unique lifting of
sections over the subfunctor, which is the form in which "is an isomorphism over `W₀`" gets
used in practice.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism whose restriction from the preimage of a subfunctor onto that subfunctor is an
isomorphism has an invertible base change to the subfunctor. This is the converse of
`AlgebraicGeometry.Space.isIso_fromPreimage_of_isIso_pullback_snd`. -/
theorem isIso_pullback_snd_of_isIso_fromPreimage (g : F ⟶ W) (W₀ : Subfunctor W)
    (h : IsIso (W₀.fromPreimage g)) : IsIso (pullback.snd g W₀.ι) := by
  have hp : IsPullback ((W₀.preimage g).ι) (W₀.fromPreimage g) g W₀.ι :=
    (Subfunctor.isPullback_fromPreimage W₀ g).flip
  have he : hp.isoPullback.hom ≫ pullback.snd g W₀.ι = W₀.fromPreimage g :=
    hp.isoPullback_hom_snd
  have _ := h
  have _ : IsIso (hp.isoPullback.hom ≫ pullback.snd g W₀.ι) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left hp.isoPullback.hom _

/-- A morphism which restricts to an isomorphism from the preimage of a subfunctor onto that
subfunctor lifts every section lying in the subfunctor. This is the existence counterpart of
`AlgebraicGeometry.Space.eq_of_app_eq_of_mem`. -/
theorem exists_app_eq_of_mem (g : F ⟶ W) (W₀ : Subfunctor W) (hiso : IsIso (W₀.fromPreimage g))
    {A : (BigFppfOver B S hS)ᵒᵖ} {w : W.obj A} (hw : w ∈ W₀.obj A) :
    ∃ x : F.obj A, g.app A x = w := by
  have _ := hiso
  refine ⟨((inv (W₀.fromPreimage g)).app A ⟨w, hw⟩).val, ?_⟩
  have hid := ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id (W₀.fromPreimage g)) A) (⟨w, hw⟩ : W₀.toFunctor.obj A)
  simp only [NatTrans.comp_app, NatTrans.id_app] at hid
  exact congrArg Subtype.val hid

/-- Unique lifting of sections over the subfunctor: a morphism which restricts to an
isomorphism from the preimage of a subfunctor onto that subfunctor lifts every section lying
in the subfunctor, uniquely. -/
theorem existsUnique_app_eq_of_mem (g : F ⟶ W) (W₀ : Subfunctor W)
    (hiso : IsIso (W₀.fromPreimage g)) {A : (BigFppfOver B S hS)ᵒᵖ} {w : W.obj A}
    (hw : w ∈ W₀.obj A) : ∃! x : F.obj A, g.app A x = w := by
  obtain ⟨x, hx⟩ := exists_app_eq_of_mem B S hS g W₀ hiso hw
  refine ⟨x, hx, fun x' hx' => ?_⟩
  refine eq_of_app_eq_of_mem B S hS g W₀ hiso (hx'.trans hx.symm) ?_
  rw [hx']; exact hw

end AlgebraicGeometry.Space

end

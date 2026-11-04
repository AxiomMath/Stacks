module

public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# Detecting the shift compatibility of the tensorator of a lax monoidal functor

`CategoryTheory.Functor.LaxMonoidal.CommShift R T` is two families of one-variable conditions,
one for each reading `CategoryTheory.Functor.LaxMonoidal.μNatTransFst R Y` and `μNatTransSnd R X`
of the tensorator.  Each is a `CategoryTheory.NatTrans.CommShift`, and so may be tested after
restriction along an essentially surjective shift-compatible functor by
`CategoryTheory.NatTrans.commShift_of_whiskerLeft`.  The *fixed* object of the other variable
can be moved to the image of that functor as well, because the condition only depends on it up
to isomorphism: that is the content of this file.

Together the two reductions say that for a tensorator whose value is only computable at a family
of chosen models -- the K-flat complexes, for the derived tensor product -- the whole condition
may be checked on that family.

## Main results

* `CategoryTheory.Functor.LaxMonoidal.commShift_μNatTransFst_of_iso` and
  `commShift_μNatTransSnd_of_iso`: **the condition in one variable depends on the fixed object of
  the other only up to isomorphism.**
* `CategoryTheory.Functor.LaxMonoidal.CommShift.of_essSurj₂`: **the tensorator of a lax monoidal
  functor commutes with the shift as soon as both of its one-variable readings do after
  restriction along two essentially surjective shift-compatible functors**, one for the varying
  and one for the fixed variable, with `CommShift.of_essSurj` the case of a single functor.

## Implementation notes

The conjugating isomorphisms are the images of the comparison isomorphism under the tensor
products of the two categories, whiskered by `R` on one side and whiskering `R` on the other.
Their shift compatibility is exactly what
`CategoryTheory.MonoidalCategory.TensorCommShift` asserts of the two tensor products, so that
class appears in the hypotheses here although `CategoryTheory.Functor.LaxMonoidal.CommShift`
itself does not mention it.

This is the one-variable analogue, for a transformation which is *not* presented as a
transformation of bifunctors, of `CategoryTheory.NatTrans.CommShift₂.of_essSurj`.  The tensorator
is a morphism of bifunctors, but writing it as one would require naming the two bifunctors
`(X, Y) ↦ R X ⊗ R Y` and `(X, Y) ↦ R (X ⊗ Y)` and equipping each with a
`CategoryTheory.Functor.CommShift₂` structure -- hence a `CategoryTheory.CommShift₂Setup` and the
sign coherence between the two variables, neither of which either conclusion needs.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ v v' u₁ u₂ u u'

namespace Functor.LaxMonoidal

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
  {A : Type u₂} [Category.{v₂} A] [MonoidalCategory A]
  (R : E ⥤ A) [R.LaxMonoidal]
  (T : Type*) [AddMonoid T] [HasShift E T] [HasShift A T] [R.CommShift T]
  [∀ X : E, (tensorLeft X).CommShift T] [∀ Y : E, (tensorRight Y).CommShift T]
  [∀ X : A, (tensorLeft X).CommShift T] [∀ Y : A, (tensorRight Y).CommShift T]
  [TensorCommShift E T] [TensorCommShift A T]

/-- **The condition on the first reading of the tensorator depends on the fixed second object
only up to isomorphism.**  By `CategoryTheory.Functor.LaxMonoidal.μ_natural_right` the
transformation at `Y` is the conjugate of the one at `Y'` by the images of the comparison
isomorphism under the two tensor products, and those are shift-compatible by
`CategoryTheory.MonoidalCategory.TensorCommShift`. -/
theorem commShift_μNatTransFst_of_iso {Y Y' : E} (e : Y ≅ Y')
    (h : NatTrans.CommShift (μNatTransFst R Y') T) :
    NatTrans.CommShift (μNatTransFst R Y) T := by
  have := h
  have : NatTrans.CommShift ((curriedTensor A).flip.map (R.map e.hom)) T :=
    TensorCommShift.commShift_curriedTensor_flip_map (R.map e.hom)
  have : NatTrans.CommShift ((curriedTensor E).flip.map e.hom) T :=
    TensorCommShift.commShift_curriedTensor_flip_map e.hom
  have : NatTrans.CommShift
      (Functor.isoWhiskerLeft R ((curriedTensor A).flip.mapIso (R.mapIso e))).hom T :=
    inferInstanceAs (NatTrans.CommShift
      (Functor.whiskerLeft R ((curriedTensor A).flip.map (R.map e.hom))) T)
  have : NatTrans.CommShift
      (Functor.isoWhiskerRight ((curriedTensor E).flip.mapIso e) R).hom T :=
    inferInstanceAs (NatTrans.CommShift
      (Functor.whiskerRight ((curriedTensor E).flip.map e.hom) R) T)
  refine NatTrans.commShift_of_eq_conj
    (Functor.isoWhiskerLeft R ((curriedTensor A).flip.mapIso (R.mapIso e)))
    (Functor.isoWhiskerRight ((curriedTensor E).flip.mapIso e) R) (μNatTransFst R Y') ?_
  ext X
  dsimp only [NatTrans.comp_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.flip_map_app, curriedTensor_obj_map,
    μNatTransFst_app]
  rw [μ_natural_right_assoc, ← R.map_comp, ← MonoidalCategory.whiskerLeft_comp,
    e.hom_inv_id, MonoidalCategory.whiskerLeft_id, R.map_id, Category.comp_id]

/-- **The condition on the second reading of the tensorator depends on the fixed first object
only up to isomorphism**, the mirror of
`CategoryTheory.Functor.LaxMonoidal.commShift_μNatTransFst_of_iso` through
`CategoryTheory.Functor.LaxMonoidal.μ_natural_left`. -/
theorem commShift_μNatTransSnd_of_iso {X X' : E} (e : X ≅ X')
    (h : NatTrans.CommShift (μNatTransSnd R X') T) :
    NatTrans.CommShift (μNatTransSnd R X) T := by
  have := h
  have : NatTrans.CommShift ((curriedTensor A).map (R.map e.hom)) T :=
    TensorCommShift.commShift_curriedTensor_map (R.map e.hom)
  have : NatTrans.CommShift ((curriedTensor E).map e.hom) T :=
    TensorCommShift.commShift_curriedTensor_map e.hom
  have : NatTrans.CommShift
      (Functor.isoWhiskerLeft R ((curriedTensor A).mapIso (R.mapIso e))).hom T :=
    inferInstanceAs (NatTrans.CommShift
      (Functor.whiskerLeft R ((curriedTensor A).map (R.map e.hom))) T)
  have : NatTrans.CommShift
      (Functor.isoWhiskerRight ((curriedTensor E).mapIso e) R).hom T :=
    inferInstanceAs (NatTrans.CommShift
      (Functor.whiskerRight ((curriedTensor E).map e.hom) R) T)
  refine NatTrans.commShift_of_eq_conj
    (Functor.isoWhiskerLeft R ((curriedTensor A).mapIso (R.mapIso e)))
    (Functor.isoWhiskerRight ((curriedTensor E).mapIso e) R) (μNatTransSnd R X') ?_
  ext Y
  dsimp only [NatTrans.comp_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.mapIso_inv, curriedTensor_map_app, μNatTransSnd_app]
  rw [μ_natural_left_assoc, ← R.map_comp, ← MonoidalCategory.comp_whiskerRight,
    e.hom_inv_id, MonoidalCategory.id_whiskerRight, R.map_id, Category.comp_id]

variable {V : Type u} [Category.{v} V] [HasShift V T]
  {V' : Type u'} [Category.{v'} V'] [HasShift V' T]

/-- **The tensorator of a lax monoidal functor commutes with the shift as soon as both of its
one-variable readings do after restriction along two essentially surjective shift-compatible
functors -- the varying variable along one and the fixed variable along the other.**

The varying variable is reduced by `CategoryTheory.NatTrans.commShift_of_whiskerLeft` and the
fixed one by `CategoryTheory.Functor.LaxMonoidal.commShift_μNatTransFst_of_iso`, whose comparison
isomorphism is `CategoryTheory.Functor.objObjPreimageIso`; the two reductions are independent, so
the two variables may be restricted along different functors.

Two functors rather than one because a comparison isomorphism for a tensor product need not be
symmetric in its two arguments: the K-flat comparison of a derived tensor product, read in the
first variable, is an isomorphism of functors on the *left* K-flat complexes at a *two-sided*
K-flat fixed object, and the other way round in the second variable. -/
theorem CommShift.of_essSurj₂ (q : V ⥤ E) [q.EssSurj] [q.CommShift T]
    (q' : V' ⥤ E) [q'.EssSurj] [q'.CommShift T]
    (h₁ : ∀ L : V', NatTrans.CommShift (Functor.whiskerLeft q (μNatTransFst R (q'.obj L))) T)
    (h₂ : ∀ K : V, NatTrans.CommShift (Functor.whiskerLeft q' (μNatTransSnd R (q.obj K))) T) :
    LaxMonoidal.CommShift R T where
  commShift_μNatTransFst Y :=
    commShift_μNatTransFst_of_iso R T (q'.objObjPreimageIso Y).symm
      (NatTrans.commShift_of_whiskerLeft q _ (h₁ (q'.objPreimage Y)))
  commShift_μNatTransSnd X :=
    commShift_μNatTransSnd_of_iso R T (q.objObjPreimageIso X).symm
      (NatTrans.commShift_of_whiskerLeft q' _ (h₂ (q.objPreimage X)))

/-- **`CategoryTheory.Functor.LaxMonoidal.CommShift.of_essSurj₂` with one functor for both
variables.** -/
theorem CommShift.of_essSurj (q : V ⥤ E) [q.EssSurj] [q.CommShift T]
    (h₁ : ∀ L : V, NatTrans.CommShift (Functor.whiskerLeft q (μNatTransFst R (q.obj L))) T)
    (h₂ : ∀ K : V, NatTrans.CommShift (Functor.whiskerLeft q (μNatTransSnd R (q.obj K))) T) :
    LaxMonoidal.CommShift R T :=
  CommShift.of_essSurj₂ R T q q h₁ h₂

end Functor.LaxMonoidal

end CategoryTheory

end

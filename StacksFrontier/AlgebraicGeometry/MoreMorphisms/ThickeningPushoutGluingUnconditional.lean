module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale

/-!
# Clauses (1) to (4) of Tag 07RX for the gluing functor of Tag 07RV

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT].  The functors `F` and `G` of
[Stacks Project, Tag 07RV] are `Stacks.Pushout.baseChangeFunctor` and
`Stacks.Pushout.gluingFunctor` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing`, and the five clauses of
[Stacks Project, Tag 07RX] are proved for a triple over a pushout situation in
`StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluing`, in a form carrying
[Stacks Project, Tag 06AD] — *a thickening of an affine scheme is affine* — as an explicit
universally quantified hypothesis `H`.  That hypothesis is a theorem,
`Stacks.Thickenings.forall_isAffine_of_isThickening`, and
`Stacks.Pushout.etale_gluingFunctor_obj_iff` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale` is clause (5) for the
gluing functor with it discharged.  This file does the same for clauses (1) to (4).

## Main results

* `Stacks.Pushout.locallyOfFiniteType_gluingFunctor_obj_iff`,
  `Stacks.Pushout.flat_gluingFunctor_obj_iff`,
  `Stacks.Pushout.flat_and_locallyOfFinitePresentation_gluingFunctor_obj_iff` and
  `Stacks.Pushout.smooth_gluingFunctor_obj_iff` are clauses (1)–(4) of [Stacks Project,
  Tag 07RX] for the gluing functor of [Stacks Project, Tag 07RV] over Mathlib's canonical
  pushout.

## Implementation notes

The four statements are phrased over Mathlib's canonical pushout `pushout i f`, whose very
notation needs a `HasPushout i f` instance.  Rather than bind one, each statement opens with
`letI := hasPushout_of_isThickening i f hi`, exactly as the statements of
[Stacks Project, Tag 07RV] do, so that `pushout i f` is writable while nothing beyond `hi` and
the affineness of `f` — the hypotheses of the source — is assumed.
`Stacks.Pushout.hasPushout_of_isThickening` is the first assertion of
[Stacks Project, Tag 07RT] with its [Stacks Project, Tag 06AD] hypothesis already discharged.

**Where the rest of the tag is.**  The last assertion of Tag 07RV, that `F ∘ G` is isomorphic to
the identity functor, is `Stacks.Pushout.gluingCompBaseChangeIsoId`.  The two closing assertions
of Tag 07RX — that the counit `G(F(W')) ⟶ W'` is an isomorphism when `W'` is flat over `Y'`, and
that `F` and `G` are quasi-inverse equivalences between the schemes flat over `Y'` and the
triples whose two components are flat — are
`Stacks.Pushout.gluingAdjunction_counit_app_isIso_of_flat` and
`Stacks.Pushout.flatGluingEquivalence` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RXFlat`, which uses clause (2)
above together with the reconstruction half of [Stacks Project, Tag 07RU] in its flat-algebra
form `MilnorPatching.isIso_of_isIso_baseChange_of_isPullback`.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RU](https://stacks.math.columbia.edu/tag/07RU)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {X X' Y : Scheme.{u}}

/-- **[Stacks, Tag 07RX], clause (1).**  The scheme glued from a triple `(V, U', φ)` across the
pushout `Y' = Y ⨿_X X'` of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` is
locally of finite type over `Y'` if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
@[stacks 07RX "clause (1): locally of finite type, for the gluing functor of Tag 07RV over \
Mathlib's canonical pushout"]
theorem locallyOfFiniteType_gluingFunctor_obj_iff (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    LocallyOfFiniteType ((gluingFunctor i f hi).obj T).hom ↔
      (LocallyOfFiniteType T.obj.left.hom ∧ LocallyOfFiniteType T.obj.right.hom) := by
  let := hasPushout_of_isThickening i f hi
  rw [← gluingTriple_induced forall_isAffine_of_isThickening i f hi T]
  exact (gluingTriple forall_isAffine_of_isThickening i f hi T).locallyOfFiniteType_induced_iff

/-- **[Stacks, Tag 07RX], clause (2).**  The scheme glued from a triple `(V, U', φ)` across the
pushout `Y' = Y ⨿_X X'` of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` is flat
over `Y'` if and only if both `V ⟶ Y` and `U' ⟶ X'` are flat. -/
@[stacks 07RX "clause (2): flat, for the gluing functor of Tag 07RV over Mathlib's canonical \
pushout"]
theorem flat_gluingFunctor_obj_iff (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    Flat ((gluingFunctor i f hi).obj T).hom ↔
      (Flat T.obj.left.hom ∧ Flat T.obj.right.hom) := by
  let := hasPushout_of_isThickening i f hi
  rw [← gluingTriple_induced forall_isAffine_of_isThickening i f hi T]
  exact (gluingTriple forall_isAffine_of_isThickening i f hi T).flat_induced_iff

/-- **[Stacks, Tag 07RX], clause (3).**  The scheme glued from a triple `(V, U', φ)` across the
pushout `Y' = Y ⨿_X X'` of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` is flat
and locally of finite presentation over `Y'` if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
@[stacks 07RX "clause (3): flat and locally of finite presentation, for the gluing functor of \
Tag 07RV over Mathlib's canonical pushout"]
theorem flat_and_locallyOfFinitePresentation_gluingFunctor_obj_iff (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    (Flat ((gluingFunctor i f hi).obj T).hom ∧
        LocallyOfFinitePresentation ((gluingFunctor i f hi).obj T).hom) ↔
      ((Flat T.obj.left.hom ∧ LocallyOfFinitePresentation T.obj.left.hom) ∧
        (Flat T.obj.right.hom ∧ LocallyOfFinitePresentation T.obj.right.hom)) := by
  let := hasPushout_of_isThickening i f hi
  rw [← gluingTriple_induced forall_isAffine_of_isThickening i f hi T]
  exact (gluingTriple forall_isAffine_of_isThickening i f hi
    T).flat_and_locallyOfFinitePresentation_induced_iff

/-- **[Stacks, Tag 07RX], clause (4).**  The scheme glued from a triple `(V, U', φ)` across the
pushout `Y' = Y ⨿_X X'` of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` is
smooth over `Y'` if and only if both `V ⟶ Y` and `U' ⟶ X'` are smooth. -/
@[stacks 07RX "clause (4): smooth, for the gluing functor of Tag 07RV over Mathlib's canonical \
pushout"]
theorem smooth_gluingFunctor_obj_iff (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    Smooth ((gluingFunctor i f hi).obj T).hom ↔
      (Smooth T.obj.left.hom ∧ Smooth T.obj.right.hom) := by
  let := hasPushout_of_isThickening i f hi
  rw [← gluingTriple_induced forall_isAffine_of_isThickening i f hi T]
  exact (gluingTriple forall_isAffine_of_isThickening i f hi T).smooth_induced_iff

end Stacks.Pushout

end

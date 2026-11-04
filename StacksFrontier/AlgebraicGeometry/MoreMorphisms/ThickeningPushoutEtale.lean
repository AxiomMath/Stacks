module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluing
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Étaleness of a scheme glued across a pushout along a thickening

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT].  A compatible pair `(V, U', φ)`
glues to a scheme `V' = V ⨿_{V ×_Y X} U'` over `Y'`, by the left adjoint `G` of
[Stacks Project, Tag 07RV].  The étale clause of [Stacks Project, Tag 07RX] says that `V' ⟶ Y'`
is étale exactly when both `V ⟶ Y` and `U' ⟶ X'` are étale.

## Main definitions

* `Stacks.Pushout.thickeningAffinePushoutSituation` presents Mathlib's canonical pushout of a
  thickening and an affine morphism as an `AlgebraicGeometry.ThickeningAffinePushoutSituation`.
* `Stacks.Pushout.gluingTriple` presents a compatible pair as a triple over that situation.

## Main results

* `Stacks.Pushout.gluingTriple_induced`: the morphism to `Y'` induced by the triple is the
  structure morphism of the glued scheme.
* `Stacks.Pushout.etale_gluingFunctor_obj_iff` is the étale clause of
  [Stacks Project, Tag 07RX] for the gluing functor of Tag 07RV.

## Implementation notes

The five clauses of Tag 07RX are proved in
`StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluing` for an abstract pushout square
along a closed immersion and an affine morphism whose rings of sections form a fibre product;
all that is done here is to exhibit the canonical pushout and the gluing functor of Tag 07RV as
such a square and such a triple.  The hypothesis on sections is the fourth assertion of
Tag 07RT, which is `Stacks.Pushout.pushout_structureSheaf_isPullback`, and the affineness of
`X' ⟶ Y'` follows from that of `X ⟶ Y` because `X ⟶ X'` is a thickening.

**The hypothesis `H`.**  [Stacks Project, Tag 06AD] — *a thickening of an affine scheme is
affine* — is carried as the explicit universally quantified hypothesis `H`, exactly as in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing`, through which it also
enters the gluing functor itself.  It assumes nothing: Tag 06AD is a theorem,
`Stacks.Thickenings.forall_isAffine_of_isThickening`, and that is what
`Stacks.Pushout.etale_gluingFunctor_obj_iff` feeds to the conditional form.  Clauses (1) to (4)
are discharged the same way in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluingUnconditional`.

The existence of `Y' = Y ⨿_X X'` is not bound either: clause (5) opens with
`letI := hasPushout_of_isThickening i f hi`, exactly as the statements of Tag 07RV do, so it is
stated under the hypotheses of the source and no more.  The conditional form and the two
presentation definitions above it still take `[HasPushout i f]` as an instance argument.

The last assertion of Tag 07RV, that `F ∘ G` is isomorphic to the identity functor, is not used
here: the étale clause is detected on sections over affine opens, so nothing has to be
transported along that isomorphism.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-- Granted [Stacks Project, Tag 06AD], a morphism whose composition with a thickening is affine
is itself affine: the inverse image of an affine open is a thickening of an affine scheme. -/
theorem isAffineHom_of_isThickening_comp
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {X X' Y : Scheme.{u}} (i : X ⟶ X') (g : X' ⟶ Y) (hi : IsThickening i)
    [IsAffineHom (i ≫ g)] : IsAffineHom g := by
  constructor
  intro U hU
  exact H _ _ (i ∣_ (g ⁻¹ᵁ U)) (hi.morphismRestrict _) (hU.preimage (i ≫ g))

/-- Granted [Stacks Project, Tag 06AD], the pushout `Y ⨿_X X'` of a thickening `i : X ⟶ X'` and
an affine morphism `f : X ⟶ Y`, together with the identification of its sections as a fibre
product, which is the fourth assertion of [Stacks Project, Tag 07RT]. -/
noncomputable def thickeningAffinePushoutSituation
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] : ThickeningAffinePushoutSituation.{u} :=
  haveI : IsClosedImmersion i := hi.1
  haveI : IsClosedImmersion (pushout.inr i f) := (pushout_inr_isThickening H i f hi).1
  haveI : IsAffineHom (i ≫ pushout.inl i f) := by rw [pushout.condition]; infer_instance
  haveI : IsAffineHom (pushout.inl i f) := isAffineHom_of_isThickening_comp H i _ hi
  { X := X
    X' := X'
    Y := Y
    Y' := pushout i f
    i := i
    f := f
    inX' := pushout.inl i f
    inY := pushout.inr i f
    isPushout := IsPushout.of_hasPushout i f
    sections_isPullback := fun U => pushout_structureSheaf_isPullback H i f hi U }

/-- A compatible pair `(V, U', φ)` as a triple over
`Stacks.Pushout.thickeningAffinePushoutSituation`: the common restriction `U` is the fibre
product `V ×_Y X = U' ×_{X'} X`, and `V' = V ⨿_U U'`. -/
noncomputable def gluingTriple
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] (T : gluingData i f) :
    (thickeningAffinePushoutSituation H i f hi).Triple :=
  haveI : IsAffineHom (gluingSourceMap i f T) :=
    MorphismProperty.of_isPullback (gluingSourceMap_isPullback i f T).flip inferInstance
  haveI := gluingHasPushout i f hi T
  { T := thickeningAffinePushoutSituation H (pullback.fst T.obj.right.hom i)
      (gluingSourceMap i f T)
      (isThickening_of_isPullback (IsPullback.of_hasPullback T.obj.right.hom i) hi)
    toX' := T.obj.right.hom
    toY := T.obj.left.hom
    toX := pullback.snd T.obj.right.hom i
    isPullback_i := IsPullback.of_hasPullback _ _
    isPullback_f := gluingSourceMap_isPullback i f T }

/-- The morphism `V' ⟶ Y'` induced by the triple of a compatible pair is the structure morphism
of the glued scheme. -/
theorem gluingTriple_induced
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] (T : gluingData i f) :
    (gluingTriple H i f hi T).induced = ((gluingFunctor i f hi).obj T).hom := by
  have := gluingHasPushout i f hi T
  change _ = (gluingPushoutData i f T).hom
  refine pushout.hom_ext ?_ ?_
  · exact (gluingTriple H i f hi T).inX'_comp_induced.trans
      (gluingPushoutData_inl i f T).symm
  · exact (gluingTriple H i f hi T).inY_comp_induced.trans
      (gluingPushoutData_inr i f T).symm

/-- **Stacks Project, Tag 07RX, the étale clause, granted Tag 06AD.**  The scheme glued from a
compatible pair `(V, U', φ)` across the pushout `Y' = Y ⨿_X X'` of a thickening `i : X ⟶ X'` and
an affine morphism `f : X ⟶ Y` is étale over `Y'` if and only if both `V ⟶ Y` and `U' ⟶ X'` are
étale. -/
theorem etale_gluingFunctor_obj_iff_of_isAffine_of_isThickening
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] (T : gluingData i f) :
    Etale ((gluingFunctor i f hi).obj T).hom ↔
      (Etale T.obj.left.hom ∧ Etale T.obj.right.hom) := by
  rw [← gluingTriple_induced H i f hi T]
  exact (gluingTriple H i f hi T).etale_induced_iff

/-- **Stacks 07RX, clause (5).** The glued scheme of Tag 07RV over Mathlib's canonical pushout is
étale over the pushout exactly when both of its pieces are étale over their bases. -/
@[stacks 07RX "clause (5): étale, for the gluing functor of Tag 07RV over Mathlib's canonical \
pushout"]
theorem etale_gluingFunctor_obj_iff {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    Etale ((gluingFunctor i f hi).obj T).hom ↔
      (Etale T.obj.left.hom ∧ Etale T.obj.right.hom) :=
  let := hasPushout_of_isThickening i f hi
  etale_gluingFunctor_obj_iff_of_isAffine_of_isThickening
    Stacks.Thickenings.forall_isAffine_of_isThickening i f hi T


end Stacks.Pushout

end

module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.DescentIso
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism

/-!
# Effectivity relative to a morphism and relative to its one-member family

A descent datum for a single morphism `f : X ⟶ S` of schemes is a descent datum for the
one-member family consisting of `f`, and the library carries two canonical-datum functors for
it: `AlgebraicGeometry.DescentData.canonicalFunctor`, which pulls the trivial descent datum of
an `S`-scheme back along the square expressing `f` as a base change of `𝟙 S`, and
`AlgebraicGeometry.canonicalFamilyDescentFunctor`, which writes the components of the canonical
datum of a family down directly. The two agree, so the two notions of effectivity they define
agree as well.

## Main definitions

* `AlgebraicGeometry.DescentData.pulledBackTrivialDatumIso` identifies the pullback of a descent
  datum relative to `𝟙 S` with the canonical descent datum of its underlying `S`-scheme.
* `AlgebraicGeometry.DescentData.canonicalFunctorIso` is the resulting isomorphism of
  canonical-datum functors.

## Main results

* `AlgebraicGeometry.DescentData.actOn_id`: a descent datum relative to the identity of `S` acts
  by the first projection.
* `AlgebraicGeometry.DescentData.isFamilyEffective_iff_isEffective`, with the two implications
  `AlgebraicGeometry.DescentData.isFamilyEffective_of_isEffective` and
  `AlgebraicGeometry.DescentData.isEffective_of_isFamilyEffective`: **the two notions of
  effectivity of a descent datum relative to a single morphism agree.**

## Implementation notes

Both constructions are compared through the gluing action on the literal fibre products rather
than by unfolding either of them. The pullback functor of a commutative square exposes its
gluing isomorphism only through the projections of the fibre products it lives on
(`AlgebraicGeometry.DescentData.PullbackFunctor.sourceMap` and its companions), and the
canonical datum of a family exposes its transition map only through the two projections which
characterize it; `AlgebraicGeometry.DescentData.isoOfActOn` turns the resulting pair of
projection identities into an isomorphism of descent data.

`AlgebraicGeometry.CanonicalDatum.datum` and `AlgebraicGeometry.CanonicalDatum.functor` are
made `implicit_reducible` for this file. Their components are the base changes
`(Over.pullback (f i)).obj U`, and the statements below compose with the projections of those
fibre products, so the identification of a component with its base change has to be available
to the elaborator and not only to `exact`.

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

attribute [local implicit_reducible] CanonicalDatum.datum CanonicalDatum.functor

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- A descent datum relative to the identity morphism of `S` has nothing to glue: its gluing
action on `V ×_S S` is the first projection. -/
lemma actOn_id (D : DescentData (fun _ : Unit ↦ 𝟙 S)) :
    D.actOn = pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) := by
  have hsnd : pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) ≫ (D.obj ()).hom =
      pullback.snd ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) := by
    simpa using pullback.condition (f := (D.obj ()).hom ≫ 𝟙 S) (g := 𝟙 S)
  have key : pullback.lift (pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S))
      (pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) ≫ (D.obj ()).hom)
      (Category.assoc _ _ _).symm = 𝟙 _ :=
    pullback.hom_ext ((pullback.lift_fst _ _ _).trans (Category.id_comp _).symm)
      ((pullback.lift_snd _ _ _).trans (hsnd.trans (Category.id_comp _).symm))
  calc D.actOn
      = pullback.lift (pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S))
          (pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) ≫ (D.obj ()).hom)
          (Category.assoc _ _ _).symm ≫ D.actOn := by rw [key, Category.id_comp]
    _ = pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) := D.act_self _

variable (f) in
/-- The canonical descent datum of a scheme over `S` relative to the one-member family
consisting of `f : X ⟶ S`. -/
abbrev canonicalSingletonFamilyDatum (U : Over S) : DescentDatum f :=
  (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor.obj U

/-- The gluing action of the canonical descent datum of an `S`-scheme `U` relative to the
one-member family `f`, followed by the projection to `U`, forgets the second factor: this is one
of the two identities characterizing the canonical transition map. -/
lemma canonicalSingletonFamilyDatum_actOn_comp_fst (U : Over S) :
    (canonicalSingletonFamilyDatum f U).actOn ≫ pullback.fst U.hom f =
      pullback.fst (((canonicalSingletonFamilyDatum f U).obj ()).hom ≫ f) f ≫
        pullback.fst U.hom f := by
  have h := (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).gluing U () ()
  simp only [eqToHom_refl, Over.id_left, Category.id_comp] at h
  simpa only [DescentData.actOn, Category.assoc] using h

/-- Pulling a descent datum relative to the identity of `S` back along the square expressing
`f : X ⟶ S` as a base change of `𝟙 S` gives the canonical descent datum, relative to the
one-member family `f`, of its underlying scheme over `S`. -/
def pulledBackTrivialDatumIso (P : PullbackFunctor (𝟙 S) f (𝟙 S) f (by simp))
    (T : DescentData (fun _ : Unit ↦ 𝟙 S)) :
    P.functor.obj T ≅ canonicalSingletonFamilyDatum f (T.obj ()) := by
  refine isoOfActOn (P.objIso T) ?_
  have hE : (canonicalSingletonFamilyDatum f (T.obj ())).actOn ≫ pullback.snd (T.obj ()).hom f =
      pullback.snd (((canonicalSingletonFamilyDatum f (T.obj ())).obj ()).hom ≫ f) f :=
    (canonicalSingletonFamilyDatum f (T.obj ())).actOn_hom
  apply pullback.hom_ext
  · rw [Category.assoc, P.actOn_objIso_fst T, actOn_id T, P.sourceMap_fst T, Category.assoc,
      canonicalSingletonFamilyDatum_actOn_comp_fst, actOnMap_fst_assoc]
  · rw [Category.assoc, P.objIso_hom_left_snd T, actOn_hom, Category.assoc, hE, actOnMap_snd]

/-- **The canonical descent datum functor of a morphism is the canonical descent datum functor
of the one-member family consisting of it.** -/
def canonicalFunctorIso (f : X ⟶ S) :
    canonicalFunctor f ≅ (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor :=
  NatIso.ofComponents
    (fun U ↦ pulledBackTrivialDatumIso (pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp))
      ((trivialFunctor S).obj U))
    fun g ↦ hom_ext fun _ ↦
      ((pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).map ((trivialFunctor S).map g)).symm

/-- **The two notions of effectivity of a descent datum relative to a single morphism agree.**
Being isomorphic to the canonical descent datum of an `S`-scheme relative to `f`, in the sense
of the one-member family consisting of `f`, is the same as being so in the sense of the pullback
of a trivial descent datum. -/
theorem isFamilyEffective_iff_isEffective (D : DescentDatum f) :
    D.IsFamilyEffective ↔ D.IsEffective := by
  constructor
  · rintro ⟨U, ⟨e⟩⟩
    exact ⟨U, ⟨(canonicalFunctorIso f).app U ≪≫ e⟩⟩
  · rintro ⟨U, ⟨e⟩⟩
    exact ⟨U, ⟨((canonicalFunctorIso f).app U).symm ≪≫ e⟩⟩

/-- An effective descent datum relative to a single morphism is effective relative to the
one-member family consisting of that morphism. -/
theorem isFamilyEffective_of_isEffective {D : DescentDatum f} (h : D.IsEffective) :
    D.IsFamilyEffective :=
  (isFamilyEffective_iff_isEffective D).2 h

/-- A descent datum relative to a single morphism which is effective for the one-member family
consisting of that morphism is effective. -/
theorem isEffective_of_isFamilyEffective {D : DescentDatum f} (h : D.IsFamilyEffective) :
    D.IsEffective :=
  (isFamilyEffective_iff_isEffective D).1 h

end AlgebraicGeometry.DescentData

end

end

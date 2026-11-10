module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Splittings
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingSituations

/-!
# Étale localization of a groupoid scheme, conditional on the finite part

Stacks 04RW says that in the quasi-splitting situation of Stacks 04RV there is an algebraic
space `U'`, an étale morphism `U' ⟶ U` and a point of `U'` over the chosen point `u` such that
the restriction `R|_{U'}` is quasi-split there.  Its proof is: by Stacks 04RU the finite part of
the groupoid supplies such a `U'` together with an open subspace of the arrow space of
`R|_{U'}` which is a subgroupoid with finite source and target, and any such subgroupoid is
automatically a quasi-splitting at every point, because the identity arrow of the subgroupoid at
a point is an idempotent arrow of the ambient groupoid and therefore *is* the ambient identity
arrow there.

This file proves the second half outright, and states the first half with the input from
Stacks 04RU carried as an explicit hypothesis,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePartSubgroupoid`.  That hypothesis is not an
assumption: all three clauses of Stacks 04RU are proved in this library, clause (3) — the
groupoid structure on the finite part together with its morphism to the given groupoid — in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/Groupoid.lean` at line 2036 and
in `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidStructure.lean` at
line 655, and
`AlgebraicGeometry.Space.finitePartSubgroupoid` discharges it.

The scheme-to-space comparison the statement needs is
`Stacks.Groupoids.GroupoidScheme.realization`, so no realization of the groupoid scheme has to
be carried inside the existential.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePartSubgroupoid`: the output of Stacks
  04RU in the form its consumers use — an étale morphism to the object space together with an
  open finite subgroupoid of the restriction along it.

## Main results

* `Deformation.GroupoidInFunctors.identity_eq_of_idempotent`: an arrow whose source and target
  are a given object and which is idempotent is the identity arrow at that object.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isQuasiSplitAt_of_openFiniteSubgroupoid`: an open
  finite subgroupoid is a quasi-splitting at *every* point of the object space.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_quasiSplitting`: the quasi-splitting of
  `R|_{U'}` at every point of `U'`, from a finite part given as a hypothesis.

## Implementation notes

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isQuasiSplitAt_of_openFiniteSubgroupoid` is stated
for an arbitrary point and so needs no hypothesis relating the point to anything: the argument is
that the open finite subgroupoid, being pointwise a groupoid, has an identity arrow at the point,
that arrow composes with itself to itself, and an idempotent arrow of a groupoid with equal
source and target is an identity.  Consequently the statement below concludes quasi-splitting at
every point of `U'`, which removes any need to assume a point.

What it therefore does *not* produce is the residue-field point of `U'` above `u`; without such
a point the conclusion is satisfied by the empty `U'`.  That point comes from decomposing the
fibre `R ×_{s, U} Spec(κ(u))` along the quasi-finiteness of `s` at `e(u)`, and is produced in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasiSplittingEtaleLocalization.lean`.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RW](https://stacks.math.columbia.edu/tag/04RW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.GroupoidInFunctors

/-- An arrow of a groupoid in functors whose source and target are both a given object and
which composes with itself to itself is the identity arrow at that object. -/
theorem identity_eq_of_idempotent {J : Type u} [Category.{v} J] (G : GroupoidInFunctors J)
    (T : J) (x : G.Evaluation T) (a : G.arrows.obj T)
    (hs : G.source.app T a = x) (ht : G.target.app T a = x)
    (ha : G.compose T a a (hs.trans ht.symm) = a) : G.identity T x = a := by
  let e := G.evaluationArrowEquiv T x x
  let f : x ⟶ x := e.symm ⟨a, hs, ht⟩
  have hf : (e f).1 = a := congrArg Subtype.val (e.apply_symm_apply _)
  have hff : f ≫ f = f := by
    refine e.injective (Subtype.ext ?_)
    dsimp only [e]
    rw [G.evaluationArrowEquiv_comp]
    simpa only [show (G.evaluationArrowEquiv T x x f).1 = a from hf] using ha
  have hid : f = 𝟙 x := by
    apply (cancel_mono f).1
    simpa using hff
  exact (congrArg (fun g => (e g).1) hid).symm.trans hf

end Deformation.GroupoidInFunctors

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **An open finite subgroupoid contains the identity arrow at every point of the object
space.**

The identity arrow of the subgroupoid at the point is an arrow of the ambient groupoid with both
endpoints at the point which composes with itself to itself, hence is the ambient identity arrow
there; so the subgroupoid contains it. -/
theorem contains_identityOnPoints_of_openFiniteSubgroupoid
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (H : OpenFiniteSubgroupoid G) (p : Space.points C S hS G.objects.obj) :
    ∃ q : Space.points C S hS H.arrows.toFunctor,
      Space.pointsMap C S hS H.arrows.toFunctor H.arrows.ι q = identityOnPoints G p := by
  let F : Deformation.GroupoidInFunctors ((BigFppfOver C S hS)ᵒᵖ) :=
    { objects := G.objects.obj
      arrows := H.arrows.toFunctor
      source := H.arrows.ι ≫ G.source.hom
      target := H.arrows.ι ≫ G.target.hom
      comp := H.comp
      pointwiseGroupoid := H.pointwiseGroupoid }
  induction p using Quot.inductionOn with | _ p =>
  let T := Opposite.op p.siteObject
  let x : F.Evaluation T := p.value
  let a := F.identity T x
  have hs : G.source.hom.app T a.1 = p.value :=
    (F.evaluationArrowEquiv T x x (𝟙 x)).2.1
  have ht : G.target.hom.app T a.1 = p.value :=
    (F.evaluationArrowEquiv T x x (𝟙 x)).2.2
  have haa : F.compose T a a (hs.trans ht.symm) = a := by
    have hh := F.evaluationArrowEquiv_comp T (𝟙 x) (𝟙 x)
    rw [Category.id_comp] at hh
    exact hh.symm
  have hid : G.toGroupoidInFunctors.identity T p.value = a.1 :=
    Deformation.GroupoidInFunctors.identity_eq_of_idempotent G.toGroupoidInFunctors T
      p.value a.1 hs ht
      ((H.comp_restricts T ⟨(a, a), hs.trans ht.symm⟩).symm.trans
        (congrArg Subtype.val haa))
  refine ⟨Space.FieldValuedPoint.class C S hS H.arrows.toFunctor
    { carrier := p.carrier, field := p.field, contained := p.contained,
      toBase := p.toBase, value := a }, ?_⟩
  change Space.FieldValuedPoint.class C S hS G.arrows.obj
    { carrier := p.carrier, field := p.field, contained := p.contained,
      toBase := p.toBase, value := a.1 } = _
  rw [← hid]
  rfl

/-- An open finite subgroupoid of a groupoid in algebraic spaces is a quasi-splitting at every
point of the object space: it contains the identity arrow there. -/
theorem isQuasiSplitAt_of_openFiniteSubgroupoid (G : GroupoidInAlgebraicSpaces C S hS B)
    (H : OpenFiniteSubgroupoid G) (p : Space.points C S hS G.objects.obj) :
    IsQuasiSplitAt G p :=
  ⟨{ H with
    contains_identity := contains_identityOnPoints_of_openFiniteSubgroupoid G H p }⟩

/-- The output of Stacks 04RU in the form its consumers use: an algebraic space with an étale
morphism to the object space of the given groupoid, together with an open subspace of the arrow
space of the restriction along it which is a subgroupoid with finite source and target.

All three clauses of Stacks 04RU are proved in this library: clauses (1) and (2) — the étale
projection and the universal finite open and closed subspace of `R ×_{s, U, g} U'` — in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/Groupoid.lean` at lines 277 and
322, and clause (3) — the groupoid structure on that subspace and the morphism of groupoids to
the given one — in the same file at line 2036 and in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidStructure.lean` at
line 655.  This structure packages what the
consumers below use, and `AlgebraicGeometry.Space.finitePartSubgroupoid` builds it. -/
structure FinitePartSubgroupoid (G : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The new space of objects `U'`. -/
  objects : AlgebraicSpaces C S hS
  /-- The projection `g : U' ⟶ U`. -/
  objectProjection : objects ⟶ G.objects
  /-- The projection is étale. -/
  objectProjection_etale : Space.IsEtale C S hS objectProjection.hom
  /-- The finite part, as an open finite subgroupoid of the restriction `R|_{U'}`. -/
  restrictedSubgroupoid : OpenFiniteSubgroupoid (restrict G objectProjection).groupoid

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- In the quasi-splitting situation of Stacks 04RV, given the finite part of the realized
groupoid as an open finite subgroupoid of a restriction along an étale morphism, there is an
algebraic space `U'`, an étale morphism `g : U' ⟶ U` of algebraic spaces, and the restriction
`R|_{U'}` is quasi-split at every point of `U'`. -/
theorem exists_etale_quasiSplitting (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (F : FinitePartSubgroupoid (D.groupoid.realization C hS hU hR hP)) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      ∀ u' : AlgebraicGeometry.Space.points C D.S hS
          (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid.objects.obj,
        IsQuasiSplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid u' :=
  ⟨F.objects, F.objectProjection, F.objectProjection_etale,
    fun u' => isQuasiSplitAt_of_openFiniteSubgroupoid _ F.restrictedSubgroupoid u'⟩

end Stacks.Groupoids.GroupoidScheme

end

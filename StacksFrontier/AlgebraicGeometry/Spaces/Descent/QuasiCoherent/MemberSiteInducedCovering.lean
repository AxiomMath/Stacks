module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteSheafCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice

/-!
# The covering of a chart of a member induced by a covering sieve of the charts of the members

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X`.  The charts of the members of that family form a site,
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite`, whose objects are the pairs `(i, V)` of
a member and a chart of it and whose topology is restricted along
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctor` from the small étale topology of `X`;
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteSheafCondition.lean` reads
the sheaf condition on it as a condition on the image sieves in the small étale site of `X`.

A morphism `k : (j, W) ⟶ (i, V)` of that site induces a chart
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionChart` of `Y i` over `V`, with
structure morphism `.memberTransitionHom`: that is the chart of `Y i` over which a descent datum
reads the transition from `i` to `j`. **This file shows that the induced charts of the arrows of a
covering sieve of `(i, V)` cover `V`**, which is what turns a gluing obligation on the charts of
the members into a gluing obligation inside the member `Y i`, where the components of a descent
datum are already sheaves.

Nothing here mentions a descent datum, a transition or a section: every statement is about the
site, which is why each holds for an arbitrary sieve and is an input to the gluing step rather than
part of it.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionPresieve`: the family of the charts
  of a member induced by the arrows of a sieve of the charts of the members, as a presieve of the
  chart that sieve is a sieve of, indexed by `.memberSieveArrows`, the arrows of that sieve.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionLift`: the factorization of a
  morphism of charts of a member through an induced chart.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionPresieve_generate_mem_topology`:
  **the charts of `Y i` induced by the arrows of a sieve of `(i, V)` whose image covers the induced
  chart of `X` generate a covering sieve of `V`.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.memberTransitionPresieve_generate_mem_memberTopology`: the same with the hypothesis read in
  the topology of the charts of the members itself.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isSheafFor_memberTransitionPresieve` and
  `.isSheafFor_memberTransitionPresieve_of_mem_memberTopology`: a sheaf on the small étale site of
  `Y i` glues uniquely over the induced charts of such a sieve.

## Implementation notes

The covering is produced by **cover lifting along postcomposition**,
`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`: the image sieve of the given
sieve covers the induced chart of `X`, hence pulls back to a covering sieve of `V` in the small
étale site of `Y i`.  What remains is combinatorial — every morphism of charts of `Y i` whose
postcomposition with `f i` lies in the image sieve factors through an induced chart — and that is
`.functorPullback_le_generate_memberTransitionPresieve`.  The factorization is the factorization in
the small étale site of `X` read back as a morphism of charts of `Y i`: the structure morphism of
the induced chart is the inducing morphism followed by the structure morphism of the target chart,
on the nose (`.memberTransitionChart_obj_hom`), so dividing the triangle over `X` by `f i` costs
nothing.  As in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePostcompSlice.lean`, that triangle is checked by
an `exact` of `AlgebraicGeometry.Space.SmallEtale.map_comp_comp_eq_of_comp_eq`, a `rewrite` inside
it
failing while building its motive: the source of the structure morphism of the induced chart is the
object of the big fppf site underlying the source chart only after unfolding, so the goal is not
type-correct at the transparency a motive is built at.

The sieve has to be *generated*: the induced charts of the arrows of a sieve are closed under the
induced charts of further arrows of the site, but not under arbitrary morphisms of charts of `Y i`,
so they form a presieve and not a sieve.

The chart `V` and its member are carried as arguments rather than read off an object `p` of the
site of the charts of the members.  With the family of induced charts indexed by the arrows of
`T : Sieve p`, which is a subtype of a type of morphisms of that site, the elaboration of the
`CategoryTheory.Presieve.ofArrows` below does not terminate when its objects are spelled `p.2`,
while it is immediate when the chart is a variable.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result, and in
particular the effectivity clause of Stacks 04W6 is not asserted.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The structure morphism of an induced chart -/

/-- **The structure morphism of the chart of a member induced by a morphism of the site of the
charts of the members is that morphism followed by the structure morphism of the target chart.**
On the nose: the induced chart is the identity chart of the chart space of the source chart pushed
forward along the morphism to the target member, and the structure morphism of that push is the
represented morphism of chart spaces composed with the structure morphism of the target chart. -/
theorem memberTransitionChart_obj_hom {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    (memberTransitionChart B S hS Yi f hf V V' k).obj.hom =
      yoneda.map k.hom.left ≫ V.obj.hom :=
  rfl

/-! ### The factorization through an induced chart -/

/-- **A morphism of charts of a member whose postcomposition with the member morphism factors
through a morphism of the site of the charts of the members factors through the chart that morphism
induces.**  The lift is the given factorization itself, read as a morphism of charts of the member:
the structure morphism of the induced chart is the inducing morphism followed by the structure
morphism of the target chart, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionChart_obj_hom`, so the triangle over
the member is the triangle over `X` of the given morphism with the member morphism cancelled. -/
def memberTransitionLift {i j : I} {V W : SmallEtale B S hS (Yi i).1}
    {V' : SmallEtale B S hS (Yi j).1}
    {k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V}
    {g : W ⟶ V}
    {a : (smallEtalePostcomp B S hS (f i) (hf i)).obj W ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V'}
    (he : (smallEtalePostcomp B S hS (f i) (hf i)).map g = a ≫ k) :
    W ⟶ memberTransitionChart B S hS Yi f hf V V' k :=
  ObjectProperty.homMk (CostructuredArrow.homMk a.hom.left
    ((SmallEtale.map_comp_comp_eq_of_comp_eq yoneda a.hom.left k.hom.left V.obj.hom
        (congrArg (fun m => m.hom.left) he).symm).trans (CostructuredArrow.w g.hom)))

/-- **The lift of a morphism of charts of a member through an induced chart is a factorization of
that morphism.**  Both sides are morphisms of charts of the member, so the equation is the equation
of the underlying morphisms of the big fppf site, which is the given factorization. -/
theorem memberTransitionLift_comp {i j : I} {V W : SmallEtale B S hS (Yi i).1}
    {V' : SmallEtale B S hS (Yi j).1}
    {k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V}
    {g : W ⟶ V}
    {a : (smallEtalePostcomp B S hS (f i) (hf i)).obj W ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V'}
    (he : (smallEtalePostcomp B S hS (f i) (hf i)).map g = a ≫ k) :
    memberTransitionLift B S hS Yi f hf he ≫ memberTransitionHom B S hS Yi f hf V V' k = g :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (congrArg (fun m => m.hom.left) he).symm)

/-! ### The induced charts of a sieve -/

/-- The arrows of a sieve of the site of the charts of the members: the index type of the family of
the charts of the member they induce. -/
abbrev memberSieveArrows {i : I} (V : SmallEtale B S hS (Yi i).1)
    (T : Sieve (memberPair B S hS Yi f hf i V)) : Type (max v (u + 1)) :=
  Σ q : MemberSite B S hS Yi f hf, { k : q ⟶ memberPair B S hS Yi f hf i V // T.arrows k }

/-- **The family of the charts of a member induced by the arrows of a sieve of the site of the
charts of the members**, as a presieve of the chart that sieve is a sieve of: one arrow
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionHom` for every arrow of the sieve. -/
def memberTransitionPresieve {i : I} (V : SmallEtale B S hS (Yi i).1)
    (T : Sieve (memberPair B S hS Yi f hf i V)) : Presieve V :=
  Presieve.ofArrows
    (fun c : memberSieveArrows B S hS Yi f hf V T =>
      memberTransitionChart B S hS Yi f hf V c.1.2 c.2.1.hom)
    (fun c => memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom)

/-- Every arrow of the sieve contributes the morphism of charts it induces to the presieve of the
induced charts.  The index is ascribed: the family of the induced charts is indexed by the arrows
of the sieve, and reading its index off the chart the arrow induces is a higher-order unification
problem the elaborator does not solve. -/
theorem memberTransitionPresieve_mem {i : I} {V : SmallEtale B S hS (Yi i).1}
    {T : Sieve (memberPair B S hS Yi f hf i V)} {q : MemberSite B S hS Yi f hf}
    {k : q ⟶ memberPair B S hS Yi f hf i V} (hk : T.arrows k) :
    memberTransitionPresieve B S hS Yi f hf V T
      (memberTransitionHom B S hS Yi f hf V q.2 k.hom) :=
  Presieve.ofArrows.mk (⟨q, k, hk⟩ : memberSieveArrows B S hS Yi f hf V T)

/-- **Every morphism of charts of a member whose image lies in the image sieve of a sieve of the
site of the charts of the members factors through one of the induced charts.**  This is the
combinatorial half of the covering statement below: the image sieve provides a factorization in the
small étale site of `X`, and
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionLift` reads it back as a morphism of
charts of the member. -/
theorem functorPullback_le_generate_memberTransitionPresieve {i : I}
    (V : SmallEtale B S hS (Yi i).1) (T : Sieve (memberPair B S hS Yi f hf i V)) :
    (T.functorPushforward (memberFunctor B S hS Yi f hf)).functorPullback
        (smallEtalePostcomp B S hS (f i) (hf i)) ≤
      Sieve.generate (memberTransitionPresieve B S hS Yi f hf V T) := by
  intro W g hg
  obtain ⟨q, k, a, hk, he⟩ := hg
  exact ⟨_, memberTransitionLift B S hS Yi f hf he, _,
    memberTransitionPresieve_mem B S hS Yi f hf hk,
    memberTransitionLift_comp B S hS Yi f hf he⟩

/-- **The charts of a member induced by the arrows of a sieve of the site of the charts of the
members whose image covers the induced chart of `X` generate a covering sieve of the chart.**
The image sieve covers the induced chart of `X`, hence pulls back to a covering sieve of the chart
in the small étale site of the member by cover lifting along postcomposition,
`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`; and that pullback is contained
in the sieve generated by the induced charts. -/
theorem memberTransitionPresieve_generate_mem_topology {i : I}
    (V : SmallEtale B S hS (Yi i).1) (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V))) :
    Sieve.generate (memberTransitionPresieve B S hS Yi f hf V T) ∈
      SmallEtale.topology B S hS (Yi i).1 V :=
  (SmallEtale.topology B S hS (Yi i).1).superset_covering
    (functorPullback_le_generate_memberTransitionPresieve B S hS Yi f hf V T)
    (SmallEtale.smallEtalePostcomp_cover_lift B S hS (f i) (hf i) V
      (T.functorPushforward (memberFunctor B S hS Yi f hf)) hT)

/-- **A sheaf on the small étale site of a member glues uniquely over the charts of that member
induced by the arrows of a sieve of the site of the charts of the members whose image covers the
induced chart of `X`.**  This is the form in which the covering is used: a gluing obligation over
such a sieve becomes a gluing obligation inside the member. -/
theorem isSheafFor_memberTransitionPresieve {i : I} {V : SmallEtale B S hS (Yi i).1}
    {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V))) :
    Presieve.IsSheafFor P (memberTransitionPresieve B S hS Yi f hf V T) :=
  hP.isSheafFor _ (memberTransitionPresieve_generate_mem_topology B S hS Yi f hf V T hT)

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- **The charts of a member induced by the arrows of a covering sieve of the site of the charts of
the members generate a covering sieve of the chart.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionPresieve_generate_mem_topology` with
its hypothesis read in the topology of the charts of the members itself, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.mem_memberTopology_iff`. -/
theorem memberTransitionPresieve_generate_mem_memberTopology {i : I}
    (V : SmallEtale B S hS (Yi i).1) (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T ∈ memberTopology B S hS Yi f hf (memberPair B S hS Yi f hf i V)) :
    Sieve.generate (memberTransitionPresieve B S hS Yi f hf V T) ∈
      SmallEtale.topology B S hS (Yi i).1 V :=
  memberTransitionPresieve_generate_mem_topology B S hS Yi f hf V T
    (mem_memberTopology_iff B S hS Yi f hf |>.1 hT)

/-- **A sheaf on the small étale site of a member glues uniquely over the charts of that member
induced by the arrows of a covering sieve of the site of the charts of the members.** -/
theorem isSheafFor_memberTransitionPresieve_of_mem_memberTopology {i : I}
    {V : SmallEtale B S hS (Yi i).1} {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T ∈ memberTopology B S hS Yi f hf (memberPair B S hS Yi f hf i V)) :
    Presieve.IsSheafFor P (memberTransitionPresieve B S hS Yi f hf V T) :=
  hP.isSheafFor _
    (memberTransitionPresieve_generate_mem_memberTopology B S hS Yi f hf V T hT)

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end

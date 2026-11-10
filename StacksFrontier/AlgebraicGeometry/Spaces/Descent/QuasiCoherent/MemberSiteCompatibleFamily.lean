module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteInducedCovering

/-!
# A compatible family on the charts of the members, read inside one member

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X` and let `D` be a descent datum for quasi-coherent modules relative to that
family.
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteInducedCovering.lean`
shows that the charts of `Y i` induced by the arrows of a covering sieve `T` of the object `(i, V)`
of the site of the charts of the members cover `V`, so that a sheaf on the small étale site of
`Y i` glues uniquely over them.

**This file turns a compatible family on the charts of the members into a compatible family over
those induced charts, and checks that the amalgamated section restricts back.**  The passage costs
no transition of the descent datum, and the reason is the content of the file: a chart `W` of `Y i`
is itself an object `(i, W)` of the site of the charts of the members, the morphisms of charts of
`Y i` are morphisms of the site between such objects
(`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagHom`), and **the structure morphism of
every induced chart is one of them and lies in `T`** —
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagSieve_memberTransitionHom`, which factors
it through the arrow of `T` that induced the chart. Over such an object the sections of the datum
are the sections of `D.F i`; so the family one starts from is already a family of sections of
`D.F i`, and nothing is transported.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagHom`: a morphism of charts of one member
  read as a morphism of the site of the charts of the members, with
  `.memberChartMap_memberDiagHom`: **the two legs of the test space of such an arrow are one and
  the same morphism**; and `.memberDiagSieve`: the sieve of charts of `Y i` whose morphism of the
  site lies in a given sieve of `(i, V)` — the part of that sieve which lives inside the member
  `Y i`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionConnect`: the morphism of the site
  from the chart induced by an arrow of the site onto the source of that arrow, which is what
  exhibits the induced chart inside the sieve.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionArrowsFamily`: a family of sections
  indexed by `.memberDiagSieve`, read as a family indexed by the arrows of the sieve, that is as a
  family of sections over the induced charts.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionPresieve_le_memberDiagSieve`: **the
  charts of a member induced by the arrows of a sieve of the charts of the members are charts of
  that member in the sieve** — the statement which makes the two families below one and the same
  data.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagSieve_mem_topology` and
  `.isSheafFor_memberDiagSieve`: **the part of a covering sieve of `(i, V)` living inside the
  member is a covering sieve of `V`**, so a sheaf on the small étale site of the member glues
  uniquely over it.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_unique_amalgamation_memberTransitionChart`:
  **the gluing statement over the induced charts, on an explicitly indexed family** — a compatible
  family of sections over the charts induced by the arrows of such a sieve has a unique
  amalgamation.  This is `.isSheafFor_memberTransitionPresieve` read through
  `CategoryTheory.Presieve.isSheafFor_arrows_iff`, with no transport in between.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionArrowsFamily_compatible`: **the
  family over the induced charts obtained from a compatible family on the charts of the members is
  compatible** for `.memberTransitionPresieve`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isAmalgamation_of_memberTransitionArrowsFamily`:
  **the section amalgamating that family restricts back to the original family**, over every chart
  of the member in the sieve and not merely over the induced charts.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_unique_isAmalgamation_memberDiagSieve` and
  its component form `.exists_unique_isAmalgamation_memberDiagSieve_component`: the two together,
  as one unique-gluing statement — the latter at the component module `D.F i` of a descent datum,
  whose sheaf condition is the one a descent datum supplies.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isIso_memberTransitionConnect`: **the connecting
  arrow of an induced chart is an isomorphism of the site**, with `.isIso_of_isIso_hom` and
  `.memberTransitionConnect_hom_hom_left` the two steps of it.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isAmalgamation_of_memberDiagHom`: **a section
  restricting correctly along the morphisms of charts of the member in a sieve restricts correctly
  along every arrow of that sieve** — the restriction back at an arrow whose source member need not
  be the target member, at no cost in the descent datum, and
  `.isSheafFor_of_existsUnique_memberDiagHom` the gluing obligation it reduces.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isSheaf_memberTopology_of_memberDiagHom`: **the
  sheaf condition on the charts of the members is the gluing obligation inside one member.**

## Implementation notes

**What is assumed of the family, and what is not.**  The family carried below is a
`CategoryTheory.Presieve.FamilyOfElements` for `.memberDiagSieve`, that is a family of sections of
`D.F i` indexed by the charts of `Y i` whose morphism of the site lies in `T`.  That is a *weaker*
datum than a compatible family on the charts of the members, which also carries sections over the
objects `(j, V')` with `j ≠ i`; the restriction of such a family to the objects `(i, W)` is a
family of the kind used here, and **the gluing statements below assume nothing about the arrows of
`T` whose source member is not `i`**.

**The arrows whose source member is not the target member cost nothing.**  Such an arrow `k` does
not have to be carried into `D.F i`, and in particular no transition of the descent datum in the
direction *onto* `i` and no cocycle is needed for it:
`AlgebraicGeometry.Space.QuasiCoherentDescent.isIso_memberTransitionConnect` says the connecting
arrow of the chart `k` induces is an **isomorphism** of the site, because its underlying morphism
of the big fppf site is the identity; `k` factors as that isomorphism followed by the morphism of
charts of `Y i` it induces (`.memberTransitionConnect_comp`), which lies in the part of the sieve
living inside the member (`.memberDiagSieve_memberTransitionHom`); and restriction along an
isomorphism is injective. That is `.isAmalgamation_of_memberDiagHom`, and
`.isSheaf_memberTopology_of_memberDiagHom` is the sheaf condition on the whole site it reduces to
the gluing obligation inside one member. All three are for an arbitrary presheaf on the site and
mention no descent datum.

**Diagonal arrows.**  `.memberChartMap_memberDiagHom` says that the two legs of the test space
of a diagonal arrow are one and the same morphism, which is the hypothesis under which
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_id_apply` applies.

**Two sieves, one family.**  The family is indexed by `.memberDiagSieve` rather than by
`.memberTransitionPresieve`, although it is the second over which the sheaf condition is available
(`.isSheafFor_memberTransitionPresieve`). Both are used: the second supplies the amalgamation, and
the first — which contains the second, hence is covering too — supplies the restriction back, over
every chart of the member in the sieve. The two are joined by uniqueness of the amalgamation over
the second, which is `.isAmalgamation_of_memberTransitionArrowsFamily`.

Nothing here inspects a transition, and the statements about an arbitrary sheaf on the small étale
site of the member therefore mention no descent datum.  The component forms instantiate them at
`D.F i`, whose sheaf condition is `CategoryTheory.SheafOfModules.isSheaf` of that component and
whose sections are read through `CategoryTheory.coyoneda`, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteSheafCondition.lean`
explain: the element-level form of the sheaf condition is not available at these universes.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
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

/-! ### The arrows of the site between two charts of one member -/

/-- **A morphism of charts of a member, read as a morphism of the site of the charts of the
members.**  The morphisms of that site are the morphisms of the induced charts of `X`, so this is
the given morphism pushed forward along the member morphism. -/
def memberDiagHom {i : I} {W V : SmallEtale B S hS (Yi i).1} (g : W ⟶ V) :
    memberPair B S hS Yi f hf i W ⟶ memberPair B S hS Yi f hf i V :=
  InducedCategory.homMk ((smallEtalePostcomp B S hS (f i) (hf i)).map g)

/-- Reading morphisms of charts of a member as morphisms of the site of the charts of the members
preserves composition: the site is an induced category, so composition is composition of the
induced morphisms of charts of `X`. -/
theorem memberDiagHom_comp {i : I} {W' W V : SmallEtale B S hS (Yi i).1} (h : W' ⟶ W)
    (g : W ⟶ V) :
    memberDiagHom B S hS Yi f hf (h ≫ g) =
      memberDiagHom B S hS Yi f hf h ≫ memberDiagHom B S hS Yi f hf g :=
  InducedCategory.hom_ext ((smallEtalePostcomp B S hS (f i) (hf i)).map_comp h g)

/-- **The two legs of the test space of a morphism of charts of one member, read as a morphism of
the site of the charts of the members, are one and the same morphism**: the morphism to the target
member of such an arrow is the structure morphism of its source chart, because the arrow commutes
the triangle over the member and not merely over `X`.

So the transition of a descent datum attached to such an arrow is a transition from a member to
*itself along one leg*, the situation of
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_id_apply`.  The identity
morphism of the site is carried as a variable `k'` with `hk' : k' = 𝟙 _`, as in
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartPair_snd'`. -/
theorem memberChartMap_memberDiagHom {i : I} {W V : SmallEtale B S hS (Yi i).1} (g : W ⟶ V)
    (k' : (smallEtalePostcomp B S hS (f i) (hf i)).obj W ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj W)
    (hk' : k' = 𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj W)) :
    memberChartMap B S hS Yi f hf V W (memberDiagHom B S hS Yi f hf g).hom =
      memberChartMap B S hS Yi f hf W W k' := by
  subst hk'
  exact ObjectProperty.hom_ext _ ((CostructuredArrow.w g.hom).trans
    (SmallEtale.map_id_comp_eq yoneda _).symm)

/-! ### The connecting arrow of an induced chart -/

/-- **The morphism of the site of the charts of the members from the chart induced by an arrow of
the site onto the source chart of that arrow.** Its underlying morphism of the big fppf site is the
identity — the induced chart is the identity chart of the chart space of the source chart pushed
forward, so the two charts have the same underlying object — and the triangle over `X` is the
triangle of the given arrow, reassociated. -/
def memberTransitionConnect {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    memberPair B S hS Yi f hf i (memberTransitionChart B S hS Yi f hf V V' k) ⟶
      memberPair B S hS Yi f hf j V' :=
  InducedCategory.homMk (ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _)
    ((SmallEtale.map_id_comp_eq yoneda _).trans
      ((CostructuredArrow.w k.hom).symm.trans (Category.assoc _ _ _).symm))))

/-- **The structure morphism of the chart induced by an arrow of the site of the charts of the
members factors that arrow**: read as a morphism of the site it is the connecting arrow followed by
the arrow itself.  Both sides are morphisms of the site, so the equation is the equation of the
underlying morphisms of the big fppf site, where it is
`CategoryTheory.Category.id_comp`: the connecting arrow carries an identity. -/
theorem memberTransitionConnect_comp {i : I} (V : SmallEtale B S hS (Yi i).1)
    {q : MemberSite B S hS Yi f hf} (k : q ⟶ memberPair B S hS Yi f hf i V) :
    memberTransitionConnect B S hS Yi f hf V q.2 k.hom ≫ k =
      memberDiagHom B S hS Yi f hf
        (memberTransitionHom B S hS Yi f hf V q.2 k.hom) :=
  InducedCategory.hom_ext (ObjectProperty.hom_ext _
    (CostructuredArrow.hom_ext _ _ (Category.id_comp _)))

/-! ### The part of a sieve living inside one member -/

/-- **The part of a sieve of an object of the site of the charts of the members which lives inside
the member**: the morphisms of charts of `Y i` into `V` whose morphism of the site lies in the
sieve.  It is a sieve because reading morphisms of charts of the member as morphisms of the site
preserves composition. -/
def memberDiagSieve {i : I} (V : SmallEtale B S hS (Yi i).1)
    (T : Sieve (memberPair B S hS Yi f hf i V)) : Sieve V where
  arrows _ g := T.arrows (memberDiagHom B S hS Yi f hf g)
  downward_closed hg h := by
    rw [memberDiagHom_comp]
    exact T.downward_closed hg _

/-- **The structure morphism of the chart of a member induced by an arrow of a sieve of the site of
the charts of the members lies in the part of that sieve living inside the member.**  The arrow of
the site it induces factors through the inducing arrow by `.memberTransitionConnect_comp`, and a
sieve is closed under precomposition. -/
theorem memberDiagSieve_memberTransitionHom {i : I} {V : SmallEtale B S hS (Yi i).1}
    {T : Sieve (memberPair B S hS Yi f hf i V)} {q : MemberSite B S hS Yi f hf}
    {k : q ⟶ memberPair B S hS Yi f hf i V} (hk : T.arrows k) :
    (memberDiagSieve B S hS Yi f hf V T).arrows
      (memberTransitionHom B S hS Yi f hf V q.2 k.hom) := by
  have h : T.arrows (memberTransitionConnect B S hS Yi f hf V q.2 k.hom ≫ k) :=
    T.downward_closed hk _
  rwa [memberTransitionConnect_comp] at h

/-- **The charts of a member induced by the arrows of a sieve of the site of the charts of the
members are charts of that member lying in the sieve.** -/
theorem memberTransitionPresieve_le_memberDiagSieve {i : I} (V : SmallEtale B S hS (Yi i).1)
    (T : Sieve (memberPair B S hS Yi f hf i V)) :
    memberTransitionPresieve B S hS Yi f hf V T ≤
      (memberDiagSieve B S hS Yi f hf V T).arrows := by
  rintro W g ⟨c⟩
  exact memberDiagSieve_memberTransitionHom B S hS Yi f hf c.2.2

/-- **The part of a covering sieve of an object of the site of the charts of the members living
inside the member is a covering sieve of the chart.**  It contains the sieve generated by the
induced charts, which covers by
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionPresieve_generate_mem_topology`. -/
theorem memberDiagSieve_mem_topology {i : I} (V : SmallEtale B S hS (Yi i).1)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V))) :
    memberDiagSieve B S hS Yi f hf V T ∈ SmallEtale.topology B S hS (Yi i).1 V :=
  (SmallEtale.topology B S hS (Yi i).1).superset_covering
    ((Sieve.generate_le_iff _ _).2
      (memberTransitionPresieve_le_memberDiagSieve B S hS Yi f hf V T))
    (memberTransitionPresieve_generate_mem_topology B S hS Yi f hf V T hT)

/-- **A sheaf on the small étale site of a member glues uniquely over the charts of that member
lying in a covering sieve of the charts of the members.** -/
theorem isSheafFor_memberDiagSieve {i : I} {V : SmallEtale B S hS (Yi i).1}
    {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V))) :
    Presieve.IsSheafFor P (memberDiagSieve B S hS Yi f hf V T).arrows :=
  hP _ (memberDiagSieve_mem_topology B S hS Yi f hf V T hT)

/-! ### The gluing statement over the induced charts -/

/-- **A compatible family of sections over the charts of a member induced by the arrows of a sieve
of the site of the charts of the members whose image covers has a unique amalgamation.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.isSheafFor_memberTransitionPresieve` read through
`CategoryTheory.Presieve.isSheafFor_arrows_iff`: the presieve of the induced charts is a
`CategoryTheory.Presieve.ofArrows` indexed by the arrows of the sieve, so the sheaf condition for
it is exactly unique gluing of a family indexed by those arrows, with no transport in between. -/
theorem exists_unique_amalgamation_memberTransitionChart {i : I}
    {V : SmallEtale B S hS (Yi i).1} {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V)))
    (y : ∀ c : memberSieveArrows B S hS Yi f hf V T,
      P.obj (Opposite.op (memberTransitionChart B S hS Yi f hf V c.1.2 c.2.1.hom)))
    (hy : Presieve.Arrows.Compatible P
      (fun c : memberSieveArrows B S hS Yi f hf V T =>
        memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom) y) :
    ∃! t : P.obj (Opposite.op V), ∀ c : memberSieveArrows B S hS Yi f hf V T,
      P.map (memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom).op t = y c :=
  (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_memberTransitionPresieve B S hS Yi f hf hP T hT) y hy

/-- **A family of sections indexed by the charts of a member lying in a sieve of the site of the
charts of the members, read as a family indexed by the arrows of that sieve**, that is as a family
of sections over the induced charts.  Nothing is transported: the structure morphism of an induced
chart *is* one of the morphisms of charts of the member in the sieve, by
`.memberDiagSieve_memberTransitionHom`. -/
def memberTransitionArrowsFamily {i : I} {V : SmallEtale B S hS (Yi i).1}
    {T : Sieve (memberPair B S hS Yi f hf i V)}
    {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (x : Presieve.FamilyOfElements P (memberDiagSieve B S hS Yi f hf V T).arrows)
    (c : memberSieveArrows B S hS Yi f hf V T) :
    P.obj (Opposite.op (memberTransitionChart B S hS Yi f hf V c.1.2 c.2.1.hom)) :=
  x (memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom)
    (memberDiagSieve_memberTransitionHom B S hS Yi f hf c.2.2)

/-- **The family over the induced charts obtained from a compatible family indexed by the charts of
the member in the sieve is compatible for the presieve of the induced charts.** Compatibility for a
`CategoryTheory.Presieve.ofArrows` is the compatibility of the underlying family at the arrows the
index produces, so this is the given compatibility with its two memberships supplied. -/
theorem memberTransitionArrowsFamily_compatible {i : I} {V : SmallEtale B S hS (Yi i).1}
    {T : Sieve (memberPair B S hS Yi f hf i V)}
    {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    {x : Presieve.FamilyOfElements P (memberDiagSieve B S hS Yi f hf V T).arrows}
    (hx : x.Compatible) :
    Presieve.Arrows.Compatible P
      (fun c : memberSieveArrows B S hS Yi f hf V T =>
        memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom)
      (memberTransitionArrowsFamily B S hS Yi f hf x) :=
  fun _ _ _ gi gj h => hx gi gj _ _ h

/-- **A compatible family of sections indexed by the charts of a member lying in a covering sieve
of the charts of the members has a unique amalgamation.** This is `.isSheafFor_memberDiagSieve`
with its definition unwound: the part of the sieve living inside the member is covering, so a sheaf
on the small étale site of the member glues over it. -/
theorem exists_unique_isAmalgamation_memberDiagSieve {i : I} {V : SmallEtale B S hS (Yi i).1}
    {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V)))
    (x : Presieve.FamilyOfElements P (memberDiagSieve B S hS Yi f hf V T).arrows)
    (hx : x.Compatible) :
    ∃! t : P.obj (Opposite.op V), x.IsAmalgamation t :=
  isSheafFor_memberDiagSieve B S hS Yi f hf hP T hT x hx

/-- **The section amalgamating the family over the induced charts restricts back to the original
family**, over every chart of the member lying in the sieve and not merely over the induced charts.
Both the part of the sieve living inside the member and the presieve of the induced charts are
covering, so each admits a unique amalgamation; the amalgamation over the first restricts correctly
over the induced charts, hence is the amalgamation over the second, hence is the given section. -/
theorem isAmalgamation_of_memberTransitionArrowsFamily {i : I}
    {V : SmallEtale B S hS (Yi i).1} {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V)))
    {x : Presieve.FamilyOfElements P (memberDiagSieve B S hS Yi f hf V T).arrows}
    (hx : x.Compatible) (t : P.obj (Opposite.op V))
    (ht : ∀ c : memberSieveArrows B S hS Yi f hf V T,
      P.map (memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom).op t =
        memberTransitionArrowsFamily B S hS Yi f hf x c) :
    x.IsAmalgamation t := by
  obtain ⟨t', ht', -⟩ :=
    exists_unique_isAmalgamation_memberDiagSieve B S hS Yi f hf hP T hT x hx
  have h : t = t' :=
    (exists_unique_amalgamation_memberTransitionChart B S hS Yi f hf hP T hT
        (memberTransitionArrowsFamily B S hS Yi f hf x)
        (memberTransitionArrowsFamily_compatible B S hS Yi f hf hx)).unique ht
      (fun c => ht' _ (memberDiagSieve_memberTransitionHom B S hS Yi f hf c.2.2))
  exact h ▸ ht'

/-! ### The component module of a descent datum -/

/-- **A compatible family of sections of a component module of a descent datum over the charts of
that member lying in a covering sieve of the charts of the members has a unique amalgamation.** The
sheaf condition used is the one the component module carries, read through
`CategoryTheory.coyoneda`. -/
theorem exists_unique_isAmalgamation_memberDiagSieve_component (D : DescentDatum B S hS Yi f)
    (i : I) {V : SmallEtale B S hS (Yi i).1} (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V)))
    (E : AddCommGrpCat.{u})
    (x : Presieve.FamilyOfElements ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E))
      (memberDiagSieve B S hS Yi f hf V T).arrows)
    (hx : x.Compatible) :
    ∃! t : ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E)).obj (Opposite.op V),
      x.IsAmalgamation t :=
  exists_unique_isAmalgamation_memberDiagSieve B S hS Yi f hf ((D.F i).isSheaf E) T hT x hx

/-- **A compatible family of sections of a component module of a descent datum over the charts of
that member induced by the arrows of a covering sieve of the charts of the members has a unique
amalgamation.** -/
theorem exists_unique_amalgamation_memberTransitionChart_component (D : DescentDatum B S hS Yi f)
    (i : I) {V : SmallEtale B S hS (Yi i).1} (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.topology B S hS X.1
        ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V)))
    (E : AddCommGrpCat.{u})
    (y : ∀ c : memberSieveArrows B S hS Yi f hf V T,
      ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E)).obj
        (Opposite.op (memberTransitionChart B S hS Yi f hf V c.1.2 c.2.1.hom)))
    (hy : Presieve.Arrows.Compatible ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E))
      (fun c : memberSieveArrows B S hS Yi f hf V T =>
        memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom) y) :
    ∃! t : ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E)).obj (Opposite.op V),
      ∀ c : memberSieveArrows B S hS Yi f hf V T,
        ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E)).map
          (memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom).op t = y c :=
  exists_unique_amalgamation_memberTransitionChart B S hS Yi f hf ((D.F i).isSheaf E) T hT y hy

/-! ### The connecting arrow of an induced chart is an isomorphism -/

/-- **A morphism of the site of the charts of the members whose morphism of the induced charts of
`X` is invertible is itself invertible.**  The site is an induced category, so a morphism of it
*is* a morphism of the charts of `X`, and an inverse there is an inverse here. -/
theorem isIso_of_isIso_hom {p q : MemberSite B S hS Yi f hf} (k : p ⟶ q) [IsIso k.hom] :
    IsIso k :=
  ⟨⟨InducedCategory.homMk (inv k.hom),
    InducedCategory.hom_ext (IsIso.hom_inv_id k.hom),
    InducedCategory.hom_ext (IsIso.inv_hom_id k.hom)⟩⟩

/-- **The morphism of the big fppf site underlying the connecting arrow of an induced chart is the
identity.**  The induced chart is the identity chart of the chart space of the source chart pushed
forward, so the two charts have the same underlying object, and the connecting arrow carries the
identity of it. -/
theorem memberTransitionConnect_hom_hom_left {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    (memberTransitionConnect B S hS Yi f hf V V' k).hom.hom.left = 𝟙 _ :=
  rfl

/-- **The connecting arrow of an induced chart is an isomorphism of the site of the charts of the
members**: its underlying morphism of the big fppf site is the identity
(`.memberTransitionConnect_hom_hom_left`). -/
theorem isIso_memberTransitionConnect {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    IsIso (memberTransitionConnect B S hS Yi f hf V V' k) := by
  have hleft : IsIso ((CostructuredArrow.proj yoneda X.1).map
      (memberTransitionConnect B S hS Yi f hf V V' k).hom.hom) := by
    change IsIso ((memberTransitionConnect B S hS Yi f hf V V' k).hom.hom.left)
    rw [memberTransitionConnect_hom_hom_left]
    exact IsIso.id _
  have hfull : IsIso (memberTransitionConnect B S hS Yi f hf V V' k).hom :=
    (ObjectProperty.isIso_hom_iff _).1 (isIso_of_reflects_iso _ (CostructuredArrow.proj yoneda X.1))
  exact isIso_of_isIso_hom B S hS Yi f hf _

/-! ### The gluing obligation reduced to the arrows inside one member -/

/-- **A section restricting correctly along every morphism of charts of the member in a sieve of
the site of the charts of the members restricts correctly along every arrow of that sieve.**

The statement is for an arbitrary presheaf of types on the site, and the hypothesis is only about
the arrows coming from morphisms of charts of the one member. -/
theorem isAmalgamation_of_memberDiagHom {P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ Type w} {i : I}
    {V : SmallEtale B S hS (Yi i).1} {T : Sieve (memberPair B S hS Yi f hf i V)}
    {x : Presieve.FamilyOfElements P T.arrows} (hx : x.Compatible)
    (t : P.obj (Opposite.op (memberPair B S hS Yi f hf i V)))
    (ht : ∀ {W : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
      (ha : T.arrows (memberDiagHom B S hS Yi f hf a)),
      P.map (memberDiagHom B S hS Yi f hf a).op t = x (memberDiagHom B S hS Yi f hf a) ha) :
    x.IsAmalgamation t := by
  intro q k hk
  have := isIso_memberTransitionConnect B S hS Yi f hf V q.2 k.hom
  have hcomp : memberTransitionConnect B S hS Yi f hf V q.2 k.hom ≫ k =
      memberDiagHom B S hS Yi f hf (memberTransitionHom B S hS Yi f hf V q.2 k.hom) :=
    memberTransitionConnect_comp B S hS Yi f hf V k
  have ha : T.arrows (memberDiagHom B S hS Yi f hf
      (memberTransitionHom B S hS Yi f hf V q.2 k.hom)) :=
    memberDiagSieve_memberTransitionHom B S hS Yi f hf hk
  have hrestr : P.map (memberTransitionConnect B S hS Yi f hf V q.2 k.hom).op (P.map k.op t) =
      x (memberDiagHom B S hS Yi f hf
        (memberTransitionHom B S hS Yi f hf V q.2 k.hom)) ha := by
    rw [← Functor.map_comp_apply, ← op_comp, hcomp]
    exact ht _ ha
  have hfam : P.map (memberTransitionConnect B S hS Yi f hf V q.2 k.hom).op (x k hk) =
      x (memberDiagHom B S hS Yi f hf
        (memberTransitionHom B S hS Yi f hf V q.2 k.hom)) ha := by
    simpa using hx (memberTransitionConnect B S hS Yi f hf V q.2 k.hom)
      (𝟙 (memberPair B S hS Yi f hf i
        (memberTransitionChart B S hS Yi f hf V q.2 k.hom))) hk ha
      (by rw [hcomp, Category.id_comp])
  exact ((isIso_iff_bijective
    (P.map (memberTransitionConnect B S hS Yi f hf V q.2 k.hom).op)).1
      inferInstance).1 (hrestr.trans hfam.symm)

/-- **The gluing obligation over a sieve of the site of the charts of the members is the gluing
obligation over the morphisms of charts of the one member in it.**  Existence is
`.isAmalgamation_of_memberDiagHom`, and uniqueness is immediate: an amalgamation over the whole
sieve is in particular one over the arrows coming from morphisms of charts of the member. -/
theorem isSheafFor_of_existsUnique_memberDiagHom {P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ Type w}
    {i : I} {V : SmallEtale B S hS (Yi i).1} (T : Sieve (memberPair B S hS Yi f hf i V))
    (h : ∀ x : Presieve.FamilyOfElements P T.arrows, x.Compatible →
      ∃! t : P.obj (Opposite.op (memberPair B S hS Yi f hf i V)),
        ∀ {W : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
          (ha : T.arrows (memberDiagHom B S hS Yi f hf a)),
          P.map (memberDiagHom B S hS Yi f hf a).op t =
            x (memberDiagHom B S hS Yi f hf a) ha) :
    Presieve.IsSheafFor P (T : Presieve (memberPair B S hS Yi f hf i V)) := by
  intro x hx
  obtain ⟨t, ht, hu⟩ := h x hx
  exact ⟨t, isAmalgamation_of_memberDiagHom B S hS Yi f hf hx t ht,
    fun t' ht' => hu t' fun a ha => ht' (memberDiagHom B S hS Yi f hf a) ha⟩

/-! ### The same with the covering sieve read on the charts of the members -/

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- `.memberDiagSieve_mem_topology` with its hypothesis read in the topology of the charts of the
members itself, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.mem_memberTopology_iff`. -/
theorem memberDiagSieve_mem_topology_of_mem_memberTopology {i : I}
    (V : SmallEtale B S hS (Yi i).1) (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T ∈ memberTopology B S hS Yi f hf (memberPair B S hS Yi f hf i V)) :
    memberDiagSieve B S hS Yi f hf V T ∈ SmallEtale.topology B S hS (Yi i).1 V :=
  memberDiagSieve_mem_topology B S hS Yi f hf V T
    (mem_memberTopology_iff B S hS Yi f hf |>.1 hT)

/-- `.exists_unique_isAmalgamation_memberDiagSieve` with its hypothesis read in the topology of the
charts of the members itself. -/
theorem exists_unique_isAmalgamation_memberDiagSieve_of_mem_memberTopology {i : I}
    {V : SmallEtale B S hS (Yi i).1} {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T ∈ memberTopology B S hS Yi f hf (memberPair B S hS Yi f hf i V))
    (x : Presieve.FamilyOfElements P (memberDiagSieve B S hS Yi f hf V T).arrows)
    (hx : x.Compatible) :
    ∃! t : P.obj (Opposite.op V), x.IsAmalgamation t :=
  exists_unique_isAmalgamation_memberDiagSieve B S hS Yi f hf hP T
    (mem_memberTopology_iff B S hS Yi f hf |>.1 hT) x hx

/-- `.isAmalgamation_of_memberTransitionArrowsFamily` with its hypothesis read in the topology of
the charts of the members itself. -/
theorem isAmalgamation_of_memberTransitionArrowsFamily_of_mem_memberTopology {i : I}
    {V : SmallEtale B S hS (Yi i).1} {P : (SmallEtale B S hS (Yi i).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (Yi i).1) P)
    (T : Sieve (memberPair B S hS Yi f hf i V))
    (hT : T ∈ memberTopology B S hS Yi f hf (memberPair B S hS Yi f hf i V))
    {x : Presieve.FamilyOfElements P (memberDiagSieve B S hS Yi f hf V T).arrows}
    (hx : x.Compatible) (t : P.obj (Opposite.op V))
    (ht : ∀ c : memberSieveArrows B S hS Yi f hf V T,
      P.map (memberTransitionHom B S hS Yi f hf V c.1.2 c.2.1.hom).op t =
        memberTransitionArrowsFamily B S hS Yi f hf x c) :
    x.IsAmalgamation t :=
  isAmalgamation_of_memberTransitionArrowsFamily B S hS Yi f hf hP T
    (mem_memberTopology_iff B S hS Yi f hf |>.1 hT) hx t ht

/-- **The sheaf condition on the charts of the members is the gluing obligation inside one
member.**  A presheaf of abelian groups on the charts of the members is a sheaf as soon as, for
every abelian group `E`, every member `i`, every chart `V` of it and every sieve of `(i, V)` whose
image covers the induced chart of `X`, a compatible family on that sieve has a unique section
restricting correctly along the morphisms of charts of `Y i` in it.

The statement is for an arbitrary presheaf of abelian groups on the site: nothing here mentions a
descent datum. -/
theorem isSheaf_memberTopology_of_memberDiagHom
    (P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (h : ∀ (E : AddCommGrpCat.{u}) (i : I) (V : SmallEtale B S hS (Yi i).1)
      (T : Sieve (memberPair B S hS Yi f hf i V)),
      T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
          SmallEtale.topology B S hS X.1
            ((memberFunctor B S hS Yi f hf).obj (memberPair B S hS Yi f hf i V)) →
        ∀ x : Presieve.FamilyOfElements (P ⋙ coyoneda.obj (Opposite.op E)) T.arrows,
          x.Compatible →
          ∃! t : (P ⋙ coyoneda.obj (Opposite.op E)).obj
              (Opposite.op (memberPair B S hS Yi f hf i V)),
            ∀ {W : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
              (ha : T.arrows (memberDiagHom B S hS Yi f hf a)),
              (P ⋙ coyoneda.obj (Opposite.op E)).map (memberDiagHom B S hS Yi f hf a).op t =
                x (memberDiagHom B S hS Yi f hf a) ha) :
    Presheaf.IsSheaf (memberTopology B S hS Yi f hf) P :=
  (isSheaf_memberTopology_iff B S hS Yi f hf P).2 fun E p T hT =>
    isSheafFor_of_existsUnique_memberDiagHom B S hS Yi f hf T (h E p.1 p.2 T hT)

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end

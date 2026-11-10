module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSitePresheaf

/-!
# The presheaf of abelian groups on the charts of the members, and the module it carries

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X` and let `D` be a descent datum for quasi-coherent modules relative to that
family.  `StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSitePresheaf.lean`
supplies the data of a presheaf of modules on the site of the charts of the members, and records
that assembling that data into a `CategoryTheory.PresheafOfModules` directly is out of reach: the
restriction map of such a presheaf lands in a restriction of scalars, so every law is an equation
transported across a varying ring map.

This file assembles the data **as a presheaf of abelian groups** instead, where the two laws are
ordinary equations in `AddCommGrpCat` with no restriction of scalars anywhere, and where the
module structures are carried separately.  `CategoryTheory.PresheafOfModules.ofPresheaf` builds
the restriction-of-scalars wrapper out of that.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAb_id_apply`: **the identity law of
  the restriction map, in the spelling with no restriction of scalars** — the transition of the
  restriction of a section along an identity morphism of the site of the charts of the members is
  that section.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartSpaceHom` is the morphism of charts of
  the chart space of the source chart onto the identity chart of the chart space of the target
  chart, and `.memberChartSpaceHom_postcomp` and `.memberChartSpaceHom_postcomp_comp` identify
  its two pushforwards with the morphisms of charts of the members that the site induces.  Those
  two identifications are what the composition law needs, and both hold **on the nose**.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionSect_restrict`: the naturality
  of the transition in the chart with its two restrictions carried as variables, and
  `.transitionSect_base_restrict`: **the change of test space composed with that naturality, as
  one law on variables.**  The two may not be composed at a consumer's concrete charts; see the
  implementation notes.  `.transitionLegsSect` and `.transitionLegsSect_congr_transport` are
  the same for the written-out reading; the transport form is the one a consumer can use.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.moduleCat_hom_apply_zero`,
  `.moduleCat_hom_apply_add`, `.val_app_apply_zero`, `.val_app_apply_add`,
  `.addCommGrpCat_hom_ofHom_mk_apply`, `.addCommGrpCat_hom_id_apply` and
  `.addCommGrpCat_hom_comp_ofHom_mk_apply`: **the four coercions a presheaf of abelian groups on
  the charts of the members is read through, one lemma each**, every one of them on variables.
  They are what discharges the additivity of a restriction map and what carries its two laws
  across the `AddCommGrpCat` wrapper; see the implementation notes for why no two of the four can
  share a lemma.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAb_comp_apply`: **the composition law
  of the restriction map, in the spelling with no restriction of scalars.**  It is
  `.memberTransitionEtaleForm_comp` — the same law with the three morphisms of charts of `X`
  carried as variables — at the morphisms of charts a composable pair of morphisms of the site
  induces, and that in turn is `.transitionEtaleForm_base_comp`, the whole join on variables,
  which rests on `.transitionSect_base_restrict_of_legs`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_base_restrict_of_legs`: **the
  change of test space composed with the naturality in the chart, with the two legs of the
  smaller test space carried as variables**, which is what lets a consumer state every step in
  its own spelling of those legs and respell nothing afterwards.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.val_map_comp_hom_apply`: two restrictions of a
  module read on a section compose.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.TransitionLegs`,
  `.transitionLegsForm` and `.transitionLegsForm_congr`: **the data a reading of the transition
  depends on, bundled, and the agreement of two readings whose data are equal, read on a
  section.**  This is what lets two spellings of a leg be identified at all; see the
  implementation notes.  `.transitionLegsSect` and `.transitionLegsSect_congr_transport` are
  the same for the written-out reading; the transport form is the one a consumer can use.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumObj`: **the sections of the
  presheaf of abelian groups over an object of the site, carrying their module structure** — the
  sections of the component module over the chart which the identity morphism of the site
  induces, ascribed as a module over the structure ring of the induced chart of `X`.  That
  ascription is the module structure `CategoryTheory.PresheafOfModules.ofPresheaf` asks for
  beyond the presheaf itself.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAb_comp_apply'`: **the composition law
  retyped onto those sections**, which is the form `map_comp` of a `CategoryTheory.Functor`
  structure instance needs; the crossing it performs may not be performed anywhere else.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.addCommGrpCat_ofHom_eq_comp`: **`map_comp` of a
  direct `AddCommGrpCat`-valued functor structure instance, reduced to the composition law of its
  restriction map on sections** — as an equation of *morphisms*, with the three additive maps
  carried bundled.  Four other shapes do not reach the goal; see the
  implementation notes.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.addCommGrpCat_ofHom_eq_id`: the same for
  `map_id`, with the object carried as a type with an `AddCommGroup` structure, which is what
  keeps the section a consumer reasons about at the type its law speaks of.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.AddMonoidHomLaws`, `.toAddMonoidHom` and
  `.toAddMonoidHom_apply`: **the two laws of an additive map, bundled as a proposition about its
  underlying function, and the map they build.**  This is what lets the additivity of a
  restriction map be proved in a *theorem* instead of in a field of a `def` -- which the kernel
  will not accept -- and it keeps the `0` and the `+` of the sections out of every
  statement written here, which the recursion depth will not accept either.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAb_id_apply'`: **the identity law
  retyped onto the sections of the presheaf**, the companion of `.memberDatumAb_comp_apply'`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbMap_laws`: **the restriction map of
  the presheaf of abelian groups has the two laws of an additive map.**  Together with
  `.AddMonoidHomLaws.toAddMonoidHom` this is the restriction map itself; what is still missing is
  recorded in the implementation notes.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.val_app_apply_of_eq_id`: a morphism of
  `𝒪`-modules equal to an identity acts as the identity on a section, **with the morphism carried
  as a variable**, which is what lets a consumer read it off a goal through the projection
  `CategoryTheory.SheafOfModules.Hom.val` instead of matching it there.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbMap_laws_id_apply`: **the identity
  law of the restriction map, stated of the instantiation of `.memberDatumAbMap_laws` rather than
  of a copy of its text** -- the form a `map_id` goal of a direct functor structure instance
  needs, and the counterpart for the identity law of what `.memberTransitionEtaleForm_comp` is for
  the composition law.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAb_comp_apply_of_eq'`: **the
  composition law of the restriction map with the composite morphism of the site carried as a
  variable**, and `.memberDatumRestrict_comp_apply_of_eq` its restriction factor.  Elaborated
  with the composite opaque, these are what an *instantiation* at `g ≫ h` reproduces, where a
  freshly elaborated copy of the same text does not.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbMap_laws_apply_of_eq`,
  `.memberDatumAbMap_laws_apply` and `.memberDatumAbMap_laws_comp_apply_aux`: **the restriction
  map of the presheaf of abelian groups read on a section, and two such readings nested**, which
  is how a `map_comp` goal is met from the written-out side.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbMap_laws_comp_apply`: **the
  composition law stated of the instantiations of `.memberDatumAbMap_laws` a `map_comp` goal
  carries**, the counterpart of `.memberDatumAbMap_laws_id_apply`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbMapId_eq` and
  `.memberDatumAbMapComp_eq`: **the two laws of the presheaf of abelian groups as equations of
  morphisms of `AddCommGrpCat`** -- the two obligations of a direct `CategoryTheory.Functor`
  structure instance, each proved.

## Implementation notes

The law is **written out** rather than stated of a named reading of the restriction map: a
named `def` or `abbrev` for that map makes the same statement elaborate and then exhausts the
recursion depth at the unification.  So the presheaf of abelian groups to be assembled
is to be a direct structure instance, in which the goal of each law is the beta-reduced
written-out term, and the laws proved here are stated in exactly that spelling.

**One identification per step.**  Every step below changes exactly one of: the spelling of a
chart, the spelling of a leg, or the presence of a `ModuleCat.restrictScalars` around a module of
sections.  A step that changes two at once times out; that is the whole reason the lemmas here
carry their morphisms and sections as *variables* with the defining equations as hypotheses,
which a consumer discharges by `rfl` on its own — where the identification is cheap, well under a
second — instead of ascribing the other spelling into a statement, where it is not.

**The connecting morphism of charts is written out, not taken from terminality.**  The identity
chart of a chart space is a terminal object of its small étale site
(`AlgebraicGeometry.Space.isTerminalIdEtaleChart`), so there is a unique morphism onto it from
the chart that a morphism of the site induces, and it is the same morphism as
`.memberChartSpaceHom`.  It may **not** be used: the terminal morphism does not agree
with `.memberTransitionHom` even on underlying morphisms (`.hom.left`) without unwinding the full
faithfulness of `CategoryTheory.yoneda`, because its left component is a `yoneda` preimage.
Written as `ObjectProperty.homMk (CostructuredArrow.homMk b.hom.left rfl)` both
`.memberChartSpaceHom_postcomp` and `.memberChartSpaceHom_postcomp_comp` are `rfl`.

**The route of the composition law.**  Every ingredient compiles on its own.  The route, for
`g : p ⟶ q` and `h : q ⟶ r` of
the site with underlying morphisms `a` and `b` of the charts of `X`, is: the naturality
`.memberTransitionSect_restrict` of the transition from `p` to `q` in the chart, along
`.memberChartSpaceHom`; then the change of test space
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_base` from the chart space of the
middle chart down to the chart space of the last; then the composition
`.transitionSect_comp` of the two transitions there, which is `D.cocycle`.
`.transitionEtaleForm_val_app_apply` is the bridge from the bundled reading to the written-out
one at each of the three transitions.  Four identifications carry it, and all four are `rfl`:

* `memberChartMap V V'' (b ≫ a) = chartMap X b ≫ memberChartMap V V' a`;
* `memberChartMap V' V'' b = chartMap X b ≫ memberChartMap V' V' (𝟙 _)`;
* `(smallEtalePostcomp (memberChartMap V V' a) _).obj ((smallEtalePostcomp (chartMap X b) _).obj
  (chartSpaceIdChart (Yi k) V'')) = memberTransitionChart V V'' (b ≫ a)`;
* the two `.memberChartSpaceHom_postcomp` lemmas.

**The identifications, ranked by what they cost together.**  Three kinds of identification occur
in the join: stripping the `ModuleCat.restrictScalars` that the target of a restriction map
carries; a *chart* crossing, between two spellings of one chart of a member; and an *inverse
image* crossing, between the sections of an inverse image over a chart and the sections of the
module over the composite chart.  Each one alone costs about a second, and **any two
of them in one elaboration step time out** at 200000 heartbeats.  Naming the restriction — a
`def` whose body is `ModuleCat.Hom.hom (M.val.map x) m`, so that the strip happens in its type —
does not help: the remaining pair still times out, and the named reading cannot be related to
its body.

What does work is to stage them as **nested type ascriptions**, one crossing per ascription:

```
etaleSectInv B S hS (memberChartMap … V V' a) _ (D.F i)
  ((smallEtalePostcomp … (chartMap … b) _).obj
    (chartSpaceIdChart … (Yi k) V''))
  (((ModuleCat.Hom.hom ((D.F i).val.map (memberTransitionHom … V V'' (b ≫ a)).op) m :
        (D.F i).val.obj (.op (memberTransitionChart … V V'' (b ≫ a)))) :
      (D.F i).val.obj (.op ((smallEtalePostcomp … (memberChartMap … V V' a) _).obj
        ((smallEtalePostcomp … (chartMap … b) _).obj (chartSpaceIdChart … (Yi k) V''))))))
```

which elaborates in about a second where the unstaged term times out.

**Why `.transitionSect_base_restrict` exists.**  With the sections staged, every ingredient of
the join elaborates, and so does `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_base`
and `.transitionSect_restrict` at the concrete charts of the members; their middle terms then
print *character-for-character alike* — this was checked by printing both — and `Eq.trans`
between them still times out at `isDefEq`.  What it cannot afford is the ambient type of the two
equations: the chart of the smaller test space is `(smallEtalePostcomp (wv ≫ vj) _).obj U` in the
one and `(smallEtalePostcomp vj _).obj ((smallEtalePostcomp wv _).obj U)` in the other, and that
identification — free on its own, `rfl` in under a second — is not affordable there.  Pinning the
two test spaces explicitly does not help.  `.transitionSect_base_restrict` performs the join
**inside a statement all of whose charts, legs and sections are variables**, where the middle
term is literally one term, and a consumer then makes a single application instead of a
composition of two.

**What remains of the composition law, and the one route that is closed.**  With
`.transitionSect_base_restrict` the first three of the six steps of the join collapse into a
single application that elaborates, and the remaining obstacle is narrow and precisely located:
the legs of the smaller test space come out of it spelled `wv ≫ vi` and `wv ≫ vj`, that is
`chartMap X b ≫ memberChartMap V V' a` and `chartMap X b ≫ memberChartMap V' V' (𝟙 _)`, while the
goal spells them `memberChartMap V V'' (b ≫ a)` and `memberChartMap V' V'' b`.  The two are
`rfl` as morphisms, in milliseconds.  Respelling one at a time by an ascription times out at
`whnf`, because the section inside the reading has to be carried across the same leg at the same
time.

The move that works everywhere else in this file — carry the thing as a **variable** with a
`rfl`-discharged hypothesis — **cannot be applied to a leg**, and the reason is not a budget but
a type error.  A leg is an argument of `AlgebraicGeometry.Space.etaleSectInv`, and the section it
is applied to is indexed by the chart that leg induces.  With the leg a variable `wi` and
`hwi : wi = wv ≫ vi` in scope, a section typed `(D.F i).val.obj (.op ((smallEtalePostcomp wi
hwi').obj U))` is rejected on the other side of the equation, where it must be
`((etaleModulePullback vi hvi).obj (D.F i)).val.obj (.op ((smallEtalePostcomp wv hwv).obj U))`:

```
Application type mismatch: the argument `s` has type
  ↑((D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS wi hwi').obj U)))
but is expected to have type
  ↑(((etaleModulePullback B S hS vi hvi).obj (D.F i)).val.obj
      (Opposite.op ((smallEtalePostcomp B S hS wv hwv).obj U)))
```

A hypothesis in scope does not make two types defeq, so the statement does not elaborate at all;
generalising the target chart as well does not help, because the section then has a type the two
`etaleSectInv`s still disagree about.

**What the obstruction actually is, and what removes it.**  Two earlier diagnoses of the leg
respelling were wrong and are recorded here so that they are not repeated.  It is **not** the
étaleness witness: two *different* witnesses `hvi hvi' : IsEtale … vi.hom` in that position are
identified by `rfl`, green in elaborator and kernel.  And it is **not** the transport: the
chart transport of `.etaleSect_eqToHom`, `HEq (eqToHom (congrArg … (smallEtalePostcomp_obj_congr
… hvi (hii ▸ hvi) hii U)) s) s`, is `subst hii; rfl`, green in seconds.

The obstruction is the **`.app (.op U)` step**, and the arguments that cost are the
**compatibility proofs** `hi : v ≫ pairFst … = vi` and `hj : v ≫ pairSnd … = vj`.  With
one opaque leg, one étaleness witness and nothing else differing:

* `transitionHom … v vi vj hi hj = transitionHom … v vi vj hi' hj'` — **morphism level** — is
  `rfl` in 0.2 s, and so is the leg respelling at the morphism level with every primed datum
  derived by transport;
* `(transitionHom … hi hj).val.app (.op U) s = (transitionHom … hi' hj').val.app (.op U) s` —
  the *same* difference, one projection lower — reports `maximum recursion depth`.

`SheafOfModules.Hom.val` is a **projection**, so two applications of it are never compared
argument by argument: the elaborator demands the morphism in constructor form, and for the
transition that means reducing through `AlgebraicGeometry.Space.modulePullbackCompIso`, which is
`CategoryTheory.Adjunction.leftAdjointUniq` of two adjunctions and does not get there.  Any
syntactic difference at all between the two sides' arguments triggers it.

**So the fix is a data change at this one interface, not a re-formalisation.**  `.TransitionLegs`
bundles `(v, vi, vj, hvi, hvj, hi, hj)`, `.transitionLegsForm` is the reading taking that bundle,
and `.transitionLegsForm_congr` transports a section across an equality of bundles.  Two things
make it work:

* the two bundles the composition law has to identify — the one spelled with the composite legs
  `chartMap X b ≫ memberChartMap V V' a` and the one spelled `memberChartMap V V'' (b ≫ a)` — are
  equal by **`rfl`**, because at the level of the bundle no projection of a sheaf morphism is in
  the way;
* with the agreement of the two readings then supplied *propositionally*, `.app (.op U)` is never
  asked for a defeq at all.

The one pitfall in stating such a congruence is to carry one section and its transport, `h ▸ s`:
the `rfl` after `subst` then has to reduce the transport **inside** `.val.app`, which is the very
thing being avoided, and it times out.  Carrying the two sections as separate variables related
by `HEq` — as `.transitionLegsForm_congr` does — makes `subst` and `cases` leave one term, and
the proof is syntactic.

**The composition law with the bundle.**  The leg respelling works.  At the two concrete bundles of
the composition law — the one
spelled with the composite legs `chartMap X b ≫ memberChartMap V V' a`, `chartMap X b ≫
memberChartMap V' V' (𝟙 _)` and the one spelled `memberChartMap V V'' (b ≫ a)`,
`memberChartMap V' V'' b`:

* their equality is `rfl`, green;
* `.transitionLegsSect_congr_transport` applied at them is green;

so the two readings are related.  Two constraints apply:

* the **two-section** form `.transitionLegsSect_congr` cannot be used at concrete data.  Its
  section types are written through the bundle's projections, so a `HEq` stated in the
  consumer's own spelling asks for two crossings in one unification and times out; stating the
  `HEq` in the projection spelling instead moves the timeout into the `HEq.rfl`.  The transport
  form is the one to use.
* a bundle **literal** must not carry a crossing in a field.  Writing the `w ≫ vi`-spelled
  bundle with `hvi := isEtale_memberChartMap … V V'' (b ≫ a)` puts the leg crossing inside the
  literal, and any statement around it then has two.  Bind such a field by a `have` of its own
  first.

**How the composition law is proved, and the four facts that decide its shape.**  The
route of the previous paragraphs is the one that works, but *not* through the bundle: the bundled
reading `.transitionLegsSect` is a **named** reading, and the rule of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartTransition.lean` applies to
it — `transitionLegsSect … L U s = etaleSect … ((transitionHom …).val.app …
(etaleSectInv … s))` exhausts the recursion depth as a `rfl`, at a literal bundle and at a
variable bundle alike, and so does `exact` of the written-out law against the goal left by
`unfold transitionLegsSect`.  A bundled law can therefore never be *derived* from the written-out
laws, and `.TransitionLegs` is kept only for what it was built for: relating two readings whose
data differ by a respelling.

What replaces it is the same idea applied to the **legs**, not to the reading.  The recorded type
error — that a leg of the smaller test space cannot be a variable — is an error only when the
sections on that side are still typed through the *composite* leg.  Typing every section and
every connecting morphism of charts on that side through the variable leg removes it, at the cost
of carrying the connecting morphism `cc` as a variable related to
`(smallEtalePostcomp vi hvi).map c` by `HEq`.  That is
`.transitionSect_base_restrict_of_legs`, and with it the join is a single application:
`.transitionEtaleForm_base_comp`.

Four things are needed in bringing that application down to the charts of the members:

* **the test spaces must be pinned in the `Yi`-spelling.**  Inferred from `chartMap X b` they come
  out as `chartSpace X ((smallEtalePostcomp (f k) (hf k)).obj V'')`, the same algebraic space on
  the nose as `chartSpace (Yi k) V''`; every later identification of charts then pays for that
  identification too, and the instantiation times out at `isDefEq`.  With `(T := …)` and
  `(T' := …)` given it takes under two seconds.
* **the morphisms of charts of `X` must be variables.**  With `memberHom (𝟙 q).unop`,
  `memberHom (g ≫ h).unop` and the rest written out, the statement of the member-level law costs
  four times as much to elaborate (5.3 s against 1.3 s) and the instantiation exceeds the
  heartbeat budget; with them carried as variables identified by `rfl`-discharged hypotheses it
  does not.  That is why `.memberTransitionEtaleForm_comp` takes `idq`, `idr`, `ba`.
* **each identification goes in a declaration of its own.**  `.memberDatumRestrict_comp_apply`,
  `.heq_memberChartSpaceHom_postcomp` and `.heq_memberTransitionHom_postcomp` are the three
  hypotheses of the member-level law at a consumer's data; inlined into one application they
  exhaust the budget together, separately each is free.
* **the middle restriction must carry its two charts explicitly.**  The chart over which the
  transition from `p` to `q` reads its target is `(smallEtalePostcomp (memberChartMap V' V' …)
    …).obj
  (chartSpaceIdChart (Yi j) V')`, which is `V'` on the nose, and `(memberTransitionHom …).op`
  takes the *natural* spelling `V'` into the implicit arguments of
  `CategoryTheory.Functor.map`.  Identifying the two there is unaffordable: the instantiation
  exhausts the recursion depth, and the `rfl` equation between the two spellings exhausts the
  heartbeat budget on its own.  Writing `Quiver.Hom.op (X := …) (Y := …)` puts the chart spelling
  in the term, where it costs nothing.  The presheaf to be assembled must therefore spell its
  restriction map that way.

Two further facts.  A `HEq` between the sections
of an **étale restriction** over a chart and the sections of the module over the composite chart
cannot be eliminated: `eq_of_heq` on it exhausts the recursion depth, which is the rule of the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSitePresheaf.lean` that those
two spellings may not meet in a
unification, met at `HEq`.  And splitting `.transitionEtaleForm_base_comp` into its two halves
and rejoining them by `.apply_congr` costs *more* than the single application, not less.

**Where the assembly of the presheaf of abelian groups stands.**  Both laws are proved, in one
and the same spelling, and the direct `CategoryTheory.Functor` structure instance
`(MemberSite …)ᵒᵖ ⥤ AddCommGrpCat` that takes them is

* `obj p := AddCommGrpCat.of (memberDatumObj … p)` — the sections read over the chart the
  **identity** morphism of the site induces, not over `p.unop.2`.  That choice is forced: the
  chart over which the transition reads its target is that one, so with it the restriction of a
  section needs no chart crossing in either of the two roles a morphism of the site plays in
  `map_comp`.
* `map g := AddCommGrpCat.ofHom ⟨⟨fun m => (transitionEtaleForm … ).val.app (.op
  (chartSpaceIdChart … (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map
  (Quiver.Hom.op (X := …) (Y := …) (memberTransitionHom … ))) m), _⟩, _⟩`.

**Four coercions, one lemma each — and that is what the two additivity obligations needed.**  A
restriction map of that instance is read through `ModuleCat.Hom.hom` in its first factor and
through the *direct application* of a morphism of sheaves of modules, i.e. through
`ConcreteCategory.hom`, in its second; the functor's laws are read through
`AddCommGrpCat.Hom.hom`; and the additive map itself is a structure literal.  No single
`map_zero`-style lemma covers two of those, which is exactly why `simp`, `simp only [map_zero]`,
`rw [map_zero, map_zero]` (`rewrite` does not find its pattern) and `map_zero _` (timeout at
`whnf`) all fail on `map_zero'` *in situ*.  With one lemma per coercion they go through:

* `map_zero' := val_app_apply_zero (transitionEtaleForm … ).val.app … ) _
  (moduleCat_hom_apply_zero ((D.F p.unop.1).val.map … ))` and the same for `map_add'` with
  `.val_app_apply_add` and `.moduleCat_hom_apply_add`.  The whole crossing between the sections of
  an étale restriction and the sections over a composite chart sits in the **argument** `z` of
  `.val_app_apply_zero`, which is a function-argument position, and nowhere else.
* `map_id := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m =>
  (addCommGrpCat_hom_ofHom_mk_apply _ _ _ m).trans ((memberDatumAb_id_apply … m).trans
  (addCommGrpCat_hom_id_apply m).symm))`.  **Term-mode `Eq.trans` through the coercion lemmas is
  what works**, and the two alternatives do not: `rw
  [addCommGrpCat_hom_ofHom_mk_apply]` reports that it does not find its pattern, and `exact` of
  the section-level law exhausts the recursion depth — although the very same reduction,
  `AddCommGrpCat.Hom.hom (AddCommGrpCat.ofHom ⟨⟨F, h0⟩, ha⟩) m = F m` with `F` a **variable**, is
  `rfl` in milliseconds.  The cost is therefore not the iota but the unifier's choice of which
  side to delta-reduce: facing the concrete body it unfolds that instead of the literal.

**The assembly, and the one remaining obstruction.**  Of the structure
instance, `obj`, `map`, `map_zero'`, `map_add'` and `map_id` all elaborate — the whole
file in under five seconds — and `map_comp` does not.  Five shapes for it fail.

* `AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => …)` chaining
  `.addCommGrpCat_hom_comp_ofHom_mk_apply` with `_` for its two functions leaves `?F_h (?F_g m)`
  to be matched against the composition law.  That is a higher-order unification: the unifier
  takes the first-order approximation `?F_h := ⇑T_h`, then solves `?F_g m` as a pattern and
  absorbs the second restriction into it, and the assignment is wrong, so the application is
  rejected — in **both** directions of the chain.  Dot-notation `.trans`/`.symm` make this worse
  by hiding the expected type: `e.symm` and `e.trans f` elaborate `e` *first*, in order to
  resolve the name, so no expected type reaches the chain and every metavariable has to be
  solved by one unification at the end.  Prefix `Eq.symm`/`Eq.trans` propagate it.
* Carrying the value of the composite as a variable removes the higher-order step, but the
  conclusion still mentions the middle object only as `AddCommGrpCat.of ↥?N`; `↥_` is a
  projection and the unifier cannot invert it, so `?N` is never determined.
* Splitting the three readings into hypotheses on variables
  (`hom A m = x`, `hom A' x = y`, `hom C m = z`, `z = y`) determines every object first order,
  but Lean postpones an argument whose expected type still has metavariables and resumes it
  after the later ones, so the crossing cannot be confined to the last hypothesis this way.
* As an equation of **morphisms** with the three maps as `(F, map_zero', map_add')` triples, the
  match against the goal assigns the two proof fields of each triple separately, which re-checks
  the additivity of the restriction map — crossing and all — six times over, and the recursion
  depth is exhausted.
* `.addCommGrpCat_ofHom_eq_comp`, the equation of morphisms with the three maps **bundled**, is
  the shape that works: there is no ambient type to cross, each object and each additive map is
  one first-order assignment, and the whole of `map_comp` reduces to its hypothesis
  `hcomp : ∀ m, F_h (F_g m) = F_c m`.

**The chart spelling is now uniform, and it is the written-out one.**  A restriction map of the
presheaf is uniform in the morphism of the site, so it spells every chart one way, and the two
laws must do the same or one factor of each differs from the restriction map by a `δ`-step of a
reducible abbreviation inside the implicit module arguments of `ModuleCat.Hom.hom` — which is a
projection, so the step cannot be taken at the consumer.  Every chart of
`.memberDatumRestrict_id_apply'`, `.memberDatumAb_id_apply`, `.memberDatumRestrict_comp_apply`,
`.memberDatumAb_comp_apply`, `.memberDatumObj` and `.memberDatumAb_comp_apply'` is therefore
written out as `smallEtalePostcomp (memberChartMap …) … |>.obj (chartSpaceIdChart …)`, which is
the `δ`-expansion of `.memberTransitionChart` at the same arguments: the statements say exactly
what they said before.

The **abbreviation** throughout is out of reach, which is why the written-out
spelling is the uniform one.  The charts of the restriction along the second morphism of the site
are those of the variable `e` of `.transitionEtaleForm_base_comp`, and that lemma's conclusion
reads `e` through `ModuleCat.Hom.hom ((D.F j).val.map e.op)`, whose implicit ring, `Ring`
instance and two modules were fixed, when *that* lemma was elaborated, in the written-out spelling
of its own variables `wvj`, `hwvj`, `U`, `vj`, `hvj`, `U₁`.  Spelling `e` of
`.memberTransitionEtaleForm_comp` with the abbreviation therefore leaves its conclusion two chart
crossings away from what `.transitionEtaleForm_base_comp` delivers, and those two may not be paid:
in the `refine` they exhaust the recursion depth, and split off into a step of their own — the
`refine` into a `have` and the conversion into an `exact` — the `exact` alone exhausts it too.  No
generalisation of `.transitionEtaleForm_base_comp` reaches them either: both charts of `e` are
pinned, up to defeq, by the types of their neighbours in the conclusion — the source by the
domain of the outer transition's reading, the target by the type of the inner transition's value —
so neither may be carried as a variable.

In the written-out direction nothing has to be paid at all: the charts of the restrictions along
the first morphism and along the composite are those of the variables `eg` and `eba` of
`.memberTransitionEtaleForm_comp`, and those enter `.transitionEtaleForm_base_comp` only through
its variables `s` and `t`, in argument position, where the consumer's own spelling is carried
through to the conclusion unchanged.  `.memberDatumRestrict_comp_apply` and
`.memberDatumRestrict_id_apply'` rest on `.val_map_comp_hom_apply` and
`.val_map_eq_id_hom_apply`, which carry the restriction as a variable, so their spelling is free;
and the second chart of each restriction is the variable `W`, which the consumer chooses.

**What `map_comp` still needs.**  With the spelling uniform, `hcomp` is no longer a question of
charts: its goal is `Fh.toZeroHom.toFun (Fg.toZeroHom.toFun m) = Fc.toZeroHom.toFun m` with the
three maps the structure literals of the `map` field, and the two sides of
`.memberDatumAb_comp_apply'` are those two readings with the projections and the betas already
performed.  The remaining obstruction is the one recorded for `map_id` above — the unifier, facing
a projection of a literal against a concrete body, unfolds the *body* — and here it has no cure of
the `map_id` kind yet.  All of these exhaust the recursion depth: `exact` of the law
against `hcomp` pointwise with the literals concrete; the same chained through a `rfl`-lemma that
reads one, or both, of the two projections off a literal with the function carried as a variable;
`AddCommGrpCat.hom_ext (AddMonoidHom.ext …)` chained through
`.addCommGrpCat_hom_comp_ofHom_mk_apply` with its three objects pinned; and the same through a
composite-on-variables lemma of the `.comp_hom_apply_eq_of_sect` kind, where the value of the
first factor comes back assigned to an *unfolded* term — the counit of the comparison of Stacks
03LU — rather than to the body of the literal.  Any shape that gets there has to keep the
unifier's attention on the literal; `obj`, `map`, `map_zero'`, `map_add'` and `map_id` all
elaborate, in under five seconds, with either choice of `obj` (`AddCommGrpCat.of` of the sections
written out, or of `.memberDatumObj`), and `map_comp` is the only field left.  A tactic block in
*any* field also breaks `map_id`, so the whole instance has to stay in term mode: with
`map_comp := by refine …`, `map_id` stops being able to assign the function of
`.addCommGrpCat_hom_ofHom_mk_apply` from the goal, and pinning that lemma's two objects does not
restore it.

**And the elaborator is not the only budget: the kernel is a second one.**  Folding the
restriction map into a named `def … : memberDatumObj … p →+ memberDatumObj … q` makes every
one of the four fields match first order -- the laws become statements about an opaque head -- but
the two additivity proofs then leave the structure instance.  `Lean.Meta.abstractNestedProofs`
rewrites the body of a `def`, replacing each nested proof whose arguments are not all local
variables by an auxiliary theorem abstracted over the whole local context, and the **kernel**
type-checks those on their own, and times out deterministically.  `.AddMonoidHomLaws` is
the cure.  The two obligations are discharged in a theorem, whose proof the kernel sees as one
term and accepts; the restriction map is `.AddMonoidHomLaws.toAddMonoidHom` of it; and the
bundling keeps the `0` and the `+` of the sections out of the statement, which matters for a
second reason -- named directly, the two laws would have to spell them at the sections of the
datum, where the instances instance search returns are not the ones the `AddMonoidHom` structure
derives from its `AddZeroClass` argument, and identifying the two paths unfolds the module
structure of the sections through a chart and exhausts the recursion depth.  The two
objects of `.AddMonoidHomLaws` carry `AddCommGroup` rather than `AddZeroClass` for the same
reason, one level up: with the weaker assumption the `AddMonoidHom` it builds and the one
`AddCommGrpCat.ofHom` expects differ in their `AddZeroClass`, and reconciling those is a
deterministic timeout of the kernel.

Five further facts about the five chart proofs inside the restriction map.  Those five -- two
`.isEtale_memberChartMap`, `.memberChartPair_fst` and
`.memberChartPair_snd'` -- are proofs whose arguments are not local variables, so inside a `def`
they too become auxiliary constants; the kernel accepts them, but a consumer that has to identify
the unfolded definition with a freshly written copy of the same text then faces proof irrelevance
under a chart crossing, and that exhausts the recursion depth.  Hoisting all five into
declarations of their own at `p`, `q` and `g` -- the one shape `abstractNestedProofs` leaves
alone -- does not help: the copies then differ at those five positions directly.  Naming the
function as a `def` and routing every consumer through that constant does not help either, for
the same reason.  **The function must therefore be written out inside the theorem that carries its
laws, and nowhere else**, and that is where `.memberDatumAbMap_laws` writes it.

**Where the assembly stands, and what the one remaining obstruction is.**  With the restriction
map `.AddMonoidHomLaws.toAddMonoidHom (.memberDatumAbMap_laws …)`, the `obj` and `map` fields of
the `CategoryTheory.Functor` structure instance elaborate, the kernel accepts them, and
**`map_comp` closes** -- `.addCommGrpCat_ofHom_eq_comp` with its three arguments read off the goal
reduces it to exactly `.memberDatumAb_comp_apply'`, with nothing to identify, because the function
in the goal and the function in that law's statement are the same term instantiated at the same
two variables `g` and `h`.

`map_id` does not.  Its goal instantiates the same function at `𝟙 p`, and **an instantiation at
`𝟙 p` cannot be identified with a statement written out at `𝟙 p`**: the implicit arguments of the
former were solved with the morphism of the site opaque, those of the latter with `(𝟙 p).unop`
reducible, and the identification exhausts the recursion depth.  All of these fail: the law
reached directly from `.addCommGrpCat_ofHom_eq_id`; reached in two steps through
`.AddMonoidHomLaws.toAddMonoidHom_apply`; `.memberDatumAb_id_apply` in place of
`.memberDatumAb_id_apply'`; the same four in a declaration of their own rather than in the field,
which rules out the depth of the structure instance as the cause; and the same with the identity
carried as a variable `g` identified by `hg : g = 𝟙 p`, where the obstruction simply moves inside
that declaration, to the `subst`.  Rebuilding the identity law at the instantiated spelling from
`.val_map_eq_id_hom_apply` and `.transitionEtaleForm_id_hom_apply` with their arguments read off
the goal does not reach it either: `transitionEtaleForm_id_hom_apply` has nothing to read its
arguments from until the middle term of the chain is fixed, and `rw` of
`.val_map_eq_id_hom_apply` fails on its motive -- `Opposite.op (chartSpaceIdChart …)` is not
type-correct at `implicit` transparency.  What is wanted is an identity law whose statement is an
**instantiation** of one written with the morphism of the site opaque, the way
`.memberDatumAb_comp_apply'` is; `.memberTransitionEtaleForm_comp` is that for the composition
law, and the identity law has no counterpart yet.

Carrying the morphism of charts of `X` as a variable `k` identified by `hk : k = memberHom …
(𝟙 p).unop` does **not** supply one: with the whole `g`-dependence of the function in
that one variable, the `subst` still leaves a goal that cannot be identified with
`.memberDatumAb_id_apply'`, whose statement is that text verbatim.  So the two elaborations of
one and the same text differ, and they differ in an implicit argument that the concrete identity
makes reducible: the restriction factor is read through `ModuleCat.Hom.hom`, whose implicit ring,
`Ring` instance and `restrictScalars` wrapper come from the ring map the morphism of the site
induces, and at an identity that ring map reduces.

**The identity law now exists in that instantiation form, and the obstruction has moved.**
`.memberDatumAbMap_laws_id_apply` is the identity law stated of the additive map
`.AddMonoidHomLaws.toAddMonoidHom` builds out of `.memberDatumAbMap_laws` **at** `q := p`,
`g := 𝟙 p` -- the function a `map_id` goal of the structure instance carries, not a copy of its
text -- and it is proved.  Four facts decide its shape and the shape of any consumer.

* Pinning implicit arguments does not reach the goal.  Neither pinning the two objects and the
  `AddCommGroup` instances of `.AddMonoidHomLaws.toAddMonoidHom`, nor ascribing the whole
  equation of morphisms at `AddCommGrpCat.of ↥(.memberDatumObj …) ⟶ AddCommGrpCat.of
  ↥(.memberDatumObj …)`, makes a written-out copy match the instantiation; both ascribed
  statements elaborate and neither closes the field.
* **A closed term never closes a field of the instance.**  `map_id` is
  `Prefunctor`-free -- `CategoryTheory.Functor` is a flat structure here -- so its goal is a
  projection of a structure literal, and facing a *concrete* `AddCommGrpCat.ofHom Fc` the unifier
  unfolds `AddCommGrpCat.ofHom` instead of reducing the literal.  With `Fc` a **metavariable** it
  must reduce the literal, and then `Fc` is assigned cleanly.  So the field must read its additive
  map off the goal, and a lemma whose conclusion is the whole equation -- however stated -- cannot
  be used.
* The remaining goal `∀ m, Fc.toZeroHom.toFun m = m` is discharged by reading **every** argument
  off it, which is what `.memberDatumAbMap_laws_id_apply` does and what `.val_app_apply_of_eq_id`
  exists for.  In the field, that reading has to be *ordered*: a term-mode application elaborates
  the identity law of the transition while the transition is still a metavariable, and then faces
  the projection unification under `.val`.  Deferring that one argument -- by an auto-bound
  parameter, or by passing it through a function type -- makes `map_id` elaborate.
* **`map_comp` then does not.**  With the restriction maps read off the `map_comp` goal
  and the two readings of `g` and `h` unfolded by `.AddMonoidHomLaws.toAddMonoidHom_apply` first:
  the two *variable* readings match `.memberDatumAb_comp_apply'` on the nose, and the third does
  not.  The third is the instantiation at `g ≫ h`, a **concrete** morphism of the site, and it
  fails for exactly the reason the identity law failed at `𝟙 p`.  So the composition law needs the
  same treatment as the identity law: a statement of it whose third reading is
  `.memberDatumAbMap_laws` at a composite carried as a **variable**, which
  `.memberTransitionEtaleForm_comp` already supports through its variable `ba`.  Until then the
  `map_comp` field closes only while `map_id` fails, which aborts the structure instance before
  `map_comp` is reached; that is why it was recorded as closing.

**The composition law now exists in that instantiation form, and both laws are proved as
equations of morphisms.**  `.memberDatumAbMap_laws_comp_apply` is the composition law stated of
the three additive maps `.AddMonoidHomLaws.toAddMonoidHom` builds out of
`.memberDatumAbMap_laws` **at** `g`, `h` and `g ≫ h`, and `.memberDatumAbMapComp_eq` and
`.memberDatumAbMapId_eq` are the two resulting equations of morphisms of `AddCommGrpCat` --
exactly the `map_comp` and `map_id` obligations of the presheaf.  Four facts decide the
route and are recorded at the declarations:

* the written-out law has to be elaborated with the composite carried as a **variable** `gh` and
  instantiated at `g ≫ h` afterwards (`.memberDatumAb_comp_apply_of_eq'`), for the reason the
  identity law records at `𝟙 p`.  Proved instead by `subst` of that variable and the existing
  `.memberDatumAb_comp_apply`, it exhausts the recursion depth: after the substitution both sides
  are concrete and the comparison falls to the `.val` projection.
* at an opaque `gh` the connecting restriction of charts **cannot be written in the statement at
  all** -- its source is the chart the composite induces -- so it is carried as a variable `cc`
  with an `HEq`, which is the shape `.memberTransitionEtaleForm_comp` already asks for.
* the bundling of the two nested readings has to be unfolded **one level at a time**, with the
  inner reading carried as a variable (`.memberDatumAbMap_laws_apply_of_eq`).  Unfolded both at
  once, by a lemma that is `rfl` on variables, the elaborator accepts the proof and the **kernel**
  reports a deterministic timeout on it -- one level of that nesting the kernel checks, two it
  does not.
* and the chain has to run **out to the written-out readings and back**, so that both middle
  terms of its two `Eq.trans`s are the written-out law.  Run the other way round, with the
  bundled readings as the middle terms, the elaborator accepts the proof and the kernel again
  reports a deterministic timeout.  Reading the law directly against the bundled goal, with no
  unfolding at all, exhausts the recursion depth in the elaborator instead.

**What the presheaf still needs is the structure instance itself, and the obstruction there is
the recursion depth of a `CategoryTheory.Functor` structure instance with two law fields.**
Whichever of `map_id` and `map_comp` is elaborated **second** reports `maximum
recursion depth`, and the first one closes.  This is independent of their shape and of their
size -- it fails with each law read off its goal (`.addCommGrpCat_ofHom_eq_id` and
`.addCommGrpCat_ofHom_eq_comp` with `_` for the additive maps), with each supplied as the closed
term `.memberDatumAbMapId_eq`/`.memberDatumAbMapComp_eq`, with the two fields in either order,
with the additive maps of `map_comp` pinned, with `obj` spelled through `.memberDatumObj` and
with it spelled through the carrier, and with the anonymous constructor in place of the `where`
block.  In every case exactly one error is reported, always at the second of the two law fields.
`map_id` additionally confirms that a **closed** term never closes it:
`.memberDatumAbMapId_eq` fails there even when it is the first law field, while the same law with
its additive map left as a metavariable closes.

So the presheaf of abelian groups does not yet exist as an object, and neither do `map_smul` and
`CategoryTheory.PresheafOfModules.ofPresheaf`; what is missing is no longer a law but a way of
presenting the two proved laws to the structure instance within the recursion depth.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.  In
particular the effectivity clause of Stacks 04W6 is not asserted.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)


/-- Two restrictions of a module along morphisms of charts, read on a section, are the
restriction along the composite.  Stated on variables, with the charts spelled as objects of the
small étale **ringed** site, which is how the presheaf of modules of an `𝒪`-module indexes its
sections. -/
theorem val_map_comp_hom_apply {C₀ : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS C₀.1 C₀.2)
    {Z₁ Z₂ Z₃ : (smallEtaleRingedSite B S hS C₀.1 C₀.2).Cᵒᵖ} (x : Z₁ ⟶ Z₂) (y : Z₂ ⟶ Z₃)
    (m : M.val.obj Z₁) :
    ModuleCat.Hom.hom (M.val.map y) (ModuleCat.Hom.hom (M.val.map x) m) =
      ModuleCat.Hom.hom (M.val.map (x ≫ y)) m := by
  rw [M.val.map_comp]
  rfl


/-! ### The four coercions a presheaf of abelian groups is read through -/

/-- **Zero, through the `ModuleCat.Hom.hom` coercion.**  Stated on variables with both modules
opaque: it is the first factor of a restriction map of the presheaf of abelian groups below, and
`simp`, `simp only [map_zero]` and `rw [map_zero]` all fail on that factor *in situ* — see the
implementation notes. -/
theorem moduleCat_hom_apply_zero {R₀ : Type u} [Ring R₀] {M N : ModuleCat.{u} R₀} (A : M ⟶ N) :
    ModuleCat.Hom.hom A 0 = 0 := map_zero _

/-- **Addition, through the `ModuleCat.Hom.hom` coercion.**  Stated on variables, like
`.moduleCat_hom_apply_zero`. -/
theorem moduleCat_hom_apply_add {R₀ : Type u} [Ring R₀] {M N : ModuleCat.{u} R₀} (A : M ⟶ N)
    (x y : M) : ModuleCat.Hom.hom A (x + y) = ModuleCat.Hom.hom A x + ModuleCat.Hom.hom A y :=
  map_add _ x y

/-- **Zero, through the direct-application coercion, with the argument carried as a variable.**
The second factor of a restriction map of the presheaf below is a morphism of sheaves of modules
read over a chart, applied directly — which elaborates through `ConcreteCategory.hom`, not
`ModuleCat.Hom.hom`, so `.moduleCat_hom_apply_zero` cannot cover it.  Carrying the argument as a
variable `z` is what makes this usable: at a consumer the argument is the value of the *first*
factor, whose type is the sections of a module over a composite chart while this factor expects
the sections of an étale restriction, and those two spellings may not meet in a unification — but
they may meet in the position of a function argument, which is where `z` puts the crossing. -/
theorem val_app_apply_zero {R₁ : Type u} [Ring R₁] {P Q : ModuleCat.{u} R₁} (T : P ⟶ Q)
    (z : P) (hz : z = 0) : T z = 0 := by
  subst hz
  exact map_zero _

/-- **Addition, through the direct-application coercion, with the arguments carried as
variables.**  This is `.val_app_apply_zero` for a sum, and for the same reason. -/
theorem val_app_apply_add {R₁ : Type u} [Ring R₁] {P Q : ModuleCat.{u} R₁} (T : P ⟶ Q)
    (z x y : P) (hz : z = x + y) : T z = T x + T y := by
  subst hz
  exact map_add _ x y

/-- **The `AddCommGrpCat` coercion of an additive map written as a structure literal.**  A direct
`CategoryTheory.Functor` structure instance into `AddCommGrpCat` leaves its laws as equations
between `AddCommGrpCat.Hom.hom (AddCommGrpCat.ofHom ⟨⟨_, _⟩, _⟩)` applied to a section, and
neither `rw` nor `exact` of the section-level law gets through that — see the implementation
notes.  Chaining with this equation does. -/
theorem addCommGrpCat_hom_ofHom_mk_apply {M N : AddCommGrpCat.{u}} (F : M → N)
    (h0 : F 0 = 0) (ha : ∀ x y, F (x + y) = F x + F y) (m : M) :
    AddCommGrpCat.Hom.hom (AddCommGrpCat.ofHom (⟨⟨F, h0⟩, ha⟩ : M →+ N)) m = F m := rfl

/-- **The `AddCommGrpCat` coercion of an identity**, read on an element: the other half of
`map_id` of such a structure instance. -/
theorem addCommGrpCat_hom_id_apply {M : AddCommGrpCat.{u}} (m : M) :
    AddCommGrpCat.Hom.hom (𝟙 M) m = m := rfl

/-- **The `AddCommGrpCat` coercion of a composite of two additive maps written as structure
literals**, read on an element: the other half of `map_comp` of such a structure instance. -/
theorem addCommGrpCat_hom_comp_ofHom_mk_apply {M N P : AddCommGrpCat.{u}} (Fg : M → N)
    (h0g : Fg 0 = 0) (hag : ∀ x y, Fg (x + y) = Fg x + Fg y) (Fh : N → P) (h0h : Fh 0 = 0)
    (hah : ∀ x y, Fh (x + y) = Fh x + Fh y) (m : M) :
    AddCommGrpCat.Hom.hom (AddCommGrpCat.ofHom (⟨⟨Fg, h0g⟩, hag⟩ : M →+ N) ≫
        AddCommGrpCat.ofHom (⟨⟨Fh, h0h⟩, hah⟩ : N →+ P)) m = Fh (Fg m) := rfl

/-- **`map_id` of an `AddCommGrpCat`-valued `CategoryTheory.Functor` structure instance, out of
the identity law of its restriction map on sections.**  The companion of
`.addCommGrpCat_ofHom_eq_comp`, stated the same way and for the same reasons: as an equation of
**morphisms**, with the additive map carried **bundled**, and with the object carried as a type
with an `AddCommGroup` structure rather than as an object of `AddCommGrpCat`.

The last of those is what the identity law needs beyond what `map_comp` needs.  Reached instead
through `AddCommGrpCat.hom_ext` and `AddMonoidHom.ext`, the section a consumer reasons about is an
element of the carrier of `AddCommGrpCat.of` of the sections, and feeding it to a law stated at the
sections themselves has to strip that `AddCommGrpCat.of` **and** cross a chart in one step, which
exhausts the recursion depth.  Here the quantifier of `hid` is over `M` itself, so the
consumer's section arrives at the type its law already speaks of. -/
theorem addCommGrpCat_ofHom_eq_id {M : Type u} [AddCommGroup M] (Fc : M →+ M)
    (hid : ∀ m, Fc.toZeroHom.toFun m = m) :
    AddCommGrpCat.ofHom Fc = 𝟙 (AddCommGrpCat.of M) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext hid)

/-- **The two laws of an additive map, bundled as a proposition about its underlying function.**

This exists to keep the zero and the addition of the two modules **out of every statement a
consumer writes**, and that is the whole of its content.  The additivity of a restriction map of
a presheaf of abelian groups on the site of the charts of the members may not be left as a field
of a `def`: the body of a `def` has its nested proofs lifted into auxiliary theorems that the
**kernel** type-checks on their own, and the two additivity obligations are a
deterministic timeout of the kernel, twice over.  Nor may they be named directly, because the
statements would have to spell `0` and `x + y` at the sections of the datum, where the instances
instance search returns are not the ones the `AddMonoidHom` structure asks for -- those come from
its own `AddZeroClass` argument -- and reconciling the two paths has to unfold the module
structure of the sections through a chart, which exhausts the recursion depth.  Bundled
like this, the `0` and the `+` occur only inside this declaration, where both sides are variables
and the reconciliation is free.

The two objects carry `AddCommGroup` and not merely `AddZeroClass` so that the `AddZeroClass` of
the resulting `AddMonoidHom` is the one `AddCommGrpCat.ofHom` derives from an `AddCommGroup`
rather than the one instance search returns: with the weaker assumption those are two different
terms, and identifying them unfolds the module structure of the sections of a datum through a
chart -- a deterministic timeout of the kernel. -/
structure AddMonoidHomLaws {M N : Type u} [AddCommGroup M] [AddCommGroup N] (F : M → N) : Prop
    where
  /-- The function carries zero to zero. -/
  map_zero : F 0 = 0
  /-- The function is additive. -/
  map_add : ∀ x y, F (x + y) = F x + F y

/-- **The additive map underlying a function with the two laws.**  The one place where the laws
are read off `.AddMonoidHomLaws`, and everything in sight is a variable. -/
def AddMonoidHomLaws.toAddMonoidHom {M N : Type u} [AddCommGroup M] [AddCommGroup N] {F : M → N}
    (h : AddMonoidHomLaws F) : M →+ N := ⟨⟨F, h.map_zero⟩, h.map_add⟩

/-- **The additive map of `.AddMonoidHomLaws.toAddMonoidHom` is the function it was built from**,
read on an element through `AddMonoidHom.toZeroHom` -- the projection
`.addCommGrpCat_ofHom_eq_id` and `.addCommGrpCat_ofHom_eq_comp` leave in their hypotheses.

A step of its own, with everything a variable, so that a functor law can be identified with its
law on sections in **two** moves: this one, which unfolds the bundling and nothing else, and then
the law.  Reached in one move the identification has to take a projection of a structure literal
and a chart crossing together, and that exhausts the recursion depth. -/
theorem AddMonoidHomLaws.toAddMonoidHom_apply {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    {F : M → N} (h : AddMonoidHomLaws F) (m : M) : h.toAddMonoidHom.toZeroHom.toFun m = F m := rfl
/-- **`map_comp` of a direct `AddCommGrpCat`-valued `CategoryTheory.Functor` structure instance,
out of the composition law of its restriction map on sections.**  Stated as an equation of
**morphisms** of `AddCommGrpCat`, with the three additive maps carried **bundled**, and both
choices are the content of it.

Four other shapes do not get there.  Chained at the element level with
`_` for its two functions, `.addCommGrpCat_hom_comp_ofHom_mk_apply` leaves `?Fh (?Fg m)` to be
matched against the composition law, a higher-order unification left undetermined in both
directions of the chain.  With the value of the composite carried as a variable instead, the
middle object of the composite occurs only as `AddCommGrpCat.of ↥?N`, and inverting that
projection is the one thing the unifier cannot do.  Splitting the three readings into hypotheses
on variables makes each of them pay the crossing between the sections of the presheaf and the
sections of an étale restriction, and together they exhaust the recursion depth.  And with the
three maps carried as `(F, map_zero', map_add')` triples rather than bundled, matching the
conclusion against the goal assigns the two **proof fields** of each triple separately, which
re-elaborates the additivity of the consumer's restriction map — crossing and all — six times
over, and that exhausts the recursion depth as well.

Bundled and at the level of morphisms, there is no ambient type to cross, each `AddCommGrpCat`
object is read off the goal first order, each additive map is one assignment, and the single
crossing that remains belongs to `hcomp`, where the consumer has already performed it. -/
theorem addCommGrpCat_ofHom_eq_comp {M N P : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (Fg : M →+ N) (Fh : N →+ P) (Fc : M →+ P)
    (hcomp : ∀ m, Fh.toZeroHom.toFun (Fg.toZeroHom.toFun m) = Fc.toZeroHom.toFun m) :
    AddCommGrpCat.ofHom Fc = AddCommGrpCat.ofHom Fg ≫ AddCommGrpCat.ofHom Fh :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => (hcomp m).symm)

end AlgebraicGeometry.Space.QuasiCoherentDescent

end

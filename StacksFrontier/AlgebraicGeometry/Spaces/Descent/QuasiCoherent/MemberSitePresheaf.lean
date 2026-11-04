module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberChartTestSpace

/-!
# The presheaf of modules on the site of the charts of the members of a descent datum

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X`, and let `D` be a descent datum for quasi-coherent modules relative to that
family.  The charts of the members of the family form a site,
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite`, whose objects are the pairs `(i, V)` of
a member and a chart of it and whose morphisms are the morphisms of the induced charts of `X`.

This file supplies the **data of a presheaf of modules on that site** out of the transition of
`D`: the sections over `(i, V)` are the sections of `D.F i` over `V`, and the restriction along a
morphism `k : (j, V') ⟶ (i, V)` is restriction inside `D.F i` to the chart of `Y i` that `k`
induces, followed by the transition from `i` to `j` read on the test space
`AlgebraicGeometry.Space.chartSpace` of `V'`.  Both factors are morphisms of modules, so the
restriction map is semilinear over the restriction map of the structure sheaf read on the charts
of the members by its type, and semilinearity is not a separate obligation.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionChart` and
  `.memberTransitionHom` are the chart of the target member that a morphism of the site induces
  and the morphism of charts from it onto the chart of that member.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberSelfLeg` and `.memberTargetChart` are the
  structure morphism of the source chart and the chart it induces on its own member, spelled as
  the ones attached to an identity morphism of the site.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionApp` is the transition attached to
  a morphism of the site, as a morphism of the modules of sections of the two component modules
  over the two charts.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumObj` and `.memberDatumMap` are the
  object and the restriction map of the presheaf, the latter **semilinear over the restriction of
  the structure sheaf of `X` read on the charts of the members**.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleConjugate_val_app_etaleSect` and
  `.etaleConjugate_val_app_apply`: **a morphism of the étale restrictions of two modules along
  two different étale morphisms, conjugated from a morphism of the inverse images, read on a
  section.**  Stated on variables.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_val_app_apply`: **the bundled
  reading `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm` of the transition,
  read on a section, is the written-out reading** of
  `StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartTransition.lean`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionHom_hom_left` and
  `.memberTransitionHom_id`: the morphism of charts a morphism of the site induces has that
  morphism as its underlying morphism of the big fppf site, and is the identity at an identity.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionForm_id`: **the transition
  attached to an identity morphism of the site is the identity**, as an equation of morphisms of
  the étale restrictions.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_id_apply`,
  `.transitionEtaleForm_id_app` and `.transitionEtaleForm_id_app'`: **the bundled reading of the
  transition from a member to itself is the identity**, on a section and as an equation of
  morphisms of the modules of sections over a chart, the last with those sections spelled as the
  sections of the component module over the induced chart.  The first is the bridge composed with
  `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_id`; both are stated on variables.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.comp_restrictScalars_eq_restrictScalarsId'`:
  **`map_id` of a presheaf of modules whose restriction map is a semilinear composite, reduced to
  a statement about sections.**  Stated on variables.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartPair_snd'` and
  `.chartToSpace_eq_memberChartMap`: the second compatibility of the test space **retyped onto
  the uniform spelling of the self leg**, which is what makes the identity law usable at all.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.val_map_eq_id_hom_apply` and
  `.memberTransitionHom_op_id`: a restriction along a morphism of charts equal to an identity
  acts as the identity on a section, and the morphism of charts attached to an identity morphism
  of the site is such a morphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumFactors_id_apply`: **the two halves of
  the identity law of the presheaf, joined** — the transition of the restriction of a section
  along an identity morphism of the site is that section, with the restriction factor read
  exactly as a field of a `PresheafOfModules` over
  `AlgebraicGeometry.Space.QuasiCoherentDescent.memberRing` reads it.  Its restriction half is
  `.memberDatumRestrict_id_hom_apply`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.apply_congr`, `.comp_hom_apply`,
  `.restrictScalars_map_hom_apply`, `.restrictScalars_map_id_hom_apply`,
  `.comp_hom_apply_eq_of_sect`, `.comp_restrictScalars_map_hom_apply` and
  `.comp_eq_restrictScalarsId'_of_sect`: the semilinear calculus of a restriction map that is a
  composite, every one of them stated on variables.  `.apply_congr` is `congrArg` with the
  equation **before** the function, and that order is what the join needs.
  `.comp_hom_apply_eq_of_sect` splits a composite with **all four modules read off the goal**,
  which is what `.comp_restrictScalars_map_hom_apply` cannot do.

## Implementation notes

The restriction map is **the composite of a restriction inside `D.F i` with the bundled reading
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm` of the transition**, both
morphisms of modules.  That the composite's type is accepted rests on three identifications which
the elaborator performs in the position of a type: the structure ring of a chart `V` of a member
`Y i` is the structure ring of the induced chart of `X` (the reason for the reducible
abbreviations of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/FullnessViaSigmaSite.lean`); the
sections of an étale restriction over a chart are the sections of the module over the composite
chart; and the chart of `Y i` the morphism induces is the identity chart of the test space pushed
forward along the first leg.  For the last, `.memberTransitionChart` is a reducible abbreviation.

**The bridge from the bundled reading to the written-out one exists, and `rfl` is what fails.**
The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartBaseChange.lean` record that
`(transitionEtaleForm …).val.app (.op U) s = etaleSect … ((transitionHom …).val.app (.op U)
(etaleSectInv … s))` exhausts the elaborator's recursion depth.  What exhausts it is the proof
`rfl`: the statement elaborates in milliseconds, and `.transitionEtaleForm_val_app_apply` proves
it through `.etaleConjugate_val_app_apply`, which is the same equation with the morphism of the
inverse images and its conjugate as variables and is proved by rewriting the two readings and the
composite — `simp only [etaleSect, etaleSectInv, comp_val_app]` after substituting the conjugate —
rather than by reduction.  Unfolding `transitionEtaleForm` inside that `simp only` instead makes
the *kernel* time out, so the conjugate must stay a variable there too.

**What this costs.**  The bridge is available only on a section of the étale
restriction, spelled `((etaleModulePullback vi hvi).obj (D.F i)).val.obj (.op U)`.  The same
section spelled `(D.F i).val.obj (.op ((smallEtalePostcomp vi hvi).obj U))` — which is what a
presheaf on the charts of the members has — is the same type definitionally, and the two spellings
may meet freely in the position of a type (`.memberDatumObj`), of an ordinary function argument
(`etaleSectInv … s`) and in the body of a retyping definition.  They may **not** meet in a
*unification*.

**Why the restriction map carries the reading written out.**  A *named* reading of the
transition — a definition whose body is `(transitionEtaleForm …).val.app (.op U)`, with or
without an ascribed type — can never be related to its own body: the `rfl` equation between the
two exhausts the heartbeat budget at `whnf`, and although `simp only [theDefinition]` does unfold
such a reading inside a goal, the goal it leaves, which *prints identically* to the written-out
identity law, cannot then be closed by `exact` of that law (recursion depth).  So no named
reading may appear in a statement one intends to prove, and `.memberTransitionApp` — which is
such a reading — is not what `.memberDatumMap` is built from.

**Why the legs are spelled uniformly.**  The identity law has to be used at an
identity morphism of the site, where the *source* leg is `memberChartMap V V k` for the `k` the
consumer meets and the *self* leg is the leg of an identity morphism.  The two must be the **same
term**: with the self leg spelled by the reducible abbreviation `.memberSelfLeg`, which differs
from `memberChartMap V V (𝟙 …)` by one delta step at reducible transparency, `exact` of the
identity law exhausts the recursion depth.  That is why the self leg below is written
`memberChartMap V' V' (memberHom (𝟙 q).unop)` — the identity morphism of the site in the spelling
a consumer of `.memberDatumMap` has — and why `.memberChartPair_snd'` exists: the *type* of the
second compatibility is an argument of the transition, and with the type of
`.memberChartPair_snd`, which says `chartToSpace`, `rw [.transitionEtaleForm_id_app]` does not
even find its pattern, while with `.memberChartPair_snd'` it fires.

**Where `map_id` stands.**  The two halves are **joined**:
`.memberDatumFactors_id_apply` says that the transition factor applied to the restriction
factor's value leaves a section alone, with the restriction factor read through the restriction
of scalars along the structure sheaf of the charts of the members — the spelling a field of a
`PresheafOfModules` over `.memberRing` imposes, and the one in which
`.comp_restrictScalars_eq_restrictScalarsId'` asks for its hypothesis.

Two things buy that join.  The restriction half is retyped onto that spelling by
`.memberDatumRestrict_id_hom_apply`, whose coercion carries its two modules **explicitly**: the
crossing between the structure sheaf of the member and the structure sheaf of the charts of the
members then happens once, between a statement and its proof, which is the one position where it
is affordable.  And the two halves are composed by `.apply_congr` rather than by `congrArg`,
because `congrArg` elaborates its function first and so pins the type of the section the
transition factor is applied to, while `.apply_congr` takes the equation first and leaves that
section at the type the restriction half gives it — a function-argument position.

**What remains, and where it fails.**  Only the reduction of `map_id` to that join is missing,
and every known route to it dies on the *middle module of the composite*.
`.memberDatumMap` is `A ≫ (ModuleCat.restrictScalars … ).map B₀`, and the middle module the
elaborator records for that `≫` is `A`'s own target — the restriction of scalars along the
structure sheaf of the **member** — while `.comp_restrictScalars_eq_restrictScalarsId'` builds
its composite with the restriction of scalars along the structure sheaf of the **charts of the
members** in that position.  The two print identically, and:

* `.comp_restrictScalars_eq_restrictScalarsId'` applied to the join, in term mode, inside
  `exact`, and through a `have`, times out at `whnf` or at `isDefEq`;
* `simp only [memberDatumMap]` followed by `.comp_hom_apply` and
  `.restrictScalars_map_hom_apply` does split the composite, and the goal it leaves prints
  character-for-character like the join, but `exact` of the join exhausts the recursion depth;
* so does `.comp_restrictScalars_map_hom_apply`, which performs both splittings and the join
  inside one lemma on variables with all four modules read off its hypotheses;
* `rw`, `simp only` and `conv_lhs => rw` with the restriction half do not find their pattern at
  all, and `.apply_congr` with its equation left a hole times out at `whnf`.

Three reshapings of `.memberDatumMap`'s **body** do not help against this: pinning the middle module by `show … from` (which leaves a `let` in the term, costs
minutes in this file and makes the kernel time out downstream); pinning it with
`@CategoryStruct.comp` and its three objects explicit (cheap, but the reduction still times
out); and spelling the second factor's restriction of scalars through the member's own structure
sheaf.  `.memberDatumObj` is kept a **reducible abbreviation**, which removes one delta step from
every such unification and costs nothing.

`.comp_eq_restrictScalarsId'_of_sect` reduces `map_id` to a statement about sections with the
restriction map carried as a variable, so instantiating it at `.memberDatumMap … (𝟙 p)` is free
and the single obligation is `ModuleCat.Hom.hom (memberDatumMap … (𝟙 p)) m = m`, which elaborates
in milliseconds.  **The elaborator proves that obligation; the kernel is what refuses it.**  Both
halves of the wall were isolated.

*The obligation is provable, and accepted by the elaborator.*  The transition factor collapses to
an identity under `.transitionEtaleForm_id_app`, and once it has, the composite splits:

```
rw [memberDatumMap, transitionEtaleForm_id_app]
exact comp_hom_apply_eq_of_sect _ _ m m (memberDatumRestrict_id_apply …) m rfl
```

elaborates with no errors and no warnings — the split reads all four modules off the goal, the
restriction half closes the first obligation on the nose in its own spelling, and the second is
`rfl` because the factor is now an identity.  `simp only` in place of `rw`, and
`.memberDatumRestrict_id_hom_apply` in place of `.memberDatumRestrict_id_apply`, elaborate too.
**Every one of them makes the kernel time out.**

*The kernel cost is the rewrite of the transition factor inside the composite, and nothing else.*
`rw [memberDatumMap]` with the goal left open is kernel-clean; `rw [memberDatumMap,
transitionEtaleForm_id_app]` with the goal left open already makes the kernel time out, so the
cost is in the rewrite's own term, not in what closes the goal.  What the motive asks for is the
identification of the module the rewritten factor lives in with the middle module of the
composite, and each of four spellings of the rewritten equation gives a kernel
timeout: the étale restriction (`.transitionEtaleForm_id_app`); the sections over the
induced chart (`.transitionEtaleForm_id_app'`); the same with the equation's type pinned by `@Eq`
to those sections, so that the motive's binder carries that spelling; and collapsing the **whole**
second factor, restriction of scalars and all, in one retyped step whose equation is typed in the
presheaf's own spelling — that last statement does not even elaborate.

*Without the collapse the split itself is out of reach.*
`refine comp_hom_apply_eq_of_sect _ _ m m ?_ m ?_` exhausts the recursion depth, with
`simp only [memberDatumMap]` before it and without.  So does the whole calculation in term mode,
and so does `.comp_restrictScalars_map_hom_apply` and the two-lemma chain that strips the
restriction of scalars from the uncollapsed factor.

*Two further routes are closed.*  `.comp_hom_apply` does **not** fire as a `simp` lemma on the
unfolded body: the module it would have to assign occurs both as the target of the composite and
as the target argument of the coercion, and the body carries two spellings of it there, which
`simp` will not identify.  And the composite cannot be written out at all: a statement containing
`A ≫ (ModuleCat.restrictScalars … ).map B₀` with both factors written explicitly times out at
`whnf`, because that composite typechecks inside `.memberDatumMap` only with the declared type
guiding the unification.  Pinning the composite's target in the obligation's statement — which is
what would let `.comp_hom_apply` fire — times out at `whnf` for the same reason.

**Why the legs are spelled uniformly, at the morphism level.**  The two legs of the test space
attached to a morphism of the site are the arguments on which the types of the transition and of
its bundled reading depend, so two spellings of one leg can never be identified afterwards.  For
`.memberTransitionApp` and `.memberTransitionForm_id` the structure morphism of the source chart
is therefore written `.memberSelfLeg`, that is as the morphism to the target member of an
*identity* morphism of the site, rather than as `AlgebraicGeometry.Space.chartToSpace`: at an
identity morphism the two legs are then one and the same term, and
`.memberTransitionForm_id` is a direct instance of
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_id`, checked in milliseconds.
Read on the sections over the identity chart of the test space the same statement is out of reach:
`memberTransitionApp … (𝟙 …) = 𝟙 …` exhausts the heartbeat budget at `whnf` in every spelling of
its two endpoints tried, although each of
`memberChartMap V V (𝟙 …) = chartToSpace (Yi i) V` and
`memberTransitionChart V V (𝟙 …) = V` is `rfl` in milliseconds.  That is the same wall
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartBaseChange.lean` records for the base change, met at the identity: an
identification of two charts is free, and is unaffordable inside the endpoints of a hom of modules
of sections.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.  In
particular the effectivity clause of Stacks 04W6 is not asserted.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

/-! ### The semilinear calculus of a restriction map, on variables -/

/-- The inverse of the identification of the restriction of scalars along an identity ring map
with the identity functor, read on a section: it leaves the section alone.  Stated on
variables. -/
theorem restrictScalarsId'_inv_app_hom_apply {R₀ : Type u} [Ring R₀] (φ : R₀ →+* R₀)
    (hφ : φ = RingHom.id R₀) (M : ModuleCat.{u} R₀) (m : M) :
    ModuleCat.Hom.hom ((ModuleCat.restrictScalarsId' φ hφ).inv.app M) m = m := rfl

/-- A morphism into the restriction of scalars along an identity ring map which leaves every
section alone is the identification of that restriction of scalars with the identity functor. -/
private theorem eq_restrictScalarsId'_of_sect {R₀ : Type u} [Ring R₀] (φ : R₀ →+* R₀)
    (hφ : φ = RingHom.id R₀) {M : ModuleCat.{u} R₀}
    (C : M ⟶ (ModuleCat.restrictScalars φ).obj M) (h : ∀ m : M, ModuleCat.Hom.hom C m = m) :
    C = (ModuleCat.restrictScalarsId' φ hφ).inv.app M :=
  ModuleCat.hom_ext (LinearMap.ext fun m =>
    (h m).trans (restrictScalarsId'_inv_app_hom_apply φ hφ M m).symm)

/-- **A semilinear map followed by the restriction of scalars of a map which undoes it on
sections is the identification of the restriction of scalars along an identity with the identity
functor.**  This is `map_id` of a presheaf of modules whose restriction map is such a composite,
reduced to a statement about sections.

Both factors, the two modules and the section-level hypothesis are the consumer's, so that no
spelling of a module of sections is ever matched: the composite in the conclusion is the
consumer's own term. -/
theorem comp_restrictScalars_eq_restrictScalarsId' {R₀ : Type u} [Ring R₀] (φ : R₀ →+* R₀)
    (hφ : φ = RingHom.id R₀) {M N : ModuleCat.{u} R₀}
    (A : M ⟶ (ModuleCat.restrictScalars φ).obj N) (B₀ : N ⟶ M)
    (h : ∀ m : M, ModuleCat.Hom.hom B₀ (ModuleCat.Hom.hom A m) = m) :
    A ≫ (ModuleCat.restrictScalars φ).map B₀ =
      (ModuleCat.restrictScalarsId' φ hφ).inv.app M :=
  eq_restrictScalarsId'_of_sect φ hφ _ h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The bridge from the bundled reading to the written-out one -/

/-- **A morphism of the étale restrictions of two modules along two different étale morphisms,
conjugated from a morphism of the inverse images, read on a section.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_val_app` for two different morphisms, with
the two conjugating comparisons of Stacks 03LW written out and the conjugate carried as a variable
identified with the composite by a hypothesis, so that a consumer states the conclusion in its own
spelling of it. -/
theorem etaleConjugate_val_app_etaleSect {T C₁ C₂ : AlgebraicSpaces B S hS} (vi : T ⟶ C₁)
    (vj : T ⟶ C₂) (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (Mi : Modules.{u, u} B S hS C₁.1 C₁.2) (Mj : Modules.{u, u} B S hS C₂.1 C₂.2)
    (β : (modulePullback B S hS vi).obj Mi ⟶ (modulePullback B S hS vj).obj Mj)
    (θ : (etaleModulePullback.{u, u} B S hS vi hvi).obj Mi ⟶
      (etaleModulePullback.{u, u} B S hS vj hvj).obj Mj)
    (hθ : θ = (modulePullbackIsoEtaleModulePullback B S hS vi hvi).inv.app Mi ≫ β ≫
      (modulePullbackIsoEtaleModulePullback B S hS vj hvj).hom.app Mj)
    (U : SmallEtale B S hS T.1)
    (m : ((modulePullback B S hS vi).obj Mi).val.obj (.op U)) :
    θ.val.app (.op U) (etaleSect B S hS vi hvi Mi U m) =
      etaleSect B S hS vj hvj Mj U (β.val.app (.op U) m) := by
  subst hθ
  simp only [etaleSect, comp_val_app,
    natIso_inv_hom_val_app B S hS (modulePullbackIsoEtaleModulePullback B S hS vi hvi)]

/-- **A morphism of the étale restrictions of two modules along two different étale morphisms,
conjugated from a morphism of the inverse images, read on a section of the source restriction.**
This is `.etaleConjugate_val_app_etaleSect` with the section of the source read back through the
comparison of Stacks 03LW, which is the form in which the written-out readings of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartLaws.lean` are stated. -/
theorem etaleConjugate_val_app_apply {T C₁ C₂ : AlgebraicSpaces B S hS} (vi : T ⟶ C₁)
    (vj : T ⟶ C₂) (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (Mi : Modules.{u, u} B S hS C₁.1 C₁.2) (Mj : Modules.{u, u} B S hS C₂.1 C₂.2)
    (β : (modulePullback B S hS vi).obj Mi ⟶ (modulePullback B S hS vj).obj Mj)
    (θ : (etaleModulePullback.{u, u} B S hS vi hvi).obj Mi ⟶
      (etaleModulePullback.{u, u} B S hS vj hvj).obj Mj)
    (hθ : θ = (modulePullbackIsoEtaleModulePullback B S hS vi hvi).inv.app Mi ≫ β ≫
      (modulePullbackIsoEtaleModulePullback B S hS vj hvj).hom.app Mj)
    (U : SmallEtale B S hS T.1)
    (s : ((etaleModulePullback.{u, u} B S hS vi hvi).obj Mi).val.obj (.op U)) :
    θ.val.app (.op U) s =
      etaleSect B S hS vj hvj Mj U
        (β.val.app (.op U) (etaleSectInv B S hS vi hvi Mi U s)) := by
  subst hθ
  simp only [etaleSect, etaleSectInv, comp_val_app]

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-! ### The bridge at the transition -/

/-- **The bundled reading of the transition of a descent datum, read on a section, is the
written-out reading.**  This is `.etaleConjugate_val_app_apply` at the transition, where the
conjugate is `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm` by its
definition. -/
theorem transitionEtaleForm_val_app_apply (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i)
    (vj : T ⟶ Yi j) (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (U : SmallEtale B S hS T.1)
    (s : ((etaleModulePullback.{u, u} B S hS vi hvi).obj (D.F i)).val.obj (.op U)) :
    (transitionEtaleForm B S hS Yi f D i j v vi vj hvi hvj hi hj).val.app (.op U) s =
      etaleSect B S hS vj hvj (D.F j) U
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (.op U)
          (etaleSectInv B S hS vi hvi (D.F i) U s)) :=
  etaleConjugate_val_app_apply B S hS vi vj hvi hvj (D.F i) (D.F j)
    (transitionHom B S hS Yi f D i j v vi vj hi hj)
    (transitionEtaleForm B S hS Yi f D i j v vi vj hvi hvj hi hj) rfl U s

/-! ### The identity law of the bundled reading -/

/-- A restriction map of an `𝒪`-module along a morphism of charts equal to an identity acts as
the identity on a section.  Stated on variables, and with the chart spelled as an object of the
small étale **ringed** site, which is the spelling the presheaf of modules of an `𝒪`-module
indexes its sections by. -/
theorem val_map_eq_id_hom_apply {C₀ : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS C₀.1 C₀.2)
    {Z : (smallEtaleRingedSite B S hS C₀.1 C₀.2).Cᵒᵖ} (c : Z ⟶ Z) (hc : c = 𝟙 Z)
    (m : M.val.obj Z) :
    ModuleCat.Hom.hom (M.val.map c) m = m := by
  subst hc
  simp only [PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
    ModuleCat.restrictScalarsId'App_inv_apply]
  rfl

/-- **The bundled reading of the transition of a descent datum from a member to itself is the
identity on sections.**  This is the identity law of the reading in the form in which the
presheaf of modules on the charts of the members needs it: the bridge
`.transitionEtaleForm_val_app_apply` turns the bundled reading into the written-out one, where
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_id` closes it.

Stated on variables — the test space, the leg, the morphism to the pairwise fibre product, the
two compatibilities and the chart are all opaque — so that a consumer instantiates it in its own
spelling instead of matching one. -/
theorem transitionEtaleForm_id_apply (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i : I) (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i)
    (hw : IsEtale B S hS w.hom)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w)
    (U : SmallEtale B S hS T.1)
    (s : ((etaleModulePullback.{u, u} B S hS w hw).obj (D.F i)).val.obj (.op U)) :
    (transitionEtaleForm B S hS Yi f D i i v w w hw hw hi hj).val.app (.op U) s = s :=
  (transitionEtaleForm_val_app_apply B S hS Yi f D i i v w w hw hw hi hj U s).trans
    (transitionSect_id B S hS Yi f D i v w hw hi hj U s)

/-- `.transitionEtaleForm_id_apply` with the section spelled as a section of the component module
over the induced chart, and the reading applied through `ModuleCat.Hom.hom`: that is the shape an
extensionality goal for a morphism of modules of sections has, and the shape in which the identity
law of a presheaf of modules on the charts of the members uses it. -/
theorem transitionEtaleForm_id_hom_apply (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i : I) (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i)
    (hw : IsEtale B S hS w.hom)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w)
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS w hw).obj U))) :
    ModuleCat.Hom.hom
        ((transitionEtaleForm B S hS Yi f D i i v w w hw hw hi hj).val.app (.op U)) s = s :=
  transitionEtaleForm_id_apply B S hS Yi f D i v w hw hi hj U s

/-- **The bundled reading of the transition of a descent datum from a member to itself, read
over a chart, is the identity morphism of the module of sections.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_id` read over a chart, and it
is the transition factor of `map_id` of the presheaf to be assembled.

Stated on variables: the morphism-level identity law is free, and a consumer rewrites with this
one rather than reducing its own composite. -/
theorem transitionEtaleForm_id_app (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i : I) (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i)
    (hw : IsEtale B S hS w.hom)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w)
    (U : SmallEtale B S hS T.1) :
    (transitionEtaleForm B S hS Yi f D i i v w w hw hw hi hj).val.app (.op U) =
      𝟙 (((etaleModulePullback.{u, u} B S hS w hw).obj (D.F i)).val.obj (.op U)) := by
  rw [transitionEtaleForm_id B S hS Yi f D i v w hw hi hj]
  rfl

/-- `.transitionEtaleForm_id_app` with the module of sections spelled as the sections of the
component module over the induced chart.  That is the spelling in which the transition factor of
a restriction map of the presheaf below meets a **rewrite**: the factor sits under a restriction
of scalars inside a composite, so the type of the equation is the binder type of the rewrite's
motive, and with the étale restriction in that position the motive asks for the sections of an
étale restriction and the sections over the composite chart to be identified where they may not
be.  Stated on variables, like the law it retypes. -/
theorem transitionEtaleForm_id_app' (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i : I) (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i)
    (hw : IsEtale B S hS w.hom)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w)
    (U : SmallEtale B S hS T.1) :
    (transitionEtaleForm B S hS Yi f D i i v w w hw hw hi hj).val.app (.op U) =
      𝟙 ((D.F i).val.obj (.op ((smallEtalePostcomp B S hS w hw).obj U))) :=
  transitionEtaleForm_id_app B S hS Yi f D i v w hw hi hj U

/-! ### The transition attached to a morphism of the charts of the members -/

variable (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- The identity chart of the chart space of a chart: the chart space is represented by the
scheme of the chart, and this is the identity of that scheme read as a chart of it. -/
abbrev chartSpaceIdChart (Z : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Z.1) :
    SmallEtale B S hS (chartSpace B S hS Z W).1 :=
  idEtaleChart B S hS ((SmallEtale.toOver B S hS Z.1).obj W)

/-- The chart of the target member that a morphism of the site of the charts of the members
induces: the identity chart of the chart space of the source chart, pushed forward along the
morphism to the target member.

This is a reducible abbreviation because it has to be recognized as the chart over which the
bundled reading of the transition reads its source, which the elaborator does only in the
position of a type. -/
abbrev memberTransitionChart {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    SmallEtale B S hS (Yi i).1 :=
  (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V V' k)
    (isEtale_memberChartMap B S hS Yi f hf V V' k)).obj (chartSpaceIdChart B S hS (Yi j) V')

/-- **The morphism of charts of the target member that a morphism of the site of the charts of
the members induces.**  It is the structure morphism that the equivalence of Stacks 04M0 attaches
to the identity chart of the chart space of the source chart, pushed forward along the represented
morphism of chart spaces. -/
def memberTransitionHom {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    memberTransitionChart B S hS Yi f hf V V' k ⟶ V :=
  ((SmallEtale.chartLocalization B S hS (Yi i).1 V).obj
    ((smallEtalePostcomp B S hS (chartMap B S hS X k) (isEtale_chartMap B S hS X k)).obj
      (chartSpaceIdChart B S hS (Yi j) V'))).hom

/-- **The morphism of charts induced by a morphism of the site of the charts of the members has
that morphism as its underlying morphism of the big fppf site.**  Postcomposition of charts leaves
the underlying morphism alone, and the equivalence of Stacks 04M0 reads it off the chart. -/
theorem memberTransitionHom_hom_left {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    (memberTransitionHom B S hS Yi f hf V V' k).hom.left = k.hom.left := rfl

/-- The morphism of charts induced by an identity morphism of the site of the charts of the
members is the identity. -/
theorem memberTransitionHom_id {i : I} (V : SmallEtale B S hS (Yi i).1) :
    memberTransitionHom B S hS Yi f hf V V
      (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)) = 𝟙 V := rfl

/-- The structure morphism of a chart of a member, spelled as the morphism to the target member
of the identity morphism of the site of the charts of the members.

The two are the same morphism on the nose.  The uniform spelling is what makes the two legs of
the test space of an identity morphism of the site *syntactically* one morphism, and so what makes
`.memberTransitionApp_id` available: the legs are the arguments on which the types of the
transition and of its bundled reading depend, and seeing two spellings of one of them as one
inside those types is the operation this material does not support. -/
abbrev memberSelfLeg {j : I} (V' : SmallEtale B S hS (Yi j).1) :
    chartSpace B S hS (Yi j) V' ⟶ Yi j :=
  memberChartMap B S hS Yi f hf V' V'
    (𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj V'))

/-- The chart of the target member over which the transition attached to a morphism of the site
of the charts of the members reads its target: the identity chart of the test space pushed forward
along `.memberSelfLeg`.  It is the source chart of that morphism on the nose.

This is a reducible abbreviation for the same reason as `.memberTransitionChart`. -/
abbrev memberTargetChart {j : I} (V' : SmallEtale B S hS (Yi j).1) :
    SmallEtale B S hS (Yi j).1 :=
  (smallEtalePostcomp B S hS (memberSelfLeg B S hS Yi f hf V')
    (isEtale_memberChartMap B S hS Yi f hf V' V'
      (𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj V')))).obj
    (chartSpaceIdChart B S hS (Yi j) V')

/-- **The transition of a descent datum attached to a morphism of the site of the charts of the
members, as a morphism of the sections of the two component modules over the two charts.**  The
test space is the chart space of the source chart, carrying the structure morphism of that chart
to its own member — spelled `.memberSelfLeg` — and the represented morphism to the target member;
the reading is taken over the identity chart of the test space, where the induced chart of the
source member is the source chart itself.

The source and the target types are ascribed: the sections of an étale restriction over a chart
are the sections of the module over the composite chart, which the elaborator recognizes only in
the position of a type. -/
def memberTransitionApp (D : DescentDatum B S hS Yi f) {i j : I}
    (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    (D.F i).val.obj (.op (memberTransitionChart B S hS Yi f hf V V' k)) ⟶
      (D.F j).val.obj (.op (memberTargetChart B S hS Yi f hf V')) :=
  (transitionEtaleForm B S hS Yi f D i j (memberChartPair B S hS Yi f hf V V' k)
      (memberChartMap B S hS Yi f hf V V' k) (memberSelfLeg B S hS Yi f hf V')
      (isEtale_memberChartMap B S hS Yi f hf V V' k)
      (isEtale_memberChartMap B S hS Yi f hf V' V'
        (𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj V')))
      (memberChartPair_fst B S hS Yi f hf V V' k)
      (memberChartPair_snd B S hS Yi f hf V V' k)).val.app
    (.op (chartSpaceIdChart B S hS (Yi j) V'))

/-- **The transition attached to an identity morphism of the site of the charts of the members is
the identity.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_id` at the test space of the
chart: the two legs of the identity morphism of the site are the one morphism `.memberSelfLeg`,
which is why they are the same argument of the transition here, and the uniform spelling of the
legs is what buys that.

It is stated as an equation of morphisms of the étale restrictions, where it is free; on sections
over the identity chart of the test space it is out of reach, as the implementation notes
record. -/
theorem memberTransitionForm_id (D : DescentDatum B S hS Yi f) {i : I}
    (V : SmallEtale B S hS (Yi i).1) :
    transitionEtaleForm B S hS Yi f D i i
        (memberChartPair B S hS Yi f hf V V
          (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))
        (memberSelfLeg B S hS Yi f hf V) (memberSelfLeg B S hS Yi f hf V)
        (isEtale_memberChartMap B S hS Yi f hf V V
          (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))
        (isEtale_memberChartMap B S hS Yi f hf V V
          (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))
        (memberChartPair_fst B S hS Yi f hf V V
          (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))
        (memberChartPair_snd B S hS Yi f hf V V
          (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))) =
      𝟙 ((etaleModulePullback.{u, u} B S hS (memberSelfLeg B S hS Yi f hf V)
        (isEtale_memberChartMap B S hS Yi f hf V V
          (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))).obj (D.F i)) :=
  transitionEtaleForm_id B S hS Yi f D i
    (memberChartPair B S hS Yi f hf V V
      (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))
    (memberSelfLeg B S hS Yi f hf V)
    (isEtale_memberChartMap B S hS Yi f hf V V
      (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))
    (memberChartPair_fst B S hS Yi f hf V V
      (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))
    (memberChartPair_snd B S hS Yi f hf V V
      (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)))

/-! ### The legs of the test space, spelled uniformly -/

/-- The structure morphism of a chart of a member is the morphism to the target member attached
to an identity morphism of the site of the charts of the members.

The two are the same morphism on the nose; the point of the statement is that the identity
morphism is carried as a variable, so that a consumer gets the equation in **its own** spelling
of that morphism. -/
theorem chartToSpace_eq_memberChartMap {j : I} (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V')
    (hk : k = 𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj V')) :
    chartToSpace B S hS (Yi j) V' = memberChartMap B S hS Yi f hf V' V' k := by
  subst hk
  rfl

/-- **The second projection of the test space of a morphism of the site of the charts of the
members, with the self leg spelled as the leg of an identity morphism of the site.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartPair_snd` retyped, and the retyping is
what the two laws of the presheaf need: the *type* of that compatibility is an argument of the
transition, so a compatibility whose type says `chartToSpace` makes every later statement about
the transition unmatchable, which is the reason `.memberChartPair_snd` is not used
directly below. -/
theorem memberChartPair_snd' {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
    (k' : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V')
    (hk' : k' = 𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj V')) :
    memberChartPair B S hS Yi f hf V V' k ≫ pairSnd B S hS Yi f i j =
      memberChartMap B S hS Yi f hf V' V' k' :=
  (memberChartPair_snd B S hS Yi f hf V V' k).trans
    (chartToSpace_eq_memberChartMap B S hS Yi f hf V' k' hk')

/-! ### The presheaf of modules -/

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- **The sections of a descent datum over an object of the site of the charts of the members**:
the sections of the component module of that member over the chart which the **identity**
morphism of the site induces, as a module over the structure ring of the induced chart of `X`.

That chart is the chart of the object itself on the nose, so these are the sections over the
chart itself.  The identity-induced spelling is the one carried because the chart over which the
transition reads its target is that one: with it the restriction of a section needs no chart
crossing in either of the two roles a morphism of the site plays in `map_comp`, which is what the
presheaf of abelian groups assembled in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf.lean` needs of
it; that file's implementation notes record the measurement.

The result type is ascribed: the structure ring of a chart of a member is the structure ring of
the induced chart of `X` definitionally but not syntactically.  **It is this ascription that
supplies the module structure** on the sections, which is the data
`CategoryTheory.PresheafOfModules.ofPresheaf` asks for beyond the presheaf itself. -/
abbrev memberDatumObj (D : DescentDatum B S hS Yi f) (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    ModuleCat ((memberRing B S hS Yi f hf).obj.obj p) :=
  (D.F p.unop.1).val.obj (Opposite.op
    ((smallEtalePostcomp B S hS
        (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
        (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2
          (memberHom B S hS Yi f hf (𝟙 p).unop))).obj
      (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2)))

omit [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)] in
/-- The morphism of charts of `Y i` attached to an identity morphism of the site of the charts of
the members is the identity, read in the opposite category.  It is `.memberTransitionHom_id` with
the identity morphism of the site spelled as a consumer of `.memberDatumMap` meets it. -/
theorem memberTransitionHom_op_id (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2
      (memberHom B S hS Yi f hf (𝟙 p).unop)).op = 𝟙 (Opposite.op p.unop.2) := rfl

/-- **The restriction factor of the restriction map of the presheaf, at an identity morphism of
the site of the charts of the members, acts as the identity on a section.**  This is the
restriction half of `map_id` of the presheaf: by `.memberTransitionHom_op_id` the morphism of
charts is an identity, and by `.val_map_eq_id_hom_apply` restriction along it is the identity.

The identity of the chart has to be met in the spelling of the small étale **ringed** site, which
is why `.val_map_eq_id_hom_apply` is stated there and its morphism is left to be inferred here. -/
theorem memberDatumRestrict_id_apply (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : memberDatumObj B S hS Yi f hf D p) :
    ModuleCat.Hom.hom ((D.F p.unop.1).val.map
      (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2
        (memberHom B S hS Yi f hf (𝟙 p).unop)).op) m = m := by
  rw [memberTransitionHom_op_id]
  exact val_map_eq_id_hom_apply B S hS (D.F p.unop.1) _ rfl m

/-- **The restriction map of the presheaf of modules attached to a descent datum, and its
semilinearity.**  Along a morphism `k : (j, V') ⟶ (i, V)` of the site of the charts of the members
it is restriction inside `D.F i` to the chart of `Y i` that `k` induces, followed by the
**bundled reading** `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm` of the
transition from `i` to `j`, read over the identity chart of the chart space of `V'`.

Both factors are morphisms of modules, so the map is **semilinear over the restriction map of the
structure sheaf read on the charts of the members** by its type: the first factor is semilinear
over the restriction along the induced morphism of charts of `Y i`, which is the restriction along
`k` of the structure sheaf of `X`, and the second is linear.

The transition factor is the reading **written out**, not the ascribed `.memberTransitionApp`, and
its two legs are spelled `memberChartMap` throughout — the self leg as `memberChartMap V' V' k'`
for the `k'` of an identity morphism of the site, and its second compatibility as
`.memberChartPair_snd'`.  Both choices are forced: see the implementation notes. -/
def memberDatumMap (D : DescentDatum B S hS Yi f) {p q : (MemberSite B S hS Yi f hf)ᵒᵖ}
    (g : p ⟶ q) :
    memberDatumObj B S hS Yi f hf D p ⟶
      (ModuleCat.restrictScalars ((memberRing B S hS Yi f hf).obj.map g).hom).obj
        (memberDatumObj B S hS Yi f hf D q) :=
  (D.F p.unop.1).val.map
      (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2
        (memberHom B S hS Yi f hf g.unop)).op ≫
    (ModuleCat.restrictScalars ((memberRing B S hS Yi f hf).obj.map g).hom).map
      ((transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1
          (memberChartPair B S hS Yi f hf p.unop.2 q.unop.2
            (memberHom B S hS Yi f hf g.unop))
          (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
            (memberHom B S hS Yi f hf g.unop))
          (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
            (memberHom B S hS Yi f hf (𝟙 q).unop))
          (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
            (memberHom B S hS Yi f hf g.unop))
          (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
            (memberHom B S hS Yi f hf (𝟙 q).unop))
          (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
            (memberHom B S hS Yi f hf g.unop))
          (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
            (memberHom B S hS Yi f hf g.unop)
            (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app
        (.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))

/-- `congrArg` with the equation before the function, so that the function is applied to a
section at the type the **equation** gives it rather than at the one the function expects.  The
argument order is the whole content: with `congrArg` the function is elaborated first, which
pins the type of its argument and so forces two spellings of one module of sections to meet in a
unification. -/
theorem apply_congr {α β : Sort*} {a₁ a₂ : α} (h : a₁ = a₂) (F : α → β) : F a₁ = F a₂ :=
  congrArg F h

/-- A composite of two morphisms of modules, read on a section.  Stated on variables, with the
three modules opaque, so that a consumer instantiates it at a composite whose middle module is
in whatever spelling that composite carries. -/
theorem comp_hom_apply {R₀ : Type u} [Ring R₀] {M N P : ModuleCat.{u} R₀} (A : M ⟶ N)
    (B₀ : N ⟶ P) (m : M) :
    ModuleCat.Hom.hom (A ≫ B₀) m = ModuleCat.Hom.hom B₀ (ModuleCat.Hom.hom A m) := rfl

/-- The restriction of scalars of a morphism of modules, read on a section: it leaves the
section alone.  Stated on variables, with the section opaque. -/
theorem restrictScalars_map_hom_apply {R₀ R₁ : Type u} [Ring R₀] [Ring R₁] (φ : R₀ →+* R₁)
    {N P : ModuleCat.{u} R₁} (B₀ : N ⟶ P) (n : N) :
    ModuleCat.Hom.hom ((ModuleCat.restrictScalars φ).map B₀) n = ModuleCat.Hom.hom B₀ n := rfl

/-- The restriction of scalars of an identity, read on a section: it leaves the section alone.
Stated on variables, with the module carried explicitly, so that a consumer whose second factor
has been collapsed to an identity closes its last obligation without naming that module. -/
theorem restrictScalars_map_id_hom_apply {R₀ R₁ : Type u} [Ring R₀] [Ring R₁] (φ : R₀ →+* R₁)
    (N : ModuleCat.{u} R₁) (n : (ModuleCat.restrictScalars φ).obj N) :
    ModuleCat.Hom.hom ((ModuleCat.restrictScalars φ).map (𝟙 N)) n = n := rfl

/-- **A restriction map which is a composite, read on a section, out of the two factors read on
sections** — with **all four modules read off the goal**.  Only `.comp_hom_apply` and
`.apply_congr` are used, so the second factor stays opaque and the middle module of the composite
is whatever spelling the consumer's own `≫` carries.

That is the whole difference from `.comp_restrictScalars_map_hom_apply`, and it is what makes
this one usable: there the second factor is written as a restriction of scalars, which pins the
middle module of the conclusion's composite to the restriction of scalars along the consumer's
ring map, while a restriction map built as a composite carries its *first factor's own target*
there — so that lemma can never match; see the implementation notes. -/
theorem comp_hom_apply_eq_of_sect {R₀ : Type u} [Ring R₀] {M N P : ModuleCat.{u} R₀}
    (A : M ⟶ N) (e : N ⟶ P) (m : M) (n : N) (hA : ModuleCat.Hom.hom A m = n)
    (q : P) (he : ModuleCat.Hom.hom e n = q) :
    ModuleCat.Hom.hom (A ≫ e) m = q :=
  (comp_hom_apply A e m).trans
    ((apply_congr hA (fun z => ModuleCat.Hom.hom e z)).trans he)

/-- **A restriction map which is a semilinear composite, read on a section, out of the two
factors read on sections.**  Stated on variables, and with the two values of the factors carried
as variables identified by hypotheses: `.comp_hom_apply` splits the composite,
`.restrictScalars_map_hom_apply` strips the restriction of scalars from the second factor, and
`.apply_congr` applies that factor to the value of the first at the type the first factor's own
hypothesis gives it.

Every module here is a variable, so a consumer instantiates the whole calculation at once and
the only crossing left is between the restriction of scalars the consumer's composite carries
and the one its first factor carries. -/
theorem comp_restrictScalars_map_hom_apply {R₀ R₁ : Type u} [Ring R₀] [Ring R₁] (φ : R₀ →+* R₁)
    {M : ModuleCat.{u} R₀} {N P : ModuleCat.{u} R₁}
    (A : M ⟶ (ModuleCat.restrictScalars φ).obj N) (B₀ : N ⟶ P) (m : M) (n : N)
    (hA : ModuleCat.Hom.hom A m = n) (q : P) (hB : ModuleCat.Hom.hom B₀ n = q) :
    ModuleCat.Hom.hom (A ≫ (ModuleCat.restrictScalars φ).map B₀) m = q :=
  (comp_hom_apply A ((ModuleCat.restrictScalars φ).map B₀) m).trans
    ((apply_congr hA
        (fun z => ModuleCat.Hom.hom ((ModuleCat.restrictScalars φ).map B₀) z)).trans
      ((restrictScalars_map_hom_apply φ B₀ n).trans hB))

/-- **A semilinear map along a ring map equal to an identity which leaves every section alone
is the identification of the restriction of scalars along an identity with the identity
functor.**  This is `map_id` of a presheaf of modules reduced to a statement about sections with
the restriction map itself carried as a **variable**, so that a consumer instantiates it at its
own restriction map and no composite has to be matched — which is what
`.comp_restrictScalars_eq_restrictScalarsId'` asks for and what resists at the member site. -/
theorem comp_eq_restrictScalarsId'_of_sect {R₀ : Type u} [Ring R₀] (φ : R₀ →+* R₀)
    (hφ : φ = RingHom.id R₀) {M : ModuleCat.{u} R₀}
    (C : M ⟶ (ModuleCat.restrictScalars φ).obj M) (h : ∀ m : M, ModuleCat.Hom.hom C m = m) :
    C = (ModuleCat.restrictScalarsId' φ hφ).inv.app M :=
  eq_restrictScalarsId'_of_sect φ hφ C h

/-- **The restriction factor of the restriction map, at an identity morphism of the site of the
charts of the members, acts as the identity on a section — through the restriction of scalars
along the structure sheaf of the charts of the members.**  This is
`.memberDatumRestrict_id_apply` retyped: that law reads the factor through the restriction of
scalars along the structure sheaf of the **member**, which is the factor's own target, while a
field of a `PresheafOfModules` over `.memberRing` reads it through the structure sheaf of the
charts of the members.  The two modules are the same definitionally and print identically, and
they may not meet in a unification; the coercion is therefore written with its two modules
**explicit**, so that the crossing happens once, between the type of this statement and its
proof.  A type ascription would do as well but leaves a `let` in the term, which nothing
downstream carries. -/
theorem memberDatumRestrict_id_hom_apply (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : memberDatumObj B S hS Yi f hf D p) :
    @ModuleCat.Hom.hom _ _ ((D.F p.unop.1).val.obj (Opposite.op p.unop.2))
        ((ModuleCat.restrictScalars ((memberRing B S hS Yi f hf).obj.map (𝟙 p)).hom).obj
          ((D.F p.unop.1).val.obj (Opposite.op (memberTransitionChart B S hS Yi f hf
            p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)))))
        ((D.F p.unop.1).val.map
          (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop)).op) m = m :=
  memberDatumRestrict_id_apply B S hS Yi f hf D p m

/-- **THE TWO HALVES OF THE IDENTITY LAW, JOINED: the transition of the restriction of a
section along an identity morphism of the site of the charts of the members is that section** —
with the restriction factor read exactly as a field of a `PresheafOfModules` over `.memberRing`
reads it.  `.memberDatumRestrict_id_hom_apply` is the restriction factor,
`.transitionEtaleForm_id_hom_apply` the transition factor.

`.apply_congr` is what makes the join go through, and its argument order is the whole content:
the transition factor is applied to the restricted section at the type the **restriction** half
gives it, which is a function-argument position, where `congrArg` would elaborate the function
first and so force two spellings of the module the two factors meet in into one unification. -/
theorem memberDatumFactors_id_apply (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : memberDatumObj B S hS Yi f hf D p) :
    ModuleCat.Hom.hom
        ((transitionEtaleForm B S hS Yi f D p.unop.1 p.unop.1
          (memberChartPair B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop))
          (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop))
          (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop))
          (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop))
          (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop))
          (memberChartPair_fst B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop))
          (memberChartPair_snd' B S hS Yi f hf p.unop.2 p.unop.2
            (memberHom B S hS Yi f hf (𝟙 p).unop)
            (memberHom B S hS Yi f hf (𝟙 p).unop) rfl)).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2)))
        (@ModuleCat.Hom.hom _ _ ((D.F p.unop.1).val.obj (Opposite.op p.unop.2))
            ((ModuleCat.restrictScalars ((memberRing B S hS Yi f hf).obj.map (𝟙 p)).hom).obj
              ((D.F p.unop.1).val.obj (Opposite.op (memberTransitionChart B S hS Yi f hf
                p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)))))
            ((D.F p.unop.1).val.map
              (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2
                (memberHom B S hS Yi f hf (𝟙 p).unop)).op) m) = m :=
  (apply_congr (memberDatumRestrict_id_hom_apply B S hS Yi f hf D p m)
      (ModuleCat.Hom.hom _)).trans
    (transitionEtaleForm_id_hom_apply B S hS Yi f D p.unop.1
      (memberChartPair B S hS Yi f hf p.unop.2 p.unop.2
        (memberHom B S hS Yi f hf (𝟙 p).unop))
      (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2
        (memberHom B S hS Yi f hf (𝟙 p).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2
        (memberHom B S hS Yi f hf (𝟙 p).unop))
      (memberChartPair_fst B S hS Yi f hf p.unop.2 p.unop.2
        (memberHom B S hS Yi f hf (𝟙 p).unop))
      (memberChartPair_snd' B S hS Yi f hf p.unop.2 p.unop.2
        (memberHom B S hS Yi f hf (𝟙 p).unop)
        (memberHom B S hS Yi f hf (𝟙 p).unop) rfl)
      (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2) m)

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end

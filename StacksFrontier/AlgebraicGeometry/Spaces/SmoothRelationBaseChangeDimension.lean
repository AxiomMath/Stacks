module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothEtaleLocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty

/-!
# The relation of a smooth refinement, and its dimension formula

Let `U' ⟶ U` be a morphism of algebraic spaces over `S` and let `s, t : R ⟶ U` be two morphisms
with common target `U`. The **doubled base change**

`R' = (U' ×_{h, U, t} R) ×_{s, U} U'`

comes with a projection `p : R' ⟶ R`, and `p` is smooth as soon as `h` is: it is a composite of
two base changes of `h`, one along `t` and one along `s`. The dimension formula of
`AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth` therefore
applies to it and gives, at a geometric point `r'` of `R'`,

`dim(𝒪_{R', r'}) = dim(𝒪_{R, p(r')}) + dim(𝒪_{R'_{p(r')}, r'})`.

This is the second of the three dimension identities that the comparison of two smooth charts in
**Stacks 0DS9** runs on. There `R = U ×_𝒳 U` is a presented self-intersection with `s` and `t` its
two projections, `h : U' ⟶ U` is a smooth morphism of charts, and `R'` is the source's
`U' ×_{U, t} R ×_{s, U} U'`, which is a presented self-intersection of `U'`; the fibre of `p` over
the identity arrow is the source's `U'_u ×_u U'_u`.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChange`: the doubled base change `R'`.
* `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeProj`: its projection `p : R' ⟶ R`.

## Main results

* `AlgebraicGeometry.Space.AlgebraicSpaces.isSmooth_relationBaseChangeProj`: `p` is smooth when
  `h` is, by Stacks 03ZE twice and Stacks 03ZD.
* `AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_relationBaseChange`: the
  dimension formula for `p`.
* `AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_relationBaseChange_split`:
  the same with the fibre term split into the closed fibres of the two legs.
* `AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`:
  the Step C identity of Stacks 0DS9 in subtraction-free form, *reduced to* the two base-change
  facts below, which it takes as hypotheses.

## What is not proved here

The doubling in Stacks 0DS9 needs, at the identity arrow, that each leg of the doubled base
change has a closed fibre of the same dimension as the closed fibre of `h` itself:

> for a cartesian square of algebraic spaces with `A = U' ×_{h, U, t} R` and `q : A ⟶ R` the base
> change of `h` along `t`, the closed fibre of `𝒪_{R, q(a)} ⟶ 𝒪_{A, a}` has the same Krull
> dimension as the closed fibre of `𝒪_{U, h(x')} ⟶ 𝒪_{U', x'}`, where `x'` is the image of `a`
> in `U'`.

This is "the fibre of a base change is the fibre of the original morphism", read on étale local
rings, and it is NOT proved in this development. It is the hypothesis `hfst`/`hsnd` of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`,
stated there once for each leg. Without it the dimension formula along the legs and the identity
of the third step of Stacks 0DS9 are statements about different rings, and the Step C identity is
not available. Nothing in this file conceals that: the two facts appear as hypotheses in the type
of the only theorem that would otherwise be Step C.

## Implementation notes

The construction is carried out in the category `AlgebraicGeometry.Space.AlgebraicSpaces` of
algebraic spaces over `S`, which has fibre products (Stacks 043C) computed as presheaf fibre
products, so the two pullback squares and their stability properties come from the general
`CategoryTheory.MorphismProperty` API rather than being rebuilt by hand. The conclusion is then
read off on the underlying presheaves, where the dimension formula lives.

No closedness hypothesis appears, and none is needed: the input is smoothness of `h`, which
holds at every point. The closedness that **Stacks 0DS9** does need enters only at the third of
its three identities.

The two morphisms `s` and `t` are arbitrary and are not assumed to be the projections of a fibre
product, nor related to each other in any way, so the statement is independent of how the
relation is presented.

**Relation to the groupoid restriction, and a bridge that is owed.**
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChange` denotes the same algebraic space as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows`
(`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupoidRestriction.lean`), the arrow space of
the restriction of a groupoid along a map to its object space, which carries Stacks 044B, 044C
and 04RN through `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict`. Both are
`{(u'₁, r, u'₂) : h(u'₁) = t(r), s(r) = h(u'₂)}`; the spellings differ, the groupoid one being
`(U' ×_{g, U, t} R) ×_R (R ×_{s, U, g} U')`, fibred over `R`, against the iterated pullback
`(U' ×_{h, U, t} R) ×_{s, U} U'` used here. **No bridge lemma between the two spellings exists
anywhere in the library**, and anything connecting the material below to the
044B/044C/04RN development will have to supply one; the scheme-level analogue of Stacks 02VB uses
the groupoid spelling too, so the spelling here is the minority one.

The reason for the spelling here is not path dependence. `restrictionArrows` takes a whole
`AlgebraicGeometry.GroupoidInAlgebraicSpaces` — a composition law, an identity and an inverse,
with their axioms — whereas everything below needs only two bare morphisms `s, t : R ⟶ U`. None
of the groupoid axioms enters any proof in this file, and the self-intersection of a smooth chart
satisfies them but does not need them for the dimension identities. Stating the results at the
weaker hypotheses keeps them applicable to a presented relation before it is known to be a
groupoid, which is the situation in Stacks 0DS9.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [Stacks Project, Tag 03ZD](https://stacks.math.columbia.edu/tag/03ZD)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.AlgebraicSpaces

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U' R : AlgebraicSpaces B S hS}

/-- The **doubled base change** `R' = (U' ×_{h, U, t} R) ×_{s, U} U'` of a pair of morphisms
`s, t : R ⟶ U` along a morphism `h : U' ⟶ U`. When `R = U ×_𝒳 U` is a presented
self-intersection with projections `s` and `t`, this is the corresponding self-intersection of
`U'`. -/
noncomputable def relationBaseChange (h : U' ⟶ U) (s t : R ⟶ U) : AlgebraicSpaces B S hS :=
  pullback (pullback.snd h t ≫ s) h

/-- The **intermediate stage** `A = U' ×_{h, U, t} R` of the doubled base change. -/
noncomputable def relationBaseChangeMid (h : U' ⟶ U) (s t : R ⟶ U) : AlgebraicSpaces B S hS :=
  pullback h t

/-- The **first leg** `R' ⟶ A` of the doubled base change: the base change of `h` along
`s ∘ pr₂ : A ⟶ U`. -/
noncomputable def relationBaseChangeFst (h : U' ⟶ U) (s t : R ⟶ U) :
    relationBaseChange B S hS h s t ⟶ relationBaseChangeMid B S hS h s t :=
  pullback.fst (pullback.snd h t ≫ s) h

/-- The **second leg** `A ⟶ R` of the doubled base change: the base change of `h` along
`t : R ⟶ U`. -/
noncomputable def relationBaseChangeSnd (h : U' ⟶ U) (s t : R ⟶ U) :
    relationBaseChangeMid B S hS h s t ⟶ R :=
  pullback.snd h t

/-- The projection `p : R' ⟶ R` of the doubled base change, through the intermediate
`U' ×_{h, U, t} R`. -/
noncomputable def relationBaseChangeProj (h : U' ⟶ U) (s t : R ⟶ U) :
    relationBaseChange B S hS h s t ⟶ R :=
  relationBaseChangeFst B S hS h s t ≫ relationBaseChangeSnd B S hS h s t

/-- The **second leg is smooth when `h` is**: it is the base change of `h` along `t`
(Stacks 03ZE). -/
theorem isSmooth_relationBaseChangeSnd (h : U' ⟶ U) (s t : R ⟶ U)
    (hh : IsSmooth B S hS h.hom) :
    IsSmooth B S hS (relationBaseChangeSnd B S hS h s t).hom :=
  MorphismProperty.pullback_snd (P := smoothMorphismProperty B S hS) h t hh

/-- The **first leg is smooth when `h` is**: it is the base change of `h` along `s ∘ pr₂`
(Stacks 03ZE). -/
theorem isSmooth_relationBaseChangeFst (h : U' ⟶ U) (s t : R ⟶ U)
    (hh : IsSmooth B S hS h.hom) :
    IsSmooth B S hS (relationBaseChangeFst B S hS h s t).hom :=
  MorphismProperty.pullback_fst (P := smoothMorphismProperty B S hS)
    (pullback.snd h t ≫ s) h hh

/-- **The projection of the doubled base change is smooth when `h` is.** It is the composite of
the base change of `h` along `t` (Stacks 03ZE) with the base change of `h` along
`s ∘ pr₂` (Stacks 03ZE again), and smoothness is stable under composition (Stacks 03ZD). -/
theorem isSmooth_relationBaseChangeProj (h : U' ⟶ U) (s t : R ⟶ U)
    (hh : IsSmooth B S hS h.hom) :
    IsSmooth B S hS (relationBaseChangeProj B S hS h s t).hom :=
  isSmooth_comp B S hS (relationBaseChange B S hS h s t).property
    (relationBaseChangeMid B S hS h s t).property R.property _ _
    (isSmooth_relationBaseChangeFst B S hS h s t hh)
    (isSmooth_relationBaseChangeSnd B S hS h s t hh)

/-- Local Noetherianity passes from `R` to the intermediate stage `A = U' ×_{h, U, t} R`, the
second leg being smooth hence locally of finite type (Stacks 04ZK). -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_relationBaseChangeMid (h : U' ⟶ U)
    (s t : R ⟶ U) (hh : IsSmooth B S hS h.hom)
    (hN : HasEtaleLocalProperty B S hS R.obj (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    HasEtaleLocalProperty B S hS (relationBaseChangeMid B S hS h s t).obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    (relationBaseChangeMid B S hS h s t).property R.property _
    (isLocallyOfFiniteType_of_isSmooth B S hS (isSmooth_relationBaseChangeSnd B S hS h s t hh))
    hN

/-- **The dimension formula along the projection of the doubled base change.** At a geometric
point `r'` of `R' = (U' ×_{h, U, t} R) ×_{s, U} U'`,

`dim(𝒪_{R', r'}) = dim(𝒪_{R, p(r')}) + dim(𝒪_{R'_{p(r')}, r'})`,

the last term being the dimension of the closed fibre of `𝒪_{R, p(r')} ⟶ 𝒪_{R', r'}`.

This is the second of the three dimension identities comparing two smooth charts in
**Stacks 0DS9**; like the first it needs no closedness of any point. -/
theorem ringKrullDim_etaleLocalRing_relationBaseChange (h : U' ⟶ U) (s t : R ⟶ U)
    (hh : IsSmooth B S hS h.hom)
    (hN : HasEtaleLocalProperty B S hS R.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (r : GeometricPoint B S hS (relationBaseChange B S hS h s t).obj) :
    ringKrullDim (etaleLocalRing B S hS (relationBaseChange B S hS h s t).obj r) =
      ringKrullDim (etaleLocalRing B S hS R.obj
          (geometricPointMap (relationBaseChangeProj B S hS h s t).hom r)) +
        ringKrullDim (closedFibreEtaleLocalRing B S hS
          (relationBaseChange B S hS h s t).property
          (relationBaseChangeProj B S hS h s t).hom r) :=
  ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth B S hS
    (relationBaseChange B S hS h s t).property R.property _
    (isSmooth_relationBaseChangeProj B S hS h s t hh) hN r

/-- **The dimension formula along the projection of the doubled base change, with the fibre
split into its two factors.** At a geometric point `r'` of `R'`,

`dim(𝒪_{R', r'}) = dim(𝒪_{R, p(r')}) + dim(𝒪_{A_{p(r')}, ·}) + dim(𝒪_{R'_{·}, r'})`,

the two fibre terms being the closed fibres of the two legs `R' ⟶ A` and `A ⟶ R`, each of
which is a base change of `h`.

This refines
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_relationBaseChange` by
naming the two factors separately instead of their sum, and it is the form in which the third
identity of **Stacks 0DS9** is meant to be applied: at the identity arrow `r' = e(ū')` the two
legs have the SAME foot `u`, so both closed fibres are the closed fibre of `h` at `ū'` and the
sum is `2 dim(𝒪_{U'_u, ū'})`. That last specialisation is not proved here — see the module
documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothRelationBaseChangeDimension.lean`.

No closedness and no cancellation are involved: the identity is two applications of
`AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth`, one for
each leg, substituted one into the other. -/
theorem ringKrullDim_etaleLocalRing_relationBaseChange_split (h : U' ⟶ U) (s t : R ⟶ U)
    (hh : IsSmooth B S hS h.hom)
    (hN : HasEtaleLocalProperty B S hS R.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (r : GeometricPoint B S hS (relationBaseChange B S hS h s t).obj) :
    ringKrullDim (etaleLocalRing B S hS (relationBaseChange B S hS h s t).obj r) =
      ringKrullDim (etaleLocalRing B S hS R.obj
            (geometricPointMap (relationBaseChangeSnd B S hS h s t).hom
              (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r))) +
          ringKrullDim (closedFibreEtaleLocalRing B S hS
            (relationBaseChangeMid B S hS h s t).property
            (relationBaseChangeSnd B S hS h s t).hom
            (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r)) +
        ringKrullDim (closedFibreEtaleLocalRing B S hS
          (relationBaseChange B S hS h s t).property
          (relationBaseChangeFst B S hS h s t).hom r) := by
  have hNmid : HasEtaleLocalProperty B S hS (relationBaseChangeMid B S hS h s t).obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_relationBaseChangeMid B S hS h s t hh hN
  rw [ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth B S hS
      (relationBaseChange B S hS h s t).property (relationBaseChangeMid B S hS h s t).property
      _ (isSmooth_relationBaseChangeFst B S hS h s t hh) hNmid r,
    ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth B S hS
      (relationBaseChangeMid B S hS h s t).property R.property
      _ (isSmooth_relationBaseChangeSnd B S hS h s t hh) hN
      (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r)]

/-- **The Step C identity of Stacks 0DS9, reduced to the two base-change facts.** In the
subtraction-free form

`dim(𝒪_{U', ū'}) + dim(𝒪_{U', ū'}) + dim(𝒪_{R, e(ū)})
    = dim(𝒪_{U, ū}) + dim(𝒪_{U, ū}) + dim(𝒪_{R', e(ū')})`,

which is `2 dim(𝒪_{U', ū'}) - dim(𝒪_{R', e(ū')}) = 2 dim(𝒪_{U, ū}) - dim(𝒪_{R, e(ū)})` with the
two differences cleared, `ringKrullDim` being valued in `WithBot ℕ∞` where subtraction is not
available.

THIS IS A REDUCTION, NOT A COMPLETE RESULT. The two hypotheses `hfst` and `hsnd` are exactly the
statement that each of the two legs of the doubled base change has, at the given point, a closed
fibre of the same dimension as the closed fibre of `h` itself — the content of "the fibre of a
base change is the fibre of the original morphism", at the level of étale local rings. They are
NOT proved anywhere in this development; see the module documentation. A caller that cannot
discharge them has not proved Step C.

What *is* proved here is everything else: the arrangement, the two applications of the dimension
formula along the legs, and the application along `h`. No cancellation in `WithBot ℕ∞` is used —
the identity is a substitution, which is why it needs no finiteness hypothesis.

TWO SEPARATE CONDITIONS ARE NEEDED TO REACH THE HYPOTHESES, and they do different work.

The first is the specialisation to the diagonal, and it is what lets a SINGLE `x'` serve both
hypotheses: the foot of the first leg is `s(p(r))` and the foot of the second is `t(p(r))`, and
these are different points of `U` in general. At the identity arrow `r = e(ū')` one has
`p(r) = e(ū)` and `s(e(ū)) = t(e(ū)) = ū`, so both feet are `ū`.

The second is CLOSEDNESS of the point in its fibre, and it is what makes either hypothesis true
at all. Being on the diagonal is NOT sufficient. Take `𝒳 = U = Spec k` with `k` separably
closed and `U' = 𝔸¹_k`, so that `R = Spec k` and `R' = 𝔸²`, and let `ū'` be the GENERIC point of
`𝔸¹` and `r = e(ū')`, the point `(x₁ - x₂)` of `𝔸²`. Here `s = t`, so the feet coincide and `r`
lies on the diagonal — and `hfst` is still false: its left-hand side is the local ring of `𝔸²`
at `(x₁ - x₂)`, of dimension `1`, and its right-hand side is the local ring of `𝔸¹` at its
generic point, a field, of dimension `0`. The obstruction is the transcendence degree lost when
the point in the fibre is not closed — the image of a closed point need not be closed — and it
is what `AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_eq` (Stacks 02FY,
`local_ring_differences`) measures.

CONSEQUENCE A READER MUST BE TOLD: at a point that is not closed in its fibre both hypotheses
are UNSATISFIABLE, so this theorem is vacuous there — and rightly so, since the same example
falsifies its conclusion there, `0 + 0 + 0` against `0 + 0 + 1`. The conclusion is sound; the
hypotheses are reachable only at a point closed in its fibre, and a caller must supply that
closedness. This is the hypothesis the whole of Stacks 0DS9 turns on, and the source offers the
same curve-with-generic-point counterexample for it. The discharge of `hfst` and `hsnd` under
closedness runs through
`AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_of_isPullback_of_isClosed`. -/
theorem ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq (h : U' ⟶ U) (s t : R ⟶ U)
    (hh : IsSmooth B S hS h.hom)
    (hNU : HasEtaleLocalProperty B S hS U.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNR : HasEtaleLocalProperty B S hS R.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (r : GeometricPoint B S hS (relationBaseChange B S hS h s t).obj)
    (x' : GeometricPoint B S hS U'.obj)
    (hfst : ringKrullDim (closedFibreEtaleLocalRing B S hS
        (relationBaseChange B S hS h s t).property
        (relationBaseChangeFst B S hS h s t).hom r) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS U'.property h.hom x'))
    (hsnd : ringKrullDim (closedFibreEtaleLocalRing B S hS
        (relationBaseChangeMid B S hS h s t).property
        (relationBaseChangeSnd B S hS h s t).hom
        (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r)) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS U'.property h.hom x')) :
    ringKrullDim (etaleLocalRing B S hS U'.obj x') +
          ringKrullDim (etaleLocalRing B S hS U'.obj x') +
        ringKrullDim (etaleLocalRing B S hS R.obj
          (geometricPointMap (relationBaseChangeSnd B S hS h s t).hom
            (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r))) =
      ringKrullDim (etaleLocalRing B S hS U.obj (geometricPointMap h.hom x')) +
            ringKrullDim (etaleLocalRing B S hS U.obj (geometricPointMap h.hom x')) +
        ringKrullDim (etaleLocalRing B S hS (relationBaseChange B S hS h s t).obj r) := by
  rw [ringKrullDim_etaleLocalRing_relationBaseChange_split B S hS h s t hh hNR r, hfst, hsnd,
    ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth B S hS U'.property U.property
      h.hom hh hNU x']
  abel

end AlgebraicGeometry.Space.AlgebraicSpaces

end

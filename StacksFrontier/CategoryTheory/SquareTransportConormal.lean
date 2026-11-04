module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Category

/-!
# Carrying a square comparison across a transport, generically

A *transport* here is a family of comparison isomorphisms `Tr i : (P i).obj M ≅ Ψ i` indexed by
the morphisms `i` of some category, comparing two ways of carrying one object `M` across a
square of functors.  Two instances of a composition law for such a transport — one for each of
the two routes around a commutative square — combine into the statement that the transport
carries one square comparison to another, once three residual factors are matched: the transport
of the two laws' right-hand sides along the equality of the two composites, the identification
of the two square comparisons on the inner side, and the cancellation of the comparisons of the
two routes' second legs.

This file proves that implication **in a generic category, with every functor, object and
morphism a variable**, together with the piece of `CategoryTheory.eqToHom` bookkeeping it
consumes.

## Why it is stated here rather than at its instance

For the reason the implementation notes of
`StacksFrontier/CategoryTheory/FactoredTransportComposition.lean` record: at a
geometric instantiation the statements being combined are stated at definitionally equal but
syntactically different spellings of the same objects, so `rw` reports that it cannot find a
pattern the goal displays, and a term-mode application of a *generic* lemma — which unifies up to
definitional equality — is the only affordable route.  Keeping the lemma generic also keeps its
hypotheses in the shape the library's statements already have, so that no argument at an
instantiation is a restatement.

**Every transport is taken along an equality supplied as an argument**, and **no lemma here takes
a family of objects indexed by a type.**  Neither is cosmetic.  At the geometric instance the
transports come from the commutativity of a square, read on two sides at definitionally equal but
syntactically different spellings of the two composites — `φ(b ≫ j')` and `φ(b) ≫ φ(j')` — and
two things happen there.  First, a version of the bookkeeping taking the index family and
forming its transports by `congrArg` is a **kernel deterministic timeout** in a single
application, while the family-free version is free; the cost is in checking the lambda family
under its binder.  Second, the ascription of one `congrArg` proof to the other's type is free
(0.4 s), and so is the equality of the two pullback functors, but the equation
`(eqToHom e₁).app M = (eqToHom e₂).app M` between the two transports **elaborates and is then a
kernel deterministic timeout** — a projection out of a stuck `Eq.rec`, which no `irreducible`
attribute reaches.  The same equation with `CategoryTheory.eqToHom_app` rewritten on the left
first, so that one side is a plain `eqToHom`, is **free (0.2 s)**: comparing two `eqToHom` terms
is a reconciliation of their endpoints plus proof irrelevance, and both are cheap.

So `Stacks.CategoryTheory.map_map_comp_eqToHom` is stated for plain **objects**, with no functor
family and no `NatTrans.app` anywhere, and taking the equality as an argument means the equation
between the two spellings is never stated at all: the elaborator reconciles them once, in the
type of an argument, where proof irrelevance applies.

## Main results

* `Stacks.CategoryTheory.reading_eqToHom`: a reading whose middle factor is the
  `CategoryTheory.NatTrans.app` of an `eqToHom` of functors, respelled with a plain `eqToHom`.
* `Stacks.CategoryTheory.map_map_comp_eqToHom`: an identity involving a transport of objects,
  pushed through two functors.
* `Stacks.CategoryTheory.square_transport_eq_of_reading`, from
  `Stacks.CategoryTheory.square_transport_aux` and
  `Stacks.CategoryTheory.square_transport_of_aux`: **the square comparison is carried across the
  transport**, from the two composition laws and the three residual identities, in two halves.
  The split is not cosmetic: at the geometric instance the two halves together exceed the
  kernel's budget in one declaration and fit in two.
* `Stacks.CategoryTheory.comp_split_cancel_right`: a composite of two morphisms with one-sided
  inverses is cancelled from the right.
* `Stacks.CategoryTheory.mid_eq_of_reading`, `Stacks.CategoryTheory.comp₃_mid_eq_of`,
  `Stacks.CategoryTheory.square_transport_aux_of_mid`,
  `Stacks.CategoryTheory.cancel_left_of_comp₃`, `Stacks.CategoryTheory.eq_comp_of_cancel_left`
  and `Stacks.CategoryTheory.eq_of_comp_cancel_right`: the same implication regrouped so that
  **no morphism is ever shared between two hypotheses in a spelling it does not already have**.
  That regrouping is what makes the geometric instance check; see the section below and the
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareTransportAgreement.lean`.

**The order of the hypotheses of `Stacks.CategoryTheory.square_transport_aux` matters**, which is
why `hmid` and `hπ` come before `hL1`: the arguments are elaborated left to right, so the shared
object is taken from the transport identity rather than from the composition law, and the one
spelling of it that is expensive to reconcile — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareTransportAgreement.lean` — then occurs once
instead of three times.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

/-- **A reading whose middle factor is the `CategoryTheory.NatTrans.app` of an `eqToHom` of
functors, respelled with a plain `eqToHom` of the two objects.**

The equality of functors is **implicit**, so that it is read off the reading `hΞ` rather than
supplied, and that is the whole point of this lemma.  At the geometric instance,
matching the `NatTrans.app` of an `eqToHom` of functors against *any* other term for it — even a
term the elaborator accepts — is a **kernel deterministic timeout**, because `.app` of a stuck
`Eq.rec` is a projection the kernel cannot take and it unfolds the functor instead.  Two
arguments of one application that both mention that factor therefore cannot be combined.  With
the equality implicit the factor occurs in exactly one argument's type, is matched first-order,
and the conversion to a plain `eqToHom` — free on its own, by
`CategoryTheory.eqToHom_app` — happens here, at plain variables.  The reading comes before the
transport of the objects so that the two functors are read off it rather than guessed from the
transport, which would leave them as metavariables and put the reconciliation of the two
spellings of the composite back into the reading's own type. -/
public theorem reading_eqToHom {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} {E : F = G} (M : C) {X Y : D}
    {u : X ⟶ F.obj M} {v : G.obj M ⟶ Y} {Ξ : X ⟶ Y}
    (hΞ : Ξ = u ≫ (eqToHom E).app M ≫ v) (hΦ : F.obj M = G.obj M) :
    Ξ = u ≫ eqToHom hΦ ≫ v := by
  rw [hΞ, eqToHom_app]

/-- **An identity involving a transport of objects, pushed through two functors.**  If `u`
followed by a transport of its target factors as `p ≫ q`, then the same holds after applying `F`
and then `G`, for any transport of the images.

True by `subst` on the transported equality, at plain variables.  **Both equalities are
arguments, and no family of objects indexed by a type appears**: at the geometric
instance, a version taking `A : ι → C` and the index equality — so that the transports
are `congrArg A h` — makes the single application a **kernel deterministic timeout**, with the
cost in checking a lambda family under its binder.  The same application with the family removed
is free.  **The factorisation comes before the transport**, so that the two objects are pinned by
it: with the transport first the objects are metavariables when its type is checked, and the
instance is a 200 000-heartbeat `isDefEq` timeout. -/
public theorem map_map_comp_eqToHom {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X Y Z Z' : C}
    {u : X ⟶ Z} {p : X ⟶ Y} {q : Y ⟶ Z'} {hA : Z = Z'}
    (key : u ≫ eqToHom hA = p ≫ q)
    (hΔ : G.obj (F.obj Z) = G.obj (F.obj Z')) :
    G.map (F.map u) ≫ eqToHom hΔ = G.map (F.map p) ≫ G.map (F.map q) := by
  subst hA
  simp only [eqToHom_refl, Category.comp_id] at key ⊢
  rw [key, F.map_comp, G.map_comp]

/-- **The first half of carrying the square comparison across the transport**: the square
comparison, followed by the composition comparison of the second route and the transport at its
composite, is the inner square comparison between the two transports of the second legs.

Read against the geometric instance: `x` is the inverse image along the left edge of the
transport at the right-hand morphism, `Ξ` the square comparison, `c₁` and `c₂` the composition
comparisons of the two routes around the square, `ε` the transport along the commutativity of
the square, `τb` and `τJ` the transports at the two second legs, `t₁` and `t₂` the transports at
the two composites, `k₁` and `k₂` the two inner composition comparisons, `δ` the transport of
the inner objects along the commutativity, and `π` the inner square comparison.

The hypotheses are: two cancellations, which say that `x` and `c₂` are invertible with the given
inverses; the reading of `Ξ` as the two composition comparisons with the transport `ε` between
them (`hΞ`); the transport identity (`hmid`); the identification of the inner square comparison
(`hπ`); and the composition law for the first route (`hL1`).

**The invertible morphisms are taken as pairs of morphisms with their cancellations, not as
`CategoryTheory.Iso`s**, and that is not cosmetic either: at the geometric instance every one of
them is the `hom` or `inv` of an isomorphism carried by a functor or read at an object, so an
`Iso`-valued argument would be a `CategoryTheory.Functor.mapIso`, a `CategoryTheory.Iso.symm` or
a `CategoryTheory.Iso.app` wrapper, and the stored proof term would differ from the existing
statements by projections the kernel has to take.  Taking the morphisms means every argument is
a subterm of an existing statement and the five cancellations are existing lemmas too.

Every morphism is implicit, determined by the hypothesis naming it, so no argument at the point
of use is a restatement.

**What this signature does not do on its own.**  `ε` occurs in two
hypotheses, `hΞ` and `hmid`, so applying this lemma directly makes the kernel convert the
reading's transport into the transport identity's.  At the geometric instance of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareTransportAgreement.lean` those two are the
same `eqToHom` with its endpoints spelled through the two different spellings of the composite
round the square, and **that conversion is a kernel deterministic timeout** — while forcing the
same two spellings to be reconciled at the level of the *objects* alone costs nothing.  The same
holds of `δ`, which occurs in `hmid` and `hπ`.  A consumer therefore applies
`Stacks.CategoryTheory.square_transport_aux_of_mid` instead, which reaches `ε` through
`Stacks.CategoryTheory.mid_eq_of_reading` and takes `δ` twice. -/
public theorem square_transport_aux {C : Type*} [Category* C]
    {Pobj Q D₁ D₂ T W W' Zobj A : C}
    {x : Pobj ⟶ Q} {x' : Q ⟶ Pobj} {c₂ : T ⟶ D₂} {c₂' : D₂ ⟶ T} {t₂ : D₂ ⟶ W'}
    {Ξ : Q ⟶ T} {c₁ : Q ⟶ D₁} {ε : D₁ ⟶ D₂} {t₁ : D₁ ⟶ W} {δ : W ⟶ W'}
    {τb : Pobj ⟶ Zobj} {k₁ : Zobj ⟶ W} {k₂ : A ⟶ W'} {π : Zobj ⟶ A}
    (hx : x ≫ x' = 𝟙 Pobj) (hc' : c₂' ≫ c₂ = 𝟙 D₂)
    (hΞ : Ξ = c₁ ≫ ε ≫ c₂')
    (hmid : t₁ ≫ δ = ε ≫ t₂)
    (hπ : k₁ ≫ δ = π ≫ k₂)
    (hL1 : x' ≫ τb ≫ k₁ = c₁ ≫ t₁) :
    (x ≫ Ξ) ≫ c₂ ≫ t₂ = τb ≫ π ≫ k₂ := by
  calc (x ≫ Ξ) ≫ c₂ ≫ t₂
      = x ≫ c₁ ≫ ε ≫ (c₂' ≫ c₂) ≫ t₂ := by
          rw [hΞ]; simp only [Category.assoc]
    _ = x ≫ (c₁ ≫ t₁) ≫ δ := by
          rw [hc', Category.id_comp, ← hmid]; simp only [Category.assoc]
    _ = x ≫ (x' ≫ τb ≫ k₁) ≫ δ := by rw [hL1]
    _ = (x ≫ x') ≫ τb ≫ k₁ ≫ δ := by simp only [Category.assoc]
    _ = τb ≫ π ≫ k₂ := by rw [hx, Category.id_comp, hπ]

/-- **A two-step split cancellation absorbs on the right.**  If `c₂` and `t₂` have the one-sided
inverses `c₂'` and `t₂'`, then post-composing with `c₂ ≫ t₂` and then with `t₂' ≫ c₂'` leaves a
morphism unchanged.  This is how `c₂ ≫ t₂` is cancelled from the right of an equation. -/
public theorem comp_split_cancel_right {C : Type*} [Category* C] {Pobj T D₂ W' : C}
    {c₂ : T ⟶ D₂} {c₂' : D₂ ⟶ T} {t₂ : D₂ ⟶ W'} {t₂' : W' ⟶ D₂}
    (hc : c₂ ≫ c₂' = 𝟙 T) (ht : t₂ ≫ t₂' = 𝟙 D₂) (f : Pobj ⟶ T) :
    f ≫ c₂ ≫ t₂ ≫ t₂' ≫ c₂' = f := by
  rw [← Category.assoc t₂, ht, Category.id_comp, hc, Category.comp_id]

/-- Cancelling `c₂ ≫ t₂` from the right, given `k₂` spelled through it. -/
private theorem eq_of_comp_cancel_right_aux {C : Type*} [Category* C]
    {Pobj Q T D₂ U W' Zobj A : C}
    {x : Pobj ⟶ Q} {Ξ : Q ⟶ T} {c₂ : T ⟶ D₂} {c₂' : D₂ ⟶ T} {t₂ : D₂ ⟶ W'} {t₂' : W' ⟶ D₂}
    {y : U ⟶ T} {τJ' : A ⟶ U} {τb : Pobj ⟶ Zobj} {k₂ : A ⟶ W'} {π : Zobj ⟶ A}
    (haux : (x ≫ Ξ) ≫ c₂ ≫ t₂ = τb ≫ π ≫ k₂) (hk : k₂ = τJ' ≫ y ≫ c₂ ≫ t₂)
    (hc : c₂ ≫ c₂' = 𝟙 T) (ht : t₂ ≫ t₂' = 𝟙 D₂) :
    x ≫ Ξ = τb ≫ π ≫ τJ' ≫ y := by
  rw [← comp_split_cancel_right hc ht (x ≫ Ξ),
    ← comp_split_cancel_right hc ht (τb ≫ π ≫ τJ' ≫ y)]
  simp only [Category.assoc, reassoc_of% haux, hk]

/-- **The square comparison is carried across the transport**, from
`Stacks.CategoryTheory.square_transport_aux` and the composition law for the second route.

The remaining hypotheses are the cancellations saying that `c₂`, `t₂`, `y` and `τJ` are
invertible with the given inverses, and the composition law `hL2` for the route round the square
whose second leg is `τJ`. -/
public theorem square_transport_of_aux {C : Type*} [Category* C]
    {Pobj Q D₂ T U W' Zobj A : C}
    {x : Pobj ⟶ Q} {c₂ : T ⟶ D₂} {c₂' : D₂ ⟶ T} {t₂ : D₂ ⟶ W'} {t₂' : W' ⟶ D₂}
    {y : U ⟶ T} {y' : T ⟶ U} {τJ : U ⟶ A} {τJ' : A ⟶ U}
    {Ξ : Q ⟶ T} {τb : Pobj ⟶ Zobj} {k₂ : A ⟶ W'} {π : Zobj ⟶ A}
    (hc : c₂ ≫ c₂' = 𝟙 T) (ht : t₂ ≫ t₂' = 𝟙 D₂)
    (hy : y ≫ y' = 𝟙 U) (hτ : τJ' ≫ τJ = 𝟙 A)
    (hL2 : y' ≫ τJ ≫ k₂ = c₂ ≫ t₂)
    (haux : (x ≫ Ξ) ≫ c₂ ≫ t₂ = τb ≫ π ≫ k₂) :
    x ≫ Ξ = τb ≫ π ≫ τJ' ≫ y := by
  refine eq_of_comp_cancel_right_aux haux ?_ hc ht
  rw [← hL2]
  simp only [reassoc_of% hy, reassoc_of% hτ]

/-- **The square comparison is carried across the transport, with the reading of the square
comparison already substituted into the goal.**

The two halves above, combined, with no variable for the square comparison: its reading is
`c₁ ≫ ε ≫ c₂'` on the nose.  This is the form a consumer uses after rewriting the proved reading
into its goal, which is the one way of consuming that reading the kernel can check — see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareTransportAgreement.lean`. -/
public theorem square_transport_eq_of_reading {C : Type*} [Category* C]
    {Pobj Q D₁ D₂ T U W W' Zobj A : C}
    {x : Pobj ⟶ Q} {x' : Q ⟶ Pobj} {c₂ : T ⟶ D₂} {c₂' : D₂ ⟶ T}
    {t₂ : D₂ ⟶ W'} {t₂' : W' ⟶ D₂} {y : U ⟶ T} {y' : T ⟶ U} {τJ : U ⟶ A} {τJ' : A ⟶ U}
    {c₁ : Q ⟶ D₁} {ε : D₁ ⟶ D₂} {t₁ : D₁ ⟶ W} {δ : W ⟶ W'}
    {τb : Pobj ⟶ Zobj} {k₁ : Zobj ⟶ W} {k₂ : A ⟶ W'} {π : Zobj ⟶ A}
    (hx : x ≫ x' = 𝟙 Pobj) (hc : c₂ ≫ c₂' = 𝟙 T) (hc' : c₂' ≫ c₂ = 𝟙 D₂)
    (ht : t₂ ≫ t₂' = 𝟙 D₂) (hy : y ≫ y' = 𝟙 U) (hτ : τJ' ≫ τJ = 𝟙 A)
    (hmid : t₁ ≫ δ = ε ≫ t₂) (hπ : k₁ ≫ δ = π ≫ k₂)
    (hL1 : x' ≫ τb ≫ k₁ = c₁ ≫ t₁) (hL2 : y' ≫ τJ ≫ k₂ = c₂ ≫ t₂) :
    x ≫ c₁ ≫ ε ≫ c₂' = τb ≫ π ≫ τJ' ≫ y :=
  square_transport_of_aux hc ht hy hτ hL2 (square_transport_aux hx hc' rfl hmid hπ hL1)

/-! ### Reaching the middle factor without ever converting one transport into another

The six lemmas below are what a geometric instantiation of the three above actually consumes, and
their shape is forced by one observation, made at the instance of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareTransportAgreement.lean` and recorded in that
file's implementation notes: when two proved statements name **one morphism** in two
definitionally equal but syntactically different spellings, forcing an application to share it is
a kernel deterministic timeout if the morphism occurs inside a **composite**, and free if it
occurs as one side of an `Eq`.

So a shared morphism is never shared here: it is **supplied, with its identification as a
separate hypothesis** — which is what the `m`/`hm` pairs of
`Stacks.CategoryTheory.comp₃_mid_eq_of` and `Stacks.CategoryTheory.cancel_left_of_comp₃` are for
— and the transport of the square's commutativity is removed from every composite altogether by
`Stacks.CategoryTheory.mid_eq_of_reading`, which solves the reading for it. -/

/-- **An equal morphism substituted for the middle factor of a three-fold composite.**

True by `subst` at plain variables.  It exists so that a consumer supplies the middle factor
itself, in the spelling the statement it must match uses, instead of inheriting the spelling of
the equation `h`: the identification `hm` is then an equation between two morphisms directly
under `Eq`, which is free, whereas sharing the morphism inside the composite is a kernel
deterministic timeout. -/
public theorem comp₃_mid_eq_of {C : Type*} [Category* C] {X Y Z W : C}
    {u : X ⟶ Y} {v : Y ⟶ Z} {w : Z ⟶ W} {t : X ⟶ W}
    (h : u ≫ v ≫ w = t) (m : Y ⟶ Z) (hm : m = v) : u ≫ m ≫ w = t := by
  subst hm
  exact h

/-- **A three-factor reading solved for its middle factor.**  If `Ξ` is `c₁ ≫ ε ≫ c₂'` and `c₁`
and `c₂'` have the one-sided inverses `c₁'` and `c₂`, then `ε` is `c₁' ≫ Ξ ≫ c₂`.

The right-hand side mentions no transport, and that is the point.  At the geometric instance `ε`
is a `CategoryTheory.eqToHom` of the commutativity of the square read at one module, and the two
statements that mention it spell its endpoints through the two different spellings of the square's
composite.  An `eqToHom` inside a composite whose endpoints have to be reconciled is a kernel
deterministic timeout; the same `eqToHom` as one side of an `Eq` — which is all it is here — is
free.  Replacing `ε` by this composite therefore makes every later step transport-free. -/
public theorem mid_eq_of_reading {C : Type*} [Category* C] {Q D₁ D₂ T : C}
    {Ξ : Q ⟶ T} {c₁ : Q ⟶ D₁} {c₁' : D₁ ⟶ Q} {ε : D₁ ⟶ D₂} {c₂' : D₂ ⟶ T} {c₂ : T ⟶ D₂}
    (hcc' : c₁' ≫ c₁ = 𝟙 D₁) (hc' : c₂' ≫ c₂ = 𝟙 D₂) (hΞ : Ξ = c₁ ≫ ε ≫ c₂') :
    c₁' ≫ Ξ ≫ c₂ = ε := by
  calc c₁' ≫ Ξ ≫ c₂
      = (c₁' ≫ c₁) ≫ ε ≫ c₂' ≫ c₂ := by rw [hΞ]; simp only [Category.assoc]
    _ = ε ≫ c₂' ≫ c₂ := by rw [hcc', Category.id_comp]
    _ = ε := by rw [hc', Category.comp_id]

/-- **The first half of carrying the square comparison across the transport, with the middle
factor reached through `Stacks.CategoryTheory.mid_eq_of_reading` rather than shared.**

This is `Stacks.CategoryTheory.square_transport_aux` with the reading replaced by the equation
`hs` that solves it for `ε`, and with the transport `δ` of the inner objects **taken twice**, as
`δ` and `δ₂`, with the identification `hδ`.  Both changes are necessary at
the geometric instance:

* `hmid` comes **first**, so that the objects `D₁` and `D₂` are read off the transport identity,
  whose statement cannot be respelled, and the reading's spelling of them — which can — is the
  one reconciled;
* `δ` occurs in `hmid` and in `hπ` in two syntactically different spellings, and sharing it is a
  kernel deterministic timeout while `hδ` is free. -/
public theorem square_transport_aux_of_mid {C : Type*} [Category* C]
    {Pobj Q D₁ D₂ T W W' Zobj A : C}
    {t₁ : D₁ ⟶ W} {δ δ₂ : W ⟶ W'} {ε : D₁ ⟶ D₂} {t₂ : D₂ ⟶ W'}
    {c₁ : Q ⟶ D₁} {c₁' : D₁ ⟶ Q} {Ξ : Q ⟶ T} {c₂ : T ⟶ D₂} {c₂' : D₂ ⟶ T}
    {x : Pobj ⟶ Q} {x' : Q ⟶ Pobj}
    {τb : Pobj ⟶ Zobj} {k₁ : Zobj ⟶ W} {k₂ : A ⟶ W'} {π : Zobj ⟶ A}
    (hmid : t₁ ≫ δ = ε ≫ t₂) (hs : c₁' ≫ Ξ ≫ c₂ = ε)
    (hc' : c₂' ≫ c₂ = 𝟙 D₂) (hL1 : x' ≫ τb ≫ k₁ = c₁ ≫ t₁)
    (hπ : k₁ ≫ δ₂ = π ≫ k₂) (hδ : δ₂ = δ)
    (hx : x ≫ x' = 𝟙 Pobj) (hcc : c₁ ≫ c₁' = 𝟙 Q) (hc : c₂ ≫ c₂' = 𝟙 T) :
    (x ≫ Ξ) ≫ c₂ ≫ t₂ = τb ≫ π ≫ k₂ := by
  subst hδ
  have hΞ : Ξ = c₁ ≫ ε ≫ c₂' := by
    rw [← hs]
    simp only [Category.assoc, reassoc_of% hcc, hc, Category.comp_id]
  exact square_transport_aux hx hc' hΞ hmid hπ hL1

/-- **The first factor of a three-fold composite cancelled against a one-sided inverse, with the
middle factor supplied.**  The middle factor is taken as `m` with its identification `hm`, for the
reason `Stacks.CategoryTheory.comp₃_mid_eq_of` exists. -/
public theorem cancel_left_of_comp₃ {C : Type*} [Category* C] {T D₂ U W' A : C}
    {y : U ⟶ T} {y' : T ⟶ U} {v : U ⟶ A} {w : A ⟶ W'} {c₂ : T ⟶ D₂} {t₂ : D₂ ⟶ W'}
    (h : y' ≫ v ≫ w = c₂ ≫ t₂) (hy : y ≫ y' = 𝟙 U) (m : U ⟶ A) (hm : m = v) :
    m ≫ w = y ≫ c₂ ≫ t₂ := by
  subst hm
  rw [← h, ← Category.assoc, hy, Category.id_comp]

/-- **A two-fold composite solved for its last factor, using a one-sided inverse of its
first.** -/
public theorem eq_comp_of_cancel_left {C : Type*} [Category* C] {T D₂ U W' A : C}
    {y : U ⟶ T} {v : U ⟶ A} {v' : A ⟶ U} {w : A ⟶ W'} {c₂ : T ⟶ D₂} {t₂ : D₂ ⟶ W'}
    (h : v ≫ w = y ≫ c₂ ≫ t₂) (hv : v' ≫ v = 𝟙 A) : w = v' ≫ y ≫ c₂ ≫ t₂ := by
  rw [← h, ← Category.assoc, hv, Category.id_comp]

/-- **The second half of carrying the square comparison across the transport**: a composite
`c₂ ≫ t₂` whose two factors have one-sided inverses is cancelled from the right of an equation.

This is `Stacks.CategoryTheory.square_transport_of_aux` with its composition law for the second
route and the cancellation of that route's second leg already combined into the single hypothesis
`hk`, by `Stacks.CategoryTheory.cancel_left_of_comp₃` and
`Stacks.CategoryTheory.eq_comp_of_cancel_left`.  The regrouping is not cosmetic: at the geometric
instance the composition law and that cancellation name the transport at the second leg in two
syntactically different spellings, so an application holding both is a kernel deterministic
timeout, while combining them one at a time — where the spelling is supplied — is free. -/
public theorem eq_of_comp_cancel_right {C : Type*} [Category* C] {Pobj Q T D₂ U W' Zobj A : C}
    {x : Pobj ⟶ Q} {Ξ : Q ⟶ T} {c₂ : T ⟶ D₂} {c₂' : D₂ ⟶ T} {t₂ : D₂ ⟶ W'} {t₂' : W' ⟶ D₂}
    {y : U ⟶ T} {τJ' : A ⟶ U} {τb : Pobj ⟶ Zobj} {k₂ : A ⟶ W'} {π : Zobj ⟶ A}
    (haux : (x ≫ Ξ) ≫ c₂ ≫ t₂ = τb ≫ π ≫ k₂) (hk : k₂ = τJ' ≫ y ≫ c₂ ≫ t₂)
    (hc : c₂ ≫ c₂' = 𝟙 T) (ht : t₂ ≫ t₂' = 𝟙 D₂) :
    x ≫ Ξ = τb ≫ π ≫ τJ' ≫ y :=
  eq_of_comp_cancel_right_aux haux hk hc ht

end Stacks.CategoryTheory

end

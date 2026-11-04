module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Pointwise products, pullbacks and pushouts of functors

For functors `D ⥤ C` into a category with the relevant limits or colimits, the product, the fibre
product and the pushout in the functor category are computed pointwise. Applied to
`D = SimplexCategory` or its opposite, this gives products, fibre products and pushouts of
(co)simplicial objects.
-/

/-!
## Pointwise products of functors

Let `C` be a category, let `D` be an index category and let `F G : D ⥤ C` be functors such that
the product `F d ⨯ G d` exists in `C` for every `d`. The *pointwise product* of `F` and `G` is
the functor `d ↦ F d ⨯ G d` acting on `φ : d ⟶ d'` by `F φ ⨯ G φ`. It is a product of `F` and
`G` in the functor category `D ⥤ C`: a morphism `W ⟶ F × G` is the same thing as a pair of
morphisms `W ⟶ F` and `W ⟶ G`, that is `Mor(W, F × G) = Mor(W, F) × Mor(W, G)`.

Nothing in either statement uses the simplex category, so both are given for an arbitrary index
category `D`. Taking `D = Δ` they are the product of two cosimplicial objects of `C` and its
universal property, [Stacks, Tag 016Z] and [Stacks, Tag 0170]; taking `D = Δᵒᵖ` they are the
same two facts for simplicial objects.

### Main definitions

* `CategoryTheory.Limits.pointwiseProd`: the functor `d ↦ F.obj d ⨯ G.obj d`,
  `f ↦ prod.map (F.map f) (G.map f)`. Its two defining clauses are available as the `simps`
  lemmas `pointwiseProd_obj` and `pointwiseProd_map`, so no user of it needs to unfold it.

### Main results

* `CategoryTheory.Limits.pointwiseProdIsProd`: the binary fan on `F`, `G` with point
  `pointwiseProd F G` and projections given degreewise by `prod.fst` and `prod.snd` is a limit.
  In particular `F` and `G` have a product in `D ⥤ C`, it is computed pointwise, and the
  source's bijection `Mor(W, F × G) = Mor(W, F) × Mor(W, G)` follows by
  `BinaryFan.IsLimit.lift'` together with `BinaryFan.IsLimit.hom_ext`.

### Implementation notes

The hypothesis is only that the pointwise products `F d ⨯ G d` exist, never `HasBinaryProducts C`
and — this being the point of the lemma — never that `F` and `G` have a product in `D ⥤ C`. That
is what distinguishes these results from Mathlib's, which reach the same conclusion from a global
hypothesis on `C`: `CategoryTheory.Limits.instHasFiniteProductsFunctor` assumes
`HasFiniteProducts C` and `CategoryTheory.Limits.evaluationPreservesLimits` assumes `HasLimits C`.
The products are taken in `C` and nowhere else.

The source writes the universal property as an equality of hom-sets; Mathlib's spelling of "this
cone is universal" is `IsLimit`, which is data rather than a proposition (compare
`CategoryTheory.Limits.prodIsProd`, of which `pointwiseProdIsProd` is the pointwise analogue), so
it is a `def`. That is the stronger and more usable form: the hom-set bijection is recovered from
it for every `W`, whereas from the bare bijections one would have to rebuild the limit structure.

Rather than fixing one natural transformation `pointwiseProd F G ⟶ F` — necessarily built by hand
from `prod.fst` and its naturality — the two projections are taken as arguments `π₁`, `π₂`
characterised by their components. Any two natural transformations with those components are
equal, so nothing is lost, and a caller with projections already in hand can apply the result to
them without an intervening rewrite.

The one step of the argument that is not a projection identity is the naturality of the degreewise
lift, isolated as `comp_lift_eq_lift_comp_map` and stated for arbitrary objects and morphisms of
`C`: a square commuting after composing with `u` and with `v` commutes after composing with
`prod.map u v`. Mathlib has no lemma of that shape; `prod.comp_lift` and `prod.lift_map`, of which
it is the composite, are its two halves.

### References

* [Stacks, Tag 016Z](https://stacks.math.columbia.edu/tag/016Z)
* [Stacks, Tag 0170](https://stacks.math.columbia.edu/tag/0170)
-/

section

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The **pointwise product** of two functors `F G : D ⥤ C`, defined when the products
`F.obj d ⨯ G.obj d` exist in `C`: it sends `d` to `F.obj d ⨯ G.obj d` and a morphism
`f : d ⟶ d'` to `prod.map (F.map f) (G.map f)`.

For `D = SimplexCategory` this is the product `U × V` of two cosimplicial objects `U`, `V`
of `C` of [Stacks, Tag 016Z]. It is the product formed pointwise in `C`, not by definition a
product in the category `D ⥤ C`; that it is one is `pointwiseProdIsProd`, [Stacks, Tag 0170]. -/
@[stacks 016Z, simps, ega "0 8.2.1" "more general", ega "I 3.3.2" "more general"]
def pointwiseProd (F G : D ⥤ C) [∀ d, HasBinaryProduct (F.obj d) (G.obj d)] : D ⥤ C where
  obj d := F.obj d ⨯ G.obj d
  map f := prod.map (F.map f) (G.map f)
  map_id d := by simp
  map_comp f g := by simp

/-- A commuting square whose vertical maps are `u` and `v` composes with `prod.map u v`: if
`g ≫ a' = a ≫ u` and `g ≫ b' = b ≫ v`, then
`g ≫ prod.lift a' b' = prod.lift a b ≫ prod.map u v`. -/
@[ega "0 8.2.5" "more general"]
private lemma comp_lift_eq_lift_comp_map {W W' X Y X' Y' : C} [HasBinaryProduct X Y]
    [HasBinaryProduct X' Y'] {g : W ⟶ W'} {a : W ⟶ X} {b : W ⟶ Y} {a' : W' ⟶ X'} {b' : W' ⟶ Y'}
    {u : X ⟶ X'} {v : Y ⟶ Y'} (ha : g ≫ a' = a ≫ u) (hb : g ≫ b' = b ≫ v) :
    g ≫ prod.lift a' b' = prod.lift a b ≫ prod.map u v := by
  rw [prod.comp_lift, prod.lift_map, ha, hb]

/-- **The pointwise product of two functors is their product**, [Stacks, Tag 0170]: for functors
`F G : D ⥤ C` whose pointwise products exist, the binary fan on `F` and `G` with point the
pointwise product `pointwiseProd F G` of [Stacks, Tag 016Z] and with projections `π₁`, `π₂`
given degreewise by `prod.fst` and `prod.snd` is a limit. Thus `F` and `G` have a product in
`D ⥤ C`, computed pointwise, and `Mor(W, F × G) = Mor(W, F) × Mor(W, G)` for every functor `W`.

For `D = Δ` this is the statement that the product `U × V` of two cosimplicial objects of `C`
is the product in the category of cosimplicial objects of `C`. -/
@[stacks 0170 "stated for an arbitrary index category `D`: the product of cosimplicial objects \
  is the case `D = SimplexCategory`, that of simplicial objects the case `D = SimplexCategoryᵒᵖ`",
  ega "0 8.2.1" "more general"]
def pointwiseProdIsProd (F G : D ⥤ C)
    [∀ d, HasBinaryProduct (F.obj d) (G.obj d)]
    (π₁ : pointwiseProd F G ⟶ F) (π₂ : pointwiseProd F G ⟶ G)
    (h₁ : ∀ d, π₁.app d = prod.fst) (h₂ : ∀ d, π₂.app d = prod.snd) :
    IsLimit (BinaryFan.mk π₁ π₂) :=
  BinaryFan.isLimitMk
    (fun s =>
      { app := fun d => prod.lift (s.fst.app d) (s.snd.app d)
        naturality := fun _ _ f => by
          exact comp_lift_eq_lift_comp_map (s.fst.naturality f) (s.snd.naturality f) })
    (fun s => by
      ext d
      dsimp only [NatTrans.comp_app]
      rw [h₁ d]
      exact prod.lift_fst _ _)
    (fun s => by
      ext d
      dsimp only [NatTrans.comp_app]
      rw [h₂ d]
      exact prod.lift_snd _ _)
    (fun _ m hm₁ hm₂ => by
      ext d
      have e₁ := congrArg (fun t => NatTrans.app t d) hm₁
      have e₂ := congrArg (fun t => NatTrans.app t d) hm₂
      dsimp only [NatTrans.comp_app] at e₁ e₂
      rw [h₁ d] at e₁
      rw [h₂ d] at e₂
      exact prod.hom_ext (e₁.trans (prod.lift_fst _ _).symm)
        (e₂.trans (prod.lift_snd _ _).symm))

end CategoryTheory.Limits

end

end

/-!
## The action on morphisms of a degreewise product of functors

Let `C` be a category, let `U` and `V` be cosimplicial objects of `C`, that is, functors `Δ ⥤ C`,
and assume the products `Uₙ ⨯ Vₙ` exist in `C` for every object `n` of `Δ`. The *product of `U`
and `V`* is the cosimplicial object which is `Uₙ ⨯ Vₙ` in degree `n` and which sends
`φ : [n] ⟶ [m]` to `U(φ) ⨯ V(φ)`.

The second of those two clauses is a consequence of the first together with the two projections,
and that is what is proved here: if `P` is a cosimplicial object equipped with maps `π₁ : P ⟶ U`
and `π₂ : P ⟶ V` whose degreewise comparison map `prod.lift (π₁ₙ) (π₂ₙ) : Pₙ ⟶ Uₙ ⨯ Vₙ` is an
isomorphism, then `P(φ)` is `U(φ) ⨯ V(φ)` read through those isomorphisms. So a cosimplicial
object which is degreewise the product of `U` and `V` over its two projections is the product of
`U` and `V`, and the definition may speak of *the* product.

Nothing in the statement uses the simplex category, so it is given for functors `F G : D ⥤ C` over
an arbitrary index category `D`; the cosimplicial case is `D = Δ` and the simplicial case
`D = Δᵒᵖ`.

### Main results

* `CategoryTheory.Limits.map_eq_prod_lift_comp_prod_map_comp_inv`: for natural transformations
  `π₁ : P ⟶ F` and `π₂ : P ⟶ G` between functors `D ⥤ C` whose degreewise products
  `F.obj d ⨯ G.obj d` exist, and `φ : d ⟶ d'` with `prod.lift (π₁.app d') (π₂.app d')` an
  isomorphism, `P.map φ = prod.lift (π₁.app d) (π₂.app d) ≫ prod.map (F.map φ) (G.map φ) ≫
  inv (prod.lift (π₁.app d') (π₂.app d'))`.

### Implementation notes

The first clause is spelled "the comparison map `prod.lift (π₁.app d) (π₂.app d)` is an
isomorphism" rather than "`P.obj d = F.obj d ⨯ G.obj d`": an equality of objects would put an
`eqToHom` in every use of the second clause, and the comparison map is what the identification of
`P.obj d` with `F.obj d ⨯ G.obj d` amounts to once the projections of `P` are named. Only
invertibility at the target `d'` is assumed, since that is all the equation uses.

The only hypothesis on `C` is the existence of the degreewise products: neither
`HasBinaryProducts C` nor the existence of a product of `F` and `G` in `D ⥤ C` is assumed.

Mathlib's `CategoryTheory.Limits.prodComparison_natural` is the corresponding square for the
comparison map `H.obj (A ⨯ B) ⟶ H.obj A ⨯ H.obj B` of a single functor `H`; here the comparison
map is assembled degreewise from two natural transformations out of `P` instead, and being an
isomorphism it is inverted rather than left on the other side of the square.

### References

* [Stacks, Tag 016Z](https://stacks.math.columbia.edu/tag/016Z)
-/

section

@[expose] public section

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **The product of two cosimplicial objects acts on morphisms by the product of the maps**,
[Stacks, Tag 016Z]: let `F G P : D ⥤ C` be functors such that the products `F.obj d ⨯ G.obj d`
exist in `C`, let `π₁ : P ⟶ F` and `π₂ : P ⟶ G` be natural transformations, and let `φ : d ⟶ d'`
be a morphism such that the comparison map `prod.lift (π₁.app d') (π₂.app d')` is an isomorphism.
Then `P.map φ` is `prod.map (F.map φ) (G.map φ)`, read through the comparison maps at `d` and
`d'`.

So the second clause of the definition of the product of `F` and `G` holds of every functor which
is degreewise the product over its two projections. The functor of the definition itself is
`pointwiseProd F G`, and that it is a product in `D ⥤ C` is `pointwiseProdIsProd`. -/
@[stacks 016Z "the definition's second clause, stated for an arbitrary functor satisfying the \
  first: it is forced by the degrees and the two projections. Stated over an arbitrary index \
  category `D`: the product of two cosimplicial objects is the case `D = SimplexCategory` and \
  that of simplicial objects the case `D = SimplexCategoryᵒᵖ`"]
theorem map_eq_prod_lift_comp_prod_map_comp_inv {F G P : D ⥤ C}
    [∀ d, HasBinaryProduct (F.obj d) (G.obj d)] (π₁ : P ⟶ F) (π₂ : P ⟶ G) {d d' : D} (φ : d ⟶ d')
    [IsIso (prod.lift (π₁.app d') (π₂.app d'))] :
    P.map φ = prod.lift (π₁.app d) (π₂.app d) ≫ prod.map (F.map φ) (G.map φ) ≫
      inv (prod.lift (π₁.app d') (π₂.app d')) := by
  rw [← Category.assoc, IsIso.eq_comp_inv]
  simp

end CategoryTheory.Limits

end

end

/-!
## Fibre products of cosimplicial objects: pointwise pullbacks in a functor category

Let `C` be a category, let `D` be an index category and let `f : F ⟶ H` and `g : G ⟶ H` be
morphisms of functors `D ⥤ C` such that the pullback `F d ×_{H d} G d` exists in `C` for every
object `d` of `D`. Then `d ↦ F d ×_{H d} G d` is again a functor `D ⥤ C`: a morphism
`φ : d ⟶ d'` of `D` acts by the morphism `F φ ×_{H φ} G φ` induced on the pullbacks by the
naturality squares of `f` and of `g`, and this assignment is functorial because the induced
morphisms compose (`CategoryTheory.Limits.pullback.map_comp`) and the identity induces the
identity (`CategoryTheory.Limits.pullback.map_id`).

For `D = Δ` — so that `F`, `G` and `H` are cosimplicial objects `V`, `W` and `U` of `C` and
`f`, `g` are morphisms `a : V ⟶ U`, `b : W ⟶ U` — this is the *fibre product of `V` and `W`
over `U`* of [Stacks, Tag 0172]: it is the cosimplicial object with
`(V ×_U W)_n = V_n ×_{U_n} W_n` and with `(V ×_U W)(φ) = V(φ) ×_{U(φ)} W(φ)` for every
`φ : ⦋n⦌ ⟶ ⦋m⦌`, on the nose. For `D = Δᵒᵖ` the same functor is the fibre product of simplicial
objects of [Stacks, Tag 016T], whose faces and degeneracies are then `d^n_i = (d^n_i, d^n_i)`
and `s^n_i = (s^n_i, s^n_i)`, these being the morphisms induced on the pullbacks.

### Main definitions

* `CategoryTheory.Limits.pointwisePullback`: the functor `d ↦ F d ×_{H d} G d` attached to a
  cospan `f : F ⟶ H`, `g : G ⟶ H` of natural transformations all of whose pointwise pullbacks
  exist; the fibre product of cosimplicial objects, resp. of simplicial objects, is the case
  `D = Δ`, resp. `D = Δᵒᵖ`. Its `@[simps]` lemmas `pointwisePullback_obj` and
  `pointwisePullback_map` are the two clauses of the source, so no user of it needs to unfold it.

### Implementation notes

Nothing in the construction uses the index category, so it is stated for an arbitrary `D` rather
than for `SimplexCategory`, and one declaration then carries both the cosimplicial fibre product
of the source and the simplicial one of [Stacks, Tag 016T]. The hypothesis is the source's and no
more: only the pointwise pullbacks `F d ×_{H d} G d` are assumed to exist, as an instance
argument `[∀ d, HasPullback (f.app d) (g.app d)]`, and neither `HasPullbacks C` nor a pullback of
`f` and `g` in the functor category `D ⥤ C` is required.

What the source warns of is not that the fibre product in the category of cosimplicial objects
may fail to exist: under the hypothesis above the pointwise pullback cones combine into a
limiting cone on `f`, `g` in `D ⥤ C` (`Limits.PullbackCone.combineIsLimit`) whose point agrees
objectwise with this functor, and that limit is the universal property
`Mor(T, V ×_U W) = Mor(T, V) ×_{Mor(T, U)} Mor(T, W)` of [Stacks, Tag 0173]. What may fail is
that a fibre product be *described* degreewise, and Mathlib's `pullback f g` is not: when `C` has
pullbacks it agrees with the degreewise object only up to the isomorphism
`Limits.pullbackObjIso f g d`. So the degreewise object is the one defined here, and for it the
two clauses of the source hold as equalities.

### References

* [Stacks, Tag 0172](https://stacks.math.columbia.edu/tag/0172)
* [Stacks, Tag 016T](https://stacks.math.columbia.edu/tag/016T)
-/

section

@[expose] public section

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F G H : D ⥤ C}

/-- **Stacks 0172.** The fibre product of cosimplicial objects, as a pointwise pullback in a
functor category. Given a cospan `f : F ⟶ H`, `g : G ⟶ H` of morphisms of functors `D ⥤ C` all
of whose pointwise pullbacks `F d ×_{H d} G d` exist, `pointwisePullback f g` is the functor
`d ↦ F d ×_{H d} G d`, a morphism `φ : d ⟶ d'` acting by the morphism `F φ ×_{H φ} G φ` that
`F φ`, `G φ` and `H φ` induce on the pullbacks. For cosimplicial objects `U`, `V`, `W` of `C`
and `a : V ⟶ U`, `b : W ⟶ U`, so for `D = Δ`, this is the fibre product `V ×_U W`, with
`(V ×_U W)_n = V_n ×_{U_n} W_n` and `(V ×_U W)(φ) = V(φ) ×_{U(φ)} W(φ)`; for simplicial objects,
so for `D = Δᵒᵖ`, it is the fibre product of [Stacks, Tag 016T]. -/
@[stacks 0172 "stated for an arbitrary index category `D`: the fibre product of cosimplicial \
  objects is the case `D = SimplexCategory`, and that of simplicial objects, Tag 016T, the \
  case `D = SimplexCategoryᵒᵖ`", simps]
noncomputable def pointwisePullback (f : F ⟶ H) (g : G ⟶ H)
    [∀ d, HasPullback (f.app d) (g.app d)] : D ⥤ C where
  obj d := pullback (f.app d) (g.app d)
  map φ := pullback.map _ _ _ _ (F.map φ) (G.map φ) (H.map φ)
    (f.naturality φ).symm (g.naturality φ).symm
  map_id d := by simp only [Functor.map_id, pullback.map_id]
  map_comp φ ψ := by simp only [Functor.map_comp, pullback.map_comp]

end CategoryTheory.Limits

end

end

/-!
## Pushouts of simplicial objects: pointwise pushouts in a functor category

Let `C` be a category, let `D` be an index category and let `f : F ⟶ G` and `g : F ⟶ H` be
morphisms of functors `D ⥤ C` such that the pushout `G d ⨿_{F d} H d` exists in `C` for every
object `d` of `D`. Then `d ↦ G d ⨿_{F d} H d` is again a functor `D ⥤ C`: a morphism
`φ : d ⟶ d'` of `D` acts by the morphism `G φ ⨿_{F φ} H φ` induced on the pushouts by the
naturality squares of `f` and of `g`, and this assignment is functorial because the induced
morphisms compose (`CategoryTheory.Limits.pushout.map_comp`) and the identity induces the
identity (`CategoryTheory.Limits.pushout.map_id`).

For `D = Δᵒᵖ` — so that `F`, `G` and `H` are simplicial objects `U`, `V` and `W` of `C` and
`f`, `g` are morphisms `a : U ⟶ V`, `b : U ⟶ W` — this is the *pushout of `V` and `W` over `U`*
of [Stacks, Tag 016W]: it is the simplicial object with `(V ⨿_U W)_n = V_n ⨿_{U_n} W_n` whose
faces and degeneracies are `d^n_i = (d^n_i, d^n_i)` and `s^n_i = (s^n_i, s^n_i)`, these being
the morphisms induced on the pushouts, on the nose; equivalently, it is the pushout of the
presheaves `V` and `W` over `U` on `Δ`, formed degreewise. For `D = Δ` the same functor is the
pushout of cosimplicial objects.

### Main definitions

* `CategoryTheory.Limits.pointwisePushout`: the functor `d ↦ G d ⨿_{F d} H d` attached to a
  span `f : F ⟶ G`, `g : F ⟶ H` of natural transformations all of whose pointwise pushouts
  exist; the pushout of simplicial objects, resp. of cosimplicial objects, is the case
  `D = Δᵒᵖ`, resp. `D = Δ`. Its `@[simps]` lemmas `pointwisePushout_obj` and
  `pointwisePushout_map` are clauses (1) and (2)–(3) of the source, so no user of it needs to
  unfold it.

### Implementation notes

Nothing in the construction uses the index category, so it is stated for an arbitrary `D` rather
than for `SimplexCategoryᵒᵖ`, and one declaration then carries both the simplicial pushout of the
source and the cosimplicial one. It is the dual of `CategoryTheory.Limits.pointwisePullback`, the
fibre product of [Stacks, Tag 0172] and [Stacks, Tag 016T]. The hypothesis is the source's and no
more: only the pointwise pushouts `G d ⨿_{F d} H d` are assumed to exist, as an instance argument
`[∀ d, HasPushout (f.app d) (g.app d)]`, and neither `HasPushouts C` nor a pushout of `f` and `g`
in the functor category `D ⥤ C` is required.

What the source warns of is not that the pushout in the category of simplicial objects may fail
to exist: the pointwise pushout cocones assemble into a colimiting cocone on `f`, `g` in `D ⥤ C`,
because a cocone there is colimiting as soon as it is so objectwise
(`Limits.evaluationJointlyReflectsColimits`), and that colimit is the universal property
`Mor(V ⨿_U W, T) = Mor(V, T) ×_{Mor(U, T)} Mor(W, T)` of [Stacks, Tag 016X]. What may fail is
that a pushout be *described* degreewise, and Mathlib's `pushout f g` is not: when `C` has
pushouts it agrees with the degreewise object only up to the isomorphism
`Limits.pushoutObjIso f g d`. So the degreewise object is the one defined here, and for it the
clauses of the source hold as equalities.

### References

* [Stacks, Tag 016W](https://stacks.math.columbia.edu/tag/016W)
* [Stacks, Tag 016X](https://stacks.math.columbia.edu/tag/016X)
-/

section

@[expose] public section

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F G H : D ⥤ C}

/-- **Stacks 016W.** The pushout of simplicial objects, as a pointwise pushout in a functor
category. Given a span `f : F ⟶ G`, `g : F ⟶ H` of morphisms of functors `D ⥤ C` all of whose
pointwise pushouts `G d ⨿_{F d} H d` exist, `pointwisePushout f g` is the functor
`d ↦ G d ⨿_{F d} H d`, a morphism `φ : d ⟶ d'` acting by the morphism `G φ ⨿_{F φ} H φ` that
`G φ`, `H φ` and `F φ` induce on the pushouts. For simplicial objects `U`, `V`, `W` of `C` and
`a : U ⟶ V`, `b : U ⟶ W`, so for `D = Δᵒᵖ`, this is the pushout `V ⨿_U W`, with
`(V ⨿_U W)_n = V_n ⨿_{U_n} W_n`, `d^n_i = (d^n_i, d^n_i)` and `s^n_i = (s^n_i, s^n_i)`; for
cosimplicial objects, so for `D = Δ`, it is their pushout. It is the dual of
`pointwisePullback`. -/
@[stacks 016W "stated for an arbitrary index category `D`: the pushout of simplicial objects \
  is the case `D = SimplexCategoryᵒᵖ`, and that of cosimplicial objects the case \
  `D = SimplexCategory`", simps]
noncomputable def pointwisePushout (f : F ⟶ G) (g : F ⟶ H)
    [∀ d, HasPushout (f.app d) (g.app d)] : D ⥤ C where
  obj d := pushout (f.app d) (g.app d)
  map φ := pushout.map _ _ _ _ (G.map φ) (H.map φ) (F.map φ)
    (f.naturality φ).symm (g.naturality φ).symm
  map_id d := by simp only [Functor.map_id, pushout.map_id]
  map_comp φ ψ := by simp only [Functor.map_comp, pushout.map_comp]

end CategoryTheory.Limits

end

end

module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.EpiMono

/-!
# A natural isomorphism from termwise isomorphisms normalized by an epimorphic cone

Two functors `F G : D ⥤ C` that receive a common object `P` by families of morphisms compatible
with their transition maps, with the family into `F` epimorphic, are isomorphic as soon as there
are termwise isomorphisms carrying one family to the other. Naturality is then automatic: the
square may be cancelled on the left by the epimorphism out of `P`.

This is the device that makes an inverse system identified termwise into an inverse system
identified as a functor. Both of its uses in this library -- the terms of an adic completion
against a given system, and the sheaf quotient tower on the complement of a closed subscheme
against the sheafification of an algebraic one -- supply `P` as the object being completed and
`p` as its projections, which are epimorphisms because the terms are quotients of it.

## Main definitions

* `CategoryTheory.natIsoOfEpiNormalizedCone`
-/

@[expose] public section

namespace CategoryTheory

/-- **Termwise isomorphisms normalized by an epimorphic cone give a natural isomorphism.** Given
functors `F G : D ⥤ C`, an object `P`, families `p n : P ⟶ F.obj n` and `q n : P ⟶ G.obj n`
compatible with the transition maps of `F` and of `G`, with every `p n` an epimorphism, and
termwise isomorphisms `e n : F.obj n ≅ G.obj n` carrying `p` to `q`, the `e n` assemble into an
isomorphism `F ≅ G`. -/
public def natIsoOfEpiNormalizedCone {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : D ⥤ C} (P : C) (p : ∀ n, P ⟶ F.obj n) (q : ∀ n, P ⟶ G.obj n)
    (hp : ∀ {m n : D} (f : m ⟶ n), p m ≫ F.map f = p n)
    (hq : ∀ {m n : D} (f : m ⟶ n), q m ≫ G.map f = q n)
    (hep : ∀ n, Epi (p n)) (e : ∀ n, F.obj n ≅ G.obj n)
    (he : ∀ n, p n ≫ (e n).hom = q n) : F ≅ G :=
  NatIso.ofComponents e (fun {i j} f => by
    have := hep i
    refine (cancel_epi (p i)).1 ?_
    rw [← Category.assoc, ← Category.assoc, hp, he, he, hq])

end CategoryTheory

end

module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local injectivity and surjectivity transport along natural bijections

Let `(C, J)` be a site, let `φ : F ⟶ G` be a map of presheaves of types and let `φ' : F' ⟶ G'` be
another one, with its values in a *different* `Type` universe. Suppose the two are identified by
bijections on sections, natural in the object of `C` — that is, suppose there are natural
bijections `F ≃ F'` and `G ≃ G'` carrying `φ` to `φ'`. Then `φ'` is locally injective, resp.
locally surjective, as soon as `φ` is.

The point is the change of universe. Two maps of presheaves valued in one universe are compared
by an isomorphism in the functor category, and `CategoryTheory.Presheaf.IsLocallyInjective` and
`.IsLocallySurjective` are then transported by the existing lemmas about composition with an
isomorphism. Across universes there is no isomorphism to form: `F` and `F'` are not objects of one
functor category. But the two conditions are conditions on *sieves*, and the sieves in question —
`CategoryTheory.Presheaf.equalizerSieve` and `CategoryTheory.Presheaf.imageSieve` — are carried to
each other *on the nose* by a natural family of bijections, so the transport needs no universe
hypothesis and no `UnivLE`.

This is what compares the two clauses of Stacks 02ZN for a 1-morphism of fibred categories with
the two clauses for its morphism-universe lift: the morphism presheaves of the lift take their
values one universe up, and the bijections identifying them are
`CategoryTheory.BasedCategory.Equivalence.morSectionEquiv`, which exists precisely because it is
stated as a bijection on sections rather than as an isomorphism of presheaves.

## Main results

* `CategoryTheory.Presheaf.isLocallyInjective_of_natEquiv`
* `CategoryTheory.Presheaf.isLocallySurjective_of_natEquiv`

## Implementation notes

Both proofs identify the relevant sieve of `φ'` with that of `φ` by `CategoryTheory.Sieve.ext`
and then appeal to the hypothesis; neither produces a new covering sieve. Naturality of each
family of bijections is taken as a hypothesis in the forward direction only, which is the form
`CategoryTheory.BasedCategory.Equivalence.morSectionEquiv_naturality` has.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

@[expose] public section

namespace CategoryTheory.Presheaf

open Opposite

universe w w' v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {F G : Cᵒᵖ ⥤ Type w} {F' G' : Cᵒᵖ ⥤ Type w'} (φ : F ⟶ G) (φ' : F' ⟶ G')
  (α : ∀ X : Cᵒᵖ, F.obj X ≃ F'.obj X) (β : ∀ X : Cᵒᵖ, G.obj X ≃ G'.obj X)

/-- **Local injectivity transports along natural bijections on sections**, with no hypothesis
relating the two `Type` universes: the equalizer sieve of two sections of `F'` is literally the
equalizer sieve of their preimages in `F`. -/
theorem isLocallyInjective_of_natEquiv
    (hα : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X), α Y (F.map f x) = F'.map f (α X x))
    (hsq : ∀ (X : Cᵒᵖ) (x : F.obj X), φ'.app X (α X x) = β X (φ.app X x))
    [IsLocallyInjective J φ] : IsLocallyInjective J φ' where
  equalizerSieve_mem {X} x' y' h := by
    have hxy : φ.app X ((α X).symm x') = φ.app X ((α X).symm y') := by
      refine (β X).injective ?_
      rwa [← hsq X ((α X).symm x'), ← hsq X ((α X).symm y'),
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hsieve : equalizerSieve x' y' =
        equalizerSieve (F := F) ((α X).symm x') ((α X).symm y') := by
      refine Sieve.ext fun Y f => ⟨fun hf => (α (op Y)).injective ?_, fun hf => ?_⟩
      · rwa [hα f.op, hα f.op, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      · have hf' := congrArg (α (op Y)) hf
        rwa [hα f.op, hα f.op, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hf'
    exact hsieve ▸ equalizerSieve_mem J φ _ _ hxy

/-- **Local surjectivity transports along natural bijections on sections**, with no hypothesis
relating the two `Type` universes: the image sieve of a section of `G'` is literally the image
sieve of its preimage in `G`. -/
theorem isLocallySurjective_of_natEquiv
    (hβ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : G.obj X), β Y (G.map f s) = G'.map f (β X s))
    (hsq : ∀ (X : Cᵒᵖ) (x : F.obj X), φ'.app X (α X x) = β X (φ.app X x))
    [IsLocallySurjective J φ] : IsLocallySurjective J φ' where
  imageSieve_mem {U} s' := by
    have hsieve : imageSieve φ' s' = imageSieve φ ((β (op U)).symm s') := by
      refine Sieve.ext fun V i => ?_
      constructor
      · rintro ⟨t', ht'⟩
        refine ⟨(α (op V)).symm t', (β (op V)).injective ?_⟩
        rw [← hsq (op V) ((α (op V)).symm t'), Equiv.apply_symm_apply, ht',
          hβ i.op ((β (op U)).symm s'), Equiv.apply_symm_apply]
      · rintro ⟨t, ht⟩
        refine ⟨α (op V) t, ?_⟩
        rw [hsq (op V) t, ht, hβ i.op ((β (op U)).symm s'), Equiv.apply_symm_apply]
    exact hsieve ▸ imageSieve_mem J φ _

end CategoryTheory.Presheaf

end

module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import StacksCore.CategoryTheory.FiberedInGroupoids

/-!
# A terminal object of a category fibred in groupoids forces the inertia to be trivial

Let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids (Stacks 003S). If `𝒮` has a terminal object
then every *vertical* endomorphism of `𝒮` — every `σ : y ⟶ y` with `p σ = 𝟙` — is the identity;
that is, the inertia of `p` (Stacks 042I) is trivial. The same holds for a terminal object of any
category mapping faithfully to `𝒮`, in particular of a full subcategory of `𝒮`.

The reason is the fill-in clause of `Functor.IsFiberedInGroupoids`: a vertical `σ : y ⟶ y` and
the identity of `y` are two solutions of one and the same fill-in problem for any morphism
`φ : y ⟶ x`, provided `σ ≫ φ = φ`; and `σ ≫ φ = φ` is automatic when `x` is terminal, there
being only one morphism `y ⟶ x` at all. So the fill-in clause identifies them.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.eq_id_of_comp_eq`: a vertical endomorphism
  absorbed by some morphism out of its object is the identity.
* `CategoryTheory.Functor.IsFiberedInGroupoids.eq_id_of_isTerminal` and
  `CategoryTheory.Functor.IsFiberedInGroupoids.eq_id_of_isTerminal_of_faithful`: triviality of
  the vertical endomorphisms, from a terminal object of `𝒮` and from a terminal object of a
  category mapping faithfully to `𝒮`.
* `CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_ne_id` and
  `CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id`: the
  contrapositives — a single nontrivial vertical endomorphism rules out a terminal object
  everywhere. (`Limits.IsTerminal` is data, not a proposition, so the conclusion is stated as
  `IsEmpty`.)

## Why this is worth stating

Terminality of an object is the hypothesis through which the comparison of cohomology along a
functor of sites identifies the two unit objects: it is what
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso` and
`CategoryTheory.Functor.final_of_isTerminal_obj` consume, hence what
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic` and
`Stacks.Cohomology.BiggerSiteModules.moduleCohomologyIsoOfAcyclic` ask for. For the fppf or étale
site of a category fibred in groupoids over the big fppf site of a scheme — and for the full
subsites of Stacks 0787 — the statements below say that hypothesis holds *only* in the inertia-free
case, that is, only when the fibre groupoids are discrete. It is therefore not available for a
general algebraic stack, and the comparison of global cohomology of Stacks 0GR0 (1)(a), (2)(a)
cannot be obtained by instantiating those two engines at a terminal object. It is available over
an *object*: the slice `𝒮/x` has the terminal object `𝟙 x` whatever the inertia of `p`, which is
why parts (1)(b) and (2)(b) of Stacks 0GR0 go through
(`AlgebraicGeometry.Stack.subsiteCohomologyOverObjectIso`).

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 042I](https://stacks.math.columbia.edu/tag/042I)
-/

@[expose] public section

namespace CategoryTheory.Functor.IsFiberedInGroupoids

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S] {p : S ⥤ C}

/-- **A vertical endomorphism absorbed by a morphism out of its object is the identity.** If
`p` is fibred in groupoids, `φ : y ⟶ x` is a morphism of `𝒮` and `σ : y ⟶ y` lies over the
identity and satisfies `σ ≫ φ = φ`, then `σ = 𝟙 y`.

Both `σ` and `𝟙 y` solve the fill-in problem of `Functor.IsFiberedInGroupoids.unique_lift` for
the pair `(φ, φ)` over `𝟙 (p y)`, which has exactly one solution.

This is Mathlib's `CategoryTheory.IsCartesian.ext` for the cartesian morphism `φ` — every
morphism of a category fibred in groupoids is strongly cartesian,
`Functor.IsFiberedInGroupoids.isStronglyCartesian` — specialized to `ψ = σ`, `ψ' = 𝟙 y`. It is
taken from the `unique_lift` field directly rather than through that route because the route
needs two `Functor.IsHomLift` instances built by hand from `hσ`, which is more work than the
fill-in clause itself. -/
theorem eq_id_of_comp_eq (hp : p.IsFiberedInGroupoids) {x y : S} (φ : y ⟶ x) (σ : y ⟶ y)
    (hσ : p.map σ = 𝟙 (p.obj y)) (hcomp : σ ≫ φ = φ) : σ = 𝟙 y := by
  obtain ⟨_, _, huniq⟩ := hp.unique_lift φ φ (𝟙 (p.obj y)) (Category.id_comp _)
  exact (huniq σ ⟨hσ, hcomp⟩).trans (huniq (𝟙 y) ⟨p.map_id y, Category.id_comp φ⟩).symm

/-- **A terminal object of a category fibred in groupoids forces the vertical endomorphisms to
be trivial.** If `p` is fibred in groupoids and `𝒮` has a terminal object, then every `σ : y ⟶ y`
lying over an identity is the identity.

There is only one morphism `y ⟶ x` into a terminal object, so `σ ≫ φ = φ` for the unique
`φ : y ⟶ x`, and `eq_id_of_comp_eq` applies. -/
theorem eq_id_of_isTerminal (hp : p.IsFiberedInGroupoids) {x y : S} (hx : Limits.IsTerminal x)
    (σ : y ⟶ y) (hσ : p.map σ = 𝟙 (p.obj y)) : σ = 𝟙 y :=
  hp.eq_id_of_comp_eq (hx.from y) σ hσ (hx.hom_ext _ _)

/-- **A single nontrivial vertical endomorphism rules out a terminal object.** If `p` is fibred
in groupoids and some object of `𝒮` carries an endomorphism over an identity which is not the
identity, then no object of `𝒮` is terminal. -/
theorem not_isTerminal_of_ne_id (hp : p.IsFiberedInGroupoids) {y : S} (σ : y ⟶ y)
    (hσ : p.map σ = 𝟙 (p.obj y)) (hne : σ ≠ 𝟙 y) (x : S) : IsEmpty (Limits.IsTerminal x) :=
  ⟨fun hx ↦ hne (hp.eq_id_of_isTerminal hx σ hσ)⟩

section Faithful

variable {T : Type u₃} [Category.{v₃} T] (ι : T ⥤ S) [ι.Faithful]

/-- **A terminal object of a category mapping faithfully to `𝒮` forces the vertical
endomorphisms of that category to be trivial.** If `p` is fibred in groupoids, `ι : 𝒯 ⥤ 𝒮` is
faithful and `𝒯` has a terminal object, then every `σ : y ⟶ y` in `𝒯` whose image lies over an
identity is the identity.

This is the form the statement takes for a *full subcategory* `𝒯 ⊆ 𝒮` — the shape of the
lisse-étale and flat-fppf subsites of Stacks 0787: the fill-in clause is used in `𝒮`, where `p`
is fibred in groupoids, and terminality is used in `𝒯`, where the subsite's would-be terminal
object would live. -/
theorem eq_id_of_isTerminal_of_faithful (hp : p.IsFiberedInGroupoids) {x y : T}
    (hx : Limits.IsTerminal x) (σ : y ⟶ y)
    (hσ : p.map (ι.map σ) = 𝟙 (p.obj (ι.obj y))) : σ = 𝟙 y := by
  refine ι.map_injective ?_
  rw [ι.map_id]
  refine hp.eq_id_of_comp_eq (ι.map (hx.from y)) (ι.map σ) hσ ?_
  rw [← ι.map_comp, hx.hom_ext (σ ≫ hx.from y) (hx.from y)]

/-- **A single nontrivial vertical endomorphism of `𝒯` rules out a terminal object of `𝒯`.** The
contrapositive of `eq_id_of_isTerminal_of_faithful`: for a faithful `ι : 𝒯 ⥤ 𝒮` over a category
fibred in groupoids `p`, one endomorphism of an object of `𝒯` which lies over an identity and is
not the identity forbids a terminal object of `𝒯`. -/
theorem not_isTerminal_of_faithful_of_ne_id (hp : p.IsFiberedInGroupoids) {y : T} (σ : y ⟶ y)
    (hσ : p.map (ι.map σ) = 𝟙 (p.obj (ι.obj y))) (hne : σ ≠ 𝟙 y) (x : T) :
    IsEmpty (Limits.IsTerminal x) :=
  ⟨fun hx ↦ hne (hp.eq_id_of_isTerminal_of_faithful ι hx σ hσ)⟩

end Faithful

end CategoryTheory.Functor.IsFiberedInGroupoids

end

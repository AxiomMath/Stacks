module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Strict functoriality of pushforward of modules on a scheme

Pushforward of sheaves of modules along a morphism of schemes is *strictly* functorial:
`Scheme.Modules.pushforward (u ≫ b)` and `Scheme.Modules.pushforward u ⋙
Scheme.Modules.pushforward b` are the same functor, and `Scheme.Modules.pushforward (𝟙 X)` is
the identity functor, both on the nose. Consequently the comparison isomorphisms
`Scheme.Modules.pushforwardId` and `Scheme.Modules.pushforwardComp` have identity components,
and so does `Scheme.Modules.pushforwardCongr` applied to a reflexivity proof. This file records
those identities, which turn a composite of coherence comparisons into a composite of
identities.

## Main results

* `Stacks.Modules.pushforward_id_eq`, `Stacks.Modules.pushforward_comp_eq`: the two strict
  functoriality identities, as equalities of functors.
* `Stacks.Modules.pushforward_id_obj`, `Stacks.Modules.pushforward_id_map`: pushforward along
  an identity is the identity functor.
* `Stacks.Modules.pushforward_comp_obj`, `Stacks.Modules.pushforward_comp_map`: pushforward
  along a composite is the composite of the pushforwards.
* `Stacks.Modules.pushforwardId_inv_app`, `Stacks.Modules.pushforwardComp_hom_app`,
  `Stacks.Modules.pushforwardCongr_rfl_inv_app`: the components of the three comparison
  isomorphisms are identities.
* `Stacks.Modules.pushforwardCongr_inv_app`: the component of the comparison of pushforwards
  along *equal* morphisms is the transport along that equality.

## Implementation notes

Mathlib states the first two families only after evaluating at an open, as
`Scheme.Modules.pushforwardId_inv_app_app` and
`Scheme.Modules.pushforwardComp_hom_app_app`. The unevaluated forms here are what a rewrite
needs when the comparison appears inside a composite of module morphisms rather than inside a
composite of maps of sections: the evaluated forms have a source and a target that agree only
up to unfolding the identity or composite morphism of schemes, so rewriting with them produces
a term whose type is correct only at full transparency.

Everything except `pushforwardCongr_rfl_inv_app` holds by `rfl`. That one needs
`CategoryTheory.Functor.map_id`, because the component of `pushforwardCongr` is the action of
the module presheaf on an identity inclusion of opens rather than an identity.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Modules

universe u

variable {X Y Z : Scheme.{u}}

/-- Pushforward along an identity is literally the identity functor. -/
public lemma pushforward_id_eq :
    Scheme.Modules.pushforward (𝟙 X) = 𝟭 X.Modules := rfl

/-- Pushforward along a composite is literally the composite of the pushforwards: Mathlib's
`Scheme.Modules.pushforward` is a *strict* functor in the morphism. -/
public lemma pushforward_comp_eq (u : X ⟶ Y) (b : Y ⟶ Z) :
    Scheme.Modules.pushforward (u ≫ b) =
      Scheme.Modules.pushforward u ⋙ Scheme.Modules.pushforward b := rfl

/-- Pushforward along an identity is the identity functor, on objects. -/
public lemma pushforward_id_obj (M : X.Modules) :
    (Scheme.Modules.pushforward (𝟙 X)).obj M = M := rfl

/-- Pushforward along an identity is the identity functor, on morphisms. -/
public lemma pushforward_id_map {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pushforward (𝟙 X)).map φ = φ := rfl

/-- Pushforward along a composite is the composite of the pushforwards, on objects. -/
public lemma pushforward_comp_obj (u : X ⟶ Y) (b : Y ⟶ Z) (M : X.Modules) :
    (Scheme.Modules.pushforward (u ≫ b)).obj M
      = (Scheme.Modules.pushforward b).obj ((Scheme.Modules.pushforward u).obj M) := rfl

/-- Pushforward along a composite is the composite of the pushforwards, on morphisms. -/
public lemma pushforward_comp_map (u : X ⟶ Y) (b : Y ⟶ Z) {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pushforward (u ≫ b)).map φ
      = (Scheme.Modules.pushforward b).map ((Scheme.Modules.pushforward u).map φ) := rfl

/-- The comparison of the identity functor with pushforward along an identity is the
identity. -/
public lemma pushforwardId_inv_app (X : Scheme.{u}) (M : X.Modules) :
    (Scheme.Modules.pushforwardId X).inv.app M = 𝟙 _ := rfl

/-- The comparison of a composite of pushforwards with the pushforward along the composite is
the identity. -/
public lemma pushforwardComp_hom_app (u : X ⟶ Y) (b : Y ⟶ Z) (M : X.Modules) :
    (Scheme.Modules.pushforwardComp u b).hom.app M = 𝟙 _ := rfl

/-- The comparison of pushforwards along a morphism with itself is the identity. -/
public lemma pushforwardCongr_rfl_inv_app (u : X ⟶ Y) (M : X.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : u = u)).inv.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  simp

/-- The comparison of the pushforwards along two *equal* morphisms is the transport along that
equality. The reflexivity case is `pushforwardCongr_rfl_inv_app`; this form is what a
coherence computation needs when the equality of morphisms is itself derived. -/
public lemma pushforwardCongr_inv_app {u v : X ⟶ Y} (h : u = v) (M : X.Modules) :
    (Scheme.Modules.pushforwardCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst h
  apply Scheme.Modules.hom_ext
  intro U
  simp

end Stacks.Modules

end

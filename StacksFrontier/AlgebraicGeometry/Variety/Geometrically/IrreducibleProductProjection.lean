module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import StacksCore.Tactic.StacksAttribute

/-!
# Irreducible components of a product with a geometrically irreducible factor

Let `k` be a field and let `X` and `Y` be schemes over `k`. If `X` is geometrically irreducible
over `k`, then the projection `p : X ×_k Y ⟶ Y` induces a bijection between the irreducible
components of `X ×_k Y` and those of `Y`, the component `Z` of the product going to its image
`p(Z)`.

## Main results

* `AlgebraicGeometry.bijOn_image_irreducibleComponents_pullback_snd`: taking images along the
  projection `X ×_k Y ⟶ Y` is a bijection from the irreducible components of `X ×_k Y` onto the
  irreducible components of `Y`.

## Implementation notes

A scheme over `k` is its structure morphism `f : X ⟶ Spec k`, the product `X ×_k Y` is the
categorical pullback of `f` along `g : Y ⟶ Spec k`, and the projection of the statement is
`pullback.snd f g`. The induced map on components is pinned rather than merely asserted to
exist: it is `fun Z ↦ (pullback.snd f g).base '' Z`, and the conclusion is a `Set.BijOn` for
that function between the two sets `irreducibleComponents _`. This says three things that a bare
equivalence of subtypes would not — that the image of a component is a component, that distinct
components have distinct images, and that every component of `Y` is hit — and it is the spelling
the sibling statements 037O and 038H already use in this library.

The source's proof has three inputs, and each is supplied by Mathlib rather than carried as a
hypothesis here.

* The scheme-theoretic fibres of `p` are irreducible, being base changes of the geometrically
  irreducible `X` by field extensions. Geometric irreducibility is
  `AlgebraicGeometry.GeometricallyIrreducible`, defined as irreducibility of every base change
  along a field-valued point, and it is stable under base change, so
  `GeometricallyIrreducible (pullback.snd f g)` is an instance given
  `GeometricallyIrreducible f`.
* The scheme-theoretic fibres are homeomorphic to the set-theoretic fibres [stacks, 01K1]. This
  is used inside `AlgebraicGeometry.Scheme.Hom.isIrreducible_preimage` through
  `AlgebraicGeometry.Scheme.Hom.range_fiberι`, which identifies the range of the inclusion of
  the scheme-theoretic fibre with the set-theoretic one; so 01K1 is discharged by Mathlib and
  does not appear as an assumption.
* The map `p` is open [stacks, 0383]. The structure morphism of a scheme over a field is
  universally open, which in Mathlib is the instance `AlgebraicGeometry.UniversallyOpen` for a
  morphism whose target is integral with a subsingleton underlying space — and `Spec k` is such
  a target. Universal openness is stable under base change, so `pullback.snd f g` is
  universally open and `AlgebraicGeometry.Scheme.Hom.isOpenMap` applies. This is where the
  hypothesis `Field k` is used; it is the only place, and dropping it would break the openness
  of `p`, which the conclusion needs.

The topological conclusion drawn from these, that an open continuous surjection with irreducible
fibres induces a bijection on irreducible components [stacks, 037A], is Mathlib's
`AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv`, itself built on
`irreducibleComponentsEquivOfIsPreirreducibleFiber`. Reading that equivalence of subtypes as a
`Set.BijOn` for the image map needs that images and preimages are mutually inverse on
components: `p ⁻¹' (p '' Z) = Z` for a component `Z` of the product is the round trip of the
equivalence, and `p '' (p ⁻¹' T) = T` is surjectivity of `p`, which geometric irreducibility
supplies.

Faithfulness to the source. The two schemes `X` and `Y` both occur in the conclusion, and the
geometric irreducibility of `X` cannot be weakened to irreducibility of `X`: for `k = ℚ` and
`X = Y = Spec ℚ(i)` the product `Spec (ℚ(i) ⊗[ℚ] ℚ(i))` has two irreducible components while
`Y` is a point, so no bijection exists. The statement is not vacuous: with `X` the affine line
over `k`, which is geometrically irreducible, and `Y` any scheme over `k`, both sides are
nonempty and the bijection is the projection's action on components.

## References

* [Stacks Project, Tag 038F](https://stacks.math.columbia.edu/tag/038F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- **Stacks 038F.** Let `k` be a field and let `X`, `Y` be schemes over `k`, presented by
their structure maps `f : X ⟶ Spec k` and `g : Y ⟶ Spec k`. If `X` is geometrically
irreducible over `k`, then `X ×_k Y ⟶ Y` induces a bijection between irreducible components:
taking images along it is a bijection from the irreducible components of `X ×_k Y` onto the
irreducible components of `Y`. -/
@[stacks 038F, ega "IV 4.5.8" "more general"]
public theorem bijOn_image_irreducibleComponents_pullback_snd
    (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [GeometricallyIrreducible f] :
    Set.BijOn (fun Z ↦ (pullback.snd f g).base '' Z)
      (irreducibleComponents (pullback (C := Scheme.{u}) f g))
      (irreducibleComponents Y) := by
  let p := pullback.snd f g
  let e := Scheme.Hom.irreducibleComponentsEquiv p p.isOpenMap
  exact Set.InvOn.bijOn (f' := (p.base ⁻¹' ·))
    ⟨fun _ hZ => congrArg Subtype.val (e.symm_apply_apply ⟨_, hZ⟩),
      fun _ _ => Set.image_preimage_eq _ p.surjective⟩
    (fun _ hZ => (e ⟨_, hZ⟩).2) fun _ hT => (e.symm ⟨_, hT⟩).2

end AlgebraicGeometry

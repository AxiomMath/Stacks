module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Groupoid schemes

A groupoid scheme over a scheme `S` consists of schemes of objects and arrows over `S`,
with source, target, composition, identity and inverse morphisms satisfying the groupoid
axioms on generalized points.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme` is a groupoid object in schemes over a fixed scheme.
* `Stacks.Groupoids.IsInvariantClosedSubscheme` is invariance of a closed subscheme of the
  object scheme under the arrows of a groupoid scheme.
* `Stacks.Groupoids.IsInvariantMonomorphism` is invariance of a monomorphism into the object
  scheme under the arrows of a groupoid scheme.

## Implementation notes

The source presents a groupoid scheme as the quintuple consisting of its objects, arrows,
source, target and composition, subject to being a groupoid after evaluation on every test
scheme. Its identity and inverse maps are then unique, and are bundled here as data; the
displayed axioms are the internal form of the pointwise groupoid axioms. Associativity and
preservation of composition are stated on generalized points, which avoids choosing a
particular model for the object of composable triples.

Invariance of a closed subscheme is an equality of scheme-theoretic inverse images rather
than only a condition on points; `Scheme.IdealSheafData.comap` is Mathlib's scheme-theoretic
inverse image of a closed subscheme.

Invariance of a monomorphism is the same kind of condition read in the subobject poset of the
arrow scheme: equality there of the two pullbacks says exactly that they are isomorphic over
the arrow scheme, which is equality of subschemes of it. The monomorphism is not asked to be
an immersion, and a subobject of the object scheme is tested by
`Stacks.Groupoids.IsInvariantMonomorphism` applied to its
`CategoryTheory.Subobject.arrow`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

/-- Two morphisms of `Over S` which agree on every generalized point are equal: it is enough to
test them on the identity of their source. The groupoid axioms below, and the lemmas about them,
are phrased on generalized points, and this is what turns such a phrasing back into an equality
of morphisms. -/
theorem overHom_ext {S : Scheme.{u}} {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ (T : Over S) (x : T ⟶ X), x ≫ f = x ≫ g) : f = g := by
  simpa using h X (𝟙 X)

/-- A groupoid object in schemes over `S`.

The fields `identity` and `inverse` are included as data, although they are uniquely determined
by `source`, `target` and `comp`. -/
@[stacks 0231 "part (1): groupoid schemes"]
structure GroupoidScheme (S : Scheme.{u}) where
  /-- The scheme of objects, as a scheme over `S`. -/
  objects : Over S
  /-- The scheme of arrows, as a scheme over `S`. -/
  arrows : Over S
  /-- The source of an arrow. -/
  source : arrows ⟶ objects
  /-- The target of an arrow. -/
  target : arrows ⟶ objects
  /-- Composition of composable arrows.  The first projection is the arrow applied last. -/
  comp : pullback source target ⟶ arrows
  /-- The identity arrow at an object. -/
  identity : objects ⟶ arrows
  /-- The inverse of an arrow. -/
  inverse : arrows ⟶ arrows
  source_identity : identity ≫ source = 𝟙 objects
  target_identity : identity ≫ target = 𝟙 objects
  source_inverse : inverse ≫ source = target
  target_inverse : inverse ≫ target = source
  source_comp : comp ≫ source = pullback.snd source target ≫ source
  target_comp : comp ≫ target = pullback.fst source target ≫ target
  left_identity : ∀ (T : Over S) (f : T ⟶ arrows)
      (w : (f ≫ target ≫ identity) ≫ source = f ≫ target),
    pullback.lift (f ≫ target ≫ identity) f w ≫ comp = f
  right_identity : ∀ (T : Over S) (f : T ⟶ arrows)
      (w : f ≫ source = (f ≫ source ≫ identity) ≫ target),
    pullback.lift f (f ≫ source ≫ identity) w ≫ comp = f
  left_inverse : ∀ (T : Over S) (f : T ⟶ arrows)
      (w : (f ≫ inverse) ≫ source = f ≫ target),
    pullback.lift (f ≫ inverse) f w ≫ comp = f ≫ source ≫ identity
  right_inverse : ∀ (T : Over S) (f : T ⟶ arrows)
      (w : f ≫ source = (f ≫ inverse) ≫ target),
    pullback.lift f (f ≫ inverse) w ≫ comp = f ≫ target ≫ identity
  assoc : ∀ (T : Over S) (f g h : T ⟶ arrows)
      (wfg : f ≫ source = g ≫ target) (wgh : g ≫ source = h ≫ target)
      (w₁ : (pullback.lift f g wfg ≫ comp) ≫ source = h ≫ target)
      (w₂ : f ≫ source = (pullback.lift g h wgh ≫ comp) ≫ target),
    pullback.lift (pullback.lift f g wfg ≫ comp) h w₁ ≫ comp =
      pullback.lift f (pullback.lift g h wgh ≫ comp) w₂ ≫ comp

/-- A closed subscheme of the objects of a groupoid scheme is invariant when its
scheme-theoretic inverse images along source and target agree. -/
@[stacks 03BC "part (3): invariant closed subschemes"]
abbrev IsInvariantClosedSubscheme {S : Scheme.{u}} (G : GroupoidScheme S)
    (Z : G.objects.left.IdealSheafData) : Prop :=
  Z.comap G.target.left = Z.comap G.source.left

/-- A monomorphism of schemes into the objects of a groupoid scheme is invariant when its
source and target pullbacks define the same subobject of the arrow scheme. -/
@[stacks 03BC "part (4): invariant monomorphisms"]
abbrev IsInvariantMonomorphism {S : Scheme.{u}} (G : GroupoidScheme S) {T : Scheme.{u}}
    (i : T ⟶ G.objects.left) [Mono i] : Prop :=
  (Subobject.pullback G.target.left).obj (Subobject.mk i) =
    (Subobject.pullback G.source.left).obj (Subobject.mk i)

/-- The identity section of the source of a groupoid scheme, on underlying schemes. -/
theorem identity_left_comp_source_left {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.identity.left ≫ G.source.left = 𝟙 G.objects.left := by
  rw [← Over.comp_left, G.source_identity, Over.id_left]

/-- The identity section of the target of a groupoid scheme, on underlying schemes. -/
theorem identity_left_comp_target_left {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.identity.left ≫ G.target.left = 𝟙 G.objects.left := by
  rw [← Over.comp_left, G.target_identity, Over.id_left]

end Stacks.Groupoids

end

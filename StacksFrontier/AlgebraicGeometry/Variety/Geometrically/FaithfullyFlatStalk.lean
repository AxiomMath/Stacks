module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Stalks

/-!
# Faithful flatness of stalk maps of flat morphisms

A flat morphism of schemes induces a faithfully flat map on local rings: the stalk map is a
flat homomorphism between local rings and is local, and a flat local homomorphism of local
rings is faithfully flat.

Specializing to the base change of a `k`-scheme along a field extension `K / k`, the local
ring of the base-changed scheme at a point `y` is faithfully flat over the local ring of the
original scheme at the image of `y`.

## Main results

* `AlgebraicGeometry.faithfullyFlat_stalkMap_fieldExtension`: for a field extension `K / k`
  and a `k`-scheme `X`, the map from the local ring of `X` at a point to the local ring of
  `X ×_{Spec k} Spec K` at any point above it is faithfully flat.

## Implementation notes

The base change is the categorical pullback of the structure morphism `X ⟶ Spec k` along
`Spec K ⟶ Spec k`. Flatness of the first projection comes from flatness of
`Spec K ⟶ Spec k`, which holds because every ring homomorphism out of a field is flat,
together with stability of flatness under base change. The hypothesis that `y` lies above
`x` is transported by an `eqToHom` between the two stalks of `X`.

## References

* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Every ring homomorphism out of a field is flat, so the morphism of spectra induced by a
field extension `K / k` is a flat morphism of schemes. -/
public lemma flat_spec_map_algebraMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  Flat.SpecMap_iff.2 (RingHom.Flat.of_isField (Field.toIsField k) _)

/-- For an extension of fields `K / k`, the map on local rings from a point of a `k`-scheme
to a point above it after base change to `K` is faithfully flat. -/
@[stacks 0C4Y "faithfully_flat_local"]
public theorem faithfullyFlat_stalkMap_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    ((eqToHom (congrArg X.presheaf.stalk hy.symm)) ≫
      (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom.FaithfullyFlat := by
  subst hy
  have := flat_spec_map_algebraMap k K
  simpa using Flat.faithfullyFlat_stalkMap
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y

end AlgebraicGeometry

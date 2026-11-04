module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import StacksFrontier.RingTheory.NodalCurve

/-!
# The normalisation of a single branch of the node is submersive

Let `k` be a field, let `A = {g ∈ k[t] ∣ g(0) = g(1)}` be the node — the affine line with the two
points `t = 0` and `t = 1` glued — and let `B = k[t, 1/t]` be the affine line with `t = 0`
removed. This file proves that

`f : Spec B ⟶ Spec A`

is **submersive**, i.e. a quotient map of underlying topological spaces. In fact it is a
homeomorphism: `StacksFrontier/RingTheory/NodalCurve.lean` already shows the map on prime spectra is
a closed embedding, and what is added here is that it is surjective, which upgrades a closed
embedding to a homeomorphism and in particular to a quotient map. Surjectivity is the point of
the construction: the prime `(t)` of `k[t]` is the one lost by inverting `t`, and the node has
already glued it to `(t − 1)`, which survives.

This `f` is the morphism of the counterexample to the Stacks Project tag 0EZK as the source
writes it, recorded as a *Stacks erratum* in the docstrings of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso`. It is submersive, as proved
here, but **not** universally submersive: base changing along the connected étale double cover
`T = Spec A[z]/(z² + z + a)` with `a = t² + t`, built in
`StacksFrontier/Examples/Algebra/NodeArtinSchreierEtaleCover.lean`, splits `T ×_S X` into two copies
of `X`, so the base change is bijective but not a homeomorphism. That is exactly the step of the
source's proof which submersivity alone does not license.

## Scope

**Nothing here refutes the tag**, and no declaration carries a Stacks tag. This closes one of the
two hypotheses the refutation must verify about `f`; the other, that the geometric fibres of `f`
are connected, is not proved here or elsewhere in the tree.

## Main results

* `Stacks.NodalCurve.surjective_comap_localizationAway` — `Spec B → Spec A` is surjective.
* `Stacks.NodalCurve.isQuotientMap_comap_localizationAway` — it is a quotient map of prime
  spectra.
* `Stacks.NodalCurve.nodeNormalization` — the morphism of affine schemes.
* `Stacks.NodalCurve.isQuotientMap_nodeNormalization` — it is submersive, in the spelling
  `(topologically Topology.IsQuotientMap)` that Stacks 0EZK uses.

## References

* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

@[expose] public noncomputable section

open Polynomial PrimeSpectrum CategoryTheory AlgebraicGeometry
open CategoryTheory.MorphismProperty

universe u

namespace Stacks.NodalCurve

variable (k : Type u) [Field k]

/-- The image of `Spec B → Spec k[t]` is the complement of the prime `(t)`: inverting `t` keeps
exactly the primes that do not contain it. -/
private theorem range_comap_localizationAway :
    Set.range (comap (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)))) =
      {P : PrimeSpectrum (Polynomial k) | (X : Polynomial k) ∉ P.asIdeal} := by
  rw [localization_away_comap_range (Localization.Away (X : Polynomial k)) (X : Polynomial k)]
  ext P
  simp

/-- **`Spec B → Spec A` is surjective.** It factors as `Spec B → Spec k[t] → Spec A`, the first
map landing on the complement of `(t)`, and the image of that complement in `Spec A` is
everything, because the node glues `(t)` to `(t − 1)`. -/
public theorem surjective_comap_localizationAway :
    Function.Surjective
      (comap (algebraMap (nodeRing k) (Localization.Away (X : Polynomial k)))) := by
  have hcomp : algebraMap (nodeRing k) (Localization.Away (X : Polynomial k)) =
      (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))).comp
        (algebraMap (nodeRing k) (Polynomial k)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [← Set.range_eq_univ, hcomp, comap_comp, Set.range_comp,
    range_comap_localizationAway]
  exact comap_nodeRingSubtype_image_eq_univ k

/-- **`Spec B → Spec A` is a quotient map.** It is a closed embedding
(`Stacks.NodalCurve.isClosedEmbedding_comap_localizationAway`) and surjective, hence a closed
continuous surjection, hence a quotient map — indeed a homeomorphism. -/
public theorem isQuotientMap_comap_localizationAway :
    Topology.IsQuotientMap
      (comap (algebraMap (nodeRing k) (Localization.Away (X : Polynomial k)))) :=
  (isClosedEmbedding_comap_localizationAway k).isClosedMap.isQuotientMap
    (continuous_comap _) (surjective_comap_localizationAway k)

/-- The morphism of affine schemes `f : Spec B ⟶ Spec A` induced by the inclusion `A ⊆ B` of the
node into the punctured affine line. -/
public def nodeNormalization :
    Spec (CommRingCat.of (Localization.Away (X : Polynomial k))) ⟶
      Spec (CommRingCat.of (nodeRing k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (nodeRing k) (Localization.Away (X : Polynomial k))))

/-- **`f` is submersive.** The underlying map of topological spaces is `comap` of `A → B`, which
is a quotient map. This is hypothesis (1) of Stacks 0EZK as the source states it. -/
public theorem isQuotientMap_nodeNormalization :
    (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}) (nodeNormalization k) :=
  isQuotientMap_comap_localizationAway k

end Stacks.NodalCurve

end

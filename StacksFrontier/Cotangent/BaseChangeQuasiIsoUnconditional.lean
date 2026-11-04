module

public import StacksFrontier.Cotangent.AnyResolutionQuasiIso

/-!
# Lemma 08QQ with Remark 08QI supplied

`StacksFrontier.Cotangent.BaseChangeQuasiIso` proves [Stacks, Tag 08QQ] on the
alternating-face-map complexes, on the cotangent complexes and in `D(B')` under Remark 08QI in
the form `CommAlgCat.CotangentComputedByEveryResolution A' B'`, taken as a parameter. That
remark is proved, as `CommAlgCat.cotangentComputedByEveryResolution` of
`StacksFrontier.Cotangent.AnyResolutionQuasiIso`, for every ring map; this file supplies it, so the
statements here take exactly the source's hypothesis `B ⊗_A^L A' = B'`, written out as the
vanishing of the positive `Tor_i^A(A', B)` together with bijectivity of `A' ⊗_A B → B'`.

## Main results

* `CommAlgCat.quasiIso_cotangentExtendScalarsMooreMap_unconditional` and
  `CommAlgCat.quasiIso_cotangentExtendScalarsComplexMap_unconditional`: **Tag 08QQ** — the
  functoriality map is a quasi-isomorphism.
* `CommAlgCat.isIso_Q_map_cotangentExtendScalarsComplexMap_unconditional`: the same read in
  `D(B')`.
* `CommAlgCat.cotangentBaseChangeIsoUnconditional`: the base-change isomorphism in `D(B')`, as
  data.

## References

* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open scoped ChangeOfRings TensorProduct

universe u

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

section Square

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u))

/-- **Stacks 08QQ on the Moore complexes.** If the square induces `B ⊗_A^L A' = B'`, the
functoriality map of Tag 08PN is a quasi-isomorphism of the alternating face map complexes.
This is `CommAlgCat.quasiIso_cotangentExtendScalarsMooreMap` with Remark 08QI supplied by
`CommAlgCat.cotangentComputedByEveryResolution`. -/
@[stacks 08QQ "on the alternating-face-map complexes: under the source's own hypothesis and with \
  no other, the functoriality map of Tag 08PN is a quasi-isomorphism"]
theorem quasiIso_cotangentExtendScalarsMooreMap_unconditional
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b)) :
    QuasiIso (cotangentExtendScalarsMooreMap b) :=
  quasiIso_cotangentExtendScalarsMooreMap b hTor hpush (cotangentComputedByEveryResolution A' B')

/-- **Stacks 08QQ.** If the commutative square `A → B`, `A → A'`, `B → B'`, `A' → B'` induces a
quasi-isomorphism `B ⊗_A^L A' = B'`, then the functoriality map `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of
Tag 08PN is a quasi-isomorphism of cotangent complexes. This is
`CommAlgCat.quasiIso_cotangentExtendScalarsComplexMap` with Remark 08QI supplied by
`CommAlgCat.cotangentComputedByEveryResolution`. -/
@[stacks 08QQ "on the cotangent complexes, under the source's own hypothesis B ⊗_A^L A' = B' and \
  no other: THE functoriality map of Tag 08PN is a quasi-isomorphism"]
theorem quasiIso_cotangentExtendScalarsComplexMap_unconditional
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b)) :
    QuasiIso (cotangentExtendScalarsComplexMap b) :=
  quasiIso_cotangentExtendScalarsComplexMap b hTor hpush
    (cotangentComputedByEveryResolution A' B')

/-- **Stacks 08QQ in the derived category.** Under the hypothesis `B ⊗_A^L A' = B'` the
functoriality map becomes an isomorphism `L_{B/A} ⊗_B^L B' ⟶ L_{B'/A'}` in `D(B')`. -/
@[stacks 08QQ "the lemma as an isomorphism in D(B'): the image of the functoriality map of \
  Tag 08PN under the localization D(B') is invertible, under the source's own hypothesis and \
  no other"]
theorem isIso_Q_map_cotangentExtendScalarsComplexMap_unconditional
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b)) :
    IsIso (DerivedCategory.Q.map (cotangentExtendScalarsComplexMap b)) :=
  isIso_Q_map_cotangentExtendScalarsComplexMap b hTor hpush
    (cotangentComputedByEveryResolution A' B')

/-- **Stacks 08QQ, the base-change isomorphism.** The isomorphism
`L_{B/A} ⊗_B^L B' ≅ L_{B'/A'}` in `D(B')` whose underlying morphism is the functoriality map of
the square. -/
@[stacks 08QQ "the base-change isomorphism itself, as data: an isomorphism in D(B') whose \
  underlying morphism is the functoriality map of Tag 08PN, under the source's own hypothesis \
  and no other"]
def cotangentBaseChangeIsoUnconditional
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b)) :
    DerivedCategory.Q.obj
        (((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, u} A' B') :=
  cotangentBaseChangeIso b hTor hpush (cotangentComputedByEveryResolution A' B')

end Square

end CommAlgCat

end

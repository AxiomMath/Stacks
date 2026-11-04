module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing

/-!
# Finite étale covers of a proper scheme over a henselian local ring

A henselian local ring `A` forms a henselian pair with its maximal ideal, so the results of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence` about a proper
scheme over a henselian pair apply with `I` the maximal ideal, and the closed fibre
`X ×_{Spec A} Spec κ(A)` is the fibre over the closed point.

Both halves of the henselian-pair condition for `(A, 𝔪)` are standard: the Jacobson radical of a
local ring is its maximal ideal; that a henselian local ring forms a henselian pair with it is
`henselianPair_maximalIdeal` of `StacksFrontier.RingTheory.Henselian.Pair.LocalRing`.

## Main results

* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_closedFibre_of_essSurj` — base change to
  the closed fibre is an equivalence on finite étale covers of a proper scheme over a henselian
  local ring, granted essential surjectivity.

## Implementation notes

The essential-surjectivity hypothesis `hes` is not weaker than the conclusion it serves: by
`AlgebraicGeometry.finiteEtaleBaseChange_essSurj_of_isEquivalence_of_isProper` it is exactly the
essential-surjectivity half of Stacks 0GS2 for the proper schemes finite étale over `X`. For a
*finite* morphism it is a theorem,
`AlgebraicGeometry.finiteEtaleBaseChange_essSurj_of_isFinite_of_henselianPair`; for a general
proper morphism it is Grothendieck existence over a complete Noetherian ring together with Artin
approximation, neither of which enters here.

Henselianity of `A` enters only through `henselianPair_maximalIdeal`, and from that only
`HenselianPair.le_jacobson` is consumed by the geometry; the factorization half is what makes the
essential-surjectivity hypothesis true, and is not used here.

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0A48, granted essential surjectivity.** If `A` is a henselian local
ring, `X` is proper over `Spec A`, and base change to the closed fibre is essentially surjective
on finite étale covers of every scheme `P` finite étale over `X`, then base change to the closed
fibre is an equivalence on finite étale covers of `X`.

This is
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`
for the henselian pair `(A, 𝔪)` of `henselianPair_maximalIdeal`. -/
theorem isEquivalence_finiteEtaleBaseChange_closedFibre_of_essSurj
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hes : ∀ P : FiniteEtaleOver X,
      (finiteEtaleBaseChange (pullback.fst (P.hom ≫ f)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))).EssSurj) :
    (finiteEtaleBaseChange
      (pullback.fst f
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj A _
    (henselianPair_maximalIdeal A) f hes

end AlgebraicGeometry

end

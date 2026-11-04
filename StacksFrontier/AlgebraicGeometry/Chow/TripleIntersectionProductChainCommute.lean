module

public import StacksFrontier.AlgebraicGeometry.Chow.TripleIntersectionProduct

/-!
# The commutation step of the triple intersection product, over an arbitrary base

`StacksFrontier.AlgebraicGeometry.Chow.TripleIntersectionProduct` sets up the five-step chain of the
source's proof of Stacks 0FC1 over a field. Its middle step is an instance of Stacks 0FBP for the
Gysin class `Δ^!` of the diagonal: the two orders in which `Δ^!` may be capped against the two
factorwise diagonals `Δ₁₂` and `Δ₂₃` of one triple product `(Y ×_S Z) ×_S W` agree, after the
transports that carry the two results into the Chow group of `Y ×_X (Z ×_X W)`.

That step mentions no exterior product and no product operation, so it makes sense over an
arbitrary base `S`, and this module states it there, as
`Stacks.Chow.DiagonalGysinCommuteOnTripleProductOverBase`. Read at the base situation of a field
it is `Stacks.Chow.DiagonalGysinCommuteOnTripleProduct`, the hypothesis of
`Stacks.Chow.isAssociativeIntersectionProduct`.

## Main definitions

* `Stacks.Chow.DiagonalGysinCommuteOnTripleProductOverBase` — the commutation step of the chain,
  over an arbitrary base situation.

## References

* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FC1](https://stacks.math.columbia.edu/tag/0FC1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section ChainCommute

variable (C : ChowSituation.{u}) (G : GysinSystem C) (hpp : ProperPushforwardDescends C)
  {X Y Z W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (g : W ⟶ X) [LocallyOfFiniteType g] (d : ℤ)
  (Dc : BivariantClass C G sX (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d)
  (n m l : ℤ)

/-- **Stacks 0FBP for the Gysin class of the diagonal**, in the instance the proofs of Stacks 0FC1
and Stacks 0FCA consume: the two orders in which `Δ^!` may be capped against the two factorwise
diagonals `Δ₁₂` and `Δ₂₃` of one triple product `(Y ×_S Z) ×_S W` agree, after the transports
that carry the two results into the Chow group of `Y ×_X (Z ×_X W)`.

This is a statement about **one** bivariant class, the two factorwise diagonals and **one**
arbitrary class `x` on the triple product. It mentions no exterior product and no product
operation, and so it makes sense over an arbitrary base `S`. It holds as soon as the restriction
of `Δ^!` along `Δ₁₂` commutes with every bivariant class,
`Stacks.Chow.diagonalGysinCommuteOnTripleProduct_of_commutesWithEveryClass`, which is the case for
the Gysin class of the diagonal of a smooth morphism,
`Stacks.Chow.diagonalGysinClass_bivariantRestriction_commutesWithEveryClass`. -/
def DiagonalGysinCommuteOnTripleProductOverBase : Prop :=
  ∀ x : chowGroup C
      (pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
        (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))) (n + m + l),
    (chowGroupDegreeEquiv C
        (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
        (intersectionProductAssocDegree n m l d))
      ((properChowPushforward C
          (pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX))
          (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
          (tripleProductAssoc a b g).hom
          (tripleProductAssoc_hom_comp_structureMorphism C sX a b g)
          (n + m - d + l - d) (hpp _ _ _ _ _))
        ((properChowPushforward C
            (pullback.fst (pullback.diagonal sX)
              (exteriorToSelfProduct C sX (pullback.fst a b ≫ a) g) ≫ sX)
            (pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX))
            (pullbackDiagonalMapIdIso (pullback.fst a b ≫ a) g sX).hom
            (pullbackDiagonalMapIdIso_hom_comp_structure C sX
              (pullback.fst a b ≫ a) g) (n + m - d + l - d) (hpp _ _ _ _ _))
          ((Dc.cap (exteriorToSelfProduct C sX (pullback.fst a b ≫ a) g)
              (n + m - d + l))
            ((chowGroupCongr C
                (exteriorToSelfProduct_comp_selfProductStructure C sX
                  (pullback.fst a b ≫ a) g).symm (n + m - d + l)).toAddMonoidHom
              ((chowPushforwardOfIso C
                  (pullback.fst (pullback.diagonal sX)
                    (firstPartialDiagonalTest sX a b g) ≫ sX)
                  (pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫
                    ((pullback.fst a b ≫ a) ≫ sX))
                  (firstPartialDiagonalPullbackIso sX a b g).hom
                  (firstPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + m - d + l))
                ((chowGroupDegreeEquiv C
                    (pullback.fst (pullback.diagonal sX)
                      (firstPartialDiagonalTest sX a b g) ≫ sX)
                    (by ring : n + m + l - d = n + m - d + l))
                  ((Dc.cap (firstPartialDiagonalTest sX a b g) (n + m + l))
                    ((chowGroupCongr C
                        (firstPartialDiagonalTest_comp_base sX a b g).symm
                        (n + m + l)).toAddMonoidHom x)))))))) =
      (properChowPushforward C
          (pullback.fst (pullback.diagonal sX)
            (exteriorToSelfProduct C sX a (pullback.fst b g ≫ b)) ≫ sX)
          (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
          (pullbackDiagonalMapIdIso a (pullback.fst b g ≫ b) sX).hom
          (pullbackDiagonalMapIdIso_hom_comp_structure C sX a
            (pullback.fst b g ≫ b)) (n + (m + l - d) - d) (hpp _ _ _ _ _))
        ((Dc.cap (exteriorToSelfProduct C sX a (pullback.fst b g ≫ b))
            (n + (m + l - d)))
          ((chowGroupCongr C
              (exteriorToSelfProduct_comp_selfProductStructure C sX a
                (pullback.fst b g ≫ b)).symm (n + (m + l - d))).toAddMonoidHom
            ((chowPushforwardOfIso C
                (pullback.fst (pullback.diagonal sX)
                  (secondPartialDiagonalTest sX a b g) ≫ sX)
                (pullback.fst (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ (a ≫ sX))
                (secondPartialDiagonalPullbackIso sX a b g).hom
                (secondPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + (m + l - d)))
              ((chowGroupDegreeEquiv C
                  (pullback.fst (pullback.diagonal sX)
                    (secondPartialDiagonalTest sX a b g) ≫ sX)
                  (by ring : n + (m + l) - d = n + (m + l - d)))
                ((Dc.cap (secondPartialDiagonalTest sX a b g) (n + (m + l)))
                  ((chowGroupCongr C
                      (secondPartialDiagonalTest_comp_base sX a b g).symm
                      (n + (m + l))).toAddMonoidHom
                    ((chowGroupDegreeEquiv C
                        (pullback.fst (a ≫ sX)
                          (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
                        (add_assoc n m l))
                      ((chowPushforwardOfIso C
                          (pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))
                              (g ≫ sX) ≫ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)))
                          (pullback.fst (a ≫ sX)
                            (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
                          (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom
                          (tripleProductAssoc_hom_comp_base (a ≫ sX) (b ≫ sX) (g ≫ sX))
                          (n + m + l))
                        x))))))))

end ChainCommute

end Stacks.Chow

end

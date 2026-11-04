module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.ContractionTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CoordinateProjectionSection

/-!
# The contraction step of Stacks 0AEM over the ground field, for a power of the projective line

The proof of [Stacks, Tag 0AEM] begins by replacing `k` by its algebraic closure, "details
omitted", in order to argue with rational points, and what it produces there is a factorization
of the given morphism through the projection of `(ℙ¹_k̄)^n` onto the coordinates in some subset
`I ⊆ Fin n`, the second factor having finite fibres over the points of the target.

`AlgebraicGeometry.Space.exists_index_factorization_finite_fibres_of_algebraicClosure` carries
that conclusion back to `k` for an arbitrary family of split projections out of a reduced
algebraic space. This file instantiates it at the family of coordinate projections of
`(ℙ¹_k)^n`, indexed by `Finset (Fin n)`, which is the family 0AEM uses: the power is reduced
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_projectiveLinePower`), each
coordinate projection is split (`AlgebraicGeometry.Space.coordinateProjectionSection_comp`),
and a finite power of the projective line is an algebraic space over `k`
(`AlgebraicGeometry.Space.isAlgebraicSpace_projectiveLinePowerFin`).

## Main results

* `AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_algebraicClosure`:
  **the contraction step of Stacks 0AEM descends from the algebraic closure to the ground
  field, at a finite power of the projective line.** If after base change to `k̄` the morphism
  factors through the projection onto the coordinates in some `I ⊆ Fin n` by a morphism with
  finite fibres on points, then it so factors over `k` itself.

## Implementation notes

The conclusion is exactly the shape of the hypothesis `h0AEMfibres` carried by
`AlgebraicGeometry.Space.morphism_projectiveLine_eq_constant` (Stacks 0AEN) and of the
hypothesis of
`AlgebraicGeometry.Space.exists_coordinateProjection_isFinite_of_exists_finite_fibres`, for the
one `n` and one target at hand; what remains between this statement and those hypotheses is the
contraction process over the algebraically closed field, which runs through the action of
`(GL_{2,k̄})^n` on `(ℙ¹_k̄)^n` and a Zariski-density statement about an orbit.

No positivity hypothesis on `n` and no nonemptiness hypothesis on the subset are needed: the
section of the coordinate projection exists for every subset, the empty one included, because
the projective line has a rational point over any field.

## References

* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-- **The contraction step of Stacks 0AEM descends from the algebraic closure to the ground
field, at a finite power of the projective line.** Let `k` be a field, let `Z` be an algebraic
space over `k` separated over the base, and let `f : (ℙ¹_k)^n ⟶ Z`. Suppose that after base
change along `Spec k̄ ⟶ Spec k` the morphism `f` factors through the projection onto the
coordinates in some finite subset `I ⊆ Fin n` by a morphism all of whose fibres on points are
finite. Then `f` factors over `k` as the projection onto the coordinates in `I` followed by a
morphism all of whose fibres on points are finite.

This is
`AlgebraicGeometry.Space.exists_index_factorization_finite_fibres_of_algebraicClosure` applied
to the family of coordinate projections of `(ℙ¹_k)^n`, whose index type is `Finset (Fin n)`;
the reducedness of the source and the sections of the projections are supplied by
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/CoordinateProjectionSection.lean`. -/
theorem exists_coordinateProjection_finite_fibres_of_algebraicClosure (n : ℕ)
    {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (qZ : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hqZ : IsSeparated B (Spec (CommRingCat.of k)) hk qZ)
    (f : projectiveLinePower k B hk (Fin n) ⟶ Z)
    (hbase : ∃ (I : Finset (Fin n)) (u :
        (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj
            (projectiveLinePower k B hk I) ⟶
          (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Z),
      (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map f =
          (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map
            (coordinateProjection k B hk n I) ≫ u ∧
        ∀ z : points B (Spec (CommRingCat.of (AlgebraicClosure k)))
            (B.contains_spec_algebraicClosure k hk)
            ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Z),
          {x : points B (Spec (CommRingCat.of (AlgebraicClosure k)))
              (B.contains_spec_algebraicClosure k hk)
              ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj
                (projectiveLinePower k B hk I)) |
            pointsMap B (Spec (CommRingCat.of (AlgebraicClosure k)))
                (B.contains_spec_algebraicClosure k hk)
                ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj
                  (projectiveLinePower k B hk I)) u x = z}.Finite) :
    ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      f = coordinateProjection k B hk n I ≫ g ∧
        ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
          {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) |
            pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) g x =
              y}.Finite :=
  exists_index_factorization_finite_fibres_of_algebraicClosure B k hk
    (fun I : Finset (Fin n) => projectiveLinePower k B hk I)
    (base_isTerminal k B hk)
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _)
    (isAlgebraicSpace_projectiveLinePowerFin k B hk n) hZ
    (hasEtaleLocalProperty_isReduced_projectiveLinePower k B hk n)
    qZ hqZ (coordinateProjection k B hk n) (coordinateProjectionSection k B hk n)
    (coordinateProjectionSection_comp k B hk n) f hbase

end AlgebraicGeometry.Space

end

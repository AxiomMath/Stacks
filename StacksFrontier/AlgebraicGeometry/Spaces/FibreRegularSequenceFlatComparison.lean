module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingRegularSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularSequenceGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties

/-!
# The fibre hypothesis of Stacks 06LW along a morphism flat at the point

Let `ξ : F ⟶ X` be a morphism of algebraic spaces over `S`, let `f₁, …, f_r` be global regular
functions on `X` and let `m : F' ⟶ F` be a morphism of algebraic spaces which is flat at a
geometric point of `F'`. The condition that the images of the `f_i` form a regular sequence in
the étale local ring at that point is the same read on `F'` along `m ≫ ξ` as read on `F` along
`ξ` at the image point.

This is the form in which the hypothesis of **Stacks 06LW** survives a comparison of two
presentations of one fibre: two 2-fibre products of the same cospan are isomorphic, an
isomorphism is flat, and this carries the regularity hypothesis from one of them to the other.

## Main results

* `AlgebraicGeometry.Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_isFlatAt`.

## Implementation notes

`AlgebraicGeometry.Space.isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt` is the same
statement for a *fixed* list of germs. What is added is the repackaging into the shape the
hypothesis of Stacks 06LW and `AlgebraicGeometry.Stack.FibreIsRegularSequenceAt` are written in,
which quantifies over the small étale neighbourhoods of its own point and builds the list with
`List.ofFn` rather than `List.map`; the two are exchanged by `List.map_ofFn`, used as an equality
of lists under `congrArg` rather than as a rewrite, the germ's type depending on the
neighbourhood.

No `@[stacks]` attribute is attached: the covering set of **Stacks 06LW** is in
`StacksFrontier/AlgebraicGeometry/Spaces/FibreSliceFlatnessEnlargement.lean`, and this is a
bookkeeping lemma about its hypothesis.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {Xs Fs Fs' : AlgebraicSpaces B S hS} (ξ : Fs ⟶ Xs) {r : ℕ}
  (fs : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Xs)).sections)

/-- **The fibre hypothesis of Stacks 06LW is unchanged by an isomorphism of the fibre.** Let
`ξ : F ⟶ X` be a morphism of algebraic spaces over `S`, let `f₁, …, f_r` be global regular
functions on `X` and let `m : F' ⟶ F` be an isomorphism of algebraic spaces. Then the images of
the `f_i` form a regular sequence in `𝒪_{F', z̄}` for the composite `m ≫ ξ` exactly when they do
in `𝒪_{F, m(z̄)}` for `ξ`.

An isomorphism is flat, so this is
`AlgebraicGeometry.Space.isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt` at `m`, with the
two germ lists moved through `List.map_ofFn`. -/
theorem forall_isRegular_etaleLocalRingMap_germ_iff_of_isFlatAt
    (m : Fs'.1 ⟶ Fs.1) (z : GeometricPoint B S hS Fs'.1)
    (hm : IsFlatAt B S hS m z.image) :
    (∀ N : SmallEtaleNeighborhood (geometricPointMap (m ≫ ξ.hom) z),
        RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs'.1 z)
          (List.ofFn fun i : Fin r => etaleLocalRingMap Fs'.2 (m ≫ ξ.hom) z
            (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap (m ≫ ξ.hom) z) (op N)
              ((fs i).eval (op N.chart))))) ↔
      ∀ N : SmallEtaleNeighborhood (geometricPointMap ξ.hom (geometricPointMap m z)),
        RingTheory.Sequence.IsRegular
            (etaleLocalRing B S hS Fs.1 (geometricPointMap m z))
          (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom (geometricPointMap m z)
            (etaleLocalRingGerm B S hS Xs.1
              (geometricPointMap ξ.hom (geometricPointMap m z)) (op N)
              ((fs i).eval (op N.chart)))) := by
  refine forall_congr' fun N => ?_
  exact (iff_of_eq (congrArg _ List.map_ofFn.symm)).trans
    ((isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt B S hS Fs'.2 Fs.2 m ξ.hom z hm _).trans
      (iff_of_eq (congrArg _ List.map_ofFn)))

end AlgebraicGeometry.Space

end

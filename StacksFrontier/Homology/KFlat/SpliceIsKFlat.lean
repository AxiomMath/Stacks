module

public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# The splice of two K-flat complexes is K-flat

Let `F : A ⥤ B ⥤ D` be a bifunctor against which K-flatness of complexes of `B` is measured.
K-flatness is two-out-of-three along a degreewise split short exact sequence of complexes
(`CochainComplex.KFlatBifunctor.kFlat_X₂_of_degreewiseSplit`). This file reads that at the
**splice** of the proof of [Stacks, Tag 0FPV]: for a
complex `E` concentrated in degrees `≥ m`, a complex `L` concentrated in degrees `≤ m - 1` and a
morphism `ψ : L⟦-1⟧ ⟶ E`, the complex

`… ⟶ L^{m-2} ⟶ L^{m-1} ⟶ E^m ⟶ E^{m+1} ⟶ …`

is `CochainComplex.mappingCone ψ` (see
`StacksFrontier/Algebra/Homology/DerivedCategory/SpliceAtADegree.lean`), and it is K-flat as soon as
`E` and `L` are. The hypothesis is read on `L` rather than on `L⟦-1⟧`: the shift is absorbed by
`CochainComplex.KFlatBifunctor.KFlat.of_iso` along
`CategoryTheory.shiftFunctorCompIsoId`, so no shift-invariance of K-flatness is needed.

This closes the gap between the splice and
`AlgebraicGeometry.RingedSite.exists_presieve_localRetract`, the producer of the local retract of
[Stacks, Tag 0FPV], which asks for K-flatness of the *whole* complex representing `M` while the
source only ever chooses `N^•` K-flat: the representative of `M` which the pseudo-coherence
induction hands the producer is the splice, and its K-flatness comes from the two halves — `L`
K-flat because it may be chosen bounded above with flat terms ([Stacks, Tag 06YQ]), `E` K-flat
because it is strictly perfect.

Nothing below is a clause of a tag; these are steps of a proof, so no `@[stacks …]` attribute is
attached.

## Main results

* `CochainComplex.KFlatBifunctor.kFlat_splice`: **the splice is K-flat**, with the hypotheses
  read on `E` and `L`.

## Implementation notes

**Why the degreewise split sequence and not the cone triangle.** Reading K-flatness off the cone
triangle of the homotopy category — the route of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_mappingCone` — asks for K-flatness of
the source and the target of the morphism, and for the splice the source is `L⟦-1⟧`: the caller
would be left owing K-flatness of a shift, for which nothing is available at this spelling. The
*rotated* cone short complex `E ⟶ mappingCone ψ ⟶ (L⟦-1⟧)⟦1⟧` avoids that. It is degreewise
split (`CochainComplex.mappingCone.triangleRotateShortComplexSplitting`), so
`CochainComplex.KFlatBifunctor.kFlat_X₂_of_degreewiseSplit` applies to it, and its third vertex
`(L⟦-1⟧)⟦1⟧` is isomorphic to `L` as a complex, so the hypothesis is the one the caller has.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 06Y2](https://stacks.math.columbia.edu/tag/06Y2)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open ComplexShape HomologicalComplex

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **The splice of [Stacks, Tag 0FPV] is K-flat.** For `ψ : L⟦-1⟧ ⟶ E` the complex
`CochainComplex.mappingCone ψ` — which, for `E` concentrated in degrees `≥ m` and `L` in degrees
`≤ m - 1`, is the complex `… ⟶ L^{m-1} ⟶ E^m ⟶ …` of the source — is K-flat as soon as `E` and
`L` are.

The rotated cone short complex `E ⟶ mappingCone ψ ⟶ (L⟦-1⟧)⟦1⟧` is degreewise split, and its
third vertex is isomorphic to `L`. -/
theorem kFlat_splice (E L : CochainComplex B ℤ) (ψ : (L⟦(-1 : ℤ)⟧) ⟶ E)
    (hE : KFlat F E) (hL : KFlat F L) :
    KFlat F (CochainComplex.mappingCone ψ) :=
  kFlat_X₂_of_degreewiseSplit F (CochainComplex.mappingCone.triangleRotateShortComplex ψ)
    (CochainComplex.mappingCone.triangleRotateShortComplexSplitting ψ) hE
    (KFlat.of_iso F hL
      ((shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) (1 : ℤ) (by lia)).app L).symm)

end CochainComplex.KFlatBifunctor

end

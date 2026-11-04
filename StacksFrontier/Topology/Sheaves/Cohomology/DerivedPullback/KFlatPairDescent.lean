module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# Descending an equality of transformations on `D(𝒪_Y) × D(𝒪_Y)` to K-flat complexes

Let `(Y, 𝒪_Y)` be a ringed space.  By Stacks 06YS the derived category `D(𝒪_Y)` is the
localization of the K-flat objects of the homotopy category at the quasi-isomorphisms between
them, and the product of two copies of that localization is a localization of pairs.  A
natural transformation between functors on `D(𝒪_Y) × D(𝒪_Y)` is therefore determined by its
components at pairs of K-flat complexes.

This is the extensionality principle the bifunctorial identities about the comparison of
Stacks 079U are proved by: both sides of such an identity are known only at pairs of K-flat
complexes — that is where `Stacks.Cohomology.DerivedPullbackTensor.modelComparison` lives —
and this lemma is what turns agreement there into equality of transformations on the whole of
`D(𝒪_Y) × D(𝒪_Y)`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`: two natural transformations
  between functors on `D(𝒪_Y) × D(𝒪_Y)` which agree at `(QK, QL)` for all K-flat cochain
  complexes `K, L` are equal.

## Implementation notes

*Why this is not already available.*  Nothing in the tree states extensionality of
transformations on `D(𝒪_Y) × D(𝒪_Y)` against pairs of K-flat complexes.  The localization
input is `Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair_isLocalization`, which is used
only to descend a transformation (through `CategoryTheory.Localization.liftNatIso`), never to
compare two of them.

*Which extensionality lemma.*  Mathlib's `CategoryTheory.Localization.natTrans_ext` applies
directly: it asks only for a localization functor, and
`Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair` is one.
`CategoryTheory.natTrans_ext_of_resolutions` is the wrong instrument here — it additionally
asks for a *functorial* resolution `R : C ⥤ C` with `η : 𝟭 C ⟶ R`, which for K-flat
resolutions of complexes of `𝒪_Y`-modules does not exist in the tree (Stacks 06YS supplies a
resolution of each complex separately, with no functoriality), and it would be redundant: the
functorial resolution is a device for *producing* a localization-like extensionality when no
localization is on hand, and here the localization itself is available.

*From K-flat homotopy objects to complexes.*  `CategoryTheory.Localization.natTrans_ext`
yields agreement at `kFlatQPair.obj M`, i.e. at `Qh` of a pair of K-flat objects of the
homotopy category.  `Stacks.Cohomology.DerivedPullbackTensor.kFlatQPairIso` identifies that
with `(QK, QL)` for the underlying pair of cochain complexes, and transporting an equality of
components along an isomorphism of objects is naturality.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe v w u

variable (Y : RingedSpace.{u, u})

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] kFlatQPair_isLocalization

/-- **An equality of natural transformations on `D(𝒪_Y) × D(𝒪_Y)` may be checked on pairs of
K-flat complexes.**  Two natural transformations between functors on `D(𝒪_Y) × D(𝒪_Y)` whose
components at `(QK, QL)` agree for every pair of K-flat cochain complexes `K, L` of
`𝒪_Y`-modules are equal.

By Stacks 06YS the K-flat objects of the homotopy category localize to `D(𝒪_Y)`, so pairs of
them localize to `D(𝒪_Y) × D(𝒪_Y)`
(`Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair_isLocalization`), and a transformation
out of a localization is determined by its components on the image of the localization
functor.  The objects `K` and `L` are arbitrary K-flat complexes, with no boundedness,
flatness or quasi-coherence assumption, and the target category `E` is arbitrary. -/
theorem natTrans_ext_of_kFlat {E : Type w} [Category.{v} E]
    {A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ⥤ E}
    (α β : A ⟶ B)
    (h : ∀ K L : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ,
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K →
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L →
      α.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
        β.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) :
    α = β :=
  Localization.natTrans_ext (kFlatQPair (Y := Y)) (kFlatQuasiIsoPair (Y := Y))
    (fun M => CategoryTheory.NatTrans.app_eq_of_iso α β (kFlatQPairIso M)
      (h M.1.obj.as M.2.obj.as M.1.property M.2.property))

end Stacks.Cohomology.DerivedPullbackTensor

end

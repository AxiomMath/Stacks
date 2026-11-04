module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatPairDescent
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# Descending an equality of transformations on `D(𝒪_Y)³` to K-flat complexes

Let `(Y, 𝒪_Y)` be a ringed space.  By Stacks 06YS the derived category `D(𝒪_Y)` is the
localization of the K-flat objects of the homotopy category at the quasi-isomorphisms between
them, so a product of three copies of that localization is a localization of triples, and a
natural transformation between functors on `D(𝒪_Y) × D(𝒪_Y) × D(𝒪_Y)` is determined by its
components at triples of K-flat complexes.

This is the three-variable companion of
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`, and it is what an
*associativity* identity about the comparison of Stacks 079U has to be descended by: such an
identity involves three derived modules, and both of its sides are known only at triples of
K-flat complexes, where the comparison is computed by ordinary total tensor complexes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.kFlatQTriple_isLocalization`: `D(𝒪_Y)³` is the
  localization of the triples of K-flat objects of the homotopy category at the
  quasi-isomorphisms between them.
* `Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat₃`: two natural transformations
  between functors on `D(𝒪_Y) × D(𝒪_Y) × D(𝒪_Y)` which agree at `(QK, QL, QM)` for all K-flat
  cochain complexes `K, L, M` are equal.

## Implementation notes

*Where the content is.*  Nowhere here.  `CategoryTheory.Functor.IsLocalization.prod` says a
product of two localizations is a localization of the product; applying it to the one-variable
localization `Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization` and the two-variable one
`Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair_isLocalization` gives the three-variable
statement, since `D × D × D` is `D × (D × D)`.  The extensionality principle is then Mathlib's
`CategoryTheory.Localization.natTrans_ext`, exactly as in the two-variable case.

*Which spelling of the tensor bifunctor.*  Every mention of it here is
`Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf`, exactly as in
`Stacks.Cohomology.DerivedPullbackTensor.kFlatQY`, and not the definitionally equal
`sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩`.  The K-flat localization asks for the additivity of the
bifunctor in each variable and for the existence of the total complexes, and those instances
are `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive`,
`.sheafTensor_obj_additive` and `.hasMapBifunctor_sheafTensor`, all stated at `X.sheaf` with
the five universes pinned.  Against an explicit `Sheaf.mk` their keys cannot match:
`SheafedSpace.sheaf` is a semireducible definition, so it is not unfolded at the transparency
instance search uses, and matching would mean inverting a projection applied to a
metavariable.

*From K-flat homotopy objects to complexes.*  `Localization.natTrans_ext` yields agreement at
`kFlatQTriple.obj M`, i.e. at `Qh` of a triple of K-flat objects of the homotopy category.  The
bridge to `(QK, QL, QM)` is `DerivedCategory.quotientCompQhIso` in the first variable and
`Stacks.Cohomology.DerivedPullbackTensor.kFlatQPairIso` in the other two, and transporting an
equality of components along an isomorphism of objects is naturality.

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

/-- Triples of K-flat objects of the homotopy category, viewed in `D(𝒪_Y)³`. -/
abbrev kFlatQTriple := (kFlatQY (Y := Y)).prod (kFlatQPair (Y := Y))

/-- The quasi-isomorphisms between triples of K-flat objects. -/
abbrev kFlatQuasiIsoTriple :=
  (CochainComplex.KFlatBifunctor.kFlatQuasiIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).prod
    (kFlatQuasiIsoPair (Y := Y))

attribute [local instance] kFlatQPair_isLocalization

/-- **`D(𝒪_Y)³` is the localization of the triples of K-flat objects at the
quasi-isomorphisms.**  A localization of a product of categories is the product of the
localizations; here the two factors are
`Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization` and
`Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair_isLocalization`. -/
theorem kFlatQTriple_isLocalization :
    (kFlatQTriple (Y := Y)).IsLocalization (kFlatQuasiIsoTriple (Y := Y)) := by
  have := Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization Y.sheaf
  have : (CochainComplex.KFlatBifunctor.kFlatQuasiIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).ContainsIdentities := by
    infer_instance
  have : (kFlatQuasiIsoPair (Y := Y)).ContainsIdentities := by infer_instance
  exact Functor.IsLocalization.prod (kFlatQY (Y := Y)) _ (kFlatQPair (Y := Y)) _

/-- The image in `D(𝒪_Y)³` of a triple of K-flat objects of the homotopy category is the image
of the underlying triple of complexes: the `Q` versus `Qh ∘ quotient` bridge, in all three
variables. -/
def kFlatQTripleIso (M : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ×
    (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ×
      (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    (kFlatQTriple (Y := Y)).obj M ≅
      (DerivedCategory.Q.obj M.1.obj.as,
        DerivedCategory.Q.obj M.2.1.obj.as, DerivedCategory.Q.obj M.2.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso _).app M.1.obj.as).prod (kFlatQPairIso M.2)

attribute [local instance] kFlatQTriple_isLocalization

/-- **An equality of natural transformations on `D(𝒪_Y)³` may be checked on triples of K-flat
complexes.**  Two natural transformations between functors on
`D(𝒪_Y) × D(𝒪_Y) × D(𝒪_Y)` whose components at `(QK, QL, QM)` agree for every triple of
K-flat cochain complexes `K, L, M` of `𝒪_Y`-modules are equal.

The objects `K`, `L` and `M` are arbitrary K-flat complexes, with no boundedness, flatness or
quasi-coherence assumption, and the target category `E` is arbitrary. -/
theorem natTrans_ext_of_kFlat₃ {E : Type w} [Category.{v} E]
    {A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ⥤ E}
    (α β : A ⟶ B)
    (h : ∀ K L M : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ,
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K →
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L →
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M →
      α.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L, DerivedCategory.Q.obj M) =
        β.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L, DerivedCategory.Q.obj M)) :
    α = β :=
  Localization.natTrans_ext (kFlatQTriple (Y := Y)) (kFlatQuasiIsoTriple (Y := Y))
    (fun M => CategoryTheory.NatTrans.app_eq_of_iso α β (kFlatQTripleIso Y M)
      (h M.1.obj.as M.2.1.obj.as M.2.2.obj.as M.1.property M.2.1.property M.2.2.property))

end Stacks.Cohomology.DerivedPullbackTensor

end

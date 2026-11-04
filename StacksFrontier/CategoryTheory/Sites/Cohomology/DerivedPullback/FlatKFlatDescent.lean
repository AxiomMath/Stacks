module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# Descending an equality of transformations on a power of `D(𝒪')` to K-flat complexes

Let `(Sh(C), 𝒪')` be a ringed topos.  By Stacks 06YS the derived category `D(𝒪')` is the
localization of the K-flat complexes with flat terms, viewed in the homotopy category, at the
quasi-isomorphisms between them, and a product of copies of that localization is a localization
of tuples.  A natural transformation between functors on `D(𝒪') × D(𝒪')`, or on `D(𝒪')³`, is
therefore determined by its components at tuples of such complexes.

These are the extensionality principles the identities about the comparison of Stacks 07A4 are
proved by: both sides of such an identity are known only at a tuple of K-flat complexes with
flat terms — that is where
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_model` lives — and these lemmas
turn agreement there into equality of transformations on the whole power.  The arity-2 form is
what the braiding law of Stacks 0FPM is proved by and the arity-3 form what the associativity law
of Stacks 0FPL is proved by, so both are here, in one module, with the triple built on the pair:
`flatKFlatModelTriplesQ` is one further `CategoryTheory.Functor.prod` over `flatKFlatModelsQ`
whose localization is read off `flatKFlatModelPairsQ_isLocalization`, and
`flatKFlatModelTriplesIso` has `flatKFlatModelPairsIso` as its second factor.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.flatKFlatModelTriplesQ`: triples of K-flat complexes with flat
  terms, as a localization of triples of objects of `D(𝒪')`.
* `Stacks.Sheaves.DerivedPullback.flatKFlatModelTriplesIso`: the bridge carrying the image of a
  triple of models under that functor to the triple of `DerivedCategory.Q`-images of the
  underlying cochain complexes.

## Main results

* `Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat`: two natural transformations
  between functors on `D(𝒪') × D(𝒪') ` which agree at `(QK, QL)` for all K-flat cochain
  complexes `K, L` of `𝒪'`-modules with flat terms are equal.
* `Stacks.Sheaves.DerivedPullback.flatKFlatModelTriplesQ_isLocalization`: triples of models
  localize to `D(𝒪')³`.
* `Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat₃`: **two natural transformations
  between functors on `D(𝒪')³` which agree at `(QK, QL, QM)` for every triple of K-flat complexes
  with flat terms are equal.**  The target category is arbitrary and the three complexes carry no
  boundedness, finiteness or quasi-coherence hypothesis.

## Implementation notes

*Why this is not already available.*  The localization input
`Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization` is used in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackTensorComparison.lean`
only to *descend* an isomorphism, through `CategoryTheory.Localization.liftNatIso`, and never to
*compare* two transformations.  The ringed-space counterpart of the present lemma is
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/KFlatPairDescent.lean`; it is stated
for `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` and for K-flatness alone, so it
does not apply to a ringed topos, and no statement of this shape exists for a site at any arity.

*Why flat terms appear and do not weaken the conclusion.*  The resolving class on the topos side
is `Stacks.Sheaves.DerivedPullback.KFlatPullback.IsKFlat`, which asks for K-flatness **and**
termwise flatness, because that is what Tag 0G7E consumes for the exactness of `f^*` on the
class.  Stacks 06YS produces a resolution with both properties, so the class still localizes to
all of `D(𝒪')` and the conclusion is an equality of transformations on the whole product
category, with no hypothesis on its objects.

*Which extensionality lemma.*  `CategoryTheory.Localization.natTrans_ext` applies directly: it
asks only for a localization functor, and `flatKFlatModelPairsQ` is one.
`CategoryTheory.natTrans_ext_of_resolutions` is the wrong instrument, as it additionally asks
for a *functorial* resolution, which Tag 06YS does not supply.

*The arity-3 form.*  Nothing in it is new mathematics beyond the arity-2 form.
`CategoryTheory.Functor.IsLocalization.prod` turns the one localization of Tag 06YS into a
localization of triples, `CategoryTheory.Localization.natTrans_ext` turns that into the
extensionality principle, and `CategoryTheory.NatTrans.app_eq_of_iso` carries the agreement from
`Qh`-images of K-flat objects of the homotopy category to `Q`-images of cochain complexes along
`flatKFlatModelTriplesIso`.  The nesting of the triple is `(K, (L, M))`, matching
`D(𝒪') × D(𝒪') × D(𝒪')`.  The ringed-space counterparts of the two arities are
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat` and
`…natTrans_ext_of_kFlat₃`, in `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/`; they
are stated for `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` and for K-flatness
alone, so neither applies to a ringed topos.

*From K-flat homotopy objects to complexes.*  `CategoryTheory.Localization.natTrans_ext` yields
agreement at `(flatKFlatModelPairsQ Y).obj M`, i.e. at `Qh` of a pair of objects of the
homotopy category.  `Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso` identifies that with
`(QK, QL)` for the underlying pair of cochain complexes, and transporting an equality of
components along an isomorphism of objects is naturality,
`CategoryTheory.NatTrans.app_eq_of_iso`.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe v w u

attribute [local instance] HasDerivedCategory.standard

variable (Y : RingedTopos.{u, u, u})
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An equality of natural transformations on `D(𝒪') × D(𝒪')` may be checked on pairs of
K-flat complexes with flat terms.**  Two natural transformations between functors on
`D(𝒪') × D(𝒪')` whose components at `(QK, QL)` agree for every pair of K-flat cochain complexes
`K, L` of `𝒪'`-modules with flat terms are equal.

By Stacks 06YS such complexes localize to `D(𝒪')`, so pairs of them localize to
`D(𝒪') × D(𝒪')` (`Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization`), and a
transformation out of a localization is determined by its components on the image of the
localization functor.  The complexes `K` and `L` are arbitrary subject to those two properties,
with no boundedness or quasi-coherence assumption, the conclusion is an equality of
transformations on the whole of `D(𝒪') × D(𝒪')`, and the target category `E` is arbitrary. -/
theorem natTrans_ext_of_flatKFlat {E : Type w} [Category.{v} E]
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤ E}
    (α β : A ⟶ B)
    (h : ∀ K L : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) →
      α.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
        β.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) :
    α = β :=
  let : (flatKFlatModelPairsQ Y).IsLocalization (flatKFlatModelPairsW Y) :=
    flatKFlatModelPairsQ_isLocalization Y
  Localization.natTrans_ext (flatKFlatModelPairsQ Y) (flatKFlatModelPairsW Y)
    (fun M => CategoryTheory.NatTrans.app_eq_of_iso α β (flatKFlatModelPairsIso Y M)
      (h M.1.obj.as M.2.obj.as M.1.property.1 M.2.property.1 M.1.property.2 M.2.property.2))

/-! ### Triples -/

/-- Triples of K-flat complexes with flat terms, as a localization of triples of objects of
`D(𝒪')`. -/
abbrev flatKFlatModelTriplesQ :
    (IsKFlat (Y := Y)).FullSubcategory ×
        (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (flatKFlatModelsQ Y).prod ((flatKFlatModelsQ Y).prod (flatKFlatModelsQ Y))

/-- Triples of quasi-isomorphisms between K-flat complexes with flat terms. -/
abbrev flatKFlatModelTriplesW :
    MorphismProperty ((IsKFlat (Y := Y)).FullSubcategory ×
      (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :=
  (flatKFlatModelsW Y).prod ((flatKFlatModelsW Y).prod (flatKFlatModelsW Y))

/-- **Triples of K-flat complexes with flat terms localize to triples of objects of `D(𝒪')`.**
A localization of a product is the product of the localizations, and each factor is
`Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ_isLocalization`, i.e. the resolutions of
[Stacks, Tag 06YS]. -/
theorem flatKFlatModelTriplesQ_isLocalization :
    (flatKFlatModelTriplesQ Y).IsLocalization (flatKFlatModelTriplesW Y) := by
  have := flatKFlatModelsQ_isLocalization Y
  have := flatKFlatModelPairsQ_isLocalization Y
  infer_instance

/-- The localization carries a triple of models to the triple of objects of `D(𝒪')` the
underlying cochain complexes represent. -/
def flatKFlatModelTriplesIso
    (P : (IsKFlat (Y := Y)).FullSubcategory ×
      (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :
    (flatKFlatModelTriplesQ Y).obj P ≅
      (DerivedCategory.Q.obj P.1.obj.as,
        DerivedCategory.Q.obj P.2.1.obj.as, DerivedCategory.Q.obj P.2.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app
      P.1.obj.as).prod (flatKFlatModelPairsIso Y P.2)

/-- **An identity of natural transformations on `D(𝒪')³` may be checked on triples of K-flat
complexes with flat terms.**

Two natural transformations between functors on `D(𝒪') × D(𝒪') × D(𝒪')` whose components at
`(QK, QL, QM)` agree for every triple `K`, `L`, `M` of K-flat complexes of `𝒪'`-modules with
flat terms are equal.  By [Stacks, Tag 06YS] those complexes localize to `D(𝒪')`, so triples of
them localize to `D(𝒪')³`, and a transformation out of a localization is determined by its
components on the image of the localization functor.  The three complexes are arbitrary subject
to K-flatness and termwise flatness, with no boundedness or quasi-coherence assumption, and the
target category `E` is arbitrary.

This is the three-variable companion of
`Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat` above, and it is stated with the same
unpacked hypotheses. -/
theorem natTrans_ext_of_flatKFlat₃ {E : Type w} [Category.{v} E]
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤ E}
    (α β : A ⟶ B)
    (h : ∀ K L M : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) M →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) →
      α.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L, DerivedCategory.Q.obj M) =
        β.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L, DerivedCategory.Q.obj M)) :
    α = β :=
  have := flatKFlatModelTriplesQ_isLocalization Y
  Localization.natTrans_ext (flatKFlatModelTriplesQ Y) (flatKFlatModelTriplesW Y)
    fun P => CategoryTheory.NatTrans.app_eq_of_iso α β (flatKFlatModelTriplesIso Y P)
      (h P.1.obj.as P.2.1.obj.as P.2.2.obj.as P.1.property.1 P.2.1.property.1 P.2.2.property.1
        P.1.property.2 P.2.1.property.2 P.2.2.property.2)

end Stacks.Sheaves.DerivedPullback

end

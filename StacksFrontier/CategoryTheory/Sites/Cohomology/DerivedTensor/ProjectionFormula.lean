module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.OrdinaryAndDerivedCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOnRingedTopoi

/-!
# The projection formula map on a ringed topos

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, `E ∈ D(O_C)` and
`K ∈ D(O_D)`.  With no finiteness, flatness or quasi-coherence hypothesis there is a canonical
map

`Rf_*E ⊗^L_{O_D} K ⟶ Rf_*(E ⊗^L_{O_C} Lf^*K)`,

Equation 21.50.0.1 of [Stacks, Tag 0B56].  It is the map adjoint, for the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6], to

`Lf^*(Rf_*E ⊗^L_{O_D} K) ≅ Lf^*Rf_*E ⊗^L_{O_C} Lf^*K ⟶ E ⊗^L_{O_C} Lf^*K`,

whose first step is the compatibility of derived pullback with the derived tensor product
([Stacks, Tag 07A4]) and whose second is the counit `Lf^*Rf_*E ⟶ E` in the first factor.

This is the abstract construction `CategoryTheory.adjunctionTensorMap`,
instantiated at the derived tensor products of [Stacks, Tag 06YU].  Those are *bifunctors* on
`D(O_D)` and on `D(O_C)` in the un-interchanged order, so the map comes out with the tensor
factors in the order the source writes them and no symmetry of `⊗^L` is needed.

## Main definitions

All in the namespace `Stacks.Cohomology.ProjectionFormulaOnRingedTopoi`.

* `projectionFormulaMapOfComparison` — the map, for an arbitrary pair of derived tensor products
  on `D(O_D)` and `D(O_C)` and an arbitrary compatibility `α` of derived pullback with them.
* `projectionFormulaMap` — **Equation 21.50.0.1**, the map at the canonical derived tensor
  products of [Stacks, Tag 06YU] and the canonical compatibility of [Stacks, Tag 07A4].  It has
  no hypothesis beyond `f` being a morphism of ringed topoi.
* `derivedPullbackSquareIso` — for a commutative square of ringed topoi, the comparison
  `L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` of the two iterated derived pullbacks around it, which is the
  arrow labelled `c` in [Stacks, Tag 0E48].

In the namespace `Stacks.AffineProjectionFormula`, over abstract adjunctions:

* `squareCompositeIso` — the same comparison for an abstract square of adjunctions.
* `TensorComparisonCompatible` — the compatibility of four tensor comparisons around a square
  with that identification; see the implementation notes.

## Main results

* `projectionFormulaMapOfComparison_naturality`,
  `projectionFormulaMap_naturality` — the map is natural in `E` and in `K` jointly;
  `projectionFormulaMap_naturality_source` and `projectionFormulaMap_naturality_target` are the
  source's two separate naturality clauses.
* `projectionFormulaMapOfComparison_eq_unit_comp`, `projectionFormulaMap_eq_unit_comp` — the map
  written through the unit of `Lf^* ⊣ Rf_*`, which is the form a consumer rewrites with.
* `Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square` — the hexagon of
  [Stacks, Tag 0E48], relating Equation 21.50.0.1 to the base change map of [Stacks, Tag 07A7],
  over abstract adjunctions; its only input is the compatibility `TensorComparisonCompatible` of
  the four comparisons of [Stacks, Tag 07A4] around the square.  The registered form of
  [Stacks, Tag 0E48] is
  `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square`.

## Implementation notes

*What is constructed and what is a parameter.*  The source stresses that the map exists
"without any further assumptions", and that is how `projectionFormulaMap` is stated: the only
hypothesis is `hmos`, which says that the continuous functor presenting `f` is a morphism of
sites, i.e. that the Lean object is a morphism of ringed topoi in the source's sense.  Both
results the source cites at this point are available in this repository and are used rather than
assumed.

* [Stacks, Tag 07A6], the adjunction `Lf^* ⊣ Rf_*` on the unbounded derived categories, is
  `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction`.
* [Stacks, Tag 07A4], the bifunctorial isomorphism `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L`, is
  `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`, stated between exactly the two
  composites of uncurried bifunctors that the abstract construction consumes.  Only its forward
  map is used: the source has a map here, not an isomorphism.

*Why the general form is kept as well.*  A derived tensor product on `D(O)` enters this
repository as a value of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, a structure
carrying the bifunctor together with the comparisons that identify it with the total tensor
complex; threading such a value as an explicit argument is the convention of
`StacksFrontier/Homology/PseudoCoherent/Products.lean` and of
`StacksFrontier/Homology/DerivedComplete/AdicKoszulTower.lean`.
`projectionFormulaMapOfComparison` is stated in that convention, and `projectionFormulaMap` is
visibly its instance at the canonical values.  The two sides of `f` need two such values, one
over `O_D` and one over `O_C`.

*Which of the two `DerivedTensorProduct` structures.*  The one over a sheaf of commutative
rings, `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, taken at `Y.O` and at `X.O`.  The
other, `Stacks.SheafOfModules.DerivedTensorProduct`, is indexed by an
`AlgebraicGeometry.RingedSite` with independent universes; a morphism of ringed topoi carries no
such datum, and the derived pullback and derived pushforward of this chain are available only at
`RingedTopos.{u, u, u}`, where the two indexings agree.  The narrowing to a single universe and
a small site is not introduced here: it comes down from the K-flat resolutions of
[Stacks, Tag 06YS] through [Stacks, Tag 06YU] and [Stacks, Tag 07A4].

*Where the canonical bifunctor comes from.*
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` is the bifunctor of
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, a choice of
element of the *proved* existence statement `exists_derivedTensorProduct` of
[Stacks, Tag 06YU].  No new choice is made here, and no other bifunctor is available: it is the
one at which [Stacks, Tag 07A4] is stated, so it is the one at which 21.50.0.1 can be written
down at all.  A consumer holding a different derived tensor product uses
`projectionFormulaMapOfComparison`.

*The tensor order.*  The two bifunctors handed to the abstract construction are the derived
tensor products with their arguments in the given order.  That is what makes the map come out as
`Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)`; the interchange that [Stacks, Tag 0B53] needs, and with it
any appeal to a symmetry of `⊗^L`, does not arise.

*What is not stated.*  That the map is an isomorphism for perfect `K` ([Stacks, Tag 0944]) is a
separate statement of the same section and is not touched here.  Nor is compatibility with the
shift or with distinguished triangles: that would ask for `Functor.CommShift` data on the derived
tensor product in each variable at the uncurried spelling, which is of a different kind than the
two inputs the source cites.

*The one input of [Stacks, Tag 0E48].*  The remark's hexagon has four arrows got
from [Stacks, Tag 07A4] — one for each of the four morphisms of the square — and one arrow `c`
which the source introduces with the words "`c` comes from `L(g')^* ∘ Lf^* = L(f')^* ∘ Lg^*`".
In this development those two iterated derived pullbacks are not equal functors: each is
*identified* with the derived pullback along the common composite by [Stacks, Tag 0D6D], and `c`
is the resulting isomorphism, `derivedPullbackSquareIso`.  Once `c` is an isomorphism rather than
an identity, the verification needs to know that the four comparisons of [Stacks, Tag 07A4] match
up across it, i.e. that

`L(f')^*(t_g) ≫ t_{f'} ≫ (c⁻¹ ⊗ c⁻¹) = c⁻¹ ≫ L(g')^*(t_f) ≫ t_{g'}`,

which is `Stacks.AffineProjectionFormula.TensorComparisonCompatible`.  That is precisely the
content the source suppresses by writing an equality of functors, and it is a statement about
[Stacks, Tag 07A4] alone — the functoriality of that comparison in the morphism of ringed topoi,
transported along [Stacks, Tag 0D6D].  For the site-presented morphisms of this file,
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso` is produced by
`CategoryTheory.Localization.liftNatIso` from its values on K-flat complexes with flat terms and
is accompanied by no compatibility with composition, with the shift or with the unit, so the
remark is not stated here.  For morphisms of ringed topoi in the two-field sense the
compatibility is
`Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso`,
and the remark is
`Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square`.

## References

* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 0943](https://stacks.math.columbia.edu/tag/0943)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-! ### The map from an arbitrary pair of derived tensor products -/

section OfComparison

variable (TD : DerivedTensorProduct Y.O) (TC : DerivedTensorProduct X.O)
  (α : Functor.uncurry.obj TD.tensor ⋙ derivedPullback f ⟶
    (derivedPullback f).prod (derivedPullback f) ⋙ Functor.uncurry.obj TC.tensor)

/-- **The projection-formula map** `Rf_*E ⊗^L_{O_D} K ⟶ Rf_*(E ⊗^L_{O_C} Lf^*K)` built from a
derived tensor product `TD` on `D(O_D)`, one `TC` on `D(O_C)`, and a comparison `α` of derived
pullback with the two: the map adjoint to `α` followed by the counit `Lf^*Rf_*E ⟶ E` in the
first factor. -/
def projectionFormulaMapOfComparison (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (TD : DerivedTensorProduct Y.O) (TC : DerivedTensorProduct X.O)
    (α : Functor.uncurry.obj TD.tensor ⋙ derivedPullback f ⟶
      (derivedPullback f).prod (derivedPullback f) ⋙ Functor.uncurry.obj TC.tensor)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (TD.tensor.obj ((derivedPushforward f).obj E)).obj K ⟶
      (derivedPushforward f).obj
        ((TC.tensor.obj E).obj ((derivedPullback f).obj K)) :=
  CategoryTheory.adjunctionTensorMap
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj TD.tensor) (Functor.uncurry.obj TC.tensor) α E K

/-- The projection-formula map of an arbitrary comparison is natural in both arguments. -/
theorem projectionFormulaMapOfComparison_naturality
    {E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (φ : E ⟶ E') (k : K ⟶ K') :
    ((TD.tensor.map ((derivedPushforward f).map φ)).app K ≫
          (TD.tensor.obj ((derivedPushforward f).obj E')).map k) ≫
        projectionFormulaMapOfComparison f hmos TD TC α E' K' =
      projectionFormulaMapOfComparison f hmos TD TC α E K ≫
        (derivedPushforward f).map
          ((TC.tensor.map φ).app ((derivedPullback f).obj K) ≫
            (TC.tensor.obj E').map ((derivedPullback f).map k)) :=
  CategoryTheory.adjunctionTensorMap_natural
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj TD.tensor) (Functor.uncurry.obj TC.tensor) α φ k

/-- The projection-formula map of an arbitrary comparison, written through the unit of
`Lf^* ⊣ Rf_*`. -/
theorem projectionFormulaMapOfComparison_eq_unit_comp
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    projectionFormulaMapOfComparison f hmos TD TC α E K =
      (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).unit.app
          ((Functor.uncurry.obj TD.tensor).obj ((derivedPushforward f).obj E, K)) ≫
        (derivedPushforward f).map
          (α.app ((derivedPushforward f).obj E, K) ≫
            (Functor.uncurry.obj TC.tensor).map
              ((DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).counit.app E ×ₘ
                𝟙 ((derivedPullback f).obj K))) :=
  CategoryTheory.adjunctionTensorMap_eq_unit_comp
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj TD.tensor) (Functor.uncurry.obj TC.tensor) α E K

end OfComparison

/-! ### Equation 21.50.0.1 -/

/-- **Equation 21.50.0.1 of [Stacks, Tag 0B56].**  For a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, `E ∈ D(O_C)` and `K ∈ D(O_D)`, the canonical map

`Rf_*E ⊗^L_{O_D} K ⟶ Rf_*(E ⊗^L_{O_C} Lf^*K)`,

with no further hypothesis.  It is the map adjoint, for the adjunction `Lf^* ⊣ Rf_*` of
[Stacks, Tag 07A6], to the bifunctorial identification
`Lf^*(Rf_*E ⊗^L K) ≅ Lf^*Rf_*E ⊗^L Lf^*K` of [Stacks, Tag 07A4] followed by the counit
`Lf^*Rf_*E ⟶ E` in the first factor. -/
@[stacks 0B56 "the map"]
def projectionFormulaMap (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E)).obj K ⟶
      (derivedPushforward f).obj
        (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj K)) :=
  projectionFormulaMapOfComparison f hmos (canonicalDerivedTensorProduct Y.O)
    (canonicalDerivedTensorProduct X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom E K

/-- Equation 21.50.0.1 is natural in `E` and in `K` jointly. -/
theorem projectionFormulaMap_naturality
    {E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (φ : E ⟶ E') (k : K ⟶ K') :
    (((derivedTensorProductFunctor Y.O).map ((derivedPushforward f).map φ)).app K ≫
          ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E')).map k) ≫
        projectionFormulaMap f hmos E' K' =
      projectionFormulaMap f hmos E K ≫
        (derivedPushforward f).map
          (((derivedTensorProductFunctor X.O).map φ).app ((derivedPullback f).obj K) ≫
            ((derivedTensorProductFunctor X.O).obj E').map ((derivedPullback f).map k)) :=
  projectionFormulaMapOfComparison_naturality f hmos (canonicalDerivedTensorProduct Y.O)
    (canonicalDerivedTensorProduct X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom φ k

/-- **Naturality of Equation 21.50.0.1 in the complex on the source**, `E ∈ D(O_C)`. -/
@[stacks 0B56 "naturality in the source complex"]
theorem projectionFormulaMap_naturality_source
    {E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (φ : E ⟶ E')
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((derivedTensorProductFunctor Y.O).map ((derivedPushforward f).map φ)).app K ≫
        projectionFormulaMap f hmos E' K =
      projectionFormulaMap f hmos E K ≫
        (derivedPushforward f).map
          (((derivedTensorProductFunctor X.O).map φ).app ((derivedPullback f).obj K)) := by
  simpa using projectionFormulaMap_naturality f hmos φ (𝟙 K)

/-- **Naturality of Equation 21.50.0.1 in the complex on the target**, `K ∈ D(O_D)`. -/
@[stacks 0B56 "naturality in the target complex"]
theorem projectionFormulaMap_naturality_target
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (k : K ⟶ K') :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E)).map k ≫
        projectionFormulaMap f hmos E K' =
      projectionFormulaMap f hmos E K ≫
        (derivedPushforward f).map
          (((derivedTensorProductFunctor X.O).obj E).map ((derivedPullback f).map k)) := by
  simpa using projectionFormulaMap_naturality f hmos (𝟙 E) k

/-- Equation 21.50.0.1 written through the unit of `Lf^* ⊣ Rf_*`: the unit at
`Rf_*E ⊗^L K`, then `Rf_*` of the comparison of [Stacks, Tag 07A4] and of the counit in the
first factor. -/
theorem projectionFormulaMap_eq_unit_comp
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    projectionFormulaMap f hmos E K =
      (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).unit.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O)).obj
            ((derivedPushforward f).obj E, K)) ≫
        (derivedPushforward f).map
          ((Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app
              ((derivedPushforward f).obj E, K) ≫
            (Functor.uncurry.obj (derivedTensorProductFunctor X.O)).map
              ((DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).counit.app E ×ₘ
                𝟙 ((derivedPullback f).obj K))) :=
  projectionFormulaMapOfComparison_eq_unit_comp f hmos (canonicalDerivedTensorProduct Y.O)
    (canonicalDerivedTensorProduct X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom E K

end Stacks.Cohomology.ProjectionFormulaOnRingedTopoi

/-! ### Compatibility with base change, over abstract adjunctions

The remark [Stacks, Tag 0E48] is a statement about two adjunctions, two further functors, four
bifunctors and four comparisons; no sheaf, complex or derived category enters its proof.  It is
therefore proved here in that generality and instantiated in
`ProjectionFormulaBaseChange.lean`, which is the same
factorization `Stacks.CategoryTheory.BaseChange` performs for the base change map itself and for
the same reason: `derivedPullback` and `derivedPushforward` are reducible abbreviations over
total derived functors, and rewriting inside a goal mentioning six of them builds a proof term
the kernel cannot check in its budget. -/

namespace Stacks.AffineProjectionFormula

section Square

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- The comparison `Lg ⋙ Lf' ≅ Lf ⋙ Lg'` of the two composites around a square both of which are
identified with one functor `Lc`.  This is the morphism underlying
`Stacks.CategoryTheory.BaseChange.pullbackComparison`, kept as an isomorphism because the
compatibility below uses its inverse as well. -/
def squareCompositeIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg' := eg ≪≫ ef.symm

lemma squareCompositeIso_hom_app (X : S) :
    (squareCompositeIso eg ef).hom.app X = eg.hom.app X ≫ ef.inv.app X := rfl

lemma squareCompositeIso_inv_app (X : S) :
    (squareCompositeIso eg ef).inv.app X = ef.hom.app X ≫ eg.inv.app X := rfl

/-- The adjunct of the base change map, in the form "apply `Lf'`, then the counit": it is the
comparison of the two composites around the square followed by `Lg'` of the counit of `Lf ⊣ Rf`.
This is `Stacks.CategoryTheory.BaseChange.homEquiv_symm_map` written without
`Adjunction.homEquiv`. -/
@[reassoc]
lemma map_baseChangeMap_comp_counit (W : T) :
    Lf'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef W) ≫
        adjf'.counit.app (Lg'.obj W) =
      (squareCompositeIso eg ef).hom.app (Rf.obj W) ≫ Lg'.map (adjf.counit.app W) := by
  have h := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map adjf adjf' eg ef W
  rw [Adjunction.homEquiv_counit] at h
  rw [h, squareCompositeIso_hom_app, Category.assoc]

/-- Naturality of a tensor comparison `α` in its first variable, with the second fixed. -/
private theorem map_comp_tensorComparison_app_prod_id {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {A : C × C ⥤ C} {B : D × D ⥤ D} (α : A ⋙ L ⟶ L.prod L ⋙ B) {M M' : C}
    (g : M ⟶ M') (N : C) :
    L.map (A.map (g ×ₘ 𝟙 N)) ≫ α.app (M', N) =
      α.app (M, N) ≫ B.map (L.map g ×ₘ 𝟙 (L.obj N)) := by
  simpa using α.naturality (g ×ₘ 𝟙 N)

variable (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')

/-- **The compatibility of four tensor comparisons around a square.**  Each of the four functors
of the square carries a comparison of the bifunctor downstairs with the bifunctor upstairs, and
the two composites around the square are identified by `squareCompositeIso`.  This says that
going down then across and going across then down give the same comparison at the pair `(M, N)`,
after transport along that identification.

When the two composites around the square are literally the same functor and the identification
is the identity — which is how the source of [Stacks, Tag 0E48] reads the square — this holds by
definition and is invisible.  It is the one input of
`adjunctionTensorMap_baseChange_square`. -/
def TensorComparisonCompatible (M N : S) : Prop :=
  Lf'.map (αg.app (M, N)) ≫
      αf'.app (Lg.obj M, Lg.obj N) ≫
        B'.map ((squareCompositeIso eg ef).hom.app M ×ₘ (squareCompositeIso eg ef).hom.app N) =
    (squareCompositeIso eg ef).hom.app (A.obj (M, N)) ≫
      Lg'.map (αf.app (M, N)) ≫ αg'.app (Lf.obj M, Lf.obj N)

/-- **[Stacks, Tag 0E48] over abstract adjunctions.**  For a square of categories in which the
two horizontal functors `Lf`, `Lf'` have right adjoints and the two composites around the square
are identified with one functor, and for bifunctors on the four corners with a comparison along
each of the four functors, the canonical map `adjunctionTensorMap` of the vertical adjunctions is
compatible with the base change map `Stacks.CategoryTheory.BaseChange.map`: the hexagon of the
remark commutes.

The only input is `TensorComparisonCompatible`; everything else is the adjunction calculus.
Concretely: both composites are maps into `Rf'`-of-something, so it is enough to compare their
adjuncts under `Lf' ⊣ Rf'`.  Those adjuncts are computed by
`map_adjunctionTensorMap_comp_counit` and `map_baseChangeMap_comp_counit`, after which the left
one is the comparison along `Lg` then along `Lf'` with the counit of `Lf ⊣ Rf` in the first
factor, and the right one is the comparison along `Lf` then along `Lg'` with the same counit in
the same factor; the compatibility identifies them. -/
theorem adjunctionTensorMap_baseChange_square (E : T) (K : S)
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' (Rf.obj E) K) :
    αg.app (Rf.obj E, K) ≫
        A'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef E ×ₘ 𝟙 (Lg.obj K)) ≫
          adjunctionTensorMap adjf' A' B' αf' (Lg'.obj E) (Lg.obj K) =
      Lg.map (adjunctionTensorMap adjf A B αf E K) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (B.obj (E, Lf.obj K)) ≫
          Rf'.map (αg'.app (E, Lf.obj K) ≫
            B'.map (𝟙 (Lg'.obj E) ×ₘ (squareCompositeIso eg ef).inv.app K)) := by
  rw [TensorComparisonCompatible] at hsq
  have h1 := map_comp_tensorComparison_app_prod_id αf'
    (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef E) (Lg.obj K)
  have h2 : Lf'.map (Lg.map (adjunctionTensorMap adjf A B αf E K)) ≫
      (squareCompositeIso eg ef).hom.app (Rf.obj (B.obj (E, Lf.obj K))) =
      (squareCompositeIso eg ef).hom.app (A.obj (Rf.obj E, K)) ≫
        Lg'.map (Lf.map (adjunctionTensorMap adjf A B αf E K)) := by
    have h := (squareCompositeIso eg ef).hom.naturality
      (adjunctionTensorMap adjf A B αf E K)
    simpa using h
  have h3 := map_comp_tensorComparison_app_prod_id αg' (adjf.counit.app E) (Lf.obj K)
  refine (adjf'.homEquiv _ _).symm.injective ?_
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    map_adjunctionTensorMap_comp_counit,
    Adjunction.counit_naturality, Adjunction.counit_naturality_assoc,
    map_baseChangeMap_comp_counit_assoc]
  conv_lhs => rw [reassoc_of% h1, ← Functor.map_comp, prod_comp, Category.comp_id,
    map_baseChangeMap_comp_counit]
  conv_rhs => rw [reassoc_of% h2, ← Functor.map_comp_assoc,
    map_adjunctionTensorMap_comp_counit, Functor.map_comp, Category.assoc,
    reassoc_of% h3, ← Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp,
    ← reassoc_of% hsq, ← Functor.map_comp, prod_comp, Iso.hom_inv_id_app]
  rfl

end Square

end Stacks.AffineProjectionFormula

/-! ### Remark 21.50.2: the identification `c` of the two iterated derived pullbacks -/

open Stacks.Cohomology.DerivedBaseChangeOnTopoi Stacks.Sheaves.DerivedPullback

namespace Stacks.Cohomology.ProjectionFormulaOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

section BaseChangeSquare

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (g' : RingedToposSiteHom X' X)
  (f' : RingedToposSiteHom X' Y') (g : RingedToposSiteHom Y' Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp g')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg' : g'.u.IsMorphismOfSites X.J X'.J)
  (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J) (hmosg : g.u.IsMorphismOfSites Y.J Y'.J)
  (h : g.comp f' = f.comp g')

/-- **The identification `c` of [Stacks, Tag 0E48].**  For a commutative square of ringed topoi,
the comparison `L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` of the two iterated derived pullbacks around it:
each is identified with the derived pullback along the common composite by [Stacks, Tag 0D6D],
and this is the resulting isomorphism.  The source writes it as the equality of functors
`L(g')^* ∘ Lf^* = L(f')^* ∘ Lg^*`. -/
def derivedPullbackSquareIso :
    derivedPullback g ⋙ derivedPullback f' ≅ derivedPullback f ⋙ derivedPullback g' :=
  Stacks.AffineProjectionFormula.squareCompositeIso
    (derivedPullbackCompIsoLeft f' g hmosf' hmosg)
    (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h)

end BaseChangeSquare

end Stacks.Cohomology.ProjectionFormulaOnRingedTopoi

end

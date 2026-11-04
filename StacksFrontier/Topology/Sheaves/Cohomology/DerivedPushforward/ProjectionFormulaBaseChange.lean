module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductBaseChange

/-!
# The projection-formula map is compatible with a commutative square of ringed spaces

Let

```
            g'
    X' ----------→ X
    |              |
 f' |              | f
    v      g       v
    Y' ----------→ Y
```

be a commutative square of ringed spaces, `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`.  Stacks 0B6B asserts
that the diagram

```
                                   Lg^*(p for f)
  Lg^*(Rf_*E ⊗^L_{𝒪_Y} K) --------------------------→ Lg^*Rf_*(E ⊗^L_{𝒪_X} Lf^*K)
            | t for g                                            | b
            v                                                    v
  Lg^*Rf_*E ⊗^L_{𝒪_{Y'}} Lg^*K                       Rf'_*L(g')^*(E ⊗^L_{𝒪_X} Lf^*K)
            | b ⊗ 1                                              | Rf'_*(t for g')
            v                                                    v
  Rf'_*L(g')^*E ⊗^L_{𝒪_{Y'}} Lg^*K                   Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} L(g')^*Lf^*K)
            | p for f'                                           | Rf'_*c
            v                                                    v
  Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} L(f')^*Lg^*K) =========== Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} L(f')^*Lg^*K)
```

commutes in `D(𝒪_{Y'})`: the arrows marked `p` are the derived projection-formula map of
Stacks 0B53, those marked `t` the comparison of derived pullback with the derived tensor
product of Stacks 079U, those marked `b` the derived base change map of Stacks 08HY, and `c` is
the identification of the two iterated derived pullbacks around the square.  The source's proof
is "We omit the verification"; the proof below is complete, with no hypothesis beyond
commutativity of the square and no hypothesis at all on `E` and `K`.

## Main definitions

* `Stacks.Cohomology.DerivedProjectionFormula.ProjectionFormulaBaseChangeSquare`: the diagram
  itself, as a predicate on a projection-formula map, two base change maps, an identification
  and a second projection-formula map, over arbitrary categories, functors and bifunctors.
* `Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackSquareIso`: the identification `c`,
  `Lg^* ⋙ L(f')^* ≅ Lf^* ⋙ L(g')^*`, which the source writes as an equality of functors.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_derivedBaseChangeMap`:
  **Stacks 0B6B**, the diagram above at the derived projection-formula map of Stacks 0B53 and
  the derived base change map of Stacks 08HY, for arbitrary `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`.
* `Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare`:
  the coherence of the four comparisons of Stacks 079U around the square, read at the shape the
  abstract diagram chase consumes.

## Implementation notes

*Where the diagram chase is.*  Not here.  The whole of it is
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`, carried out over
arbitrary categories, adjunctions and bifunctors for the canonical map
`CategoryTheory.adjunctionTensorMap` of an adjunction and the
canonical base change map `Stacks.CategoryTheory.BaseChange.map` of a square of adjunctions.
The derived projection-formula map of Stacks 0B53 and the derived base change map of Stacks 08HY
are those two constructions at the derived adjunctions of Stacks 079W, so the geometric
statement below is one argument-passing application of it.

*What the abstract chase leaves open, and why it is available here.*  Its single hypothesis is
`Stacks.AffineProjectionFormula.TensorComparisonCompatible`: the comparison of Stacks 079U along
a composite is the composite of the two comparisons, for the two ways around the square.  That
is the same input `Stacks.Cohomology.DerivedRelativeCupProduct.ComparisonCompatibleWithSquare`
asks for, and for ringed spaces it is a theorem,
`Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square`, proved
from the composition law
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` for the two
factorizations of the common composite.  The two spellings of the coherence differ by
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.compComparison_app` and one associativity,
which is `tensorComparisonCompatible_of_comparisonSquare`.  So nothing is assumed here and the
`stacks` attribute below carries no clause; the ringed-topos statement
`Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square` of
Stacks 0E48 likewise discharges it, by
`Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso`.

*Why the diagram is a predicate applied to the canonical maps.*  The derived pullbacks and
pushforwards are reducible abbreviations over total derived functors, and the four categories
here are spelled one way by the pullback development
(`SheafOfModules (structureSheafRing X)`) and another by the tensor-product
development.  A diagram written out at those and proved by one application of the abstract chase
elaborates and then fails the kernel; stating it as a predicate over abstract data and applying
it to the canonical maps keeps every concrete declaration an application of one head symbol to
arguments, which is what the kernel can check here.  The same factorization is performed for the
hexagon of Stacks 0H99 in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductBaseChange.lean`,
and for the same reason.  Nothing is weakened:
`ProjectionFormulaBaseChangeSquare` is an `@[expose]` definition whose body is the diagram, and
the canonical maps appear in it as arguments.

*Two names for the abstract projection-formula map.*  The ringed-space development of Stacks
0B53 is written at `CategoryTheory.adjunctionTensorMap` and the
abstract chase at `CategoryTheory.adjunctionTensorMap`; the two definitions have
the same body, so the `Mate` layer below is stated at the first and proved by the chase at the
second, and the reduction between them is taken over variables where it is free.

*The sheafification binders.*  `HasSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat.{u}`
on the four sites of opens are the binders the derived tensor product of Stacks 06YU is stated
under.  Both are `Prop`s and both are inhabited for every ringed space, by
`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, so they are not a weakening.

## References

* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.DerivedProjectionFormula

/-! ### The diagram, as a predicate on abstract data -/

section Predicate

variable {P P' Q Q' : Type*} [Category P] [Category P'] [Category Q] [Category Q']

/-- **The diagram of Stacks 0B6B.**

For right adjoints `Rf`, `Rf'` along the vertical edges of a commutative square, functors `Lg`,
`Lg'` along its horizontal edges, bifunctors `AP`, `AQ`, `AP'`, `AQ'` on the four categories
compared along `Lg` and `Lg'` by `αg` and `αg'`, an identification `c` of `Lg' (Lf K)` with
`Lf' (Lg K)`, and objects `E`, `K`, this says that

* the comparison `αg` at `(Rf E, K)`, followed by the base change map `bcE` in the first tensor
  factor and by the projection-formula map `p'` for the other vertical edge,

equals

* `Lg` of the projection-formula map `p`, followed by the base change map `bc` at `AQ (E, Lf K)`
  and by `Rf'` of the comparison `αg'` and of `c` in the second tensor factor.

Taking `p` and `p'` to be the derived projection-formula map of Stacks 0B53, `bc` and `bcE` the
derived base change map of Stacks 08HY and `c` the identification `derivedPullbackSquareIso`
gives exactly the diagram of Stacks 0B6B; that is
`projectionFormulaMap_derivedBaseChangeMap`. -/
def ProjectionFormulaBaseChangeSquare (Rf : Q ⥤ P) (Rf' : Q' ⥤ P') (Lf : P ⥤ Q) (Lf' : P' ⥤ Q')
    (Lg : P ⥤ P') (Lg' : Q ⥤ Q')
    (AP : P × P ⥤ P) (AQ : Q × Q ⥤ Q) (AP' : P' × P' ⥤ P') (AQ' : Q' × Q' ⥤ Q')
    (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
    (E : Q) (K : P)
    (p : AP.obj (Rf.obj E, K) ⟶ Rf.obj (AQ.obj (E, Lf.obj K)))
    (bc : Lg.obj (Rf.obj (AQ.obj (E, Lf.obj K))) ⟶ Rf'.obj (Lg'.obj (AQ.obj (E, Lf.obj K))))
    (bcE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (c : Lg'.obj (Lf.obj K) ⟶ Lf'.obj (Lg.obj K))
    (p' : AP'.obj (Rf'.obj (Lg'.obj E), Lg.obj K) ⟶
      Rf'.obj (AQ'.obj (Lg'.obj E, Lf'.obj (Lg.obj K)))) : Prop :=
  αg.app (Rf.obj E, K) ≫ AP'.map (bcE ×ₘ 𝟙 (Lg.obj K)) ≫ p' =
    Lg.map p ≫ bc ≫ Rf'.map (αg'.app (E, Lf.obj K) ≫ AQ'.map (𝟙 (Lg'.obj E) ×ₘ c))

/-- **The coherence of the four comparisons around a square, read at the shape the diagram chase
consumes.**

`Stacks.Cohomology.DerivedRelativeCupProduct.ComparisonCompatibleWithSquare` and
`Stacks.AffineProjectionFormula.TensorComparisonCompatible` are the same assertion: the
identification `eg.hom ≫ ef.inv` of the two composites around the square carries the composite
comparison down-then-across to the composite comparison across-then-down.  The first spells the
two composite comparisons through
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.compComparison` and brackets the left-hand
side to the left; the second writes them out and brackets to the right. -/
lemma tensorComparisonCompatible_of_comparisonSquare
    {Lg : P ⥤ P'} {Lf' : P' ⥤ Q'} {Lf : P ⥤ Q} {Lg' : Q ⥤ Q'} {Lc : P ⥤ Q'}
    (AP : P × P ⥤ P) (AP' : P' × P' ⥤ P') (AQ : Q × Q ⥤ Q) (AQ' : Q' × Q' ⥤ Q')
    (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αf' : AP' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ AQ')
    (αf : AP ⋙ Lf ⟶ Lf.prod Lf ⋙ AQ) (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
    {eg : Lg ⋙ Lf' ≅ Lc} {ef : Lf ⋙ Lg' ≅ Lc}
    (h : Stacks.Cohomology.DerivedRelativeCupProduct.ComparisonCompatibleWithSquare
      AP AP' AQ AQ' αg αf' αf αg' eg ef) (M N : P) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef AP AP' AQ AQ'
      αf αf' αg αg' M N := by
  simpa only [Stacks.AffineProjectionFormula.TensorComparisonCompatible,
    Stacks.AffineProjectionFormula.squareCompositeIso_hom_app,
    Stacks.Cohomology.RelativeCupProductOnRingedTopoi.compComparison_app,
    NatTrans.comp_app, Category.assoc] using h M N

end Predicate

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The diagram over abstract derived functors -/

section Mate

variable {X' X Y' Y : RingedSpace.{u, u}}
  {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
  {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))}
  {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))}
  {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  (AP : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (AQ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
  (AP' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')))
  (AQ' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
  (αf : AP ⋙ Lf ⟶ Lf.prod Lf ⋙ AQ) (αf' : AP' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ AQ')
  (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The diagram of Stacks 0B6B over abstract functors, adjunctions and bifunctors.**

This is `Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square` read as
`ProjectionFormulaBaseChangeSquare`, and restated for the two constructions the canonical
statement is phrased with: the abstract projection-formula map
`CategoryTheory.adjunctionTensorMap`, of which the derived
projection-formula map of Stacks 0B53 is an instance, and
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap`, of which the derived base
change map of Stacks 08HY is an instance.  Both agree with the constructions that lemma uses by
delta-reduction alone, and over variables those reductions are free. -/
lemma adjunctionTensorMap_derivedBaseChangeMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef AP AP' AQ AQ'
      αf αf' αg αg' (Rf.obj E) K) :
    ProjectionFormulaBaseChangeSquare Rf Rf' Lf Lf' Lg Lg' AP AQ AP' AQ' αg αg' E K
      (CategoryTheory.adjunctionTensorMap adjf AP AQ αf E K)
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef
        (AQ.obj (E, Lf.obj K)))
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef E)
      ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app K)
      (CategoryTheory.adjunctionTensorMap adjf' AP' AQ' αf'
        (Lg'.obj E) (Lg.obj K)) :=
  Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square adjf adjf' eg ef
    AP AP' AQ AQ' αf αf' αg αg' E K hsq

end Mate

/-! ### Stacks 0B6B -/

section Canonical

variable {X' X Y' Y : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : g' ≫ f = f' ≫ g)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The identification `c` of Stacks 0B6B.**  For a commutative square of ringed spaces, the
comparison `Lg^* ⋙ L(f')^* ≅ Lf^* ⋙ L(g')^*` of the two iterated derived pullbacks around it:
each is identified with the derived pullback along the common composite by the composition
isomorphism of Stacks 0D5S, and this is the resulting isomorphism.  The source writes it as the
equality of functors `L(g')^* ∘ Lf^* = L(f')^* ∘ Lg^*`. -/
def derivedPullbackSquareIso :
    derivedPullback g ⋙ derivedPullback f' ≅ derivedPullback f ⋙ derivedPullback g' :=
  Stacks.AffineProjectionFormula.squareCompositeIso
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f)

/-- **Stacks 0B6B: the derived projection-formula map is compatible with a commutative square of
ringed spaces.**

For a commutative square `g' ≫ f = f' ≫ g` of ringed spaces and arbitrary `E ∈ D(𝒪_X)`,
`K ∈ D(𝒪_Y)`, the diagram `ProjectionFormulaBaseChangeSquare` commutes at the derived
projection-formula map of Stacks 0B53 for `f` and for `f'`, the derived base change map of
Stacks 08HY and the identification `derivedPullbackSquareIso`: the comparison of Stacks 079U for
`g`, followed by base change in the first tensor factor and by the projection-formula map for
`f'`, equals the derived pullback along `g` of the projection-formula map for `f`, followed by
base change and by `Rf'_*` of the comparison of Stacks 079U for `g'` and of the identification
in the second tensor factor.

There is no boundedness, flatness or quasi-coherence hypothesis on `E` and `K`, and no
associator or symmetry of `⊗^L` is used: the diagram has binary tensor products only. -/
@[stacks 0B6B]
theorem projectionFormulaMap_derivedBaseChangeMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ProjectionFormulaBaseChangeSquare (derivedPushforward f) (derivedPushforward f')
      (derivedPullback f) (derivedPullback f') (derivedPullback g) (derivedPullback g')
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor Y'.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.sheaf))
      (pullbackTensorComparison g) (pullbackTensorComparison g') E K
      (projectionFormulaMap f E K)
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq
        ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
          (E, (derivedPullback f).obj K)))
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq E)
      ((derivedPullbackSquareIso g' f' f g sq).inv.app K)
      (projectionFormulaMap f' ((derivedPullback g').obj E) ((derivedPullback g).obj K)) :=
  adjunctionTensorMap_derivedBaseChangeMap (derivedAdjunction f) (derivedAdjunction f')
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor Y'.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.sheaf))
    (pullbackTensorComparison f) (pullbackTensorComparison f')
    (pullbackTensorComparison g) (pullbackTensorComparison g')
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f) E K
    (tensorComparisonCompatible_of_comparisonSquare _ _ _ _ _ _ _ _
      (Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square
        g' f' f g sq) _ _)

end Canonical

end Stacks.Cohomology.DerivedProjectionFormula

end

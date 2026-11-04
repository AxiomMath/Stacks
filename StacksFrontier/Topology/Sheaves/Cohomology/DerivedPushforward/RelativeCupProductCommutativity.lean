module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product is commutative

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Stacks 0FP5 asserts that the
relative cup product of Stacks 0B68 is commutative: for all `K, L ∈ D(𝒪_X)` the square

```
Rf_*K ⊗^L_{𝒪_Y} Rf_*L ------> Rf_*(K ⊗^L_{𝒪_X} L)
        |                              |
        | ψ                            | Rf_*ψ
        v                              v
Rf_*L ⊗^L_{𝒪_Y} Rf_*K ------> Rf_*(L ⊗^L_{𝒪_X} K)
```

commutes in `D(𝒪_Y)`, the horizontal arrows being the relative cup product and `ψ` the
commutativity constraint on the derived category of Stacks 0FPB.

## Main definitions

* `Stacks.Cohomology.DerivedRelativeCupProduct.PullbackTensorComparisonBraided`: the derived
  pullback–tensor comparison of Stacks 079U is compatible with the commutativity constraints
  of `D(𝒪_Y)` and `D(𝒪_X)`, i.e. `Lf^*` carries `ψ` to `ψ` through the comparison.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_braiding`: the abstract
  form.  For an adjunction `L ⊣ R`, bifunctors `A` on the source and `B` on the target, a
  comparison `α : A ⋙ L ⟶ (L × L) ⋙ B`, and symmetries `sA`, `sB` of the two bifunctors with
  `sB` natural and `α` compatible with them, the doubled-counit adjunction morphism of
  `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap` commutes with `sA` and
  `sB`.
* `Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonBraided`: the derived
  pullback–tensor comparison of Stacks 079U *is* compatible with the commutativity constraints.
* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_braiding`: the geometric
  statement, for arbitrary `K, L ∈ D(𝒪_X)` and with no finiteness, flatness or quasi-coherence
  hypothesis.

## Implementation notes

The source's proof is "Omitted".  Written out, the square is the image under the adjunction
bijection `Hom(Lf^*-, -) ≅ Hom(-, Rf_*-)` of the statement that

`Lf^*(ψ) ≫ α` and `α ≫ ψ`

agree, where `α` is the derived pullback–tensor comparison of Stacks 079U, followed in both
cases by the counit in the two tensor factors.  Naturality of `ψ` disposes of the counits, so
the whole content of Stacks 0FP5 is that `Lf^*` is a *braided* monoidal functor and not merely
a monoidal one.  `adjunctionBitensorMap_braiding` is that reduction, carried out at the
generality of an arbitrary adjunction and arbitrary symmetries of the two bifunctors, and
assumes nothing about ringed spaces.

`pullbackTensorComparisonBraided` rests on two statements: the compatibility of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison` with the braiding, which is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding` of Stacks 0FPT, and the
compatibility of `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` with the
Koszul symmetry of total tensor complexes, which is
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_braiding`; the fusion of the
two along the K-flat descent of Stacks 06YS is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`.

*The commutativity constraint.*  `ψ` is the braiding of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, which is the symmetry of
Stacks 0FPB re-seated so that its tensor product is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of Stacks 06YU on the nose — the
same bifunctor the relative cup product of Stacks 0B68 is stated over, so no transport appears
in the statement.  Its sign convention is therefore the Koszul one, `(-1)^{pq}` on the summand
of bidegree `(p, q)`, which is the convention of
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` and of
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison_braiding`; the source's `ψ` is the
commutativity constraint of Stacks 0FPB, whose signs the source fixes in More on Algebra,
Section 0FNG, and these are the same.

*Spelling of the module categories.*  As in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/KunnethMapForExt.lean`, the derived
categories are written at `Stacks.SheafOfModules.DerivedMonoidal.Mod Z.sheaf`, which is the
spelling the monoidal structure is stated over.  The spelling
`SheafOfModules (structureSheafRing Z)` that the pullback/pushforward
development uses is the same type by `rfl`, but only through a definition that instance search
does not unfold, so `structureSheafRing` is made reducible at implicit
transparency here, exactly as in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorComparison.lean`.

## References

* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.DerivedRelativeCupProduct

/-! ### The abstract statement -/

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  (sA : ∀ M N : C, A.obj (M, N) ⟶ A.obj (N, M))
  (sB : ∀ G G' : D, B.obj (G, G') ⟶ B.obj (G', G))

/-- **The abstract relative cup product is commutative.**  If `sB` is natural and the
comparison `α` carries `sA` to `sB`, then the doubled-counit adjunction morphism
`adjunctionBitensorMap` commutes with the two symmetries. -/
theorem adjunctionBitensorMap_braiding
    (hsB : ∀ {G G' H H' : D} (g : G ⟶ H) (g' : G' ⟶ H'),
      B.map (g ×ₘ g') ≫ sB H H' = sB G G' ≫ B.map (g' ×ₘ g))
    (hα : ∀ M N : C,
      L.map (sA M N) ≫ α.app (N, M) = α.app (M, N) ≫ sB (L.obj M) (L.obj N))
    (G G' : D) :
    sA (R.obj G) (R.obj G') ≫ adjunctionBitensorMap adj A B α G' G =
      adjunctionBitensorMap adj A B α G G' ≫ R.map (sB G G') := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionBitensorMap
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  rw [← Category.assoc, hα]
  simp only [Category.assoc]
  rw [hsB]

end Abstract

/-! ### The morphism of ringed spaces -/

universe u

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

-- The pullback/pushforward development and the tensor-product development name the structure
-- sheaf of a ringed space differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`; see the implementation notes.
attribute [local implicit_reducible] structureSheafRing

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The symmetry of the derived tensor product of Stacks 06YU on a ringed space: the braiding
of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, read on the uncurried
bifunctor the relative cup product is stated over. -/
def derivedBraiding (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G G' : DerivedCategory (Mod Z.sheaf)) :
    (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj (G, G') ⟶
      (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj (G', G) :=
  letI := canonicalDerivedMonoidal Z.sheaf
  letI := canonicalDerivedSymmetric Z.sheaf
  (β_ G G').hom

/-- The symmetry of the derived tensor product is the braiding of the symmetric monoidal
structure of Stacks 0FPB whose tensor product is the derived tensor product. -/
theorem derivedBraiding_eq (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G G' : DerivedCategory (Mod Z.sheaf)) :
    letI := canonicalDerivedMonoidal Z.sheaf
    letI := canonicalDerivedSymmetric Z.sheaf
    derivedBraiding Z G G' = (β_ G G').hom :=
  rfl

/-- The symmetry of the derived tensor product is natural in both derived modules. -/
theorem derivedBraiding_naturality (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {G G' H H' : DerivedCategory (Mod Z.sheaf)} (g : G ⟶ H) (g' : G' ⟶ H') :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (g ×ₘ g') ≫ derivedBraiding Z H H' =
      derivedBraiding Z G G' ≫
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
          (g' ×ₘ g) :=
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  BraidedCategory.braiding_naturality g g'

/-- **The derived pullback–tensor comparison of Stacks 079U is compatible with the
commutativity constraints** of `D(𝒪_Y)` and `D(𝒪_X)`: `Lf^*` carries the commutativity
constraint of Stacks 0FPB on `D(𝒪_Y)` to the one on `D(𝒪_X)` through the comparison.  It is
proved by `pullbackTensorComparisonBraided`. -/
def PullbackTensorComparisonBraided : Prop :=
  ∀ M N : DerivedCategory (Mod Y.sheaf),
    (derivedPullback f).map (derivedBraiding Y M N) ≫
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app (N, M) =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app (M, N) ≫
        derivedBraiding X ((derivedPullback f).obj M) ((derivedPullback f).obj N)

/-- **The derived pullback–tensor comparison of Stacks 079U is compatible with the
commutativity constraints of Stacks 0FPB.**  On a pair of K-flat complexes the comparison is
computed by the ordinary total tensor complex, the commutativity constraint of Stacks 0FPB is
computed there by the Koszul symmetry of complexes (Stacks 0FPT), and the comparison of total
tensor complexes of Stacks 01CD is braided for that symmetry; the three are fused and descended
to all of `D(𝒪_Y) × D(𝒪_Y)` by
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`. -/
theorem pullbackTensorComparisonBraided : PullbackTensorComparisonBraided f := fun M N =>
  Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding f M N

/-- **The relative cup product is commutative.**  For a morphism of ringed spaces
`f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and arbitrary `K, L ∈ D(𝒪_X)` the square

```
Rf_*K ⊗^L Rf_*L ⟶ Rf_*(K ⊗^L L)
      |                  |
      ψ                 Rf_*ψ
      v                  v
Rf_*L ⊗^L Rf_*K ⟶ Rf_*(L ⊗^L K)
```

commutes in `D(𝒪_Y)`, where the horizontal arrows are the relative cup product of Stacks 0B68
and `ψ` is the commutativity constraint of Stacks 0FPB.  The compatibility of the comparison of
Stacks 079U with those constraints is `pullbackTensorComparisonBraided`. -/
@[stacks 0FP5 "the whole tag: for a morphism of ringed spaces and arbitrary K, L in D(𝒪_X), the \
commutativity square of the relative cup product commutes.  The commutativity constraints are \
derivedBraiding of Stacks 0FPB, and their compatibility with the Stacks 079U comparison is \
pullbackTensorComparisonBraided"]
theorem relativeCupProduct_braiding (K L : DerivedCategory (Mod X.sheaf)) :
    derivedBraiding Y ((derivedPushforward f).obj K) ((derivedPushforward f).obj L) ≫
        relativeCupProduct f L K =
      relativeCupProduct f K L ≫ (derivedPushforward f).map (derivedBraiding X K L) :=
  adjunctionBitensorMap_braiding (derivedAdjunction f)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (derivedBraiding Y) (derivedBraiding X)
    (fun g g' => derivedBraiding_naturality X g g') (pullbackTensorComparisonBraided f) K L

end Stacks.Cohomology.DerivedRelativeCupProduct

end

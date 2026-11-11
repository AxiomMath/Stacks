module

public import StacksFrontier.CategoryTheory.BifunctorProdMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonAssociator
import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product is associative

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Stacks 0FP4 asserts that the
relative cup product of Stacks 0B68 is associative: for all `K, L, M ∈ D(𝒪_X)` the square

```
Rf_*K ⊗^L_{𝒪_Y} Rf_*L ⊗^L_{𝒪_Y} Rf_*M ---> Rf_*(K ⊗^L_{𝒪_X} L) ⊗^L_{𝒪_Y} Rf_*M
              |                                            |
              v                                            v
Rf_*K ⊗^L_{𝒪_Y} Rf_*(L ⊗^L_{𝒪_X} M) ----> Rf_*(K ⊗^L_{𝒪_X} L ⊗^L_{𝒪_X} M)
```

commutes in `D(𝒪_Y)`, all four arrows being relative cup products in one or the other tensor
factor.

## Main definitions

* `Stacks.Cohomology.DerivedRelativeCupProduct.derivedAssociator`: the associativity constraint
  of the derived tensor product of Stacks 06YU on a ringed space, read on the uncurried
  bifunctor the relative cup product is stated over.
* `Stacks.Cohomology.DerivedRelativeCupProduct.PullbackTensorComparisonAssociative`: the derived
  pullback–tensor comparison of Stacks 079U is compatible with the associativity constraints of
  `D(𝒪_Y)` and `D(𝒪_X)`, i.e. `Lf^*` carries the associator to the associator through the
  comparison.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_assoc`: the abstract form.
  For an adjunction `L ⊣ R`, bifunctors `A` on the source and `B` on the target, a comparison
  `α : A ⋙ L ⟶ (L × L) ⋙ B`, and associativity constraints `aA`, `aB` of the two bifunctors
  with `aB` natural and `α` compatible with them, the doubled-counit adjunction morphism of
  `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap` is associative.
* `Stacks.Cohomology.DerivedRelativeCupProduct.derivedAssociator_naturality`: the associativity
  constraint of the derived tensor product is natural in all three derived modules.
* `Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonAssociative`: the derived
  pullback–tensor comparison of Stacks 079U *is* compatible with the associativity constraints.
* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_assoc`: the geometric
  statement, **unconditionally**, for arbitrary `K, L, M ∈ D(𝒪_X)` and with no finiteness,
  flatness or quasi-coherence hypothesis.

## Implementation notes

*Where the content of the source lies.*  The source's proof is that "going around either side we
obtain the map adjoint to the obvious map

`Lf^*(Rf_*K ⊗^L Rf_*L ⊗^L Rf_*M) = Lf^*Rf_*K ⊗^L Lf^*Rf_*L ⊗^L Lf^*Rf_*M ⟶ K ⊗^L L ⊗^L M`".

Written out, that `=` is the comparison of Stacks 079U applied twice, and comparing the two
adjuncts needs exactly two facts: that the associator of the target is natural, which disposes
of the three counits, and that `Lf^*` carries the associator of `D(𝒪_Y)` to the associator of
`D(𝒪_X)` through the comparison — i.e. that `Lf^*` is a *monoidal* functor and not merely a
functor with a comparison.  `adjunctionBitensorMap_assoc` is that reduction, carried out at the
generality of an arbitrary adjunction and arbitrary associativity constraints of the two
bifunctors; it is complete and assumes nothing about ringed spaces.

*The source's suppressed brackets.*  The source writes `Rf_*K ⊗^L Rf_*L ⊗^L Rf_*M` and
`K ⊗^L L ⊗^L M` without brackets.  Neither is a Lean object, so the square below is bracketed to
the left in its upper-left corner and the two associators appear as honest arrows: `aA` on the
left edge, where the source's unbracketed source object has to be re-bracketed before the cup
product can be applied in the last two factors, and `Rf_*aB` at the end of the upper path, where
the two paths would otherwise land in `Rf_*((K ⊗ L) ⊗ M)` and `Rf_*(K ⊗ (L ⊗ M))`.  Nothing is
absorbed into a transport: both are maps between objects of one category that this development
has.

*NOTHING IS ASSUMED.*  `PullbackTensorComparisonAssociative` was carried as a hypothesis for as
long as the two statements it rests on were absent; both are now available, and
`pullbackTensorComparisonAssociative` discharges it, so `relativeCupProduct_assoc` is Stacks
0FP4 outright.  The two statements are the compatibility of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison` with the associator, which is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_associator` of Stacks 0FPT, and the
compatibility of `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` with the
associator of total tensor complexes, which is
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_associator`; the fusion of the
two along the K-flat descent of Stacks 06YS is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator`.  Everything else —
the whole adjunction calculus the source's one-paragraph proof refers to, and the naturality of
the associator — is proved here.

The ringed-topos counterpart of this statement, Stacks 0FPL, is
`Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_assoc`, for an arbitrary
morphism of ringed topoi.  Here, as there, the constraints are those of the monoidal structure of
Stacks 0FPB (`derivedAssociator`), their naturality is proved (`derivedAssociator_naturality`),
and the compatibility of the comparison is proved as well.

*The associativity constraint is the repository's own.*  `aA` and `aB` are the associators of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, the monoidal structure of
Stacks 0FPB re-seated so that its tensor product is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of Stacks 06YU on the nose — the
same bifunctor the relative cup product of Stacks 0B68 is stated over, so no comparison
isomorphism appears in the statement.

*Spelling of the module categories.*  As in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt`, the derived
categories are written at `Stacks.SheafOfModules.DerivedMonoidal.Mod Z.sheaf`, which is the
spelling the monoidal structure is stated over.  The spelling
`SheafOfModules (structureSheafRing Z)` that the pullback/pushforward
development uses is the same type by `rfl`, but only through a definition that instance search
does not unfold, so `structureSheafRing` is made reducible at implicit
transparency here, exactly as in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison`.

## References

* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FPL](https://stacks.math.columbia.edu/tag/0FPL)
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

/-- The defining property of `adjunctionBitensorMap`: its adjoint transpose is the comparison
followed by the counit of `L ⊣ R` in both factors. -/
lemma adjunctionBitensorMap_transpose (G G' : D) :
    L.map (adjunctionBitensorMap adj A B α G G') ≫ adj.counit.app (B.obj (G, G')) =
      α.app (R.obj G, R.obj G') ≫ B.map (adj.counit.app G ×ₘ adj.counit.app G') := by
  have h := (adj.homEquiv (A.obj (R.obj G, R.obj G')) (B.obj (G, G'))).symm_apply_apply
    (α.app (R.obj G, R.obj G') ≫ B.map (adj.counit.app G ×ₘ adj.counit.app G'))
  rwa [Adjunction.homEquiv_counit] at h

/-- The abstract relative cup product precomposed with a map, as a single adjoint transpose. -/
private lemma adjunctionBitensorMap_pre {Z : C} (G G' : D)
    (v : Z ⟶ A.obj (R.obj G, R.obj G')) :
    v ≫ adjunctionBitensorMap adj A B α G G' =
      adj.homEquiv _ _ (L.map v ≫ α.app (R.obj G, R.obj G') ≫
        B.map (adj.counit.app G ×ₘ adj.counit.app G')) := by
  unfold adjunctionBitensorMap
  rw [← Adjunction.homEquiv_naturality_left]
  rfl

/-- **The abstract relative cup product is associative.**  Let `aA` and `aB` be associativity
constraints for the two bifunctors, let `aB` be natural (`haB`), and let the comparison `α` be
compatible with the two constraints (`hα`, the associativity law of a monoidal functor).  Then
contracting the first two factors first and contracting the last two factors first give the same
map `A(A(R G₁, R G₂), R G₃) ⟶ R (B (G₁, B (G₂, G₃)))`. -/
theorem adjunctionBitensorMap_assoc
    (aA : ∀ P Q S : C, A.obj (A.obj (P, Q), S) ⟶ A.obj (P, A.obj (Q, S)))
    (aB : ∀ U V W : D, B.obj (B.obj (U, V), W) ⟶ B.obj (U, B.obj (V, W)))
    (haB : ∀ {U U' V V' W W' : D} (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W'),
      B.map (B.map (u ×ₘ v) ×ₘ w) ≫ aB U' V' W' =
        aB U V W ≫ B.map (u ×ₘ B.map (v ×ₘ w)))
    (hα : ∀ P Q S : C,
      α.app (A.obj (P, Q), S) ≫ B.map (α.app (P, Q) ×ₘ 𝟙 (L.obj S)) ≫
          aB (L.obj P) (L.obj Q) (L.obj S) =
        L.map (aA P Q S) ≫ α.app (P, A.obj (Q, S)) ≫ B.map (𝟙 (L.obj P) ×ₘ α.app (Q, S)))
    (G₁ G₂ G₃ : D) :
    A.map (adjunctionBitensorMap adj A B α G₁ G₂ ×ₘ 𝟙 (R.obj G₃)) ≫
        adjunctionBitensorMap adj A B α (B.obj (G₁, G₂)) G₃ ≫ R.map (aB G₁ G₂ G₃) =
      aA (R.obj G₁) (R.obj G₂) (R.obj G₃) ≫
        A.map (𝟙 (R.obj G₁) ×ₘ adjunctionBitensorMap adj A B α G₂ G₃) ≫
          adjunctionBitensorMap adj A B α G₁ (B.obj (G₂, G₃)) := by
  rw [← Category.assoc, adjunctionBitensorMap_pre, ← Adjunction.homEquiv_naturality_right,
    ← Category.assoc (aA _ _ _), adjunctionBitensorMap_pre]
  congr 1
  simp only [Category.assoc]
  -- Both adjuncts reduce to `L aA ≫ α ≫ B(1 ×ₘ α) ≫ B(ε ×ₘ B(ε ×ₘ ε))`.  The first seven
  -- rewrites bring the left-hand one into the shape of `hα` and apply it; the last six do the
  -- same to the right-hand one.
  rw [reassoc_of% (bifunctor_comparison_naturality A B α
        (adjunctionBitensorMap adj A B α G₁ G₂) (𝟙 (R.obj G₃))),
    L.map_id,
    ← reassoc_of% (bifunctor_map_comp_left B
        (L.map (adjunctionBitensorMap adj A B α G₁ G₂))
        (adj.counit.app (B.obj (G₁, G₂))) (adj.counit.app G₃)),
    adjunctionBitensorMap_transpose,
    reassoc_of% (bifunctor_map_comp_left B (α.app (R.obj G₁, R.obj G₂))
        (B.map (adj.counit.app G₁ ×ₘ adj.counit.app G₂)) (adj.counit.app G₃)),
    haB (U := L.obj (R.obj G₁)) (U' := G₁) (V := L.obj (R.obj G₂)) (V' := G₂)
        (W := L.obj (R.obj G₃)) (W' := G₃)
        (adj.counit.app G₁) (adj.counit.app G₂) (adj.counit.app G₃),
    reassoc_of% (hα (R.obj G₁) (R.obj G₂) (R.obj G₃)),
    L.map_comp, Category.assoc,
    reassoc_of% (bifunctor_comparison_naturality A B α (𝟙 (R.obj G₁))
        (adjunctionBitensorMap adj A B α G₂ G₃)),
    L.map_id,
    ← bifunctor_map_comp_right B (P := L.obj (R.obj G₁)) (P' := G₁) (adj.counit.app G₁)
        (L.map (adjunctionBitensorMap adj A B α G₂ G₃))
        (adj.counit.app (B.obj (G₂, G₃))),
    adjunctionBitensorMap_transpose,
    bifunctor_map_comp_right B (P := L.obj (R.obj G₁)) (P' := G₁) (adj.counit.app G₁)
        (α.app (R.obj G₂, R.obj G₃))
        (B.map (adj.counit.app G₂ ×ₘ adj.counit.app G₃))]

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

/-- The associativity constraint of the derived tensor product of Stacks 06YU on a ringed space:
the associator of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, read on the
uncurried bifunctor the relative cup product is stated over. -/
def derivedAssociator (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G G' G'' : DerivedCategory (Mod Z.sheaf)) :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj
        ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj (G, G'),
          G'') ⟶
      (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj
        (G, (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj (G', G'')) :=
  letI := canonicalDerivedMonoidal Z.sheaf
  (α_ G G' G'').hom

/-- The associativity constraint of the derived tensor product is the associator of the monoidal
structure of Stacks 0FPB whose tensor product is the derived tensor product. -/
theorem derivedAssociator_eq (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G G' G'' : DerivedCategory (Mod Z.sheaf)) :
    letI := canonicalDerivedMonoidal Z.sheaf
    derivedAssociator Z G G' G'' = (α_ G G' G'').hom :=
  rfl

/-- The associativity constraint of the derived tensor product is natural in all three derived
modules. -/
theorem derivedAssociator_naturality (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {G G' G'' H H' H'' : DerivedCategory (Mod Z.sheaf)}
    (u : G ⟶ H) (v : G' ⟶ H') (w : G'' ⟶ H'') :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
          (u ×ₘ v) ×ₘ w) ≫
        derivedAssociator Z H H' H'' =
      derivedAssociator Z G G' G'' ≫
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
          (u ×ₘ (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map (v ×ₘ w)) :=
  let := canonicalDerivedMonoidal Z.sheaf
  MonoidalCategory.associator_naturality u v w

/-- **The derived pullback–tensor comparison of Stacks 079U is compatible with the associativity
constraints** of `D(𝒪_Y)` and `D(𝒪_X)`: `Lf^*` carries the associator of the monoidal structure
of Stacks 0FPB on `D(𝒪_Y)` to the one on `D(𝒪_X)` through the comparison.  It is proved by
`pullbackTensorComparisonAssociative`; the statement is kept as a named proposition because it
is what the diagram chase of `adjunctionBitensorMap_assoc` consumes. -/
def PullbackTensorComparisonAssociative : Prop :=
  ∀ M N P : DerivedCategory (Mod Y.sheaf),
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app
          ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj (M, N),
            P) ≫
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
          ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app (M, N) ×ₘ
            𝟙 ((derivedPullback f).obj P)) ≫
          derivedAssociator X ((derivedPullback f).obj M) ((derivedPullback f).obj N)
            ((derivedPullback f).obj P) =
      (derivedPullback f).map (derivedAssociator Y M N P) ≫
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app
            (M, (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj (N, P)) ≫
          (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            (𝟙 ((derivedPullback f).obj M) ×ₘ
              (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app (N, P))


/-- **The derived pullback–tensor comparison of Stacks 079U is compatible with the associativity
constraints of Stacks 0FPB.**  On a triple of K-flat complexes the comparison is computed by the
ordinary total tensor complex, the associativity constraint of Stacks 0FPB is computed there by
the associator of complexes (Stacks 0FPT), and the comparison of total tensor complexes of
Stacks 01CD is compatible with that associator; the three are fused and descended to all of
`D(𝒪_Y) × D(𝒪_Y) × D(𝒪_Y)` by
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator`. -/
theorem pullbackTensorComparisonAssociative : PullbackTensorComparisonAssociative f :=
  fun M N P =>
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator f M N P

/-- **The relative cup product is associative.**  For a morphism of ringed spaces
`f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and arbitrary `K, L, M ∈ D(𝒪_X)` the square

```
(Rf_*K ⊗^L Rf_*L) ⊗^L Rf_*M ⟶ Rf_*(K ⊗^L L) ⊗^L Rf_*M ⟶ Rf_*((K ⊗^L L) ⊗^L M)
            |                                                      |
            | a                                                    | Rf_*a
            v                                                      v
Rf_*K ⊗^L (Rf_*L ⊗^L Rf_*M) ⟶ Rf_*K ⊗^L Rf_*(L ⊗^L M) ⟶ Rf_*(K ⊗^L (L ⊗^L M))
```

commutes in `D(𝒪_Y)`, where the four unlabelled arrows are relative cup products of Stacks 0B68
in one or the other tensor factor and `a` is the associativity constraint of Stacks 0FPB.  The
compatibility of the comparison of Stacks 079U with those constraints is
`pullbackTensorComparisonAssociative`. -/
@[stacks 0FP4 "associativity of the relative cup product, for a morphism of ringed spaces and \
  arbitrary K, L, M in D(O_X): the associativity constraints are those of Tag 0FPB \
  (derivedAssociator), and their compatibility with the comparison of Tag 079U is \
  pullbackTensorComparisonAssociative"]
theorem relativeCupProduct_assoc
    (K L M : DerivedCategory (Mod X.sheaf)) :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
        (relativeCupProduct f K L ×ₘ 𝟙 ((derivedPushforward f).obj M)) ≫
        relativeCupProduct f
            ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).obj (K, L))
            M ≫
          (derivedPushforward f).map (derivedAssociator X K L M) =
      derivedAssociator Y ((derivedPushforward f).obj K) ((derivedPushforward f).obj L)
          ((derivedPushforward f).obj M) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
            (𝟙 ((derivedPushforward f).obj K) ×ₘ relativeCupProduct f L M) ≫
          relativeCupProduct f K
            ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).obj (L, M)) :=
  adjunctionBitensorMap_assoc (derivedAdjunction f)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (derivedAssociator Y) (derivedAssociator X)
    (fun u v w => derivedAssociator_naturality X u v w)
    (pullbackTensorComparisonAssociative f) K L M

end Stacks.Cohomology.DerivedRelativeCupProduct

end

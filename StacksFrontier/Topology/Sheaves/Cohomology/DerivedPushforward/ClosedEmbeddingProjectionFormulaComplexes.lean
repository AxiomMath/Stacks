module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaStalks
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingPushforwardColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorProductCompatibility
import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit

/-!
# The projection formula for a closed embedding, at the level of complexes

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying continuous map is
a homeomorphism onto a closed subset.  This file carries out the *complex-level* step of the
source's proof of [Stacks, Tag 0B55]: for arbitrary cochain complexes `A^•` of `𝒪_X`-modules and
`B^•` of `𝒪_Y`-modules there is an isomorphism of complexes

`Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)`.

There is no flatness, boundedness or finiteness hypothesis on either complex, and no hypothesis
on `f` beyond the closed embedding.

The two inputs are already in this directory and are used unchanged.  The *termwise* statement is
`Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIso`, the ordinary projection formula
`f_*G ⊗_{𝒪_Y} H ≅ f_*(G ⊗_{𝒪_X} f^*H)` for a bare closed embedding and arbitrary `G`, `H`,
proved there on stalks.  The passage from the termwise statement to the totalizations is
`Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_totalMap_modulePushforward`, that `f_*`
commutes with the total complex of an unbounded bicomplex.

## Main results

* `projectionFormulaMap'_natural_left` and `projectionFormulaMap'_natural_right`: the two
  one-sided naturalities of the ordinary projection-formula morphism, restated at the
  `Stacks.SheafOfModules.Tensor.sheafTensor` presentation of the tensor product.  These carry no
  hypothesis on `f`.
* `projectionBicomplexIso`: **the termwise isomorphism of bicomplexes.**  The bicomplex
  `(i, j) ↦ f_*A^i ⊗_{𝒪_Y} B^j` is isomorphic to the one obtained by applying `f_*` to each term
  of `(i, j) ↦ A^i ⊗_{𝒪_X} f^*B^j`.
* `complexProjectionFormulaIso`: **the projection formula for complexes**,
  `Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)`, for arbitrary `A^•` and `B^•`.
* `nonempty_derivedPushforwardDerivedPullbackIsoTensor`: **the derived consequence at the
  structure sheaf**, `Rf_*Lf^*G ≅ Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} G` for arbitrary `G ∈ D(𝒪_Y)`, and
  `derivedPushforwardDerivedPullbackIsoTensor`, one such isomorphism.

## What of [Stacks, Tag 0B55] is not here

The conclusion of the tag — that the derived morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

of [Stacks, Tag 0B53] is invertible for arbitrary `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)` — is **not
proved here**, and nothing below mentions that morphism.  What is missing is exactly one
identity: that after representing `K` by a K-flat complex `B^•`, whose pullback is again K-flat
by [Stacks, Tag 06YC], and `E` by any complex `A^•`, the morphism of [Stacks, Tag 0B53] becomes
`Q` of `complexProjectionFormulaIso`.  That is a mate computation for the adjunction
`Lf^* ⊣ Rf_*`, and it is the *only* thing owed: every comparison it has to be stated through is
already in the library, and `derivedProjectionFormulaIsoOfKFlat` below already assembles the
first three of them at `A^• = 𝒪_X[0]`.

* `Q(f_*A^•) ≅ Rf_*(Q A^•)`: `Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory`
  together with `Functor.mapDerivedCategoryFactors`, or equivalently the invertibility of
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit`, which is
  `Stacks.Cohomology.ExactPushforwardAdjunction.isIso_derivedPushforwardUnit_app`.
* `Lf^*(Q B^•) ≅ Q(f^*B^•)` for `B^•` K-flat:
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat`.
* The K-flat presentation of the derived tensor product of [Stacks, Tag 06YU]:
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonRight`.
* The compatibility of the [Stacks, Tag 079U] comparison with the termwise comparison of
  [Stacks, Tag 01CD]: `…DerivedPullbackTensor.derivedPullbackTensorIso_toTensor_comm`, which is
  [Stacks, Tag 0FP0].  It carries no K-flatness hypothesis, which is what makes it usable at
  the pair `(Rf_*E, K)` — whose left entry is never K-flat for a closed embedding, `f_*A^•`
  being annihilated by the kernel ideal of `f^♯` and hence not flat.
* The derived counit of `Lf^* ⊣ Rf_*` solved below `Qh` for an exact pushforward:
  `Stacks.Cohomology.ExactPushforwardAdjunction.derivedAdjunction_counit_app_eq`.  This is the
  only side of the adjunction the computation needs, the identity being proved by transposing.

Once the identity is available, the derived statement follows for arbitrary
`E` and `K` by `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_congr_left`
and `isIso_projectionFormulaMap_congr_right`, which transport invertibility along an isomorphism
in either variable with no hypothesis at all, together with
`Stacks.DerivedTensor.RingedSite.kFlatModelIso` to put `K` into K-flat form.

What *is* available without that mate computation is the single instance `E = 𝒪_X`, as a bare
isomorphism rather than as invertibility of the canonical map:
`nonempty_derivedPushforwardDerivedPullbackIsoTensor` below.  Both derived functors involved are
computable on a K-flat representative `B^•` of `G` — `Rf_*` is `f_*` on derived categories by
[Stacks, Tag 08KS], `Lf^*(QB^•)` is `Q(f^*B^•)` by [Stacks, Tag 06YJ], and the derived tensor
product with a K-flat right factor is the total tensor complex by [Stacks, Tag 06YU] — so the
isomorphism is `Q` of `complexProjectionFormulaIso` at `A^• = 𝒪_X[0]`.  This says nothing about
the morphism of [Stacks, Tag 0B53], and is not the tag.

## Implementation notes

*Why the two tensor presentations have to be bridged.*  The library has two constructions of the
tensor product of sheaves of modules.  `Stacks.RingedSpace.tensorSheaf`, in which the ordinary
projection-formula morphism is stated, is an uncurried bifunctor on a product category indexed by
`Stacks.RingedSpace.structureRingSheaf`; `Stacks.SheafOfModules.Tensor.sheafTensor`, from which
the bicomplex and the derived tensor product are built, is curried and indexed by a ringed site's
own sheaf of rings.  They are the same functor up to currying, and the identifications are true
by `rfl`, but `rfl` is not enough on its own: the two naturality statements have to be *stated*
at the `sheafTensor` presentation, which is what the two lemmas below do.  Each is deduced from
the two-sided `Stacks.ProjectionFormula.projectionFormulaMap'_natural` by specializing one
argument to an identity and rewriting with `CategoryTheory.Functor.map_id`; the currying is then
absorbed by the definitional unfolding that `exact` performs.

*Why the bridging is done by `exact` and not by rewriting.*  A `simp only` with the currying
identifications fails here, because the sheaf of rings of a ringed space has three spellings in
this library — `structureSheafRing`, `Stacks.RingedSpace.structureRingSheaf`
and a ringed site's own — and a rewrite in the middle of a term indexed by one of them produces a
goal that is not type-correct at the transparency `simp` works at.  Discharging the square by
`exact` instead leaves the unfolding to the definitional equality check, which sees through all
three.

*Why two reducibility attributes are needed.*  Instance search matches up to reducible unfolding
only, so the additivity of `f_*` and the `HasTotal` instances of the bicomplexes are not found
when the category is presented at a different one of those three spellings.  Marking
`structureSheafRing` and `TopCat.Sheaf` locally implicitly reducible collapses
them, which is the same device, for the same reason, as in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingPushforwardColimits`.
Where even that is not enough — the invertibility of the totalization comparison, whose statement
mentions two `HasTotal` instances that have to agree syntactically — the witness is passed to
`CategoryTheory.asIso` as an explicit argument, so that a definitional equality check replaces
the search.

*On the cost of elaborating this.*  All of it elaborates within the default heartbeat limit; the
file needs no raised limits and no relaxed transparency.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.ProjectionFormula
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.ClosedEmbeddingPushforward
open scoped CategoryTheory.Prod

universe u

noncomputable section

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The two one-sided naturalities, at the `sheafTensor` presentation -/

/-- **Naturality of the ordinary projection-formula morphism in the target module**, stated at
the `Stacks.SheafOfModules.Tensor.sheafTensor` presentation of the tensor product: tensoring
`f_*G` with a morphism `k : H ⟶ H'` of `𝒪_Y`-modules commutes with
`Stacks.ProjectionFormula.projectionFormulaMap'`.  There is no hypothesis on `f`.

This is `Stacks.ProjectionFormula.projectionFormulaMap'_natural` with the source argument an
identity; the only work is that the source lemma moves both arguments at once, through the
uncurried `Stacks.RingedSpace.tensorSheaf`, whereas a bicomplex differential moves one at a
time, through the curried `sheafTensor`. -/
lemma projectionFormulaMap'_natural_right (G : SheafOfModules.{u} (structureRingSheaf X))
    {H H' : SheafOfModules.{u} (structureRingSheaf Y)} (k : H ⟶ H') :
    ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj ((pushforwardFunctor f).obj G)).map k ≫
        projectionFormulaMap' f G H' =
      projectionFormulaMap' f G H ≫ (pushforwardFunctor f).map
        (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).map ((pullbackFunctor f).map k)) := by
  have sourceMap :=
    (congrArg
      (fun morphism => (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} Y.sheaf)).map
        (morphism ×ₘ k)) ((pushforwardFunctor f).map_id G)).trans
      ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Y.sheaf
        (𝟙 ((pushforwardFunctor f).obj G)) k).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map Y.sheaf
          ((pushforwardFunctor f).obj G) k).symm)
  have targetMap :=
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf
      (𝟙 G) ((pullbackFunctor f).map k)).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map X.sheaf G
        ((pullbackFunctor f).map k)).symm
  rw [← sourceMap, ← targetMap]
  exact projectionFormulaMap'_natural f (𝟙 G) k

/-- **Naturality of the ordinary projection-formula morphism in the source module**, stated at
the `Stacks.SheafOfModules.Tensor.sheafTensor` presentation of the tensor product.  There is no
hypothesis on `f`.  This is the companion of `projectionFormulaMap'_natural_right`, obtained by
specializing the target argument of `Stacks.ProjectionFormula.projectionFormulaMap'_natural` to
an identity. -/
lemma projectionFormulaMap'_natural_left {G G' : SheafOfModules.{u} (structureRingSheaf X)}
    (g : G ⟶ G') (H : SheafOfModules.{u} (structureRingSheaf Y)) :
    ((sheafTensor.{u, u, u, u, u} Y.sheaf).map ((pushforwardFunctor f).map g)).app H ≫
        projectionFormulaMap' f G' H =
      projectionFormulaMap' f G H ≫ (pushforwardFunctor f).map
        (((sheafTensor.{u, u, u, u, u} X.sheaf).map g).app ((pullbackFunctor f).obj H)) := by
  have sourceMap :=
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Y.sheaf
      ((pushforwardFunctor f).map g) (𝟙 H)).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_map_app Y.sheaf
        ((pushforwardFunctor f).map g) H).symm
  have targetMap :=
    (congrArg
      (fun morphism => (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} X.sheaf)).map
        (g ×ₘ morphism)) ((pullbackFunctor f).map_id H)).trans
      ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf g
        (𝟙 ((pullbackFunctor f).obj H))).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_map_app X.sheaf g
          ((pullbackFunctor f).obj H)).symm)
  rw [← sourceMap, ← targetMap]
  exact projectionFormulaMap'_natural f g (𝟙 H)

/-! ### The termwise isomorphism of bicomplexes -/

/-- **The projection formula termwise on a pair of complexes**, as an isomorphism of bicomplexes:
for `f` a homeomorphism onto a closed subset and arbitrary cochain complexes `A^•` on `X` and
`B^•` on `Y`, the bicomplex `(i, j) ↦ f_*A^i ⊗_{𝒪_Y} B^j` is isomorphic to the bicomplex obtained
by applying `f_*` to every term of `(i, j) ↦ A^i ⊗_{𝒪_X} f^*B^j`.

Each component is `Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIso`, the ordinary
projection formula for a closed embedding, and the two families of squares are the two one-sided
naturalities above.  Nothing here is flat, bounded or finite. -/
def projectionBicomplexIso
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (((sheafTensor.{u, u, u, u, u} Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        (((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj A)).obj B ≅
      (letI : (modulePushforward f).Additive :=
        modulePushforward_additive f
       HomologicalComplex₂.TotalMap.mapBicomplex
        (C := SheafOfModules.{u} (structureSheafRing X))
        (D := SheafOfModules.{u} (structureSheafRing Y)) (modulePushforward f)
        ((((sheafTensor.{u, u, u, u, u} X.sheaf).mapBifunctorHomologicalComplex
            (.up ℤ) (.up ℤ)).obj A).obj
          (((modulePullback f).mapHomologicalComplex (.up ℤ)).obj B))) :=
  letI : (modulePushforward f).Additive :=
    modulePushforward_additive f
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIso f (A.X i) (B.X j) hf)
      (fun j j' _ => (projectionFormulaMap'_natural_right f (A.X i) (B.d j j')).symm))
    (fun i i' _ => by
      ext j : 1
      exact (projectionFormulaMap'_natural_left f (A.d i i') (B.X j)).symm)

/-! ### The projection formula for complexes -/

/-- **The projection formula for a closed embedding, at the level of complexes.**  For a morphism
of ringed spaces `f : X ⟶ Y` whose underlying continuous map is a homeomorphism onto a closed
subset, and for *arbitrary* cochain complexes `A^•` of `𝒪_X`-modules and `B^•` of `𝒪_Y`-modules,

`Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)`.

There is no flatness, boundedness or finiteness hypothesis on either complex.

This is the complex-level step of the source's proof of [Stacks, Tag 0B55].  It is the termwise
isomorphism `projectionBicomplexIso` on totalizations, composed with the comparison
`Tot(f_*(-)) ⟶ f_*(Tot(-))`, which is invertible by
`Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_totalMap_modulePushforward` because `f_*`
commutes with arbitrary direct sums.  The derived statement of [Stacks, Tag 0B55] does not follow
from this without the identification described in the module docstring, and is not proved here. -/
@[stacks 0B55 "step 2: the projection formula holds at the level of complexes"]
def complexProjectionFormulaIso
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    ((tensorComplex Y.sheaf).obj
        (((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj A)).obj B ≅
      ((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj
        (((tensorComplex X.sheaf).obj A).obj
          (((modulePullback f).mapHomologicalComplex (.up ℤ)).obj B)) := by
  letI : (modulePushforward f).Additive := modulePushforward_additive f
  letI : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Y
  letI : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} X
  let e := projectionBicomplexIso f hf A B
  letI := HomologicalComplex₂.hasTotal_of_iso e (.up ℤ)
  have h := isIso_totalMap_modulePushforward f hf
    ((((sheafTensor.{u, u, u, u, u} X.sheaf).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj A).obj
      (((modulePullback f).mapHomologicalComplex (.up ℤ)).obj B))
  exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫ @asIso _ _ _ _ _ h

/-! ### The derived consequence at the structure sheaf -/

section Derived

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)

attribute [local instance] HasDerivedCategory.standard

/-- The structure sheaf of a ringed space, as a cochain complex concentrated in degree zero. -/
def unitComplex (X : RingedSpace.{u, u}) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit (structureSheafRing X))

variable [PreservesFiniteColimits (modulePushforward f)]

/-- `Rf_*(QC^•) ≅ Q(f_*C^•)`: pushforward along a closed embedding is exact, so the chosen
derived pushforward is the functor it induces on derived categories. -/
def derivedPushforwardQIso (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedPushforward f).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory f).app _ ≪≫
    ((modulePushforward f).mapDerivedCategoryFactors.app C)

/-- **The source of the morphism of [Stacks, Tag 0B53], on complex representatives:**

`Rf_*(QA^•) ⊗^𝐋_{𝒪_Y} QB^• ≅ Q(Tot(f_*A^• ⊗_{𝒪_Y} B^•))` for `B^•` K-flat.

This is the left-hand endpoint of `complexProjectionFormulaIso` read in the derived category:
`derivedPushforwardQIso` in the left tensor factor, then the K-flat presentation of the derived
tensor product of [Stacks, Tag 06YU]. -/
def derivedSourceQIso (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y B) :
    ((canonicalDerivedTensorProduct Y.sheaf).tensor.obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A))).obj (DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj (((tensorComplex Y.sheaf).obj
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)).obj B) :=
  ((canonicalDerivedTensorProduct Y.sheaf).tensor.mapIso (derivedPushforwardQIso f A)).app _ ≪≫
    (canonicalDerivedTensorProduct Y.sheaf).comparisonRight _ B hB

/-- **The target of the morphism of [Stacks, Tag 0B53], on complex representatives:**

`Q(f_*Tot(A^• ⊗_{𝒪_X} f^*B^•)) ≅ Rf_*(QA^• ⊗^𝐋_{𝒪_X} Lf^*(QB^•))` for `B^•` K-flat.

This is the right-hand endpoint of `complexProjectionFormulaIso` read in the derived category:
`derivedPushforwardQIso`, then inside `Rf_*` the K-flat presentation of the derived tensor
product — `f^*B^•` is K-flat by [Stacks, Tag 06YC] — and `Lf^*(QB^•) ≅ Q(f^*B^•)`. -/
def derivedTargetQIso (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y B) :
    DerivedCategory.Q.obj
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((tensorComplex X.sheaf).obj A).obj
            (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj B))) ≅
      (derivedPushforward f).obj
        (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj A)).obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj B))) :=
  (derivedPushforwardQIso f _).symm ≪≫
    (derivedPushforward f).mapIso
      (((canonicalDerivedTensorProduct X.sheaf).comparisonRight A _
          (Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional f B hB)).symm ≪≫
        ((canonicalDerivedTensorProduct X.sheaf).tensor.obj
            (DerivedCategory.Q.obj A)).mapIso
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat f B hB).symm)

/-- `Rf_*Lf^*(QB^•) ≅ Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} QB^•` for a K-flat complex `B^•`, the two sides being
`Q` of the two sides of `complexProjectionFormulaIso` at `A^• = 𝒪_X[0]`.

K-flatness of `B^•` is what makes every functor in sight computable on it: the derived tensor
product with a K-flat right factor is the total tensor complex, and `Lf^*(QB^•)` is `Q(f^*B^•)`.
The left factor `𝒪_X[0]` disappears from `Tot(𝒪_X[0] ⊗_{𝒪_X} f^*B^•)` by the Koszul symmetry
followed by the unit law. -/
private def derivedProjectionFormulaIsoOfKFlat
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y B) :
    (derivedPushforward f).obj ((derivedPullback f).obj (DerivedCategory.Q.obj B)) ≅
      ((canonicalDerivedTensorProduct Y.sheaf).tensor.obj
          ((derivedPushforward f).obj (DerivedCategory.Q.obj (unitComplex X)))).obj
        (DerivedCategory.Q.obj B) :=
  (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory f).app _ ≪≫
    (modulePushforward f).mapDerivedCategory.mapIso
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat f B hB) ≪≫
    ((modulePushforward f).mapDerivedCategoryFactors.app _) ≪≫
    DerivedCategory.Q.mapIso
      (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.sheaf (unitComplex X) _ ≪≫
          Stacks.SheafOfModules.tensorComplexUnitIso X.sheaf _)).symm ≪≫
    (DerivedCategory.Q.mapIso (complexProjectionFormulaIso f hf (unitComplex X) B)).symm ≪≫
    ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight _ B hB).symm ≪≫
    ((canonicalDerivedTensorProduct Y.sheaf).tensor.mapIso
      (derivedPushforwardQIso f (unitComplex X))).symm.app _

/-- **The projection formula at the structure sheaf, in the derived category.**  For a morphism
of ringed spaces whose underlying map is a homeomorphism onto a closed subset and arbitrary
`G ∈ D(𝒪_Y)`, `Rf_*Lf^*G` is the derived tensor product of `Rf_*𝒪_X` with `G`.

This is `complexProjectionFormulaIso` at `A^• = 𝒪_X[0]` and at a K-flat representative of `G`;
it is not a statement about the morphism of [Stacks, Tag 0B53], and is not that tag. -/
theorem nonempty_derivedPushforwardDerivedPullbackIsoTensor
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    Nonempty ((derivedPushforward f).obj ((derivedPullback f).obj G) ≅
      ((canonicalDerivedTensorProduct Y.sheaf).tensor.obj
          ((derivedPushforward f).obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
              (SheafOfModules.unit (structureSheafRing X))))).obj G) := by
  obtain ⟨B, g, hB, -, hg, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y
    (DerivedCategory.Q.objPreimage G)
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  have e : DerivedCategory.Q.obj B ≅ G :=
    asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso G
  have eu : (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
          (SheafOfModules.unit (structureSheafRing X))) ≅
      (derivedPushforward f).obj (DerivedCategory.Q.obj (unitComplex X)) :=
    (derivedPushforward f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) 0).app
        (SheafOfModules.unit (structureSheafRing X)))
  exact ⟨((derivedPushforward f).mapIso ((derivedPullback f).mapIso e)).symm ≪≫
    derivedProjectionFormulaIsoOfKFlat f hf B hB ≪≫
    ((canonicalDerivedTensorProduct Y.sheaf).tensor.obj _).mapIso e ≪≫
    ((canonicalDerivedTensorProduct Y.sheaf).tensor.mapIso eu).symm.app G⟩

/-- A choice of the isomorphism `Rf_*Lf^*G ≅ Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} G` of
`nonempty_derivedPushforwardDerivedPullbackIsoTensor`.  It depends on a K-flat resolution of `G`
and is canonical in nothing. -/
def derivedPushforwardDerivedPullbackIsoTensor
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPushforward f).obj ((derivedPullback f).obj G) ≅
      ((canonicalDerivedTensorProduct Y.sheaf).tensor.obj
          ((derivedPushforward f).obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
              (SheafOfModules.unit (structureSheafRing X))))).obj G :=
  Classical.choice (nonempty_derivedPushforwardDerivedPullbackIsoTensor f hf G)

end Derived

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

end

end

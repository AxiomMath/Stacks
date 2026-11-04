module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Homology.TotalComplexTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback and the derived tensor product on a ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Stacks 079U asserts a
canonical bifunctorial isomorphism

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`

for `K, L ∈ D(𝒪_Y)`.  The source proves it by reducing to K-flat `K` and `L`, where both
sides are total tensor complexes, and then exhibiting the isomorphism

`Tot(f^*K ⊗_{𝒪_X} f^*L) ⟶ f^*Tot(K ⊗_{𝒪_Y} L)`

"whose constituents are the isomorphisms `f^*K^p ⊗_{𝒪_X} f^*L^q ⟶ f^*(K^p ⊗_{𝒪_Y} L^q)` of
Modules, Lemma 01CD".  This file supplies that reduction: the K-flatness statements it needs,
unconditionally, and the passage from the degreewise comparison of Stacks 01CD to the
comparison of total complexes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.kFlat_tensorComplex`: **Stacks 079R at a ringed space**,
  in the
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat` spelling — `Tot(K ⊗_{𝒪_Y} L)` is
    K-flat when `K` and `L` are.
* `Stacks.Cohomology.DerivedPullbackTensor.kFlat_modulePullback_tensorComplex` and
  `Stacks.Cohomology.DerivedPullbackTensor.kFlat_tensorComplex_modulePullback`: the two complexes
    the two sides of
  Stacks 079U are computed by, `f^*Tot(K ⊗_{𝒪_Y} L)` and `Tot(f^*K ⊗_{𝒪_X} f^*L)`, are both
  K-flat.
* `Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts`: `f^*`
  preserves exactly the
  coproducts occurring in a total complex over `ℤ`.
* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso`: **the isomorphism the source
  names**,
  `f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)`, built from an arbitrary degreewise
  comparison of the two tensor bifunctors along `f^*`, and
  `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso`, the same with that
    comparison supplied by
  the tree's own Stacks 01CD morphism.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat`: **a K-flat complex computes
  `Lf^*`**, as an
  isomorphism `Lf^*(QM) ≅ Q(f^*M)`, unconditionally.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIsoOfKFlat`: **Stacks 079U on
  K-flat representatives**,
  `Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`.

## Implementation notes

*Everything here is unconditional, and nothing here carries the `079U` attribute.*  No
statement in the last two sections carries invertibility of the components of
`Stacks.RingedSpace.comparisonNatTrans` — Stacks 01CD, not a hypothesis of Stacks 079U — as a
hypothesis: `Stacks.RingedSpace.comparisonNatTrans_app_isIso` is an instance, so instance search
supplies it.  What is still missing for the `079U`
attribute is the *shape* of the source statement, not a hypothesis: Stacks 079U is an
isomorphism of *bifunctors on the derived categories*, and what is built here is its value on
K-flat representatives.  The descent to arbitrary objects of `D(𝒪_Y)` — and with it the
naturality of that value in homotopy classes of maps between K-flat complexes — is not here.

*The degreewise comparison is also available as an argument, not only as the tree's term.*
This follows the tree's own precedent at
`AlgebraicGeometry.SheafOfModules.stalkTotalComplexIso`, which leaves its comparison `ε` as
an argument.  Here the reason is weaker than it was there: the total tensor complex
`Stacks.SheafOfModules.Tensor.tensorComplex` is built from the *curried*
  `Stacks.SheafOfModules.Tensor.sheafTensor`, while
`Stacks.RingedSpace.comparisonNatTrans` is stated over the *uncurried*
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor _)`, so both APIs use the
same canonical tensor product.  So no bridge isomorphism is needed and
`pullbackTensorComplexIsoOfIsIso` supplies `ε` directly; the general form is kept because it is
the one a different model of `f^*` would use.

*Do not mix the two tensor spellings inside one tactic proof.*  With a pair `(A, B)`
whose components are typed as `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y` and a
  bifunctor expecting
`SheafOfModules (Stacks.RingedSpace.structureRingSheaf Y)`, the naturality square is not
type-correct at `implicit` transparency — the two ring-sheaf spellings differ by a
semireducible `def` — so `dsimp only [Functor.comp_map, Functor.prod_map]` silently does
nothing and the following `rw [Functor.map_id]` reports *"did not find an occurrence"* against
a goal that visibly contains `f^*(𝟙 B)`.  The degreewise-comparison section is therefore written
at the `pullbackFunctor`/`sheafTensor`/`structureRingSheaf` spelling, and the passage to the
other spelling is left to the conversion check at the application site, where it is free.

*The retyped pullback.*  `StacksDraft.KFlat.modulePullback f` is
`RingedSpaceModuleAdjunction.modulePullback f` retyped over `Stacks.SheafOfModules.Tensor.ringSheaf
  _.sheaf`,
which is the spelling `Stacks.SheafOfModules.Tensor.sheafTensor` and hence
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat` are stated at.
The two are `rfl`-equal; the retyping exists because a complex whose type is written at the
other spelling leaves the module universe of the tensor bifunctor unsolved at the moment its
instance arguments are synthesized.

*Colimit preservation is not found by instance search.*  `f^*` is a left adjoint and so
preserves all colimits, but `PreservesColimitsOfSize` at the ambient universes is not seen as
supplying `PreservesColimitsOfShape (Discrete T)` for `T : Type 0`, because the shrinking step
`preservesColimitsOfSize_shrink` is a lemma and not an instance.  The shrunk and antidiagonal
forms are therefore named below, exactly as
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesAntidiagonalCoproducts` is.  The
shrinking also has to be *written at the un-retyped spelling* and transported by the
conversion check: a `letI` of the `RingedSpaceModuleAdjunction` form is not seen by instance
search for the `StacksDraft.KFlat` form, which is a semireducible `def`.

*The universe narrowing, inherited.*  The derived tensor product of Stacks 06YU is available
only with the site's object, hom, ring and module universes all equal and the site small, a
narrowing that `Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct` records as coming down
  the chain
from `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` and ultimately
  `Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda`.
A ringed space `RingedSpace.{u, u}` satisfies it on the nose — `Opens Y.carrier` is a `Type u`
whose category instance is `Preorder.smallCategory` — so nothing is narrowed *here*; the
narrowing is recorded because it is inherited rather than chosen.

*The four sheafification binders.*  `HasSheafify` and `WEqualsLocallyBijective` for
`AddCommGrpCat.{u}` on the two open-cover sites are the binders Stacks 06YU's derived tensor
product is stated under, and the tagged statement of Stacks 079U carries them too.  Both
are `Prop`s and both are inhabited for every ringed space, by
`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.Tensor
  (sheafTensor sheafTensor_uncurry_map sheafTensor_map_app sheafTensor_obj_map
    sheafTensor_additive sheafTensor_obj_additive hasMapBifunctor_sheafTensor)
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

noncomputable section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-! ### K-flatness of the complexes the two sides of Stacks 079U are computed by -/

section KFlat

variable (Y : RingedSpace.{u, u})

/-- **Stacks 079R at a ringed space.**  The total tensor complex of two K-flat complexes of
`𝒪_Y`-modules is K-flat.

This is `Stacks.SheafOfModules.kFlat_tensorComplex` read at `Y.sheaf`; the restatement exists
only to put it at the `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat` spelling, which is
  the one the pullback statements
below are written at. -/
theorem kFlat_tensorComplex (K L : CochainComplex
  (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) (hL :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y
      (((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _ ⟨Y.presheaf, Y.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj K).obj L) :=
  let := sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
  let := sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
  let := fun (left right : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) =>
    hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩ left right
  Stacks.SheafOfModules.kFlat_tensorComplex (R := ⟨Y.presheaf, Y.IsSheaf⟩) hK hL

end KFlat

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The complex computing the left-hand side of Stacks 079U is K-flat.**  For K-flat `K` and
`L`, the complex `f^*Tot(K ⊗_{𝒪_Y} L)` is K-flat: `Tot(K ⊗ L)` is K-flat by Stacks 079R and
degreewise pullback preserves K-flatness by Stacks 06YC.

This is what makes `Lf^*(K ⊗^L L)` computable by `f^*Tot(K ⊗ L)`: the canonical comparison of
a left derived functor is invertible on its resolving class, and the resolving class for `Lf^*`
is the K-flat complexes. -/
theorem kFlat_modulePullback_tensorComplex (K L : CochainComplex
  (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) (hL :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X (((StacksDraft.KFlat.modulePullback
      f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _
          ⟨Y.presheaf, Y.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj K).obj L))
        :=
  kFlat_modulePullback_unconditional f _ (kFlat_tensorComplex Y K L hK hL)

/-- **The complex computing the right-hand side of Stacks 079U is K-flat.**  For K-flat `K` and
`L`, the complex `Tot(f^*K ⊗_{𝒪_X} f^*L)` is K-flat, by Stacks 06YC in each variable and then
Stacks 079R on `X`. -/
theorem kFlat_tensorComplex_modulePullback (K L : CochainComplex
  (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) (hL :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X
      (((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _ ⟨X.presheaf, X.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).obj
          (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)).obj
        (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) :=
  kFlat_tensorComplex X _ _ (kFlat_modulePullback_unconditional f K hK)
    (kFlat_modulePullback_unconditional f L hL)

/-! ### `f^*` preserves the coproducts occurring in a total complex -/

/-- `f^*` preserves colimits indexed by a category whose objects and morphisms live in
`Type 0`.

This is `RingedSpaceModuleAdjunction.preservesColimits_modulePullback` — `f^*` is a left
adjoint — shrunk in size.  The shrinking is not found by instance search, since
`preservesColimitsOfSize_shrink` is a lemma and not an instance. -/
lemma modulePullback_preservesColimitsOfSize_zero :
    PreservesColimitsOfSize.{0, 0} (StacksDraft.KFlat.modulePullback f) :=
  let := RingedSpaceModuleAdjunction.preservesColimits_modulePullback f
  preservesColimitsOfSize_shrink (RingedSpaceModuleAdjunction.modulePullback f)

/-- **`f^*` preserves the coproducts occurring in the total complex of a double cochain complex
over `ℤ`**: those indexed by an antidiagonal `ComplexShape.π (up ℤ) (up ℤ) (up ℤ) ⁻¹' {n}`.

This is the hypothesis of `CategoryTheory.Functor.mapBifunctorTotalIso`, so this lemma is what
makes the total tensor complex transport along `f^*` at all. -/
lemma modulePullback_preservesAntidiagonalCoproducts (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      (StacksDraft.KFlat.modulePullback f) :=
  let := modulePullback_preservesColimitsOfSize_zero f
  inferInstance

/-! ### The comparison of total complexes -/

/-- **The total tensor complex transports along `f^*`.**  If `f^*` carries the tensor product of
`𝒪_Y`-modules to the tensor product of `𝒪_X`-modules — that is, if there are isomorphisms
`ε : f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B` natural in `A` and in `B`, which is Stacks 01CD —
then it carries the total tensor complex to the total tensor complex:

`f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)`.

This is the isomorphism the proof of Stacks 079U names, together with the statement that its
constituents are the degreewise isomorphisms of Stacks 01CD: that is exactly what `ε` is, and
`CategoryTheory.Functor.mapBifunctorTotalIso` is the assembly. -/
def pullbackTensorComplexIso
    (ε : ∀ A B : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y,
      (StacksDraft.KFlat.modulePullback f).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩).obj
            ((StacksDraft.KFlat.modulePullback f).obj A)).obj
          ((StacksDraft.KFlat.modulePullback f).obj B))
    (hε₁ : ∀ {A A' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y} (u : A ⟶ A') (B :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y),
      (StacksDraft.KFlat.modulePullback f).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨(Y).presheaf, (Y).IsSheaf⟩).map u).app B) ≫ (ε A' B).hom =
        (ε A B).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩).map
              ((StacksDraft.KFlat.modulePullback f).map u)).app
            ((StacksDraft.KFlat.modulePullback f).obj B))
    (hε₂ : ∀ (A : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) {B B' :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y} (v : B ⟶ B'),
      (StacksDraft.KFlat.modulePullback f).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).map v) ≫ (ε A B').hom =
        (ε A B).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩).obj
              ((StacksDraft.KFlat.modulePullback f).obj A)).map
            ((StacksDraft.KFlat.modulePullback f).map v))
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    ((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _ ⟨Y.presheaf, Y.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj K).obj L) ≅
      ((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _ ⟨X.presheaf, X.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).obj
          (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)).obj
        (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) := by
  letI : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Y
  letI : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} X
  letI := fun n : ℤ => modulePullback_preservesAntidiagonalCoproducts f n
  letI : (show AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y ⥤
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X from
        StacksDraft.KFlat.modulePullback f).Additive :=
    StacksDraft.KFlat.modulePullback_additive f
  letI : (show AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y ⥤
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y ⥤
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y from
        sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).Additive :=
    sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
  letI : (show AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X ⥤
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X ⥤
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X from
        sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).Additive :=
    sheafTensor_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩
  letI : ∀ left : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y,
      ((show AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y ⥤
        AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y ⥤
        AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y from
          sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj left).Additive :=
    sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
  letI : ∀ left : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X,
      ((show AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X ⥤
        AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X ⥤
        AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X from
          sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj left).Additive :=
    sheafTensor_obj_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩
  refine CategoryTheory.Functor.mapBifunctorTotalIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩)
    (StacksDraft.KFlat.modulePullback f) (StacksDraft.KFlat.modulePullback f)
    (StacksDraft.KFlat.modulePullback f) ?_
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ?_ ?_ K L
  · exact ε
  · exact hε₁
  · exact hε₂

/-! ### The comparison supplied by the tree's own Stacks 01CD morphism -/

section DegreewiseComparison

open scoped CategoryTheory.Prod

-- Invertibility of the components of `Stacks.RingedSpace.comparisonNatTrans` — the canonical
-- morphism `f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B` of Stacks 01CD — was the hypothesis of this
-- section.  It is now an instance, `Stacks.RingedSpace.comparisonNatTrans_app_isIso`, so
-- everything below is unconditional and instance search supplies it.

/-- **Stacks 01CD as a degreewise comparison** `f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B`.

The comparison and the total tensor complex use the same canonical `sheafTensor`.
The naturality formulas below use its native maps in each variable; the product-category
naturality square is simplified using the generic laws for `Functor.uncurry`. -/
def comparisonAppIso (A B : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)) :
    (Stacks.RingedSpace.pullbackFunctor f).obj
        (((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B) ≅
      ((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
        ((Stacks.RingedSpace.pullbackFunctor f).obj A)).obj
        ((Stacks.RingedSpace.pullbackFunctor f).obj B) :=
  letI := Stacks.RingedSpace.comparisonNatTrans_app_isIso f (A, B)
  asIso ((Stacks.RingedSpace.comparisonNatTrans f).app (A, B))

/-- The naturality square of `Stacks.RingedSpace.comparisonNatTrans` at `v ×ₘ w`, with the images
of `v ×ₘ w` under the two uncurried tensor bifunctors rewritten as `m` and `m'`. -/
private lemma comparisonAppIso_naturality_aux
    {A A' B B' : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)}
    (v : A ⟶ A') (w : B ⟶ B')
    {p : (Stacks.RingedSpace.pullbackFunctor f).obj A ⟶
      (Stacks.RingedSpace.pullbackFunctor f).obj A'}
    {q : (Stacks.RingedSpace.pullbackFunctor f).obj B ⟶
      (Stacks.RingedSpace.pullbackFunctor f).obj B'}
    (hp : (Stacks.RingedSpace.pullbackFunctor f).map v = p)
    (hq : (Stacks.RingedSpace.pullbackFunctor f).map w = q)
    {m : ((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B ⟶
      ((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj A').obj B'}
    {m' : ((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
        ((Stacks.RingedSpace.pullbackFunctor f).obj A)).obj
        ((Stacks.RingedSpace.pullbackFunctor f).obj B) ⟶
      ((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
        ((Stacks.RingedSpace.pullbackFunctor f).obj A')).obj
        ((Stacks.RingedSpace.pullbackFunctor f).obj B')}
    (hm : (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).map
      (v ×ₘ w) = m)
    (hm' : (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).map
      (p ×ₘ q) = m') :
    (Stacks.RingedSpace.pullbackFunctor f).map m ≫ (comparisonAppIso f A' B').hom =
      (comparisonAppIso f A B).hom ≫ m' := by
  subst hp hq hm hm'
  exact (Stacks.RingedSpace.comparisonNatTrans f).naturality (v ×ₘ w)

/-- The degreewise comparison is natural in the first module variable: this is the naturality
square of `Stacks.RingedSpace.comparisonNatTrans` at a morphism `v ×ₘ 𝟙` of the product
category, with `f^*(𝟙 B)` normalised to `𝟙 (f^*B)`. -/
lemma comparisonAppIso_naturality_left
    {A A' : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)} (v : A ⟶ A')
    (B : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)) :
    (Stacks.RingedSpace.pullbackFunctor f).map
          (((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).map v).app B) ≫
        (comparisonAppIso f A' B).hom =
      (comparisonAppIso f A B).hom ≫
        ((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).map
          ((Stacks.RingedSpace.pullbackFunctor f).map v)).app
          ((Stacks.RingedSpace.pullbackFunctor f).obj B) :=
  comparisonAppIso_naturality_aux f v (𝟙 B) rfl ((Stacks.RingedSpace.pullbackFunctor f).map_id B)
    ((sheafTensor_uncurry_map ⟨Y.presheaf, Y.IsSheaf⟩ v (𝟙 B)).trans
      (sheafTensor_map_app ⟨Y.presheaf, Y.IsSheaf⟩ v B).symm)
    ((sheafTensor_uncurry_map ⟨X.presheaf, X.IsSheaf⟩ ((Stacks.RingedSpace.pullbackFunctor f).map v)
      (𝟙 ((Stacks.RingedSpace.pullbackFunctor f).obj B))).trans
        (sheafTensor_map_app ⟨X.presheaf, X.IsSheaf⟩ ((Stacks.RingedSpace.pullbackFunctor f).map v)
          ((Stacks.RingedSpace.pullbackFunctor f).obj B)).symm)

/-- The degreewise comparison is natural in the second module variable. -/
lemma comparisonAppIso_naturality_right
    (A : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y))
    {B B' : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)} (w : B ⟶ B') :
    (Stacks.RingedSpace.pullbackFunctor f).map
          (((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj A).map w) ≫
        (comparisonAppIso f A B').hom =
      (comparisonAppIso f A B).hom ≫
        ((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
          ((Stacks.RingedSpace.pullbackFunctor f).obj A)).map
          ((Stacks.RingedSpace.pullbackFunctor f).map w) :=
  comparisonAppIso_naturality_aux f (𝟙 A) w ((Stacks.RingedSpace.pullbackFunctor f).map_id A) rfl
    ((sheafTensor_uncurry_map ⟨Y.presheaf, Y.IsSheaf⟩ (𝟙 A) w).trans
      (sheafTensor_obj_map ⟨Y.presheaf, Y.IsSheaf⟩ A w).symm)
    ((sheafTensor_uncurry_map ⟨X.presheaf, X.IsSheaf⟩
      (𝟙 ((Stacks.RingedSpace.pullbackFunctor f).obj A))
      ((Stacks.RingedSpace.pullbackFunctor f).map w)).trans
        (sheafTensor_obj_map ⟨X.presheaf, X.IsSheaf⟩ ((Stacks.RingedSpace.pullbackFunctor f).obj A)
          ((Stacks.RingedSpace.pullbackFunctor f).map w)).symm)

/-- **`f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)`, from Stacks 01CD alone.**  This is
`pullbackTensorComplexIso` with its degreewise comparison supplied by the tree's own Stacks
01CD morphism, so the only hypothesis left is invertibility of that morphism's components. -/
def pullbackTensorComplexIsoOfIsIso (K L : CochainComplex
  (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    ((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _ ⟨Y.presheaf, Y.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj K).obj L) ≅
      ((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _ ⟨X.presheaf, X.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).obj
          (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)).obj
        (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) :=
  pullbackTensorComplexIso f (comparisonAppIso f)
    (fun {_ _} v B => comparisonAppIso_naturality_left f v B)
    (fun A {_ _} w => comparisonAppIso_naturality_right f A w) K L

end DegreewiseComparison

/-! ### The derived-category consequences -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **A K-flat complex computes the derived pullback.**  For K-flat `M`, the derived pullback
`Lf^*(QM)` is the image in `D(𝒪_X)` of the degreewise pullback `f^*M`.

This is `Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`
  packaged as an
isomorphism, with the `Q` versus `Qh ∘ quotient` bridge `DerivedCategory.quotientCompQhIso`
inserted at both ends.  It is unconditional. -/
def derivedPullbackIsoOfKFlat
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hM : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y M) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj (DerivedCategory.Q.obj
      M) ≅
      DerivedCategory.Q.obj
        (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing Y))).app M).symm ≪≫
    (@asIso _ _ _ _ ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M))
      (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f M hM))
        ≪≫
    (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X))).app
      (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)

/-- **The derived pullback of the total tensor complex of two K-flat complexes is computed
degreewise**, unconditionally.  This is the left-hand side of Stacks 079U: `K ⊗^L L` is
`Q(Tot(K ⊗ L))` for K-flat `K` and `L`, that complex is K-flat by Stacks 079R, and a K-flat
complex computes `Lf^*`. -/
def derivedPullbackTensorComplexIso
    (K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) (hL :
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y L) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj (((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _
          ⟨Y.presheaf, Y.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj K).obj L))
          ≅
      DerivedCategory.Q.obj
        (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((@Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} _ _ _
          ⟨Y.presheaf, Y.IsSheaf⟩
          inferInstance inferInstance
          (sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)
          (hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj K).obj
            L)) :=
  derivedPullbackIsoOfKFlat f _ (kFlat_tensorComplex Y K L hK hL)

/-! ### Stacks 079U on K-flat representatives -/

section KFlatRepresentatives

-- The four sheafification hypotheses are `Prop`s, inhabited for *every* ringed space by
-- `Stacks.AssociatedSheaf.hasModuleSheafify` and
-- `Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, so they are not a weakening.
-- They are the binders the derived tensor product of Stacks 06YU is stated under.
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 079U on K-flat representatives**:
`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L` for K-flat complexes `K` and `L` of
`𝒪_Y`-modules.

This is the isomorphism the source constructs, and it is constructed here the way the source
constructs it.  Reading the composite left to right:

1. `K ⊗^L L` is `Q(Tot(K ⊗ L))`, because `K` and `L` are K-flat — the `comparison` field of
   `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`;
2. `Lf^*` of that is `Q(f^*Tot(K ⊗ L))`, because `Tot(K ⊗ L)` is K-flat by Stacks 079R and a
   K-flat complex computes `Lf^*` — `derivedPullbackTensorComplexIso`;
3. `f^*Tot(K ⊗ L)` is `Tot(f^*K ⊗ f^*L)`, degreewise by Stacks 01CD —
   `pullbackTensorComplexIsoOfIsIso`;
4. `Tot(f^*K ⊗ f^*L)` is `f^*K ⊗^L f^*L`, because `f^*K` and `f^*L` are K-flat by Stacks 06YC;
5. `f^*K` and `f^*L` are `Lf^*K` and `Lf^*L`, by the same computation as step 2 —
   `derivedPullbackIsoOfKFlat`.

What is *not* here is the passage from K-flat representatives to arbitrary objects of
`D(𝒪_Y)`, which is what makes the source's statement bifunctorial. -/
def derivedPullbackTensorIsoOfKFlat
    (K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) (hL :
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y L) :
    letI := sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
    letI := sheafTensor_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩
    letI := sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
    letI := sheafTensor_obj_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩
    letI := fun (left right : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) =>
      hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩ left right
    letI := fun (left right : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) =>
      hasMapBifunctor_sheafTensor.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩ left right
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          ⟨Y.presheaf, Y.IsSheaf⟩).tensor.obj
          (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)) ≅
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          ⟨X.presheaf, X.IsSheaf⟩).tensor.obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
            (DerivedCategory.Q.obj K))).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          (DerivedCategory.Q.obj L)) :=
  letI := sheafTensor_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
  letI := sheafTensor_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩
  letI := sheafTensor_obj_additive.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩
  letI := sheafTensor_obj_additive.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩
  letI := fun (left right : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) =>
    hasMapBifunctor_sheafTensor.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩ left right
  letI := fun (left right : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) =>
    hasMapBifunctor_sheafTensor.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩ left right
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          ⟨Y.presheaf, Y.IsSheaf⟩).comparison K L hK hL)
        ≪≫
    derivedPullbackTensorComplexIso f K L hK hL ≪≫
    DerivedCategory.Q.mapIso (pullbackTensorComplexIsoOfIsIso f K L) ≪≫
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          ⟨X.presheaf, X.IsSheaf⟩).comparison _ _
      (kFlat_modulePullback_unconditional f K hK)
      (kFlat_modulePullback_unconditional f L hL)).symm ≪≫
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          ⟨X.presheaf, X.IsSheaf⟩).tensor.mapIso
      (derivedPullbackIsoOfKFlat f K hK).symm).app _ ≪≫
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          ⟨X.presheaf, X.IsSheaf⟩).tensor.obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj K))).mapIso
      (derivedPullbackIsoOfKFlat f L hL).symm

end KFlatRepresentatives

end Derived

end

end Stacks.Cohomology.DerivedPullbackTensor

end

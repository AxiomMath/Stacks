module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackHomComplexMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryHomEquivMiddleDinaturality

/-!
# The cochain-level comparison of Hom complexes: Tag 08J8, naturality, retracts and split sums

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
`Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap` is the canonical map of
complexes

`h^*𝓗om^•_{𝒪_Y}(E, F) ⟶ 𝓗om^•_{𝒪_X}(h^*E, h^*F)`

at the internal Hom complex of Tag 0A8Z.  This file equips it with everything the abstract
transpose construction of Tag 08I3 can give once **all four clauses of Tag 08J8 hold at the
cochain level**, which they now do: the two source clauses are
`curryHomEquivPair_naturality_source` and the two internal-hom clauses are
`AlgebraicGeometry.RingedSite.curryHomEquiv_dinaturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryHomEquivMiddleDinaturality`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.curryHomEquivPair_dinaturality`: Tag 08J8 in its
  internal-hom variable, in the shape `Transpose.TensorHomEquivDinatural` is stated at.
* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap_naturality_source`: the
  comparison is natural in its first argument, for an arbitrary morphism of complexes.
* `Stacks.Cohomology.DerivedInternalHomPullback.isIso_pullbackHomComplexMap_of_retract`:
  invertibility of the comparison passes to a retract of its first argument.
* `Stacks.Cohomology.DerivedInternalHomPullback.isIso_pullbackHomComplexMap_of_splitSum`:
  invertibility passes to a finite split sum of its first argument.

## Why this is the shape Tag 0GM7 clause (1) needs

Clause (1) is local on `Y`, and perfectness (Stacks 08CM) gives a strictly perfect model only
locally.  Invertibility of a morphism of `D(𝒪_Y)` has no restriction compatibility in this
development, whereas quasi-isomorphy of a morphism of **complexes** does, by
`AlgebraicGeometry.RingedSite.quasiIso_of_coversTop`.  So the dévissage of the comparison has to
be run on the complexes, and that is what the four cochain-level clauses of Tag 08J8 unlock: the
transfer lemmas below are the cochain-level counterparts of
`…InternalHomPullbackDevissage.isIso_derivedPullbackSheafHomMap_of_retract_singleUnit` and
`…InternalHomPullbackFiniteFree.isIso_derivedPullbackSheafHomMap_of_splitSum_singleUnit`, and
unlike those they cost nothing beyond additivity and so remain available after restriction to an
open.

## Nothing here is tagged

These are steps of the proof of Tag 0GM7, not clauses of it; the published map is the derived one,
which already carries the registration of Tag 08I3.  The three existing registrations of
Tag 0GM7 are untouched and no clause of it is proved or weakened here.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance_reducible] StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

/-! ### Tag 08J8 in its internal-hom variable, at the cochain level -/

section Dinaturality

variable (Z : RingedSpace.{u, u})

attribute [local instance 10000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **Tag 08J8 in its internal-hom variable, for the cochain-level currying bijection of
Tag 0A90**, in the shape `Transpose.TensorHomEquivDinatural` is stated at: the transpose of `ψ`
postcomposed with the map induced by `φ : B' ⟶ B` is the transpose of `ψ` precomposed with
`1 ⊗ φ`.

It is `AlgebraicGeometry.RingedSite.curryHomEquiv_dinaturality` with the curried spelling of the
total tensor complex traded for the uncurried one by `uncurry_map_id_mkHom`.  The map the
internal Hom bifunctor of Tag 0A8Z induces from `φ` is `homMap φ (𝟙 C)` by definition of
`AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor`, which is why no bridge is needed on that
side. -/
theorem curryHomEquivPair_dinaturality
    (A B B' C : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (φ : B' ⟶ B)
    (ψ : A ⟶ ((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Z)).obj (op B)).obj C) :
    AlgebraicGeometry.RingedSite.curryHomEquivPair
        (AlgebraicGeometry.RingedSpace.ringedSite Z) A B' C
        (ψ ≫ ((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
          (AlgebraicGeometry.RingedSpace.ringedSite Z)).map φ.op).app C) =
      (totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z).sheaf)).map (𝟙 A ×ₘ φ) ≫
        AlgebraicGeometry.RingedSite.curryHomEquivPair
          (AlgebraicGeometry.RingedSpace.ringedSite Z) A B C ψ := by
  rw [uncurry_map_id_mkHom
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z).sheaf).map₂HomologicalComplexReg
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) A φ]
  exact AlgebraicGeometry.RingedSite.curryHomEquiv_dinaturality
    (AlgebraicGeometry.RingedSpace.ringedSite Z) A C φ ψ

end Dinaturality

/-! ### Naturality, retracts and split sums of the first argument -/

section Transfer

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

attribute [local instance 10000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The cochain-level comparison is natural in its first argument**, for an arbitrary morphism
`φ : E' ⟶ E` of complexes of `𝒪_Y`-modules and arbitrary `F`:

`h^*𝓗om^•(φ, 1) ≫ cmp_{E'} = cmp_E ≫ 𝓗om^•(h^*φ, 1)`.

This is `Transpose.homComparison_naturality_source` at the Tag 0A8Z data, with all four clauses
of Tag 08J8 supplied at the cochain level — the two source ones by
`curryHomEquivPair_naturality_source` and the two internal-hom ones by
`curryHomEquivPair_dinaturality`.  No hypothesis on `φ`, `E`, `E'` or `F`. -/
theorem pullbackHomComplexMap_naturality_source
    {E E' : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ} (φ : E' ⟶ E)
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackComplex h).map
          (((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
            (AlgebraicGeometry.RingedSpace.ringedSite Y)).map φ.op).app F) ≫
        pullbackHomComplexMap h E' F =
      pullbackHomComplexMap h E F ≫
        ((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
          (AlgebraicGeometry.RingedSpace.ringedSite X)).map
            ((pullbackComplex h).map φ).op).app ((pullbackComplex h).obj F) :=
  Transpose.homComparison_naturality_source (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y).sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (pullbackTensorComplexNatIso h)
    (curryHomEquivPair_naturality_source Y) (curryHomEquivPair_dinaturality Y)
    (curryHomEquivPair_naturality_source X) (curryHomEquivPair_dinaturality X) φ F

/-- **Invertibility of the cochain-level comparison passes to a retract of its first argument.**
If `E'` is a retract of `E` — so `E' ⟶ E ⟶ E'` is the identity — and the comparison at `E` is
invertible, then so is the comparison at `E'`.

Only the naturality of the comparison in its first argument is used: no shift, no triangulated
structure, no hypothesis on `F`. -/
theorem isIso_pullbackHomComplexMap_of_retract
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    {E E' : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ}
    (i : E' ⟶ E) (r : E ⟶ E') (hir : i ≫ r = 𝟙 E')
    (hE : IsIso (pullbackHomComplexMap h E F)) :
    IsIso (pullbackHomComplexMap h E' F) :=
  Transpose.isIso_homComparison_of_retract (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y).sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (pullbackTensorComplexNatIso h)
    (curryHomEquivPair_naturality_source Y) (curryHomEquivPair_dinaturality Y)
    (curryHomEquivPair_naturality_source X) (curryHomEquivPair_dinaturality X) F i r hir hE

/-- **The internal Hom complex of Tag 0A8Z is additive in its contravariant variable.**  The flip
acts on a morphism of `(Comp(Mod 𝒪_Z))ᵒᵖ` by `AlgebraicGeometry.RingedSite.homMap` at its unop and
an identity, and that is additive in the morphism of sources by
`AlgebraicGeometry.RingedSite.homMap_add_left`. -/
theorem additive_sheafHomComplexFlip (Z : RingedSpace.{u, u})
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    ((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Z)).flip.obj F).Additive where
  map_add {K L f g} := by
    change AlgebraicGeometry.RingedSite.homMap (AlgebraicGeometry.RingedSpace.ringedSite Z)
        (f + g).unop (𝟙 F) =
      AlgebraicGeometry.RingedSite.homMap (AlgebraicGeometry.RingedSpace.ringedSite Z)
          f.unop (𝟙 F) +
        AlgebraicGeometry.RingedSite.homMap (AlgebraicGeometry.RingedSpace.ringedSite Z)
          g.unop (𝟙 F)
    rw [unop_add, AlgebraicGeometry.RingedSite.homMap_add_left]

/-- The left-hand side of the cochain-level comparison, read as a functor of its first argument,
is additive: the internal Hom complex in its contravariant variable followed by the degreewise
pullback, which is `CategoryTheory.Functor.mapHomologicalComplex` of an additive functor. -/
theorem additive_comparisonSourceFunctorComplex
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (Transpose.comparisonSourceFunctor (pullbackComplex h)
      (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
        (AlgebraicGeometry.RingedSpace.ringedSite Y)) F).Additive :=
  have := additive_sheafHomComplexFlip Y F
  inferInstanceAs
    (((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y)).flip.obj F ⋙ pullbackComplex h).Additive)

/-- The right-hand side of the cochain-level comparison, read as a functor of its first argument,
is additive: the opposite of the degreewise pullback, additive by Mathlib's
`CategoryTheory.Functor.op_additive`, followed by the internal Hom complex in its contravariant
variable. -/
theorem additive_comparisonTargetFunctorComplex
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (Transpose.comparisonTargetFunctor (pullbackComplex h)
      (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
        (AlgebraicGeometry.RingedSpace.ringedSite X)) F).Additive :=
  have := additive_sheafHomComplexFlip X ((pullbackComplex h).obj F)
  inferInstanceAs
    (((pullbackComplex h).op ⋙
      (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
        (AlgebraicGeometry.RingedSpace.ringedSite X)).flip.obj
          ((pullbackComplex h).obj F)).Additive)

attribute [local instance] additive_comparisonSourceFunctorComplex
  additive_comparisonTargetFunctorComplex

/-- **Invertibility of the cochain-level comparison passes to a finite split sum of its first
argument.**  If `E` carries families `ι j : A j ⟶ E` and `π j : E ⟶ A j` indexed by a finite type
with `∑ j, π j ≫ ι j = 𝟙 E` — which is `CategoryTheory.Limits.biproduct.total` when `E` is a
biproduct — and the comparison is invertible at every `A j`, then it is invertible at `E`.

This is `Transpose.isIso_homComparison_of_splitSum` at the Tag 0A8Z cochain data.  The two
additivity binders it asks for are discharged: both sides are composites of an internal Hom
complex in its contravariant variable with the degreewise pullback, and `h^*` on complexes is
`CategoryTheory.Functor.mapHomologicalComplex` of an additive functor. -/
theorem isIso_pullbackHomComplexMap_of_splitSum
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    {J : Type*} [Fintype J]
    {E : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ}
    (A : J → CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (ι : ∀ j, A j ⟶ E) (π : ∀ j, E ⟶ A j)
    (hsum : ∑ j : J, π j ≫ ι j = 𝟙 E)
    (hA : ∀ j, IsIso (pullbackHomComplexMap h (A j) F)) :
    IsIso (pullbackHomComplexMap h E F) :=
  Transpose.isIso_homComparison_of_splitSum (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y).sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (pullbackTensorComplexNatIso h)
    (curryHomEquivPair_naturality_source Y) (curryHomEquivPair_dinaturality Y)
    (curryHomEquivPair_naturality_source X) (curryHomEquivPair_dinaturality X) F A ι π hsum hA

end Transfer

end Stacks.Cohomology.DerivedInternalHomPullback

end

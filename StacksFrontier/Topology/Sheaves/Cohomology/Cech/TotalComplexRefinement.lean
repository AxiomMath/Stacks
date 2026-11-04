module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.LargeColimits
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksCore.CategoryTheory.Limits.Shapes.Countable
import StacksCore.Tactic.StacksAttribute

/-!
# The map on total Čech complexes induced by a refinement

Let `C` be a category with finite products, let `U : I → C` and `V : J → C` be two families of
objects, and let `t : V ⟶ U` be a refinement of the first by the second, that is a morphism of
the associated formal coproducts: a map `t : J → I` on indices together with morphisms
`V_j ⟶ U_{t j}`. For a complex of abelian presheaves `F^•` on `C`, restriction along the
components of `t` gives a map of total Čech complexes

`T_t : Tot(Č^•(U, F^•)) ⟶ Tot(Č^•(V, F^•))`,

natural in `F^•`. This is the transformation of Stacks 08BM, used there to compare the Čech
complexes of two coverings and to pass to the limit over refinements.

## Main definitions

* `Stacks.Cech.cechComplexFunctorInt`: the nonnegatively graded Čech complex of a family,
  regarded as a complex indexed by the integers.
* `Stacks.Cech.cechBicomplexFunctor` and `Stacks.Cech.cechTotalComplexFunctor`: the Čech
  construction applied degreewise to a complex of presheaves, and the total complex of the
  resulting bicomplex.
* `Stacks.Cech.totalMapOfCechMap`: the totalization of a natural map of Čech-complex functors.
* `Stacks.Cech.CechRefinementTransformation`: the functorial transformation attached to a
  refinement, together with the formula for its components.

## Main results

* `Stacks.Cech.cechTotalComplexRefinement` (Stacks 08BM): a refinement `t : V ⟶ U` induces
  such a transformation, whose Čech-degree-`n` component is restriction along the `n`-th power
  of `t`.

## Implementation notes

A refinement is represented by a morphism of formal coproducts
`FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U`; its index map is the function `t` of the
source and its component morphisms are the inclusions of the members of the refining family.
The component formula `cechMap_f` says, in every Čech degree, that the map is restriction
along the corresponding power `FormalCoproduct.powerMap` of `t`, so the transformation cannot
be replaced by an unrelated natural map.

Mathlib's Čech complex of a family is indexed by `ℕ`, so it is first extended by zero to a
`ℤ`-indexed complex along `embeddingUpNat`; the Čech degree is then the first degree of the
resulting double complex, and the two integer gradings are totalized. The hypotheses that the
Čech-complex functor preserves zero morphisms and that the relevant bicomplexes have total
complexes are carried as fields of the structure rather than as instance arguments, because
they are what makes the two totalizations in the statement exist and they must be the same
witnesses on both sides of `map_eq`.

## References

* [Stacks Project, Tag 08BM](https://stacks.math.columbia.edu/tag/08BM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe w v u

namespace Stacks.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- The Čech complex of a family, extended by zero from nonnegative degrees to an
integer-indexed cochain complex. -/
noncomputable def cechComplexFunctorInt {I : Type w} (U : I → C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ CochainComplex AddCommGrpCat.{w} ℤ :=
  CategoryTheory.cechComplexFunctor U ⋙
    embeddingUpNat.extendFunctor AddCommGrpCat.{w}

/-- Applying the integer-indexed Čech complex degreewise to a complex of presheaves, with the
Čech degree placed first. -/
noncomputable def cechBicomplexFunctor {I : Type w} (U : I → C)
    [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U).PreservesZeroMorphisms] :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ) :=
  (CategoryTheory.cechComplexFunctor U ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{w}).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor AddCommGrpCat.{w} (up ℤ) (up ℤ)

/-- The functor sending a complex of presheaves to the total complex of its Čech bicomplex. -/
noncomputable def cechTotalComplexFunctor {I : Type w} (U : I → C)
    [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U).PreservesZeroMorphisms]
    [∀ (K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ)), K.HasTotal (up ℤ)] :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ ⥤ CochainComplex AddCommGrpCat.{w} ℤ :=
  cechBicomplexFunctor U ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{w} (up ℤ) (up ℤ) (up ℤ)

/-- Totalize a natural map between the nonnegative Čech-complex functors. -/
noncomputable def totalMapOfCechMap {I J : Type w} (U : I → C) (V : J → C)
    [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U).PreservesZeroMorphisms]
    [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) V).PreservesZeroMorphisms]
    [∀ (K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ)), K.HasTotal (up ℤ)]
    (α : CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U ⟶
      CategoryTheory.cechComplexFunctor V) :
    cechTotalComplexFunctor U ⟶ cechTotalComplexFunctor V :=
  (((α.hcomp (𝟙 (embeddingUpNat.extendFunctor AddCommGrpCat.{w}))).mapHomologicalComplex
      (up ℤ)).hcomp
      (𝟙 (HomologicalComplex₂.flipFunctor AddCommGrpCat.{w} (up ℤ) (up ℤ)))).hcomp
    (𝟙 (HomologicalComplex₂.totalFunctor AddCommGrpCat.{w} (up ℤ) (up ℤ) (up ℤ)))

/-- The data of the natural transformation on total Čech complexes associated to a refinement
`t : V ⟶ U`. -/
structure CechRefinementTransformation {I J : Type w} (U : I → C) (V : J → C)
    (t : FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U) where
  /-- The Čech complex of `U` preserves zero morphisms. -/
  preservesZeroU :
    (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U).PreservesZeroMorphisms
  /-- The Čech complex of `V` preserves zero morphisms. -/
  preservesZeroV :
    (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) V).PreservesZeroMorphisms
  /-- Double complexes of abelian groups have total complexes. -/
  hasTotal : ∀ (K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ)), K.HasTotal (up ℤ)
  /-- The map of Čech complexes induced by the refinement. -/
  cechMap : CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U ⟶
    CategoryTheory.cechComplexFunctor V
  /-- In Čech degree `n` the map is restriction along the `n`-th power of the refinement. -/
  cechMap_f (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (cechMap.app P).f n =
      ((FormalCoproduct.evalOp C AddCommGrpCat.{w}).obj P).map
        (FormalCoproduct.powerMap t (Fin (n + 1))).op
  /-- The induced map on total Čech complexes. -/
  map :
    letI := preservesZeroU
    letI := preservesZeroV
    letI := hasTotal
    cechTotalComplexFunctor U ⟶ cechTotalComplexFunctor V
  /-- The induced map is the totalization of `cechMap`. -/
  map_eq :
    letI := preservesZeroU
    letI := preservesZeroV
    letI := hasTotal
    map = totalMapOfCechMap U V cechMap

/-- **Stacks 08BM.** A refinement `t : V ⟶ U` induces, naturally in a complex of presheaves,
the restriction map `Tot(Č^•(U, F^•)) ⟶ Tot(Č^•(V, F^•))`. -/
@[stacks 08BM, ega "III 6.6.7" "partial"]
noncomputable def cechTotalComplexRefinement {I J : Type w} (U : I → C) (V : J → C)
    (t : FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U) :
    CechRefinementTransformation U V t :=
  let cechPreservesZero {T : Type w} (W : T → C) :
      (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) W).PreservesZeroMorphisms :=
    ⟨by
      intro P Q
      apply HomologicalComplex.Hom.ext
      funext n
      simp only [HomologicalComplex.zero_f]
      change Limits.Pi.map (fun i ↦ (0 : P.obj _ ⟶ Q.obj _)) = 0
      ext j
      simp⟩
  letI := cechPreservesZero U
  letI := cechPreservesZero V
  letI : HasCountableCoproducts AddCommGrpCat.{w} := inferInstance
  letI : HasProducts.{w} AddCommGrpCat.{w} := inferInstance
  letI : ∀ (K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ)), K.HasTotal (up ℤ) :=
    inferInstance
  let cechMap : CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U ⟶
      CategoryTheory.cechComplexFunctor V :=
    { app := fun P ↦
        (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w}).map
          ((FormalCoproduct.cechFunctor.map t).rightOp.hcomp
            (𝟙 ((FormalCoproduct.evalOp C AddCommGrpCat.{w}).obj P)))
      naturality := by
        intros X Y f
        apply HomologicalComplex.Hom.ext
        funext n
        dsimp [cechComplexFunctor,
          CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
          CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
          AlgebraicTopology.alternatingCofaceMapComplex,
          AlgebraicTopology.AlternatingCofaceMapComplex.map,
          AlgebraicTopology.AlternatingCofaceMapComplex.obj,
          FormalCoproduct.cechFunctor]
        simpa using (((FormalCoproduct.evalOp C AddCommGrpCat.{w}).map f).naturality
          (FormalCoproduct.powerMap t (ToType ({ len := n } : SimplexCategory))).op).symm }
  { preservesZeroU := inferInstance
    preservesZeroV := inferInstance
    hasTotal := fun K ↦ inferInstance
    cechMap := cechMap
    cechMap_f := by
      intro P n
      dsimp [cechMap, cechComplexFunctor,
        CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
        CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
        AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.map,
        FormalCoproduct.cechFunctor]
      simp only [Functor.hcomp_id, Functor.whiskerRight_app, Functor.rightOp_obj,
        FormalCoproduct.cech_obj, NatTrans.rightOp_app, FormalCoproduct.evalOp_obj_map,
        Quiver.Hom.unop_op, FormalCoproduct.powerMap_φ]
      ext i
      simp
    map := totalMapOfCechMap U V cechMap
    map_eq := rfl }

end Stacks.Cech

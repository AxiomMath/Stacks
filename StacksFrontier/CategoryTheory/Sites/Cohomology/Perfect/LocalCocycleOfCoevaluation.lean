module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualCoevaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.UnitComplexCocycles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
import StacksCore.Tactic.StacksAttribute

/-!
# The restricted coevaluation is locally the map of complexes attached to a cocycle

Stacks 0FPV's first assertion is proved by writing the coevaluation, locally on the site, as a
finite sum of pure tensors. The first step is to make it a *map of complexes* at all: the
coevaluation is a morphism of the derived category, and only after restricting along the arrows
of a covering sieve is it the image of a morphism of complexes. That is Stacks 08FR (1),
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`, applicable because the unit
complex is strictly perfect on every slice.

This file performs that application and converts its output into the form the direct-summand step
consumes. A map of complexes out of `O[0]|_V` is the same thing as a cocycle section of the
target in degree zero (`AlgebraicGeometry.RingedSite.cocycleOfUnitComplexHom` and
`unitComplexHomOfCocycle`), and that cocycle is the `η(1)` of the source's argument — the section
which the next step writes as a finite sum of pure tensors.

## Implementation notes

08FR (1) returns its morphism over the *iterated* slice: `β` has source
`((overMap R f).mapHomologicalComplex _).obj (O[0]|_U)`, whereas the cocycle correspondence is
stated for `O[0]|_V`. These two are identified by `Stacks.SheafOfModules.overFunctorMapComplexIso`,
the degreewise form of `overFunctor R U ⋙ overMap R f ≅ overFunctor R V`, and the conjugation by
it is what appears in the statement below. Per that file's own warning the comparison is used as
given and not replaced by an `Iso.refl`.

The five instance existentials of 08FR (1) are carried through rather than discharged against
the ambient instances: `PreservesFiniteLimits` carries data, so an ambient instance need not be
the one the covering sieve produced, and a statement that silently swapped them would be about a
different morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Category
  Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.LeftDualOnASite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The restricted coevaluation is, on a covering sieve, the map of complexes attached to a
cocycle section in degree zero.** This is Stacks 08FR (1) applied to
`AlgebraicGeometry.RingedSite.coevaluationUnitHomRestrict`, with its morphism of complexes
transported to the slice over `V` and read as a cocycle.

The section `t` is the `η(1)` of the proof of Stacks 0FPV: the next step of that proof writes it,
after a further refinement, as a finite sum of pure tensors. -/
public theorem exists_coveringSieve_cocycle_coevaluationUnitHomRestrict
    (Mc Nc : Complexes X.O) (hM : KFlat X.O Mc) (hN : KFlat X.O Nc)
    (η : letI := derivedMonoidal X.O
      𝟙_ (DerivedModules X.O) ⟶ DerivedCategory.Q.obj Mc ⊗ DerivedCategory.Q.obj Nc)
    (U : X.C) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        ∃ (hsheaf : HasSheafify (X.J.over V) AddCommGrpCat.{u})
          (hlocal : (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}),
          letI := hsheaf
          letI := hlocal
          letI : HasDerivedCategory
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
            HasDerivedCategory.standard _
          ∃ (hadd :
              (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).Additive)
            (hlim : PreservesFiniteLimits
              (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f))
            (hcolim : PreservesFiniteColimits
              (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f)),
            letI := hadd
            letI := hlim
            letI := hcolim
            ∃ (t : (((Mc ⊗ Nc : Complexes X.O)).X 0).val.obj (op V))
              (ht : (((Mc ⊗ Nc : Complexes X.O)).d 0 1).val.app (op V) t = 0),
              (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                  f).mapDerivedCategory.map
                    (X.coevaluationUnitHomRestrict Mc Nc hM hN η U) ≫
                  (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                      f).mapDerivedCategoryFactors.hom.app
                    (X.restrictComplex (Mc ⊗ Nc : Complexes X.O) U) =
                (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                    f).mapDerivedCategoryFactors.hom.app
                    (X.restrictComplex X.structureSheafComplex U) ≫
                  DerivedCategory.Q.map
                    ((Stacks.SheafOfModules.overFunctorMapComplexIso
                        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).hom.app
                        X.structureSheafComplex ≫
                      X.unitComplexHomOfCocycle t ht ≫
                      (Stacks.SheafOfModules.overFunctorMapComplexIso
                          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).inv.app
                        (Mc ⊗ Nc : Complexes X.O)) := by
  obtain ⟨S, hS, hrep⟩ := AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap X U
    (X.isStrictlyPerfect_restrictComplex_structureSheafComplex U)
    (X.coevaluationUnitHomRestrict Mc Nc hM hN η U)
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨hsheaf, hlocal, hadd, hlim, hcolim, β, hβ⟩ := hrep f hf
  refine ⟨hsheaf, hlocal, hadd, hlim, hcolim, ?_⟩
  let γ := (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).inv.app X.structureSheafComplex ≫ β ≫
    (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).hom.app (Mc ⊗ Nc : Complexes X.O)
  refine ⟨X.cocycleOfUnitComplexHom γ, X.cocycleOfUnitComplexHom_d _, ?_⟩
  rw [X.unitComplexHom_ext (γ := γ) (X.cocycleOfUnitComplexHom_unitComplexHomOfCocycle _ _)]
  simp only [γ, assoc, Iso.hom_inv_id_app_assoc]
  exact hβ

end Stacks.Cohomology.LeftDualOnASite

end

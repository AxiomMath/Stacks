module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionComparison
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.QuasiInverseObject
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Abelian

/-!
# `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))` as a functor to graded modules

Let `A` be a graded ring and `X = Proj A`. Stacks 0BXF names `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))` as the
quasi-inverse of its equivalence. This file builds that assignment as a **functor** from sheaves
of `𝒪_X`-modules to graded `A`-modules, for every cut `k`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.truncatedTwistedSectionsObj`: the graded
  `A`-module `⨁_{n ≥ k} Γ(X, ℱ(n))`, as an object of `GradedModuleCat A`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.truncatedTwistedSectionsFunctor`: **the
  functor `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))`.**

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.truncatedTwistedSectionsFunctor_obj_iso`:
  the associated sheaf of the value of the functor is `ℱ` again, for `ℱ` quasi-coherent on a
  Noetherian `Proj A`. This is the object half of the statement that the functor is a
  quasi-inverse.

## Implementation notes

The three typeclass fields of `GradedModuleCat` are all supplied by existing instances once the
`A`-module structure on `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` is introduced from the canonical datum
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule`: the grading of the
truncation is `Stacks.GradedModule.truncationAboveGrading`, which is already `AddSubgroup`-valued
— the spelling `GradedModuleCat.grade` asks for — and its `DirectSum.Decomposition` and
`SetLike.GradedSMul` are the instances of
`StacksFrontier/RingTheory/GradedAlgebra/ModuleTruncation.lean`. So no transport between the
`Submodule ℤ`-valued grading of the twisted global sections and an `AddSubgroup`-valued one is
needed anywhere, which is what makes the object definition instance-clean.

On morphisms the functor is `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.truncationAboveMap`
applied to `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsLinearMap`, whose
degree-preservation is
`Stacks.AlgebraicGeometry.ProjTwistComparison.twistedSectionsMap_mem_grading`; the two functor laws
reduce to `twistedSectionsMap_id` and `twistedSectionsMap_comp`.

## What this is not

The functor lands in **all** graded `A`-modules, not in the finitely generated ones, and it is
stated here with no finiteness hypothesis. Corestricting it to `Mod^fg_A` — which is what Stacks
0BXF's quasi-inverse has to do — is Tag 0B5Q's clause (4):
`coherentTruncatedTwistedSectionsFunctor` in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/EssentiallySurjective.lean` is the
corestriction, over a grading carrier in the ring's universe, which is clause (4)'s hypothesis.
Fullness of the arrow is independent of all of this: it comes from the quasi-inverse being an
equivalence, which is
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_coherentIrrelevantQuotientEquivalence` in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/Equivalence.lean` and rests on parts (3)
to (6) of Tag 0B5R.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedGlobalSectionsGrading
  twistedGlobalSectionsModule twistedSectionsLinearMap
  isTwistedSectionsSMul_twistedGlobalSectionsModule twistedSectionsMap twistedSectionsMap_id
  twistedSectionsMap_comp)
open Stacks.AlgebraicGeometry.ProjTwistComparison (twistedSectionsMap_mem_grading)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The graded `A`-module `⨁_{n ≥ k} Γ(X, ℱ(n))`**, as an object of the category of graded
modules. -/
public def truncatedTwistedSectionsObj (F : SheafOfModules.{u} (projRingSheaf 𝒮)) (k : ℤ) :
    GradedModuleCat.{u, u, w} 𝒮 :=
  letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
  letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
  { carrier := ↥(truncationAbove 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k)
    grade := truncationAboveGrading 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k }

/-- The grading of `truncatedTwistedSectionsObj 𝒮 F k` is the truncation above `k` of the grading
of the twisted global sections. -/
@[simp]
public theorem grade_truncatedTwistedSectionsObj (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    (k : ℤ) :
    letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
    (truncatedTwistedSectionsObj 𝒮 F k).grade =
      truncationAboveGrading 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k := rfl

/-- **The map `⨁_{n ≥ k} Γ(X, ℱ(n)) ⟶ ⨁_{n ≥ k} Γ(X, 𝒢(n))` induced by `ψ : ℱ ⟶ 𝒢`.** -/
public def truncatedTwistedSectionsMap {F G : SheafOfModules.{u} (projRingSheaf 𝒮)} (ψ : F ⟶ G)
    (k : ℤ) : truncatedTwistedSectionsObj 𝒮 F k ⟶ truncatedTwistedSectionsObj 𝒮 G k :=
  letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
  letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
  letI := (twistedGlobalSectionsModule 𝒮 G).moduleInst
  letI := (twistedGlobalSectionsModule 𝒮 G).gradedSMul
  { toLinearMap := truncationAboveMap 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
      (twistedGlobalSectionsGrading 𝒮 G)
      (twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F
        (twistedGlobalSectionsModule 𝒮 F))
        (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 G
          (twistedGlobalSectionsModule 𝒮 G)) ψ)
      (twistedSectionsMap_mem_grading 𝒮 ψ) k
    map_grade := truncationAboveMap_mem_grading 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
      (twistedGlobalSectionsGrading 𝒮 G) _ (twistedSectionsMap_mem_grading 𝒮 ψ) k }

/-- **The functor `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))`**, whose nonnegative case `k = 0` is the
quasi-inverse named by Stacks 0BXF. -/
public def truncatedTwistedSectionsFunctor (k : ℤ) :
    SheafOfModules.{u} (projRingSheaf 𝒮) ⥤ GradedModuleCat.{u, u, w} 𝒮 where
  obj F := truncatedTwistedSectionsObj 𝒮 F k
  map ψ := truncatedTwistedSectionsMap 𝒮 ψ k
  map_id F := by
    refine GradedModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact DFunLike.congr_fun (twistedSectionsMap_id (E := F) 𝒮) _
  map_comp {F G H} ψ χ := by
    refine GradedModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact DFunLike.congr_fun (twistedSectionsMap_comp 𝒮 ψ χ) _

/-- The value of `truncatedTwistedSectionsFunctor 𝒮 k` at `F` is
`truncatedTwistedSectionsObj 𝒮 F k`. -/
@[simp]
public theorem truncatedTwistedSectionsFunctor_obj (k : ℤ)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮)) :
    (truncatedTwistedSectionsFunctor 𝒮 k).obj F = truncatedTwistedSectionsObj 𝒮 F k := rfl

/-- **The associated sheaf of `⨁_{n ≥ k} Γ(X, ℱ(n))` is `ℱ` again**, for `ℱ` quasi-coherent and
`A` Noetherian graded: the object half of the statement that
`truncatedTwistedSectionsFunctor` is a quasi-inverse of `M ↦ M̃`. -/
public def truncatedTwistedSectionsFunctor_obj_iso [IsNoetherianRing S] (k : ℤ)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) :
    (associatedModuleSheafFunctor.{u, u, w} 𝒮).obj
      ((truncatedTwistedSectionsFunctor 𝒮 k).obj F) ≅ F :=
  truncatedTwistedSectionsIsoOfNoetherian 𝒮 F hqc k

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end

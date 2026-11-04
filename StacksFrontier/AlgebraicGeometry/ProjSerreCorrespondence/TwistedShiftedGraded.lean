module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TwistedToShiftedScalar
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TwistedSectionsFunctor
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.Multiplication
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted and the shifted graded modules of global sections agree

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `X = Proj 𝒮`, and `M = ⨁_{n ∈ ℤ} 𝒨 n` a
graded `S`-module. There are two graded `S`-modules of global sections attached to `M`:

`N  = ⨁_{n ∈ ℤ} Γ(X, M̃(n))`   and   `N' = ⨁_{n ∈ ℤ} Γ(X, M(n)~)`,

the first built from the twists of the associated sheaf and the second from the associated
sheaves of the shifted modules. The comparison `N → N'` of Tag 0B5R (3),
`Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections`, is a morphism in the category
of graded `S`-modules, and an isomorphism there when the standard opens of the degree-one
homogeneous elements cover `X`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.shiftedSectionsGradedModule`: the graded
  `S`-module `N' = ⨁_{n ∈ ℤ} Γ(X, M(n)~)` as an object of the category of graded modules.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.canonicalShiftedMap`: the map `M → N'` of
  Tag 01MR, as a morphism of graded `S`-modules.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedToShiftedLinearMap` and
  `twistedToShiftedGradedMap`: the comparison `N → N'` as an `S`-linear map, respectively as a
  morphism of graded `S`-modules.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedShiftedGradedIso`: the isomorphism
  `N ≅ N'` of graded `S`-modules, under the degree-one covering hypothesis.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.bijective_twistedToShiftedSections`: under
  the degree-one covering hypothesis the comparison is bijective.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIso_twistedToShiftedGradedMap`: hence it is
  an isomorphism in the category of graded `S`-modules, which is abelian.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.globalSectionsModuleMap_smul_of`: a
  homogeneous scalar of degree `i` carries the degree-`n` summand of `N'` to the degree-`i + n`
  summand by the homogeneous scalar action on sections.

## References

* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (associatedModuleSheaf associatedModuleSheafSectionsEquiv twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjCoherentII
  (twistedToShiftedComponent twistedToShiftedSections twistedToShiftedSections_component
    bijective_twistedToShiftedComponent)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (GradedModuleCat)
open Stacks.AlgebraicGeometry.ProjShiftedSections
open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S : Type u} {M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-! ### The graded module of shifted global sections -/

/-- The canonical `S`-module structure of Tag 01MR on `⨁_{n ∈ ℤ} Γ(Proj 𝒮, M(n)~)`, separated
from its bundled datum `GlobalSectionsModuleMap`. -/
@[instance_reducible]
def shiftedGlobalSectionsModuleInstance : Module S (shiftedModuleGlobalSections 𝒮 𝒨) :=
  (globalSectionsModuleMap 𝒮 𝒨).moduleInst

attribute [local instance] shiftedGlobalSectionsModuleInstance
attribute [local instance] twistedGlobalSectionsModuleInstance

/-- **The graded `S`-module `⨁_{n ∈ ℤ} Γ(Proj 𝒮, M(n)~)` of Tag 01MR, as an object of the
category of graded `S`-modules.** -/
def shiftedSectionsGradedModule : GradedModuleCat.{u, u, w} 𝒮 where
  carrier := shiftedModuleGlobalSections 𝒮 𝒨
  grade n := (shiftedModuleGlobalSectionsGrading 𝒮 𝒨 n).toAddSubgroup
  decomposition := decompositionToAddSubgroup (shiftedModuleGlobalSectionsGrading 𝒮 𝒨)
  gradedSMul := ⟨(globalSectionsModuleMap 𝒮 𝒨).gradedSMul.smul_mem⟩

/-- **The canonical map `M → ⨁_{n ∈ ℤ} Γ(Proj 𝒮, M(n)~)` of Tag 01MR, as a morphism of graded
`S`-modules**, for `M` the object `P` of the category of graded modules. -/
@[ega "II 2.6.2" "partial"]
def canonicalShiftedMap (P : GradedModuleCat.{u, u, w} 𝒮) :
    P ⟶ shiftedSectionsGradedModule 𝒮 P.grade where
  toLinearMap := (globalSectionsModuleMap 𝒮 P.grade).hom
  map_grade n m hm :=
    (DirectSum.mem_rangeGrading ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 P.grade k) n _).mpr
      ⟨_, (globalSectionsModuleMap 𝒮 P.grade).map_homogeneous n ⟨m, hm⟩⟩

/-! ### The full formula for a homogeneous scalar on the shifted global sections -/

/-- **A homogeneous scalar of degree `i` carries the degree-`n` summand of
`⨁_{n ∈ ℤ} Γ(Proj 𝒮, M(n)~)` to the degree-`i + n` summand**, by the homogeneous scalar action on
sections. -/
theorem globalSectionsModuleMap_smul_of (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (t : shiftedSectionsComponent 𝒮 𝒨 n) :
    (a : S) • (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n t :
        shiftedModuleGlobalSections 𝒮 𝒨) =
      DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) ((i : ℤ) + n)
        (homogeneousScalarGlobalSections 𝒮 𝒨 i n a t) := by
  have hmem : ((a : S) • (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n t :
      shiftedModuleGlobalSections 𝒮 𝒨)) ∈
      shiftedModuleGlobalSectionsGrading 𝒮 𝒨 ((i : ℤ) + n) :=
    (globalSectionsModuleMap 𝒮 𝒨).gradedSMul.smul_mem a.2
      ((DirectSum.mem_rangeGrading ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n _).mpr
        ⟨t, rfl⟩)
  obtain ⟨w, hw⟩ :=
    (DirectSum.mem_rangeGrading ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k)
      ((i : ℤ) + n) _).mp hmem
  rw [hw]
  refine congrArg _ ?_
  have hcomp : DirectSum.component ℤ ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k)
      ((i : ℤ) + n) ((a : S) • (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n t :
        shiftedModuleGlobalSections 𝒮 𝒨)) = w := by
    rw [hw, ← DirectSum.apply_eq_component, DirectSum.of_eq_same]
  apply (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤).injective
  apply Subtype.ext
  funext x
  have hval := (globalSectionsModuleMap 𝒮 𝒨).smul_homogeneous i n a t x
  rw [hcomp] at hval
  exact hval.trans (homogeneousScalarGlobalSections_apply 𝒮 𝒨 i n a t x).symm

/-! ### The comparison as an `S`-linear map -/

/-- The comparison on the degree-`n` summand: the assembled comparison sends the `n`-th summand
to the `n`-th summand by the degreewise comparison. -/
theorem twistedToShiftedSections_of (n : ℤ)
    (s : twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) n) :
    twistedToShiftedSections 𝒮 𝒨
        (DirectSum.of (fun k : ℤ =>
          twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) k) n s) =
      DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n
        (twistedToShiftedComponent 𝒮 𝒨 n s) :=
  DirectSum.toAddMonoid_of
    (fun k : ℤ => (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) k).comp
      (twistedToShiftedComponent 𝒮 𝒨 k)) n s

/-- **The comparison `N → N'` of Tag 0B5R (3), as an `S`-linear map.** -/
def twistedToShiftedLinearMap :
    twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨) →ₗ[S]
      shiftedModuleGlobalSections 𝒮 𝒨 where
  toFun := twistedToShiftedSections 𝒮 𝒨
  map_add' := map_add (twistedToShiftedSections 𝒮 𝒨)
  map_smul' := ProjCoherentII.twistedToShiftedSections_smul 𝒮 𝒨

/-- **The comparison `N → N'` of Tag 0B5R (3), as a morphism of graded `S`-modules.** -/
def twistedToShiftedGradedMap :
    twistedSectionsGradedModule 𝒮 (associatedModuleSheaf 𝒮 𝒨) ⟶
      shiftedSectionsGradedModule 𝒮 𝒨 where
  toLinearMap := twistedToShiftedLinearMap 𝒮 𝒨
  map_grade n x hx := by
    obtain ⟨s, rfl⟩ :=
      (DirectSum.mem_rangeGrading ℤ (fun k : ℤ =>
        twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) k) n x).mp hx
    exact (DirectSum.mem_rangeGrading ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n _).mpr
      ⟨_, twistedToShiftedSections_of 𝒮 𝒨 n s⟩

/-! ### The isomorphism -/

/-- **The comparison `N → N'` is bijective** once `Proj 𝒮` is covered by the standard opens of
the degree-one homogeneous elements. -/
theorem bijective_twistedToShiftedSections
    (hcover : ProjTwistDegreeOneCover.DegreeOneCover 𝒮) :
    Function.Bijective (twistedToShiftedSections 𝒮 𝒨) := by
  have hbij : ∀ n : ℤ, Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n) := fun n =>
    bijective_twistedToShiftedComponent 𝒮 𝒨 (d := 1) hcover (by simp)
  constructor
  · intro x y hxy
    refine DFinsupp.ext fun n => (hbij n).1 ?_
    have h := congrArg
      (DirectSum.component ℤ ℤ (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) n) hxy
    rwa [twistedToShiftedSections_component, twistedToShiftedSections_component] at h
  · intro y
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of n t =>
        obtain ⟨s, hs⟩ := (hbij n).2 t
        exact ⟨DirectSum.of _ n s, by rw [twistedToShiftedSections_of, hs]⟩
    | add y z hy hz =>
        obtain ⟨u, hu⟩ := hy
        obtain ⟨v, hv⟩ := hz
        exact ⟨u + v, by rw [map_add, hu, hv]⟩

/-- **The comparison `N → N'` is an isomorphism of graded `S`-modules** under the degree-one
covering hypothesis. -/
theorem isIso_twistedToShiftedGradedMap
    (hcover : ProjTwistDegreeOneCover.DegreeOneCover 𝒮) :
    IsIso (twistedToShiftedGradedMap 𝒮 𝒨) := by
  have hbij := bijective_twistedToShiftedSections 𝒮 𝒨 hcover
  have _ : Mono (twistedToShiftedGradedMap 𝒮 𝒨) :=
    GradedModuleCat.mono_of_injective hbij.1
  have _ : Epi (twistedToShiftedGradedMap 𝒮 𝒨) :=
    GradedModuleCat.epi_of_surjective hbij.2
  exact isIso_of_mono_of_epi _

/-- **The two graded `S`-modules of global sections agree**: if `Proj 𝒮` is covered by the
standard opens of the degree-one homogeneous elements then the comparison of Tag 0B5R (3) is an
isomorphism

`⨁_{n ∈ ℤ} Γ(Proj 𝒮, M̃(n)) ≅ ⨁_{n ∈ ℤ} Γ(Proj 𝒮, M(n)~)`

of graded `S`-modules. -/
def twistedShiftedGradedIso (hcover : ProjTwistDegreeOneCover.DegreeOneCover 𝒮) :
    twistedSectionsGradedModule 𝒮 (associatedModuleSheaf 𝒮 𝒨) ≅
      shiftedSectionsGradedModule 𝒮 𝒨 :=
  @asIso _ _ _ _ (twistedToShiftedGradedMap 𝒮 𝒨) (isIso_twistedToShiftedGradedMap 𝒮 𝒨 hcover)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end

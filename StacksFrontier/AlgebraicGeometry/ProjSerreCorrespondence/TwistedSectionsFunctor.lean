module

public import StacksFrontier.Algebra.DirectSum.GradedSubmodule
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Truncation
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Abelian

/-!
# Twisted global sections as a functor to graded modules

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring and `X = Proj 𝒮`. Tag 03GK attaches to a
sheaf of `𝒪_X`-modules `ℱ` the graded `S`-module `⨁_{n ∈ ℤ} Γ(X, ℱ(n))`, and that construction
is covariant in `ℱ`. This file bundles it as a functor

`ℱ ↦ ⨁_{n ∈ ℤ} Γ(X, ℱ(n))`

from sheaves of modules on `Proj 𝒮` to the category of graded `S`-modules, and does the same for
the nonnegative truncation `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))`, which is the quasi-inverse named in Tags
0BXD and 0BXF.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedSectionsGradedModule`: the graded
  `S`-module `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` as an object of the category of graded modules.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedSectionsGradedMap`: the morphism of
  graded modules induced by a morphism of sheaves.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedSectionsFunctor`: the two together,
  as a functor.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegTwistedSectionsSubmodule` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegTwistedSectionsGrade`: the degree-`≥ 0`
  truncation `⨁_{n ≥ 0} Γ(X, ℱ(n))` and its grading.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegTwistedSections`: that truncation as an
  object of the category of graded modules.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegTwistedSectionsFunctor`: the truncation
  as a functor, the quasi-inverse of Tags 0BXD and 0BXF before any coherence or finiteness
  restriction.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedSectionsFunctor_obj` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedSectionsFunctor_map`: the bundled
  functor is the construction just described.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegTwistedSectionsGrade_eq_bot`: the
  pieces of the truncation in negative degrees vanish.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegTwistedSectionsFunctor_obj` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegTwistedSectionsFunctor_map`: the same
  for the truncated functor.

## Implementation notes

The `S`-module structure on `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` is not an instance in the library but the
datum `Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule`, because it is
not canonical for instance search; `twistedGlobalSectionsModuleInstance` makes the canonical one
an instance for this file alone. The functor laws are `twistedSectionsMap_id` and
`twistedSectionsMap_comp`, which need no module structure at all.

`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat` grades by additive subgroups
while `twistedGlobalSectionsGrading` is a family of `ℤ`-submodules, so the gradings are passed
through `Submodule.toAddSubgroup`; `decompositionToAddSubgroup` transports a decomposition along
that passage, which is possible because the two families have the same members and hence the same
subtypes.

The truncation is the `S`-submodule
`Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule.truncation` at `k = 0`,
with its scalars restricted to `ℤ` so that `Submodule.inducedGrading` applies to it; the `S`-action
survives restriction of scalars as `Submodule.restrictScalars.origModule`. That submodule is
homogeneous — a component of a section with nothing in negative degrees is again such a section,
because a component in a negative degree is killed by the uniqueness of the decomposition — so
`Submodule.inducedGrading.decomposition` supplies the grading of the truncation, and its pieces in
negative degrees are `⊥` rather than being cut off by hand.

**No `stacks` attribute.** Tag 03GK is the graded module structure and already carries an attribute
at `AlgebraicGeometry.ProjectiveSpectrum.Proj.globalSectionsPairing`; the bundling recorded here is
one component of Tags 0BXD and 0BXF, not a covering set for either.

## References

* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistSheafOfModules twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (GradedModuleCat)
open Stacks.AlgebraicGeometry.ProjTwistedSections
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

/-! ### Transporting a decomposition to the underlying additive subgroups -/

/-- A decomposition of a module by a family of submodules is a decomposition by the family of
underlying additive subgroups: the two families have the same members, hence the same subtypes
and the same coercion into the module. -/
@[instance_reducible]
def decompositionToAddSubgroup {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] :
    DirectSum.Decomposition fun i => (ℳ i).toAddSubgroup where
  decompose' := DirectSum.Decomposition.decompose' (ℳ := ℳ)
  left_inv := DirectSum.Decomposition.left_inv (ℳ := ℳ)
  right_inv := DirectSum.Decomposition.right_inv (ℳ := ℳ)

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- The canonical `S`-module structure of Tag 03GK on `⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))`, separated
from its bundled datum. It is made an instance only locally in this file: the library keeps the
structure inside `TwistedGlobalSectionsModule` because it is not canonical for instance search. -/
@[instance_reducible]
def twistedGlobalSectionsModuleInstance : Module S (twistedGlobalSections 𝒮 F) :=
  (twistedGlobalSectionsModule 𝒮 F).moduleInst

attribute [local instance] twistedGlobalSectionsModuleInstance

/-! ### The graded module of twisted global sections -/

/-- **The graded `S`-module `⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))` of Tag 03GK, as an object of the
category of graded `S`-modules.** -/
def twistedSectionsGradedModule : GradedModuleCat.{u, u, w} 𝒮 where
  carrier := twistedGlobalSections 𝒮 F
  grade n := (twistedGlobalSectionsGrading 𝒮 F n).toAddSubgroup
  decomposition := decompositionToAddSubgroup (twistedGlobalSectionsGrading 𝒮 F)
  gradedSMul := ⟨(twistedGlobalSectionsModule 𝒮 F).gradedSMul.smul_mem⟩

variable {E F' G : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))}

/-- **A morphism of sheaves of modules on `Proj 𝒮`, read on twisted global sections**, as a
degree-preserving morphism of graded `S`-modules. -/
def twistedSectionsGradedMap (φ : E ⟶ F') :
    twistedSectionsGradedModule 𝒮 E ⟶ twistedSectionsGradedModule 𝒮 F' where
  toLinearMap := twistedSectionsLinearMap 𝒮
    (twistedGlobalSectionsModule 𝒮 E).smul_homogeneous
    (twistedGlobalSectionsModule 𝒮 F').smul_homogeneous φ
  map_grade := by
    intro n m hm
    obtain ⟨s, rfl⟩ :=
      (DirectSum.mem_rangeGrading ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 E j) n m).mp hm
    exact (DirectSum.mem_rangeGrading ℤ
      (fun j : ℤ => twistedSectionsComponent 𝒮 F' j) n _).mpr
      ⟨twistedSectionsMapComponent 𝒮 φ n s, twistedSectionsMap_of 𝒮 φ n s⟩

/-- **The twisted global sections of Tag 03GK, as a functor** from sheaves of modules on
`Proj 𝒮` to graded `S`-modules. -/
def twistedSectionsFunctor :
    SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) ⥤
      GradedModuleCat.{u, u, w} 𝒮 where
  obj F := twistedSectionsGradedModule 𝒮 F
  map φ := twistedSectionsGradedMap 𝒮 φ
  map_id F := GradedModuleCat.hom_ext <| LinearMap.ext fun x =>
    DFunLike.congr_fun (twistedSectionsMap_id 𝒮 (E := F)) x
  map_comp φ ψ := GradedModuleCat.hom_ext <| LinearMap.ext fun x =>
    DFunLike.congr_fun (twistedSectionsMap_comp 𝒮 φ ψ) x

/-- The functor sends a sheaf to its graded module of twisted global sections. -/
@[simp]
theorem twistedSectionsFunctor_obj :
    (twistedSectionsFunctor 𝒮).obj F = twistedSectionsGradedModule 𝒮 F := rfl

/-- The functor sends a morphism of sheaves to the induced morphism of graded modules. -/
@[simp]
theorem twistedSectionsFunctor_map (φ : E ⟶ F') :
    (twistedSectionsFunctor 𝒮).map φ = twistedSectionsGradedMap 𝒮 φ := rfl

/-! ### The nonnegative truncation -/

/-- **The degree-`≥ 0` truncation `⨁_{n ≥ 0} Γ(Proj 𝒮, ℱ(n))`**, as a `ℤ`-submodule of the
twisted global sections: the `S`-submodule of Tag 0B5R at `k = 0`, with its scalars restricted so
that the `ℤ`-grading of the ambient module can be induced on it. -/
def nonnegTwistedSectionsSubmodule : Submodule ℤ (twistedGlobalSections 𝒮 F) :=
  Submodule.restrictScalars ℤ
    (TwistedGlobalSectionsModule.truncation 𝒮 F (twistedGlobalSectionsModule 𝒮 F) 0)

/-- The `S`-module structure on the degree-`≥ 0` truncation, which survives the restriction of
scalars used to define it. -/
@[instance_reducible]
def nonnegTwistedSectionsModule : Module S (nonnegTwistedSectionsSubmodule 𝒮 F) :=
  inferInstanceAs (Module S
    (TwistedGlobalSectionsModule.truncation 𝒮 F (twistedGlobalSectionsModule 𝒮 F) 0))

attribute [local instance] nonnegTwistedSectionsModule

/-- A twisted global section lies in the degree-`≥ 0` truncation exactly when all its components
in negative degrees vanish. -/
theorem mem_nonnegTwistedSectionsSubmodule (x : twistedGlobalSections 𝒮 F) :
    x ∈ nonnegTwistedSectionsSubmodule 𝒮 F ↔
      ∀ n : ℤ, n < 0 →
        DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n x = 0 :=
  Iff.rfl

/-- A section of the degree-`≥ 0` truncation has no nonzero component in a negative degree. -/
private theorem nonneg_of_apply_ne_zero_of_mem_nonnegTwistedSectionsSubmodule
    {x : twistedGlobalSections 𝒮 F} (hx : x ∈ nonnegTwistedSectionsSubmodule 𝒮 F) {m : ℤ}
    (hm : (x : ⨁ j : ℤ, twistedSectionsComponent 𝒮 F j) m ≠ 0) : 0 ≤ m := by
  by_contra hlt
  refine hm ?_
  have h0 := (mem_nonnegTwistedSectionsSubmodule 𝒮 F x).mp hx m (not_le.mp hlt)
  rwa [← DirectSum.apply_eq_component] at h0

/-- Every homogeneous component of a section of the degree-`≥ 0` truncation lies in the
truncation: in a nonnegative degree because the whole homogeneous piece does, and in a negative
degree because the section is a sum of homogeneous sections of other degrees. -/
theorem decompose_mem_nonnegTwistedSectionsSubmodule (n : ℤ) (x : twistedGlobalSections 𝒮 F)
    (hx : x ∈ nonnegTwistedSectionsSubmodule 𝒮 F) :
    ((DirectSum.decompose (twistedGlobalSectionsGrading 𝒮 F) x n :
        twistedGlobalSectionsGrading 𝒮 F n) : twistedGlobalSections 𝒮 F) ∈
      nonnegTwistedSectionsSubmodule 𝒮 F := by
  classical
  by_cases hn : 0 ≤ n
  · exact coe_twistedGlobalSectionsGrading_subset_truncation 𝒮 F
      (twistedGlobalSectionsModule 𝒮 F).smul_homogeneous 0 n hn
      (DirectSum.decompose (twistedGlobalSectionsGrading 𝒮 F) x n).2
  · have hmem : x ∈ ⨆ (j : ℤ) (_ : j ≠ n), twistedGlobalSectionsGrading 𝒮 F j := by
      rw [← DirectSum.sum_support_of x]
      refine Submodule.sum_mem _ fun j hj => ?_
      refine Submodule.mem_iSup_of_mem j
        (Submodule.mem_iSup_of_mem (show j ≠ n by
          have := nonneg_of_apply_ne_zero_of_mem_nonnegTwistedSectionsSubmodule 𝒮 F hx
            (DFinsupp.mem_support_iff.mp hj)
          omega) ?_)
      exact (DirectSum.mem_rangeGrading ℤ
        (fun i : ℤ => twistedSectionsComponent 𝒮 F i) j _).mpr ⟨x j, rfl⟩
    rw [DirectSum.coe_decompose_apply_eq_zero_of_mem_iSup_ne
      (twistedGlobalSectionsGrading 𝒮 F) n x hmem]
    exact Submodule.zero_mem _

/-- **The grading of the degree-`≥ 0` truncation**: the degree-`n` piece is the degree-`n` piece
of `⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))`, read inside the truncation. -/
def nonnegTwistedSectionsGrade (n : ℤ) : AddSubgroup (nonnegTwistedSectionsSubmodule 𝒮 F) :=
  (Submodule.inducedGrading (twistedGlobalSectionsGrading 𝒮 F)
    (nonnegTwistedSectionsSubmodule 𝒮 F) n).toAddSubgroup

/-- A section of the truncation is homogeneous of degree `n` exactly when it is homogeneous of
degree `n` in the ambient twisted global sections. -/
theorem mem_nonnegTwistedSectionsGrade (n : ℤ) (x : nonnegTwistedSectionsSubmodule 𝒮 F) :
    x ∈ nonnegTwistedSectionsGrade 𝒮 F n ↔
      (x : twistedGlobalSections 𝒮 F) ∈ twistedGlobalSectionsGrading 𝒮 F n :=
  Iff.rfl

/-- **The pieces of the truncation in negative degrees vanish**: a section of a single twist of
negative degree has a nonzero component there unless it is zero. -/
theorem nonnegTwistedSectionsGrade_eq_bot (n : ℤ) (hn : n < 0) :
    nonnegTwistedSectionsGrade 𝒮 F n = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨s, hs⟩ := (DirectSum.mem_rangeGrading ℤ
    (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n (x : twistedGlobalSections 𝒮 F)).mp
    ((mem_nonnegTwistedSectionsGrade 𝒮 F n x).mp hx)
  have hzero := (mem_nonnegTwistedSectionsSubmodule 𝒮 F (x : twistedGlobalSections 𝒮 F)).mp x.2 n hn
  rw [hs, ← DirectSum.apply_eq_component, DirectSum.of_eq_same] at hzero
  refine AddSubgroup.mem_bot.mpr (Subtype.ext ?_)
  rw [hs, hzero, map_zero]
  rfl

/-- The degree-`≥ 0` truncation is graded by the pieces it inherits from the ambient twisted
global sections. -/
@[instance_reducible]
def nonnegTwistedSectionsDecomposition :
    DirectSum.Decomposition (nonnegTwistedSectionsGrade 𝒮 F) :=
  letI := Submodule.inducedGrading.decomposition (twistedGlobalSectionsGrading 𝒮 F)
    (nonnegTwistedSectionsSubmodule 𝒮 F) (decompose_mem_nonnegTwistedSectionsSubmodule 𝒮 F)
  decompositionToAddSubgroup
    (Submodule.inducedGrading (twistedGlobalSectionsGrading 𝒮 F)
      (nonnegTwistedSectionsSubmodule 𝒮 F))

/-- The homogeneous pieces of the truncation are permuted by homogeneous scalars exactly as the
pieces of the ambient twisted global sections are. -/
theorem nonnegTwistedSectionsGradedSMul :
    SetLike.GradedSMul 𝒮 (nonnegTwistedSectionsGrade 𝒮 F) := by
  constructor
  intro _ _ _ _ ha hx
  exact (twistedGlobalSectionsModule 𝒮 F).gradedSMul.smul_mem ha hx

/-- **The graded `S`-module `⨁_{n ≥ 0} Γ(Proj 𝒮, ℱ(n))`**, the object the quasi-inverse of Tags
0BXD and 0BXF attaches to a sheaf of modules on `Proj 𝒮`. -/
def nonnegTwistedSections : GradedModuleCat.{u, u, w} 𝒮 where
  carrier := nonnegTwistedSectionsSubmodule 𝒮 F
  grade := nonnegTwistedSectionsGrade 𝒮 F
  decomposition := nonnegTwistedSectionsDecomposition 𝒮 F
  gradedSMul := nonnegTwistedSectionsGradedSMul 𝒮 F

/-- A morphism of sheaves carries the degree-`≥ 0` truncation into the degree-`≥ 0` truncation:
it preserves degrees, so it cannot create a component in a negative degree. -/
theorem map_mem_nonnegTwistedSectionsSubmodule (φ : E ⟶ F')
    (x : twistedGlobalSections 𝒮 E) (hx : x ∈ nonnegTwistedSectionsSubmodule 𝒮 E) :
    twistedSectionsMap 𝒮 φ x ∈ nonnegTwistedSectionsSubmodule 𝒮 F' := by
  classical
  refine (mem_nonnegTwistedSectionsSubmodule 𝒮 F' _).mpr fun n hn => ?_
  rw [← DirectSum.sum_support_of x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm0 := nonneg_of_apply_ne_zero_of_mem_nonnegTwistedSectionsSubmodule 𝒮 E hx
    (DFinsupp.mem_support_iff.mp hm)
  rw [twistedSectionsMap_of, ← DirectSum.apply_eq_component,
    DirectSum.of_eq_of_ne _ _ _ (by omega : n ≠ m)]

/-- **A morphism of sheaves on the degree-`≥ 0` truncations**, as an `S`-linear map. -/
def nonnegTwistedSectionsLinearMap (φ : E ⟶ F') :
    nonnegTwistedSectionsSubmodule 𝒮 E →ₗ[S] nonnegTwistedSectionsSubmodule 𝒮 F' where
  toFun x := ⟨twistedSectionsMap 𝒮 φ (x : twistedGlobalSections 𝒮 E),
    map_mem_nonnegTwistedSectionsSubmodule 𝒮 φ _ x.2⟩
  map_add' _ _ := Subtype.ext (map_add (twistedSectionsMap 𝒮 φ) _ _)
  map_smul' a _ := Subtype.ext (twistedSectionsMap_smul 𝒮
    (twistedGlobalSectionsModule 𝒮 E).smul_homogeneous
    (twistedGlobalSectionsModule 𝒮 F').smul_homogeneous φ a _)

/-- The induced map on the degree-`≥ 0` truncations preserves every degree: a homogeneous section
of degree `n` goes to the twist of that section, in the same degree. -/
theorem nonnegTwistedSectionsLinearMap_mem_grade (φ : E ⟶ F') (n : ℤ)
    (x : nonnegTwistedSectionsSubmodule 𝒮 E) (hx : x ∈ nonnegTwistedSectionsGrade 𝒮 E n) :
    nonnegTwistedSectionsLinearMap 𝒮 φ x ∈ nonnegTwistedSectionsGrade 𝒮 F' n := by
  obtain ⟨s, hs⟩ := (DirectSum.mem_rangeGrading ℤ
    (fun j : ℤ => twistedSectionsComponent 𝒮 E j) n (x : twistedGlobalSections 𝒮 E)).mp
    ((mem_nonnegTwistedSectionsGrade 𝒮 E n x).mp hx)
  refine (mem_nonnegTwistedSectionsGrade 𝒮 F' n _).mpr ?_
  exact (DirectSum.mem_rangeGrading ℤ
    (fun j : ℤ => twistedSectionsComponent 𝒮 F' j) n _).mpr
    ⟨twistedSectionsMapComponent 𝒮 φ n s, by
      change twistedSectionsMap 𝒮 φ (x : twistedGlobalSections 𝒮 E) = _
      rw [hs, twistedSectionsMap_of]⟩

/-- The identity acts as the identity on the degree-`≥ 0` truncation. -/
theorem nonnegTwistedSectionsLinearMap_id (x : nonnegTwistedSectionsSubmodule 𝒮 F) :
    nonnegTwistedSectionsLinearMap 𝒮 (𝟙 F) x = x :=
  Subtype.ext (DFunLike.congr_fun (twistedSectionsMap_id 𝒮 (E := F))
    (x : twistedGlobalSections 𝒮 F))

/-- A composite acts as the composite on the degree-`≥ 0` truncation. -/
theorem nonnegTwistedSectionsLinearMap_comp (φ : E ⟶ F') (ψ : F' ⟶ G)
    (x : nonnegTwistedSectionsSubmodule 𝒮 E) :
    nonnegTwistedSectionsLinearMap 𝒮 (φ ≫ ψ) x =
      nonnegTwistedSectionsLinearMap 𝒮 ψ (nonnegTwistedSectionsLinearMap 𝒮 φ x) :=
  Subtype.ext (DFunLike.congr_fun (twistedSectionsMap_comp 𝒮 φ ψ)
    (x : twistedGlobalSections 𝒮 E))

/-- **A morphism of sheaves on the degree-`≥ 0` truncations**, as a degree-preserving morphism of
graded `S`-modules. -/
def nonnegTwistedSectionsMap (φ : E ⟶ F') :
    nonnegTwistedSections 𝒮 E ⟶ nonnegTwistedSections 𝒮 F' where
  toLinearMap := nonnegTwistedSectionsLinearMap 𝒮 φ
  map_grade n x hx := nonnegTwistedSectionsLinearMap_mem_grade 𝒮 φ n x hx

/-- **The quasi-inverse of Tags 0BXD and 0BXF, as a functor** on all sheaves of modules on
`Proj 𝒮`: a sheaf `ℱ` goes to the graded `S`-module `⨁_{n ≥ 0} Γ(Proj 𝒮, ℱ(n))`. Neither the
restriction to coherent sheaves nor the finite generation of the result is recorded here. -/
def nonnegTwistedSectionsFunctor :
    SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) ⥤
      GradedModuleCat.{u, u, w} 𝒮 where
  obj F := nonnegTwistedSections 𝒮 F
  map φ := nonnegTwistedSectionsMap 𝒮 φ
  map_id F := GradedModuleCat.hom_ext <|
    LinearMap.ext (nonnegTwistedSectionsLinearMap_id 𝒮 F)
  map_comp φ ψ := GradedModuleCat.hom_ext <|
    LinearMap.ext (nonnegTwistedSectionsLinearMap_comp 𝒮 φ ψ)

/-- The truncated functor sends a sheaf to `⨁_{n ≥ 0} Γ(Proj 𝒮, ℱ(n))`. -/
@[simp]
theorem nonnegTwistedSectionsFunctor_obj :
    (nonnegTwistedSectionsFunctor 𝒮).obj F = nonnegTwistedSections 𝒮 F := rfl

/-- The truncated functor sends a morphism of sheaves to the induced morphism of graded
modules. -/
@[simp]
theorem nonnegTwistedSectionsFunctor_map (φ : E ⟶ F') :
    (nonnegTwistedSectionsFunctor 𝒮).map φ = nonnegTwistedSectionsMap 𝒮 φ := rfl

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end

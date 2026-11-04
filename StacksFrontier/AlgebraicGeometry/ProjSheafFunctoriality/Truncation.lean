module

public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.EventuallyBijective
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.SheafMapIsIso
public import StacksFrontier.RingTheory.GradedAlgebra.ModuleTruncation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Truncating a graded module does not change its associated sheaf

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring, `X = Proj 𝒮`, and let `M` be a
`ℤ`-graded `S`-module. For an integer `k` the truncation `M_{≥ k} = ⨁_{n ≥ k} M_n` is again a
graded `S`-module, and the inclusion `M_{≥ k} ⟶ M` induces an **isomorphism** of associated
sheaves: the two modules agree in every degree `≥ k`, and the associated sheaf only sees the
large degrees.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.gradedTruncation`: the truncation
  `M_{≥ k}` as an object of `GradedModuleCat 𝒮`.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.gradedTruncationι`: the inclusion
  `M_{≥ k} ⟶ M`.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafTruncationAboveIso`
  and `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafTruncationIso`:
  **the isomorphism `(M_{≥ k})~ ≅ M̃`**, for a grading given as a bare family and for one given
  by an object of `GradedModuleCat`.

## Main results

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.injective_gradedTruncationι`: the inclusion
  is injective on carriers.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.grade_gradedTruncation_eq_bot`: the
  truncation is trivial in every degree `< k`.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.isIso_map_gradedTruncationι`: the induced
  morphism of associated sheaves is an isomorphism.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.moduleFinite_gradedTruncation`: over a
  Noetherian ring the truncation of a finite module is finite.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.truncationAboveMap` and
  `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.truncationAboveMap_mem_grading`: the
  truncation is functorial in degree-preserving maps.

## Implementation notes

The underlying submodule, its grading, its decomposition and the graded action are all
`Stacks.GradedModule.truncationAbove` and its companions in
`StacksFrontier/RingTheory/GradedAlgebra/ModuleTruncation.lean`; what this file adds is the
packaging as an object of `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat`,
which nothing else in the library does, and the consequence for the associated sheaf.

The isomorphism is `Stacks.AlgebraicGeometry.ProjStalkGlobalSections`
`.isIso_associatedModuleSheafMap_of_eventually_bijective` at `N₀ = k`, whose two hypotheses are
exactly `Stacks.GradedModule.eq_zero_of_truncationAbove_subtype_eq_zero` (injectivity of an
inclusion) and `Stacks.GradedModule.exists_mem_truncationAboveGrading` (a homogeneous element of
a kept degree already lies in the truncation). That theorem forces the module to live in the
ring's universe, so the isomorphism is stated at `GradedModuleCat.{u, u, w}` while the
truncation itself is available in any universe.

Both forms are kept because the two consumers differ. A tag which has its graded module as an
object of `GradedModuleCat` wants the functor form; the twisted-section modules
`⨁_{n ∈ ℤ} Γ(X, ℱ(n))` of Tags 03GK and 0AG5 carry their grading as a bare family of
`Submodule ℤ`s instead, and for those the bare form applies with no transport between the two
spellings of a homogeneous piece.

This file is about `M ↦ M̃` alone and mentions no Serre class, so it is shared by every tag which
needs to replace a graded module by a truncation without changing the sheaf — the twisted-section
quasi-inverses of Tags 0BXD and 0BXF among them.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.GradedModule
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u v w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### For a bare grading of a module -/

section Bare

variable {M : Type u} [AddCommGroup M] [Module S M]
  {τ : Type*} [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The inclusion `M_{≥ k} ⟶ M` induces an isomorphism of associated sheaves**, for a grading
given as a bare family rather than through `GradedModuleCat`. The two hypotheses of
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections`
`.isIso_associatedModuleSheafMap_of_eventually_bijective` at `N₀ = k` are that an inclusion is
injective and that a homogeneous element of a kept degree already lies in the truncation. -/
@[ega "II 3.4.2" "special case"]
public theorem isIso_associatedModuleSheafMap_truncationAbove (k : ℤ) :
    IsIso (associatedModuleSheafMap 𝒮 (truncationAboveGrading 𝒮 𝒨 k) 𝒨
      (truncationAbove 𝒮 𝒨 k).subtype (truncationAbove_subtype_mem 𝒮 𝒨 k)) :=
  ProjStalkGlobalSections.isIso_associatedModuleSheafMap_of_eventually_bijective 𝒮
    (truncationAboveGrading 𝒮 𝒨 k) 𝒨 (truncationAbove 𝒮 𝒨 k).subtype
    (truncationAbove_subtype_mem 𝒮 𝒨 k) (N₀ := k)
    (fun _ _ _ _ h => eq_zero_of_truncationAbove_subtype_eq_zero 𝒮 𝒨 k h)
    (fun _ hj _ hm => exists_mem_truncationAboveGrading 𝒮 𝒨 k hj hm)

/-! #### Functoriality of the truncation -/

section Map

variable {N : Type u} [AddCommGroup N] [Module S N]
  {υ : Type*} [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

/-- **A degree-preserving map carries a truncation into the truncation at the same cut.** Its
homogeneous components are the images of the components, so a vanishing component below the cut
stays vanishing. -/
public theorem map_mem_truncationAbove (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (k : ℤ) {x : M}
    (hx : x ∈ truncationAbove 𝒮 𝒨 k) : φ x ∈ truncationAbove 𝒮 𝒩 k := by
  intro i hi
  rw [decompose_apply_eq 𝒨 𝒩 φ hφ x i,
    (mem_truncationAbove_iff 𝒮 𝒨 k x).mp hx i hi, map_zero]

/-- **The map induced on the truncations by a degree-preserving map.** -/
public def truncationAboveMap (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (k : ℤ) :
    ↥(truncationAbove 𝒮 𝒨 k) →ₗ[S] ↥(truncationAbove 𝒮 𝒩 k) :=
  LinearMap.codRestrict (truncationAbove 𝒮 𝒩 k)
    (φ.comp (truncationAbove 𝒮 𝒨 k).subtype)
    (fun x => map_mem_truncationAbove 𝒮 𝒨 𝒩 φ hφ k x.2)

/-- The map induced on truncations is `φ` on underlying elements. -/
@[simp]
public theorem coe_truncationAboveMap (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (k : ℤ) (x : ↥(truncationAbove 𝒮 𝒨 k)) :
    ((truncationAboveMap 𝒮 𝒨 𝒩 φ hφ k x : ↥(truncationAbove 𝒮 𝒩 k)) : N) = φ (x : M) := rfl

/-- The induced map on truncations is degree-preserving for the inherited gradings. -/
public theorem truncationAboveMap_mem_grading (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (k : ℤ) (i : ℤ)
    (x : ↥(truncationAbove 𝒮 𝒨 k)) (hx : x ∈ truncationAboveGrading 𝒮 𝒨 k i) :
    truncationAboveMap 𝒮 𝒨 𝒩 φ hφ k x ∈ truncationAboveGrading 𝒮 𝒩 k i :=
  hφ i (x : M) hx

end Map

/-- **The isomorphism `(M_{≥ k})~ ≅ M̃`** for a bare grading. -/
public def associatedModuleSheafTruncationAboveIso (k : ℤ) :
    ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 (truncationAboveGrading 𝒮 𝒨 k) ≅
      ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨 :=
  haveI := isIso_associatedModuleSheafMap_truncationAbove 𝒮 𝒨 k
  asIso (associatedModuleSheafMap 𝒮 (truncationAboveGrading 𝒮 𝒨 k) 𝒨
    (truncationAbove 𝒮 𝒨 k).subtype (truncationAbove_subtype_mem 𝒮 𝒨 k))

/-- The forward map of `associatedModuleSheafTruncationAboveIso` is the morphism of associated
sheaves induced by the inclusion `M_{≥ k} ⟶ M`. -/
@[simp]
public theorem associatedModuleSheafTruncationAboveIso_hom (k : ℤ) :
    (associatedModuleSheafTruncationAboveIso 𝒮 𝒨 k).hom =
      associatedModuleSheafMap 𝒮 (truncationAboveGrading 𝒮 𝒨 k) 𝒨
        (truncationAbove 𝒮 𝒨 k).subtype (truncationAbove_subtype_mem 𝒮 𝒨 k) := rfl

end Bare

/-! ### For an object of `GradedModuleCat` -/

/-- **The truncation `M_{≥ k} = ⨁_{n ≥ k} M_n` of a graded module**, as an object of the
category of graded modules. -/
@[ega "II 8.2.1" "special case"]
public def gradedTruncation (X : GradedModuleCat.{u, v, w} 𝒮) (k : ℤ) :
    GradedModuleCat.{u, v, w} 𝒮 where
  carrier := ↥(truncationAbove 𝒮 X.grade k)
  grade := truncationAboveGrading 𝒮 X.grade k

/-- The grading of `gradedTruncation 𝒮 X k` is the grading inherited from `X`. -/
@[simp]
public theorem grade_gradedTruncation (X : GradedModuleCat.{u, v, w} 𝒮) (k : ℤ) :
    (gradedTruncation 𝒮 X k).grade = truncationAboveGrading 𝒮 X.grade k := rfl

/-- The truncation is trivial in every degree below the cut. -/
public theorem grade_gradedTruncation_eq_bot (X : GradedModuleCat.{u, v, w} 𝒮) {k i : ℤ}
    (hi : i < k) : (gradedTruncation 𝒮 X k).grade i = ⊥ :=
  truncationAboveGrading_eq_bot 𝒮 X.grade k hi

/-- **The inclusion `M_{≥ k} ⟶ M`.** -/
public def gradedTruncationι (X : GradedModuleCat.{u, v, w} 𝒮) (k : ℤ) :
    gradedTruncation 𝒮 X k ⟶ X where
  toLinearMap := (truncationAbove 𝒮 X.grade k).subtype
  map_grade i m hm := truncationAbove_subtype_mem 𝒮 X.grade k i m hm

/-- The underlying linear map of `gradedTruncationι` is the inclusion of the submodule. -/
@[simp]
public theorem gradedTruncationι_toLinearMap (X : GradedModuleCat.{u, v, w} 𝒮) (k : ℤ) :
    (gradedTruncationι 𝒮 X k).toLinearMap = (truncationAbove 𝒮 X.grade k).subtype := rfl

/-- The inclusion `M_{≥ k} ⟶ M` is injective on underlying modules. -/
public theorem injective_gradedTruncationι (X : GradedModuleCat.{u, v, w} 𝒮) (k : ℤ) :
    Function.Injective (gradedTruncationι 𝒮 X k).toLinearMap :=
  Subtype.coe_injective

/-- A homogeneous element of a kept degree lies in the image of the inclusion. -/
public theorem exists_gradedTruncationι_eq (X : GradedModuleCat.{u, v, w} 𝒮) {k j : ℤ}
    (hj : k ≤ j) {m : X.carrier} (hm : m ∈ X.grade j) :
    ∃ x : (gradedTruncation 𝒮 X k).carrier, x ∈ (gradedTruncation 𝒮 X k).grade j ∧
      (gradedTruncationι 𝒮 X k).toLinearMap x = m :=
  exists_mem_truncationAboveGrading 𝒮 X.grade k hj hm

/-- **The inclusion of a truncation induces an isomorphism of associated sheaves.** -/
public theorem isIso_map_gradedTruncationι (X : GradedModuleCat.{u, u, w} 𝒮) (k : ℤ) :
    IsIso ((associatedModuleSheafFunctor.{u, u, w} 𝒮).map (gradedTruncationι 𝒮 X k)) :=
  isIso_associatedModuleSheafMap_truncationAbove 𝒮 X.grade k

/-- **The isomorphism `(M_{≥ k})~ ≅ M̃`.** -/
public def associatedModuleSheafTruncationIso (X : GradedModuleCat.{u, u, w} 𝒮) (k : ℤ) :
    (associatedModuleSheafFunctor.{u, u, w} 𝒮).obj (gradedTruncation 𝒮 X k) ≅
      (associatedModuleSheafFunctor.{u, u, w} 𝒮).obj X :=
  haveI := isIso_map_gradedTruncationι 𝒮 X k
  asIso ((associatedModuleSheafFunctor.{u, u, w} 𝒮).map (gradedTruncationι 𝒮 X k))

/-- The forward map of `associatedModuleSheafTruncationIso` is the image of `gradedTruncationι`
under `associatedModuleSheafFunctor`. -/
@[simp]
public theorem associatedModuleSheafTruncationIso_hom (X : GradedModuleCat.{u, u, w} 𝒮)
    (k : ℤ) :
    (associatedModuleSheafTruncationIso 𝒮 X k).hom =
      (associatedModuleSheafFunctor.{u, u, w} 𝒮).map (gradedTruncationι 𝒮 X k) := rfl

/-- **Over a Noetherian ring the truncation of a finite graded module is finite**, being a
submodule of it. -/
public theorem moduleFinite_gradedTruncation [IsNoetherianRing S]
    (X : GradedModuleCat.{u, v, w} 𝒮) (hX : Module.Finite S X.carrier) (k : ℤ) :
    Module.Finite S (gradedTruncation 𝒮 X k).carrier := by
  have := hX
  have : IsNoetherian S X.carrier := isNoetherian_of_isNoetherianRing_of_finite S X.carrier
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (truncationAbove 𝒮 X.grade k))

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

end

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Boundedness
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnconditionalBoundedness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# A derived limit of quasi-coherent sheaves has bounded coherator

Let `X` be a quasi-compact and quasi-separated scheme, let `(𝓕ₙ)` be an inverse system of
quasi-coherent `𝒪_X`-modules and let `K = R lim 𝓕ₙ` in `D(𝒪_X)`. The hypercohomology of `K` over
an affine open is concentrated in degrees `0` and `1`, so the boundedness property of the
coherator ([Stacks, Tag 0CSA]) puts `DQ_X(K)` in `D^b_QCoh(𝒪_X)`.

[Stacks, Tag 0CSA] is used in the form
`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs`, which holds for a
quasi-compact quasi-separated scheme and an arbitrary coherator with no further input, so the
conclusion here has no hypothesis beyond those of the source.

## Main results

* `Stacks.Duality.Coherator.affineAmplitudeIn_of_isDerivedLimit_single`: such a `K` has affine
  amplitude in `[0, 1]`, which is the hypothesis of [Stacks, Tag 0CSA].
* `Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_isDerivedLimit_single`:
  **[Stacks, Tag 0CSB]** — `DQ_X(K)` lies in `D^b_QCoh(𝒪_X)`, for every coherator `DQ_X` of `X`.
* `Stacks.Duality.Coherator.exists_coherator_isGE_isLE_obj_of_isDerivedLimit_single`: the same
  with the coherator produced by [Stacks, Tag 0CR0] rather than given, so that nothing beyond
  `X` being quasi-compact and quasi-separated and the `𝓕ₙ` being quasi-coherent is assumed.

## Implementation notes

Everything here is at the locally small model of `D(𝒪_X)`, which is the model in which
[Stacks, Tag 0CSA] and the vocabulary of [Stacks, Tag 0CR2] are stated; `RΓ(U, -)` is
accordingly `Stacks.Duality.Coherator.derivedSectionsLocallySmall`, valued in
`Γ(X, U)`-modules. The commutation of `RΓ(U, -)` with derived limits is [Stacks, Tag 08U1] in
the model-agnostic form `Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`, applied to
`Stacks.Cohomology.sectionsFunctor`, which preserves countable products because it is an
evaluation of sheaves of modules.

The affine-open vanishing used is the module-valued reading of [Stacks, Tag 01XB], obtained from
the abelian-group-valued one by
`Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup`.

## References

* [Stacks Project, Tag 0CSB](https://stacks.math.columbia.edu/tag/0CSB)
* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Duality.Coherator

/-- **Serre vanishing on an affine open, read in `Γ(X, U)`-modules** ([Stacks, Tag 01XB]). The
positive right derived functors of sections over an affine open vanish on a quasi-coherent
module. -/
private lemma isZero_rightDerived_sectionsFunctor_of_isAffineOpen (X : Scheme.{u}) (M : X.Modules)
    [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X U).rightDerived p).obj M) :=
  Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
    X.ringCatSheaf U p M
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X M U hU p hp)

/-- Sections over an open preserve countable products, being an evaluation of sheaves of
modules. -/
private lemma preservesProducts_sectionsFunctor (X : Scheme.{u}) (U : X.Opens) :
    PreservesLimitsOfShape (Discrete ℕ) (Stacks.Cohomology.sectionsFunctor X U) := by
  dsimp only [Stacks.Cohomology.sectionsFunctor]
  exact SheafOfModules.evaluationPreservesLimitsOfShape _ _ _

/-- The hypercohomology over an open of a sheaf placed in degree zero with no higher cohomology
on that open is concentrated in degree zero: above degree zero by the vanishing, below it by left
t-exactness of the derived sections functor. -/
private lemma isZero_homology_derivedSectionsLocallySmall_single (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules)
    (hM : ∀ p : ℕ, 0 < p →
      IsZero (((Stacks.Cohomology.sectionsFunctor X U).rightDerived p).obj M))
    (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) j).obj
      ((derivedSectionsLocallySmall X U).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj M))) := by
  rcases lt_trichotomy j 0 with h | h | h
  · exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (Stacks.Cohomology.sectionsFunctor X U) _ 0 j h
  · exact absurd h hj
  · exact Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero
      (Stacks.Cohomology.sectionsFunctor X U) (derivedSectionsLocallySmall X U)
      (derivedSectionsLocallySmallUnit X U)
      Stacks.Cohomology.Localization.enoughKInjectives M hM 0 j h

/-- **[Stacks, Tag 08U1] for sections over an open of a scheme.** `RΓ(U, -)` carries a derived
limit to a derived limit: `RΓ(U, R lim Kₙ) = R lim RΓ(U, Kₙ)`. -/
private lemma isDerivedLimit_map_derivedSectionsLocallySmall (X : Scheme.{u}) (U : X.Opens)
    (K : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory X.Modules) (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct fun n : ℕ ↦ (derivedSectionsLocallySmall X U).obj (K.obj ⟨n⟩),
      letI := h
      IsDerivedLimit (K ⋙ derivedSectionsLocallySmall X U)
        ((derivedSectionsLocallySmall X U).obj L) := by
  have := preservesProducts_sectionsFunctor X U
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨h, δ', hT'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (Stacks.Cohomology.sectionsFunctor X U) (derivedSectionsLocallySmall X U)
    (derivedSectionsLocallySmallUnit X U) K L p ⟨δ, hT⟩
  exact ⟨h, _, δ', hT'⟩

/-- **The hypothesis of [Stacks, Tag 0CSA] at a derived limit of quasi-coherent sheaves.** Let
`(𝓕ₙ)` be an inverse system of quasi-coherent `𝒪_X`-modules and let `L` be a derived limit in
`D(𝒪_X)` of the system `(𝓕ₙ)` placed in degree zero. Then `H^i(U, L) = 0` for every affine open
`U ⊆ X` and every `i` outside `[0, 1]`.

Sections over `U` commute with derived limits, so `RΓ(U, L) = R lim RΓ(U, 𝓕ₙ)`, and each
`RΓ(U, 𝓕ₙ)` is concentrated in degree zero because `𝓕ₙ` is quasi-coherent and `U` is affine. In
the Milnor short exact sequence `0 → lim¹ H^{i-1}(U, 𝓕ₙ) → H^i(U, L) → lim H^i(U, 𝓕ₙ) → 0` both
outer terms then vanish as soon as `i ≠ 0` and `i ≠ 1`. -/
theorem affineAmplitudeIn_of_isDerivedLimit_single (X : Scheme.{u}) (𝓕 : ℕᵒᵖ ⥤ X.Modules)
    (hqc : ∀ n : ℕ, (𝓕.obj ⟨n⟩).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦ (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩]
    (L : DerivedCategory X.Modules)
    (hL : IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0) L) :
    AffineAmplitudeIn X 0 1 L := by
  intro U i hi
  have hi0 : i ≠ 0 := by rcases hi with h | h <;> omega
  have hi1 : i ≠ 1 := by rcases hi with h | h <;> omega
  obtain ⟨hprodΓ, hRL⟩ :=
    isDerivedLimit_map_derivedSectionsLocallySmall X U.1
      (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0) L hL
  let := hprodΓ
  have hterm : ∀ (n : ℕ) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) j).obj
        (((𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0) ⋙
          derivedSectionsLocallySmall X U.1).obj ⟨n⟩)) := by
    intro n j hj
    have := hqc n
    exact isZero_homology_derivedSectionsLocallySmall_single X U.1 (𝓕.obj ⟨n⟩)
      (fun q hq ↦ isZero_rightDerived_sectionsFunctor_of_isAffineOpen X (𝓕.obj ⟨n⟩) U.1 U.2 q hq)
      j hj
  obtain ⟨a, b, -, hdeg⟩ :=
    DerivedCategory.isDerivedLimit_homology_shortExact
      ((𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0) ⋙ derivedSectionsLocallySmall X U.1)
      ((derivedSectionsLocallySmall X U.1).obj L) hRL
  obtain ⟨e, ι, q, w, -, -, -, hShortExact⟩ := hdeg i
  refine isZero_X₂_of_shortExact hShortExact ?_ ?_
  · exact isZero_cokernel_of_isZero
      (isZero_limit_of_forall_isZero _ fun n ↦ hterm n.as (i - 1) (by omega)) _
  · exact isZero_limit_of_forall_isZero _ fun n ↦ hterm n.unop i hi0

/-- **[Stacks, Tag 0CSB].** Let `X` be a quasi-compact and quasi-separated scheme, let `DQ` be a
coherator of `X` and let `L` be a derived limit in `D(𝒪_X)` of an inverse system `(𝓕ₙ)` of
quasi-coherent `𝒪_X`-modules placed in degree zero. Then `DQ L` lies in `D^b_QCoh(𝒪_X)`: its
cohomology sheaves vanish below degree `0` and above degree `1 + N` for some `N` depending only
on `X` and `DQ`.

The affine amplitude of `L` is `[0, 1]`, so this is the boundedness property of the coherator,
[Stacks, Tag 0CSA] in the form
`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs`, applied with `a = 0` and
`b = 1`. -/
@[stacks 0CSB "the conclusion that the R lim in D_QCoh(𝒪_X), i.e. DQ_X(R lim 𝓕ₙ), lies in \
D^b_QCoh(𝒪_X), for every coherator DQ of X"]
theorem exists_isGE_isLE_coherator_obj_of_isDerivedLimit_single (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
    (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]
    (𝓕 : ℕᵒᵖ ⥤ X.Modules) (hqc : ∀ n : ℕ, (𝓕.obj ⟨n⟩).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦ (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩]
    (L : DerivedCategory X.Modules)
    (hL : IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0) L) :
    ∃ N : ℤ, ((quasiCoherentι X).obj (DQ.obj L)).IsGE 0 ∧
      ((quasiCoherentι X).obj (DQ.obj L)).IsLE (1 + N) :=
  have ⟨N, hN⟩ := exists_isGE_isLE_coherator_obj_of_qcqs X DQ adj
  ⟨N, hN 0 1 L (affineAmplitudeIn_of_isDerivedLimit_single X 𝓕 hqc L hL)⟩

/-- **[Stacks, Tag 0CSB] with the coherator produced rather than given.** Let `X` be a
quasi-compact and quasi-separated scheme and let `L` be a derived limit in `D(𝒪_X)` of an inverse
system `(𝓕ₙ)` of quasi-coherent `𝒪_X`-modules placed in degree zero. Then there are a coherator
`DQ` of `X` — an exact right adjoint of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` — and an integer
`N` with `DQ L` in `D^b_QCoh(𝒪_X)`, its cohomology sheaves vanishing below degree `0` and above
degree `1 + N`.

The coherator is the one of [Stacks, Tag 0CR0],
`Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_quasiCoherentι`, and the bound is
`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_isDerivedLimit_single`, which holds
for every coherator. -/
theorem exists_coherator_isGE_isLE_obj_of_isDerivedLimit_single (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (𝓕 : ℕᵒᵖ ⥤ X.Modules) (hqc : ∀ n : ℕ, (𝓕.obj ⟨n⟩).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦ (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩]
    (L : DerivedCategory X.Modules)
    (hL : IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0) L) :
    ∃ (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
      (adj : quasiCoherentι X ⊣ DQ) (_ : DQ.CommShift ℤ) (_ : adj.IsTriangulated) (N : ℤ),
      ((quasiCoherentι X).obj (DQ.obj L)).IsGE 0 ∧
        ((quasiCoherentι X).obj (DQ.obj L)).IsLE (1 + N) := by
  obtain ⟨DQ, adj, hcs, htri⟩ := exists_isTriangulated_rightAdjoint_quasiCoherentι X
  exact ⟨DQ, adj, hcs, htri,
    exists_isGE_isLE_coherator_obj_of_isDerivedLimit_single X DQ adj 𝓕 hqc L hL⟩

end Stacks.Duality.Coherator

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.EventuallyBijectiveStalk
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-!
# The associated-sheaf morphism is an isomorphism when eventually bijective

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring and let `φ : M →ₗ[S] N` be a
degree-preserving linear map of `ℤ`-graded `S`-modules, with `M` and `N` in the *same* universe
as `S` (so that `associatedModuleSheaf 𝒮 𝒨 : SheafOfModules.{u} O`, matching the forced single
universe of `AlgebraicGeometry.SheafOfModules.stalkMap`). If `φ` restricts to a bijection on
homogeneous components in every sufficiently large degree, then
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ : M̃ ⟶ Ñ`
is an isomorphism of the associated sheaves. This follows from the bijectivity of
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.bijOn_degreeZeroModuleAt_of_eventually_bijective`
on stalks, via `AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`.

## Main results

* `stalkMap_associatedModuleSheafMap_eval`: under the identification of the stalk
  `associatedModuleSheafStalk` with `AlgebraicGeometry.SheafOfModules.stalkObj`, the stalk map of
  `associatedModuleSheafMap` agrees with `LocalizedModule.map` through the evaluation maps into the
  ambient fibers.
* `isIso_associatedModuleSheafMap_of_eventually_bijective`: if `φ` is bijective on homogeneous
  components in all sufficiently large degrees, then `associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ` is an
  isomorphism.

## Implementation notes

The identification of `AlgebraicGeometry.SheafOfModules.stalkObj O x (associatedModuleSheaf 𝒮 𝒨)`
with `associatedModuleSheafStalk 𝒮 𝒨 x` is definitional: both unfold to
`colimit ((OpenNhds.inclusion x).op ⋙ (associatedModuleSheaf 𝒮 𝒨).val.presheaf)`, the former
through `TopCat.Presheaf.stalk`, `TopCat.Presheaf.stalkFunctor` and the defining equation
`colim.obj F = colimit F` of the colimit functor, the latter by its own definition. Likewise
`TopCat.Presheaf.germ` and `associatedModuleSheafGerm` both unfold to
`colimit.ι (...) (op ⟨U, hx⟩)` applied to the section, so they agree on the nose. The general
stalk-map formula `AlgebraicGeometry.SheafOfModules.stalkMap_germ` thus composes directly with the
germ lemmas for `associatedModuleSheafGerm`, without any intervening `eqToHom` or transport.

The modules `M` and `N` lie in the universe of `S`, so that `SheafOfModules.{max u v}` becomes
`SheafOfModules.{u}`, the only universe at which `AlgebraicGeometry.SheafOfModules.stalkMap` is
defined.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S M N : Type u} {σ : Type w}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {τ : Type*} [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  {υ : Type*} [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

omit [Decomposition 𝒨] in
/-- The stalk of `associatedModuleSheaf` computed through
`AlgebraicGeometry.SheafOfModules.stalkObj` is, on the nose, the hand-built
`associatedModuleSheafStalk`. -/
theorem stalkObj_eq (x : ProjectiveSpectrum.top 𝒮) :
    (AlgebraicGeometry.SheafOfModules.stalkObj _ x
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨) : Type u) =
      associatedModuleSheafStalk 𝒮 𝒨 x := rfl

omit [Decomposition 𝒨] in
/-- The germ map through `TopCat.Presheaf.germ` and the hand-built
`associatedModuleSheafGerm` agree on the nose, once their target types are identified by
`stalkObj_eq`. -/
theorem germ_eq (x : ProjectiveSpectrum.top 𝒮) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (hx : x ∈ U) (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) :
    (TopCat.Presheaf.germ (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf
      U x hx).hom s = associatedModuleSheafGerm 𝒮 𝒨 x U hx s := rfl

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- **The stalk map of `associatedModuleSheafMap` is the localization of `φ`, read through the
evaluation maps into the ambient fibers.** Evaluating the stalk map at any stalk element and
pushing the result into the ambient fiber of `N` agrees with applying `φ`'s localization to the
evaluation of that element in the ambient fiber of `M`. -/
theorem stalkMap_associatedModuleSheafMap_eval (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (x : ProjectiveSpectrum.top 𝒮)
    (z : associatedModuleSheafStalk 𝒮 𝒨 x) :
    (associatedModuleSheafStalkEval 𝒮 𝒩 x
        ((AlgebraicGeometry.SheafOfModules.stalkMap _ x
          (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ)).hom z) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) =
      LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ
        (associatedModuleSheafStalkEval 𝒮 𝒨 x z :
          ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) := by
  obtain ⟨U, hx, s, rfl⟩ := associatedModuleSheafStalk_exists_germ 𝒮 𝒨 x z
  have hstalk :
      (AlgebraicGeometry.SheafOfModules.stalkMap _ x
          (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ)).hom
        (associatedModuleSheafGerm 𝒮 𝒨 x U hx s) =
      associatedModuleSheafGerm 𝒮 𝒩 x U hx
        ((associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app (op U) s) :=
    AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x _ U hx s
  rw [hstalk, associatedModuleSheafStalkEval_germ, associatedModuleSheafStalkEval_germ]
  rfl

/-- **Isomorphy of the associated-sheaf morphism from eventual bijectivity.** If a
degree-preserving linear map `φ : M →ₗ[S] N` of graded `S`-modules in the same universe as
`S` restricts to a bijection on homogeneous components in every sufficiently large degree, the
induced morphism of associated sheaves on `Proj(S)` is an isomorphism. -/
theorem isIso_associatedModuleSheafMap_of_eventually_bijective
    (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) {N₀ : ℤ}
    (hinj : ∀ j : ℤ, N₀ ≤ j → ∀ m : M, m ∈ 𝒨 j → φ m = 0 → m = 0)
    (hsurj : ∀ j : ℤ, N₀ ≤ j → ∀ n : N, n ∈ 𝒩 j → ∃ m : M, m ∈ 𝒨 j ∧ φ m = n) :
    CategoryTheory.IsIso (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ) := by
  classical
  rw [AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap]
  intro x
  have hbij := bijOn_degreeZeroModuleAt_of_eventually_bijective 𝒮 𝒨 𝒩 φ hφ hinj hsurj x
  constructor
  · intro z₁ z₂ hz
    apply (associatedModuleSheafStalkEquiv 𝒮 𝒨 x).injective
    apply Subtype.ext
    have h1 := stalkMap_associatedModuleSheafMap_eval 𝒮 𝒨 𝒩 φ hφ x z₁
    have h2 := stalkMap_associatedModuleSheafMap_eval 𝒮 𝒨 𝒩 φ hφ x z₂
    rw [hz] at h1
    exact hbij.injOn (Subtype.mem _) (Subtype.mem _) (h1.symm.trans h2)
  · intro w
    obtain ⟨wM, hwM, hgw⟩ := hbij.surjOn (associatedModuleSheafStalkEval 𝒮 𝒩 x w).2
    obtain ⟨zM, hzM⟩ := (associatedModuleSheafStalkEquiv 𝒮 𝒨 x).surjective ⟨wM, hwM⟩
    refine ⟨zM, ?_⟩
    apply (associatedModuleSheafStalkEquiv 𝒮 𝒩 x).injective
    apply Subtype.ext
    change (associatedModuleSheafStalkEval 𝒮 𝒩 x
        ((AlgebraicGeometry.SheafOfModules.stalkMap _ x
          (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ)).hom zM) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) =
      (associatedModuleSheafStalkEval 𝒮 𝒩 x w :
        ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x)
    rw [stalkMap_associatedModuleSheafMap_eval 𝒮 𝒨 𝒩 φ hφ x zM]
    have hzM' : (associatedModuleSheafStalkEval 𝒮 𝒨 x zM :
        ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) = wM :=
      congrArg Subtype.val hzM
    rwa [hzM']

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections

end

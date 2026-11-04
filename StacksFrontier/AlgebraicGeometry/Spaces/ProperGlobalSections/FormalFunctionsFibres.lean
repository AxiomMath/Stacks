module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FibreThickeningSections

/-!
# Formal functions on a proper algebraic space, read on the fibres over `Spec (A / Iⁿ)`

Let `V` be an affine locally Noetherian object of the big fppf site over `S`, `A = Γ(V, 𝒪_V)`,
`I ⊆ A` an ideal and `f : X ⟶ V` a proper morphism of algebraic spaces.  This file proves

* `Γ(X, 𝒪_X)` is a finite `A`-module (Stacks 08AS in degree zero), and
* the restriction maps `Γ(X, 𝒪_X) ⟶ Γ(X ×_V Spec (A / Iⁿ), 𝒪)` induce an isomorphism of
  `A`-modules `Γ(X, 𝒪_X)^∧_I ≅ limₙ Γ(X ×_V Spec (A / Iⁿ), 𝒪)` (the theorem on formal functions
  in degree zero, Stacks 08AZ, read on the fibres).

The second statement combines `AlgebraicGeometry.Space.adicCompletionSectionsEquiv` (the
theorem on formal functions for `H⁰(X, 𝒪_X / Iⁿ 𝒪_X)`) with the identification of
`𝒪_X / Iⁿ 𝒪_X` with the direct image of the structure sheaf of the fibre
(`AlgebraicGeometry.Space.idealQuotientIsoPushforwardFibreThickening`) and the compatibility of
that identification with projections and transitions
(`AlgebraicGeometry.Space.pushforwardSectionsTopos_map_eq`,
`AlgebraicGeometry.Space.pushforwardSectionsTopos_transition`).

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionsOver`: `Γ(W, 𝒪_W)` as an `A`-module along `W ⟶ V`.
* `AlgebraicGeometry.Space.fibreSpace`: the fibre `X ×_V Spec (A / Iⁿ)`, with its inclusion
  `fibreInclusion` into `X` and the inclusions `fibreTransition` between fibres.
* `AlgebraicGeometry.Space.fibreFunctionsMap`, `AlgebraicGeometry.Space.fibreRestriction`:
  restriction of functions.
* `AlgebraicGeometry.Space.adicCompletionFibreFunctionsEquiv`: the isomorphism.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_globalFunctionsOver_of_isProper`.
* `AlgebraicGeometry.Space.adicCompletionFibreFunctionsEquiv_of`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

universe u

namespace Stacks.IntertwinedFiltration

/-- The comparison of `Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`,
precomposed with the completion of a linear equivalence, read at a level on a representative. -/
theorem adicCompletionEquivTowerLimitOfEventualRange_congr_apply {A : Type*} [CommRing A]
    {M H : Type*} [AddCommGroup M] [Module A M] [AddCommGroup H] [Module A H]
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
    (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (π : ∀ n, H →ₗ[A] P n) (I : Ideal A) (c : ℕ)
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hker : ∀ n, I ^ n • (⊤ : Submodule A H) ≤ LinearMap.ker (π n))
    (hker' : ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A H))
    (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n))
    (e : M ≃ₗ[A] H) (x : AdicCompletion I M) (n : ℕ) (m : M)
    (hm : x.val n = Submodule.Quotient.mk m) :
    (adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange
      (AdicCompletion.congr I e x)).1 n = π n (e m) := by
  show quotKerEmbed P π n (Submodule.factor (hker n) ((AdicCompletion.congr I e x).val n)) = _
  rw [AdicCompletion.congr_apply, AdicCompletion.map_val_apply, hm]
  rfl

end Stacks.IntertwinedFiltration

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasInjectiveResolutions_modules

section Functions

variable (V : BigFppfOver B S hS)

/-- `Γ(W, 𝒪_W)` as a module over `Γ(V, 𝒪_V)` along `g : W ⟶ V`. -/
abbrev globalFunctionsOver {W : AlgebraicSpaces B S hS} (g : W ⟶ schemeSpace V) :
    ModuleCat.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  (ModuleCat.restrictScalars (pullbackRingHom B V g)).obj
    (ModuleCat.of _ ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS W.1 W.2).O)))

/-- Restriction of functions along a morphism `k : W ⟶ W'` over `V`, as a map of
`Γ(V, 𝒪_V)`-modules. -/
def restrictFunctionsOver {W W' : AlgebraicSpaces B S hS} (k : W ⟶ W') (g' : W' ⟶ schemeSpace V)
    (g : W ⟶ schemeSpace V) (hg : k ≫ g' = g) :
    globalFunctionsOver V g' →ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
      globalFunctionsOver V g where
  toFun x := globalSectionsRingHomSite B S hS k x
  map_add' := map_add _
  map_smul' a x :=
    (map_mul (globalSectionsRingHomSite B S hS k) (pullbackRingHom B V g' a) x).trans
      (congrArg (· * globalSectionsRingHomSite B S hS k x) (by
        rw [← hg, ← globalSectionsRingHomSite_comp_pullbackRingHom]
        rfl))

/-- `restrictFunctionsOver` is the pullback of global functions along `k`. -/
theorem restrictFunctionsOver_apply {W W' : AlgebraicSpaces B S hS} (k : W ⟶ W')
    (g' : W' ⟶ schemeSpace V) (g : W ⟶ schemeSpace V) (hg : k ≫ g' = g)
    (x : globalFunctionsOver V g') :
    restrictFunctionsOver V k g' g hg x = globalSectionsRingHomSite B S hS k x :=
  rfl

end Functions

section Fibres

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ schemeSpace V)

/-- For `m ≤ n`, the subspace `Spec (A / Iᵐ)` of `V` is contained in `Spec (A / Iⁿ)`. -/
theorem adicQuotientSubspace_le {m n : ℕ} (h : m ≤ n) :
    (adicQuotientSubspace V I m).1 ≤ (adicQuotientSubspace V I n).1 := by
  obtain ⟨t, ht⟩ := (exists_comp_adicCompletionQuotientObjHom_iff (V := V) (K := I)
    (adicCompletionQuotientObjHom B S hS V I m) n).2 (by
      rw [ker_appTop_adicCompletionQuotientObjHom]
      exact Ideal.pow_le_pow_right h)
  rintro T y ⟨x, rfl⟩
  refine ⟨x ≫ t, ?_⟩
  show (x ≫ t) ≫ adicCompletionQuotientObjHom B S hS V I n =
    x ≫ adicCompletionQuotientObjHom B S hS V I m
  rw [Category.assoc, ht]

/-- For `m ≤ n`, the fibre `X ×_V Spec (A / Iᵐ)` is contained in `X ×_V Spec (A / Iⁿ)`. -/
theorem fibreThickening_le {m n : ℕ} (h : m ≤ n) :
    (fibreThickening V I f m).1 ≤ (fibreThickening V I f n).1 :=
  fun T x hx => adicQuotientSubspace_le V I h _ hx

/-- **The fibre `X ×_V Spec (A / Iⁿ)`**, as an algebraic space. -/
abbrev fibreSpace (n : ℕ) : AlgebraicSpaces B S hS :=
  ⟨(fibreThickening V I f n).1.toFunctor, (fibreThickening V I f n).2.1⟩

/-- The inclusion of the fibre `X ×_V Spec (A / Iⁿ)` into `X`. -/
abbrev fibreInclusion (n : ℕ) : fibreSpace V I f n ⟶ X :=
  subspaceInclusion B S hS X (fibreThickening V I f n)

/-- The inclusion `X ×_V Spec (A / Iᵐ) ⟶ X ×_V Spec (A / Iⁿ)` for `m ≤ n`. -/
def fibreTransition {m n : ℕ} (h : m ≤ n) : fibreSpace V I f m ⟶ fibreSpace V I f n :=
  ObjectProperty.homMk (Subfunctor.homOfLe (fibreThickening_le V I f h))

/-- The transition between fibres commutes with their inclusions into `X`. -/
theorem fibreTransition_comp {m n : ℕ} (h : m ≤ n) :
    fibreTransition V I f h ≫ fibreInclusion V I f n = fibreInclusion V I f m :=
  ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι (fibreThickening_le V I f h))

/-- `Γ(X ×_V Spec (A / Iⁿ), 𝒪)` as an `A`-module. -/
abbrev fibreFunctions (n : ℕ) : ModuleCat.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  globalFunctionsOver V (fibreInclusion V I f n ≫ f)

/-- Restriction of functions from `X ×_V Spec (A / Iⁿ)` to `X ×_V Spec (A / Iᵐ)`, `m ≤ n`. -/
def fibreFunctionsMap (m n : ℕ) (h : m ≤ n) :
    fibreFunctions V I f n →ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] fibreFunctions V I f m :=
  restrictFunctionsOver V (fibreTransition V I f h) _ _
    (by rw [← Category.assoc, fibreTransition_comp])

/-- Restriction of functions from `X` to `X ×_V Spec (A / Iⁿ)`. -/
def fibreRestriction (n : ℕ) :
    globalFunctionsOver V f →ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] fibreFunctions V I f n :=
  restrictFunctionsOver V (fibreInclusion V I f n) f _ rfl

end Fibres

section ZeroCohomology

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O))))

/-- The identification `R⁰Γ = Γ` of the right derived functors of the global sections in degree
zero, `Γ` being left exact. -/
def rightDerivedZeroIsoGlobalSections (X : AlgebraicSpaces B S hS) :=
  haveI := preservesFiniteLimits_globalSectionsFunctor_ringUniverse
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  Functor.rightDerivedZeroIsoSelf (globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- `H⁰(X, M) ⟶ Γ(X, M)`, the identification of degree-zero cohomology with global sections. -/
def sectionsOfCohomologyZero (M : Modules.{u, u} B S hS X.1 X.2) :
    cohomologyRes φ 0 M → M.sections :=
  fun y => ((rightDerivedZeroIsoGlobalSections X).hom.app M).hom y

/-- `Γ(X, M) ⟶ H⁰(X, M)`, the inverse identification. -/
def cohomologyZeroOfSections (M : Modules.{u, u} B S hS X.1 X.2) :
    M.sections → cohomologyRes φ 0 M :=
  fun s => ((rightDerivedZeroIsoGlobalSections X).inv.app M).hom s

/-- `sectionsOfCohomologyZero` is a left inverse of `cohomologyZeroOfSections`. -/
theorem sectionsOfCohomologyZero_cohomologyZeroOfSections (M : Modules.{u, u} B S hS X.1 X.2)
    (s : M.sections) : sectionsOfCohomologyZero φ M (cohomologyZeroOfSections φ M s) = s :=
  congrArg (fun h => h.hom s) (Iso.inv_hom_id_app (rightDerivedZeroIsoGlobalSections X) M)

/-- `cohomologyZeroOfSections` is a left inverse of `sectionsOfCohomologyZero`. -/
theorem cohomologyZeroOfSections_sectionsOfCohomologyZero (M : Modules.{u, u} B S hS X.1 X.2)
    (y : cohomologyRes φ 0 M) : cohomologyZeroOfSections φ M (sectionsOfCohomologyZero φ M y) = y :=
  congrArg (fun h => h.hom y) (Iso.hom_inv_id_app (rightDerivedZeroIsoGlobalSections X) M)

/-- The map `H⁰(X, M) ⟶ Γ(X, M)` is bijective. -/
theorem bijective_sectionsOfCohomologyZero (M : Modules.{u, u} B S hS X.1 X.2) :
    Function.Bijective (sectionsOfCohomologyZero φ M) :=
  Function.bijective_iff_has_inverse.2 ⟨cohomologyZeroOfSections φ M,
    cohomologyZeroOfSections_sectionsOfCohomologyZero φ M,
    sectionsOfCohomologyZero_cohomologyZeroOfSections φ M⟩

/-- The identification `H⁰(X, M) ⟶ Γ(X, M)` is natural in the module `M`. -/
theorem sectionsOfCohomologyZero_naturality {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N)
    (y : cohomologyRes φ 0 M) :
    sectionsOfCohomologyZero φ N (cohomologyResMap φ 0 g y) =
      SheafOfModules.sectionsMap g (sectionsOfCohomologyZero φ M y) :=
  congrArg (fun h => h.hom y) ((rightDerivedZeroIsoGlobalSections X).hom.naturality g)

/-- The global sections of the structure module are the ring of global functions, as modules over
that ring. -/
def unitSectionsLinearEquiv (X : AlgebraicSpaces B S hS) :
    ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)) ≃ₗ[↥(GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))]
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).sections where
  toFun m := ⟨m.1, m.2⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `H⁰(X, 𝒪_X)` is `Γ(X, 𝒪_X)`, linearly over `A`. -/
def globalFunctionsEquivCohomologyZero :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of _ ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≃ₗ[A]
      cohomologyRes φ 0 (SheafOfModules.unit _) :=
  ((ModuleCat.restrictScalars φ).mapIso ((unitSectionsLinearEquiv X).toModuleIso ≪≫
    ((rightDerivedZeroIsoGlobalSections X).app (SheafOfModules.unit _)).symm)).toLinearEquiv

/-- `globalFunctionsEquivCohomologyZero` sends a global function to the degree-zero cohomology
class of the corresponding section of the structure module. -/
theorem globalFunctionsEquivCohomologyZero_apply
    (m : (ModuleCat.restrictScalars φ).obj (ModuleCat.of _ ↥(GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))) :
    globalFunctionsEquivCohomologyZero φ m =
      cohomologyZeroOfSections φ (SheafOfModules.unit _) ⟨m.1, m.2⟩ :=
  rfl

end ZeroCohomology

section Bijections

/-- An isomorphism of sheaves of modules induces a bijection on global sections. -/
theorem sectionsMap_bijective_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N) :
    Function.Bijective (SheafOfModules.sectionsMap e.hom) :=
  Function.bijective_iff_has_inverse.2 ⟨SheafOfModules.sectionsMap e.inv,
    fun x => (congrArg (fun h => SheafOfModules.sectionsMap h x) e.hom_inv_id).trans
      (SheafOfModules.sectionsMap_id x),
    fun x => (congrArg (fun h => SheafOfModules.sectionsMap h x) e.inv_hom_id).trans
      (SheafOfModules.sectionsMap_id x)⟩

/-- For a module `Q` on `Y` isomorphic to `k_* 𝒪_W`, the map from global sections of `Q` to global
sections of the structure module of `W` is bijective. -/
theorem pushforwardSectionsTopos_bijective {W Y : AlgebraicSpaces B S hS} (k : W ⟶ Y)
    {Q : Modules.{u, u} B S hS Y.1 Y.2}
    (c : Q ≅ (modulePushforward B S hS k).obj (SheafOfModules.unit (structureRingSheaf B S hS W))) :
    Function.Bijective (pushforwardSectionsTopos k c) :=
  (Equiv.bijective _).comp (sectionsMap_bijective_of_iso
    (c ≪≫ ((modulePushforwardIso B S hS k).app (toposUnit B S hS W)).symm))

/-- Global sections of the structure module at the topos spelling, as global functions. -/
def toposSectionsToGlobalFunctions (W : AlgebraicSpaces B S hS)
    (z : (toposUnit B S hS W).sections) :
    ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS W.1 W.2).O)) :=
  ⟨z.1, z.2⟩

/-- Restriction of functions at the site spelling, on global sections at the topos spelling, is
restriction at the topos spelling. -/
theorem globalSectionsRingHomSite_toposSectionsToGlobalFunctions {W W' : AlgebraicSpaces B S hS}
    (j : W ⟶ W') (z : (toposUnit B S hS W').sections) :
    (globalSectionsRingHomSite B S hS j (toposSectionsToGlobalFunctions W' z)).1 =
      (globalSectionsRingHom (smallEtaleRingedToposModulesHom B S hS j) ⟨z.1, z.2⟩).1 :=
  rfl

/-- `toposSectionsToGlobalFunctions` is bijective. -/
theorem toposSectionsToGlobalFunctions_bijective (W : AlgebraicSpaces B S hS) :
    Function.Bijective (toposSectionsToGlobalFunctions W) :=
  Function.bijective_iff_has_inverse.2 ⟨fun w => ⟨w.1, w.2⟩, fun _ => rfl, fun _ => rfl⟩

end Bijections

section Main

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ schemeSpace V)

/-- `H⁰(X, 𝒪_X / Iⁿ 𝒪_X) ⟶ Γ(X ×_V Spec (A / Iⁿ), 𝒪)`, the composite of `H⁰ = Γ`, of
`𝒪_X / Iⁿ 𝒪_X ≅ i_*𝒪` and of Stacks 0732. -/
def fibreSectionsOfCohomologyZero (n : ℕ) :
    sectionsTower (pullbackRingHom B V f) (structureSheafModule B S hS X) I n →
      fibreFunctions V I f n :=
  toposSectionsToGlobalFunctions (fibreSpace V I f n) ∘
    pushforwardSectionsTopos (fibreInclusion V I f n)
      (idealQuotientIsoPushforwardFibreThickening V I f n) ∘
    sectionsOfCohomologyZero (pullbackRingHom B V f)
      (idealQuotient (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n))

/-- The map `H⁰(X, 𝒪_X / Iⁿ 𝒪_X) ⟶ Γ(X ×_V Spec (A / Iⁿ), 𝒪)` is bijective. -/
theorem fibreSectionsOfCohomologyZero_bijective (n : ℕ) :
    Function.Bijective (fibreSectionsOfCohomologyZero V I f n) :=
  (toposSectionsToGlobalFunctions_bijective _).comp ((pushforwardSectionsTopos_bijective _ _).comp
    (bijective_sectionsOfCohomologyZero _ _))

/-- The underlying section of `fibreSectionsOfCohomologyZero` applied to a class. -/
theorem fibreSectionsOfCohomologyZero_val (n : ℕ)
    (y : sectionsTower (pullbackRingHom B V f) (structureSheafModule B S hS X) I n) :
    (fibreSectionsOfCohomologyZero V I f n y).1 =
      (pushforwardSectionsTopos (fibreInclusion V I f n)
        (idealQuotientIsoPushforwardFibreThickening V I f n) (sectionsOfCohomologyZero
          (pullbackRingHom B V f)
          (idealQuotient (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n)) y)).1 :=
  rfl

/-- `fibreSectionsOfCohomologyZero` is the composite of its three constituent maps. -/
theorem fibreSectionsOfCohomologyZero_apply (n : ℕ)
    (y : sectionsTower (pullbackRingHom B V f) (structureSheafModule B S hS X) I n) :
    fibreSectionsOfCohomologyZero V I f n y =
      toposSectionsToGlobalFunctions (fibreSpace V I f n) (pushforwardSectionsTopos
        (fibreInclusion V I f n) (idealQuotientIsoPushforwardFibreThickening V I f n)
          (sectionsOfCohomologyZero (pullbackRingHom B V f)
            (idealQuotient (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n)) y)) :=
  rfl

/-- `fibreFunctionsMap` is the pullback of functions along `fibreTransition`. -/
theorem fibreFunctionsMap_apply (m n : ℕ) (h : m ≤ n) (x : fibreFunctions V I f n) :
    fibreFunctionsMap V I f m n h x =
      globalSectionsRingHomSite B S hS (fibreTransition V I f h) x :=
  rfl

/-- The image of a global function `m` of `X` in `H⁰(X, 𝒪_X / Iⁿ 𝒪_X)` corresponds to the
restriction of `m` to the fibre `X ×_V Spec (A / Iⁿ)`. -/
theorem fibreSectionsOfCohomologyZero_proj (n : ℕ) (m : globalFunctionsOver V f) :
    fibreSectionsOfCohomologyZero V I f n (sectionsTowerProj (pullbackRingHom B V f)
      (structureSheafModule B S hS X) I n
      (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f) m)) =
      fibreRestriction V I f n m := by
  refine Subtype.ext ?_
  have h1 : sectionsOfCohomologyZero (pullbackRingHom B V f)
      (idealQuotient (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n))
      (sectionsTowerProj (pullbackRingHom B V f) (structureSheafModule B S hS X) I n
        (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f) m)) =
      SheafOfModules.sectionsMap
        (idealQuotientπ (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n))
        ⟨m.1, m.2⟩ := by
    rw [sectionsOfCohomologyZero_naturality, globalFunctionsEquivCohomologyZero_apply]
    exact congrArg (SheafOfModules.sectionsMap _)
      (sectionsOfCohomologyZero_cohomologyZeroOfSections _ _ _)
  show (pushforwardSectionsTopos (fibreInclusion V I f n)
      (idealQuotientIsoPushforwardFibreThickening V I f n) (sectionsOfCohomologyZero
        (pullbackRingHom B V f)
        (idealQuotient (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n))
        (sectionsTowerProj (pullbackRingHom B V f) (structureSheafModule B S hS X) I n
          (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f) m)))).1 = _
  rw [h1]
  exact pushforwardSectionsTopos_map_eq (fibreThickening V I f n)
    (idealQuotientπ (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n))
    (idealQuotientIsoPushforwardFibreThickening V I f n)
    (idealQuotientπ_comp_idealQuotientIsoPushforwardFibreThickening_hom V I f n) ⟨m.1, m.2⟩

/-- `fibreSectionsOfCohomologyZero` intertwines the transition maps of the tower
`H⁰(X, 𝒪_X / Iⁿ 𝒪_X)` with the restrictions between fibres. -/
theorem fibreSectionsOfCohomologyZero_transition (m n : ℕ) (h : m ≤ n)
    (y : sectionsTower (pullbackRingHom B V f) (structureSheafModule B S hS X) I n) :
    fibreSectionsOfCohomologyZero V I f m
        (sectionsTowerMap (pullbackRingHom B V f) (structureSheafModule B S hS X) I m n h y) =
      fibreFunctionsMap V I f m n h (fibreSectionsOfCohomologyZero V I f n y) := by
  refine Subtype.ext ?_
  rw [fibreSectionsOfCohomologyZero_val, fibreFunctionsMap_apply,
    fibreSectionsOfCohomologyZero_apply,
    globalSectionsRingHomSite_toposSectionsToGlobalFunctions]
  rw [sectionsOfCohomologyZero_naturality]
  have key := pushforwardSectionsTopos_transition (fibreThickening V I f m)
    (fibreThickening V I f n)
    (fibreTransition V I f h) (fibreTransition_comp V I f h)
    (idealQuotientπ (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n))
    (idealQuotientπ (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ m))
    (idealQuotientMap (pullbackRingHom B V f) (structureSheafModule B S hS X)
      (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m))
    (idealQuotientπ_idealQuotientMap _ _ _)
    (idealQuotientIsoPushforwardFibreThickening V I f n)
    (idealQuotientIsoPushforwardFibreThickening V I f m)
    (idealQuotientπ_comp_idealQuotientIsoPushforwardFibreThickening_hom V I f n)
    (idealQuotientπ_comp_idealQuotientIsoPushforwardFibreThickening_hom V I f m)
    (sectionsOfCohomologyZero (pullbackRingHom B V f)
      (idealQuotient (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n)) y)
  exact key

end Main

section Theorem

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)

include hf

/-- The `Fact` form of the étale-local Noetherian property of a proper space over an affine base. -/
private theorem fact_hasEtaleLocalProperty_isLocallyNoetherian :
    Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :=
  have := ‹IsAffine ((BigFppfOver.toScheme B S hS).obj V)›
  ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper_of_isAffine V f hf⟩

/-- The tower of `H⁰(X, 𝒪_X / Iⁿ 𝒪_X)` attached to `x ∈ Γ(X, 𝒪_X)^∧_I` by the theorem on formal
functions for the structure sheaf. -/
def formalSectionsTowerOf (x : AdicCompletion I (globalFunctionsOver V f)) :
    Stacks.IntertwinedFiltration.towerLimit
      (fun n : ℕ => (sectionsTower (pullbackRingHom B V f) (structureSheafModule B S hS X) I n :
        Type (u + 1)))
      (sectionsTowerMap (pullbackRingHom B V f) (structureSheafModule B S hS X) I) :=
  haveI : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper_of_isAffine V f hf⟩
  adicCompletionSectionsEquiv V f hf (structureSheafModule B S hS X) I
    (AdicCompletion.congr I (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f)) x)

/-- `formalSectionsTowerOf` is injective. -/
theorem formalSectionsTowerOf_injective : Function.Injective (formalSectionsTowerOf V I f hf) := by
  have := fact_hasEtaleLocalProperty_isLocallyNoetherian V f hf
  exact (adicCompletionSectionsEquiv V f hf (structureSheafModule B S hS X) I).injective.comp
    (AdicCompletion.congr I (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f))).injective

/-- `formalSectionsTowerOf` is surjective. -/
theorem formalSectionsTowerOf_surjective :
    Function.Surjective (formalSectionsTowerOf V I f hf) := by
  have := fact_hasEtaleLocalProperty_isLocallyNoetherian V f hf
  exact (adicCompletionSectionsEquiv V f hf (structureSheafModule B S hS X) I).surjective.comp
    (AdicCompletion.congr I (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f))).surjective

/-- If the level-`n` component of `x` is represented by a global function `m`, then the level-`n`
term of `formalSectionsTowerOf x` is the image of `m` in `H⁰(X, 𝒪_X / Iⁿ 𝒪_X)`. -/
theorem formalSectionsTowerOf_apply (x : AdicCompletion I (globalFunctionsOver V f)) (n : ℕ)
    (m : globalFunctionsOver V f) (hm : x.val n = Submodule.Quotient.mk m) :
    (formalSectionsTowerOf V I f hf x).1 n =
      sectionsTowerProj (pullbackRingHom B V f) (structureSheafModule B S hS X) I n
        (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f) m) := by
  have := fact_hasEtaleLocalProperty_isLocallyNoetherian V f hf
  exact Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange_congr_apply
    _ _ _ I _ _ _ _ _ (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f)) x n m hm

/-- **The comparison map of the theorem on formal functions on the fibres**,
`Γ(X, 𝒪_X)^∧_I ⟶ limₙ Γ(X ×_V Spec (A / Iⁿ), 𝒪)`, as a function. -/
def fibreFunctionsTowerOf (x : AdicCompletion I (globalFunctionsOver V f)) :
    Stacks.IntertwinedFiltration.towerLimit (fun n : ℕ => (fibreFunctions V I f n : Type (u + 1)))
      (fibreFunctionsMap V I f) :=
  ⟨fun n => fibreSectionsOfCohomologyZero V I f n ((formalSectionsTowerOf V I f hf x).1 n),
    fun m n h => by
      change fibreFunctionsMap V I f m n h (fibreSectionsOfCohomologyZero V I f n _) = _
      rw [← fibreSectionsOfCohomologyZero_transition,
        Stacks.IntertwinedFiltration.towerLimit_compat]⟩

/-- If the level-`n` component of `x` is represented by a global function `m`, then the level-`n`
term of `fibreFunctionsTowerOf x` is the restriction of `m` to the fibre `X ×_V Spec (A / Iⁿ)`. -/
theorem fibreFunctionsTowerOf_apply (x : AdicCompletion I (globalFunctionsOver V f)) (n : ℕ)
    (m : globalFunctionsOver V f) (hm : x.val n = Submodule.Quotient.mk m) :
    (fibreFunctionsTowerOf V I f hf x).1 n = fibreRestriction V I f n m := by
  show fibreSectionsOfCohomologyZero V I f n ((formalSectionsTowerOf V I f hf x).1 n) = _
  rw [formalSectionsTowerOf_apply V I f hf x n m hm, fibreSectionsOfCohomologyZero_proj]

/-- **The comparison map of the theorem on formal functions on the fibres**, as a map of
`A`-modules. -/
def fibreFunctionsTowerMap :
    AdicCompletion I (globalFunctionsOver V f) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
      Stacks.IntertwinedFiltration.towerLimit (fun n : ℕ => (fibreFunctions V I f n : Type (u + 1)))
        (fibreFunctionsMap V I f) where
  toFun := fibreFunctionsTowerOf V I f hf
  map_add' x y := by
    refine Stacks.IntertwinedFiltration.towerLimit_ext fun n => ?_
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
    have hab : (x + y).val n = Submodule.Quotient.mk (a + b) := by
      rw [AdicCompletion.val_add_apply, ← ha, ← hb]
      rfl
    change (fibreFunctionsTowerOf V I f hf (x + y)).1 n =
      (fibreFunctionsTowerOf V I f hf x).1 n + (fibreFunctionsTowerOf V I f hf y).1 n
    rw [fibreFunctionsTowerOf_apply V I f hf _ n _ hab,
      fibreFunctionsTowerOf_apply V I f hf _ n _ ha.symm,
      fibreFunctionsTowerOf_apply V I f hf _ n _ hb.symm, map_add]
  map_smul' r x := by
    refine Stacks.IntertwinedFiltration.towerLimit_ext fun n => ?_
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hra : (r • x).val n = Submodule.Quotient.mk (r • a) := by
      rw [AdicCompletion.val_smul_apply, ← ha]
      rfl
    change (fibreFunctionsTowerOf V I f hf (r • x)).1 n =
      r • (fibreFunctionsTowerOf V I f hf x).1 n
    rw [fibreFunctionsTowerOf_apply V I f hf _ n _ hra,
      fibreFunctionsTowerOf_apply V I f hf _ n _ ha.symm,
      map_smul]

/-- `fibreFunctionsTowerMap` is injective. -/
theorem fibreFunctionsTowerMap_injective :
    Function.Injective (fibreFunctionsTowerMap V I f hf) := by
  intro x y hxy
  refine formalSectionsTowerOf_injective V I f hf
    (Stacks.IntertwinedFiltration.towerLimit_ext fun n => ?_)
  exact (fibreSectionsOfCohomologyZero_bijective V I f n).1
    (congrArg (fun z : Stacks.IntertwinedFiltration.towerLimit _ (fibreFunctionsMap V I f) =>
      z.1 n) hxy)

/-- `fibreFunctionsTowerMap` is surjective. -/
theorem fibreFunctionsTowerMap_surjective :
    Function.Surjective (fibreFunctionsTowerMap V I f hf) := by
  intro w
  choose z hz using fun n => (fibreSectionsOfCohomologyZero_bijective V I f n).2 (w.1 n)
  have hzc : ∀ (m n : ℕ) (h : m ≤ n),
      sectionsTowerMap (pullbackRingHom B V f) (structureSheafModule B S hS X) I m n h (z n) =
        z m := fun m n h =>
    (fibreSectionsOfCohomologyZero_bijective V I f m).1 (by
      rw [fibreSectionsOfCohomologyZero_transition, hz, hz]
      exact Stacks.IntertwinedFiltration.towerLimit_compat w m n h)
  obtain ⟨x, hx⟩ := formalSectionsTowerOf_surjective V I f hf ⟨z, hzc⟩
  refine ⟨x, Stacks.IntertwinedFiltration.towerLimit_ext fun n => ?_⟩
  show fibreSectionsOfCohomologyZero V I f n ((formalSectionsTowerOf V I f hf x).1 n) = _
  rw [hx]
  exact hz n

/-- **The theorem on formal functions in degree zero, on the fibres** (Stacks 08AZ for `p = 0` and
`F = 𝒪_X`): for an affine locally Noetherian object `V` of the site with `A = Γ(V, 𝒪_V)`, an ideal
`I ⊆ A` and a proper morphism of algebraic spaces `f : X ⟶ V`, the restriction maps
`Γ(X, 𝒪_X) ⟶ Γ(X ×_V Spec (A / Iⁿ), 𝒪)` induce an isomorphism of `A`-modules
`Γ(X, 𝒪_X)^∧_I ≅ limₙ Γ(X ×_V Spec (A / Iⁿ), 𝒪)`. -/
def adicCompletionFibreFunctionsEquiv :
    AdicCompletion I (globalFunctionsOver V f) ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
      Stacks.IntertwinedFiltration.towerLimit (fun n : ℕ => (fibreFunctions V I f n : Type (u + 1)))
        (fibreFunctionsMap V I f) :=
  LinearEquiv.ofBijective (fibreFunctionsTowerMap V I f hf)
    ⟨fibreFunctionsTowerMap_injective V I f hf, fibreFunctionsTowerMap_surjective V I f hf⟩

/-- **The isomorphism is defined by the restriction maps**: the image in the completion of a global
function `x` of `X` goes to the family of its restrictions to the fibres. -/
theorem adicCompletionFibreFunctionsEquiv_of (x : globalFunctionsOver V f) (n : ℕ) :
    Stacks.IntertwinedFiltration.towerLimit.proj n
        (adicCompletionFibreFunctionsEquiv V I f hf (AdicCompletion.of I _ x)) =
      fibreRestriction V I f n x :=
  fibreFunctionsTowerOf_apply V I f hf _ n x rfl

/-- **Global functions of a proper algebraic space over an affine Noetherian object are finite**
(Stacks 08AS in degree zero): `Γ(X, 𝒪_X)` is a finite `Γ(V, 𝒪_V)`-module. -/
theorem moduleFinite_globalFunctionsOver_of_isProper :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (globalFunctionsOver V f) := by
  have := fact_hasEtaleLocalProperty_isLocallyNoetherian V f hf
  have := moduleFinite_cohomology_of_isProper_of_isAffine B V f hf (structureSheafModule B S hS X) 0
  exact Module.Finite.equiv (globalFunctionsEquivCohomologyZero (pullbackRingHom B V f)).symm

end Theorem

end AlgebraicGeometry.Space

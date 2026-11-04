module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.KoszulResolution
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.KoszulComplexChern
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The Koszul resolution of `i_* 𝒪_X` in the derived category

Let `E = Proj_X(Sym^*(𝒞)[T])`, `𝒦 = Ker(π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1))` with `φ : 𝒦 ⟶ 𝒪_E`, and
`i : X ⟶ E` the zero section. The augmentation `⋀⁰ 𝒦 ≅ 𝒪_E ⟶ i_* 𝒪_X` makes the Koszul complex
`⋯ ⟶ ⋀² 𝒦 ⟶ 𝒦 ⟶ 𝒪_E` of `φ` a resolution of `i_* 𝒪_X`: the chain map to `i_* 𝒪_X` in degree
zero is a quasi-isomorphism. Read in cohomological degrees `≤ 0`, the Koszul complex is
therefore isomorphic to `i_* 𝒪_X` in `D(𝒪_E)`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.zeroSecUnit`: the module `i_* 𝒪_X` on `E`.
* `Stacks.Chow.ProjectiveCompletion.koszulChainAug`: the augmentation of the Koszul complex.

## Main results

* `Stacks.Chow.ProjectiveCompletion.quasiIso_koszulChainAug`: the augmentation is a
  quasi-isomorphism.
* `Stacks.Chow.ProjectiveCompletion.koszulComplexIso`: the Koszul complex is isomorphic to
  `i_* 𝒪_X` in the derived category.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.ProjectiveCompletion

attribute [local instance 2000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

/-- **The module `i_* 𝒪_X`** on the projective completion, for the zero section `i`. -/
abbrev zeroSecUnit : (space 𝒞).Modules :=
  (Scheme.Modules.pushforward (zeroSec 𝒞 r)).obj (SheafOfModules.unit X.ringCatSheaf)

/-- The degree-one differential of the Koszul complex is contraction `𝒦 ⟶ 𝒪_E` by `φ`. -/
theorem koszulChain_d_one_zero :
    (Scheme.Modules.koszulChain (kernelModule 𝒞) (koszulMap 𝒞)).d 1 0 =
      Scheme.Modules.koszulContraction (kernelModule 𝒞) (koszulMap 𝒞) 0 := by
  unfold Scheme.Modules.koszulChain
  exact ChainComplex.of_d
    (fun n : ℕ => Scheme.Modules.exteriorPower (kernelModule 𝒞) ((n : ℕ) : ℤ))
    (Scheme.Modules.koszulContraction (kernelModule 𝒞) (koszulMap 𝒞)) 0

/-- The degree-one differential of the Koszul complex followed by the augmentation `𝒪_E ⟶ i_* 𝒪_X`
is zero. -/
theorem koszulChain_d_one_zero_comp_koszulAug :
    (Scheme.Modules.koszulChain (kernelModule 𝒞) (koszulMap 𝒞)).d 1 0 ≫ koszulAug 𝒞 r = 0 :=
  (congrArg (· ≫ koszulAug 𝒞 r) (koszulChain_d_one_zero 𝒞)).trans
    (koszulContraction_zero_comp_koszulAug 𝒞 r)

/-- Exactness of a short complex depends only on its two maps. -/
theorem exact_mk_of_eq {C : Type*} [Category C] [HasZeroMorphisms C] {A B D : C}
    {f f' : A ⟶ B} {g g' : B ⟶ D} (w : f ≫ g = 0) (w' : f' ≫ g' = 0) (hf : f = f') (hg : g = g')
    (h : (ShortComplex.mk f' g' w').Exact) : (ShortComplex.mk f g w).Exact := by
  subst hf hg
  exact h

/-- **The augmentation of the Koszul complex**, the chain map to `i_* 𝒪_X` in degree zero. -/
def koszulChainAug : Scheme.Modules.koszulChain (kernelModule 𝒞) (koszulMap 𝒞) ⟶
    (ChainComplex.single₀ (space 𝒞).Modules).obj (zeroSecUnit 𝒞 r) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨koszulAug 𝒞 r, koszulChain_d_one_zero_comp_koszulAug 𝒞 r⟩

/-- **The Koszul complex of `φ` resolves `i_* 𝒪_X`**: its augmentation is a
quasi-isomorphism. -/
theorem quasiIso_koszulChainAug : QuasiIso (koszulChainAug 𝒞 r) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff,
      ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by rfl) (by rfl)]
    exact ⟨exact_mk_of_eq _ _ (koszulChain_d_one_zero 𝒞)
      (ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _) (exact_koszulAug 𝒞 r),
      epi_koszulAug 𝒞 r⟩
  | succ n =>
    exact (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ n)).2
      (exactAt_koszulChain 𝒞 (r := r) n)

/-- `i_* 𝒪_X` in degree zero, extended from `ℕ` to `ℤ`. -/
def zeroSecSingleIso :
    ((ChainComplex.single₀ (space 𝒞).Modules).obj (zeroSecUnit 𝒞 r)).extend
        ComplexShape.embeddingDownNat ≅
      (CochainComplex.singleFunctor (space 𝒞).Modules 0).obj (zeroSecUnit 𝒞 r) :=
  HomologicalComplex.extendSingleIso _ _ _ _ (by simp)

/-- The augmentation of the Koszul complex in cohomological degrees `≤ 0`. -/
def koszulComplexAug : Scheme.Modules.koszulComplex (kernelModule 𝒞) (koszulMap 𝒞) ⟶
    (CochainComplex.singleFunctor (space 𝒞).Modules 0).obj (zeroSecUnit 𝒞 r) :=
  HomologicalComplex.extendMap (koszulChainAug 𝒞 r) ComplexShape.embeddingDownNat ≫
    (zeroSecSingleIso 𝒞 r).hom

/-- The augmentation of the Koszul complex, in cohomological degrees `≤ 0`, is a
quasi-isomorphism. -/
theorem quasiIso_koszulComplexAug : QuasiIso (koszulComplexAug 𝒞 r) := by
  have h1 : QuasiIso (HomologicalComplex.extendMap (koszulChainAug 𝒞 r)
      ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 (quasiIso_koszulChainAug 𝒞 r)
  exact quasiIso_comp (hφ := h1) (hφ' := quasiIso_of_isIso _) _ _

/-- **The Koszul complex is `i_* 𝒪_X` in the derived category**: in `D(𝒪_E)` the Koszul complex
of `φ`, in cohomological degrees `≤ 0`, is isomorphic to `i_* 𝒪_X` placed in degree zero. -/
def koszulComplexIso :
    DerivedCategory.Q.obj (Scheme.Modules.koszulComplex (kernelModule 𝒞) (koszulMap 𝒞)) ≅
      (DerivedCategory.singleFunctor (space 𝒞).Modules 0).obj (zeroSecUnit 𝒞 r) :=
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (koszulComplexAug 𝒞 r)).2
    (quasiIso_koszulComplexAug 𝒞 r)
  asIso (DerivedCategory.Q.map (koszulComplexAug 𝒞 r)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (space 𝒞).Modules 0).app (zeroSecUnit 𝒞 r)).symm

end Stacks.Chow.ProjectiveCompletion

end

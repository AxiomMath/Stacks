/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyOverRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite

/-!
# The Euler characteristic of a module supported in an open subspace

Let `j : X ⟶ Y` be an open immersion of algebraic spaces over `S`, `N` a quasi-coherent
`𝒪_Y`-module of finite type whose support lies in `X`, and `M` a quasi-coherent `𝒪_Y`-module.
Then the cohomology of `N ⊗ M` on `Y` is that of `j^*N ⊗ j^*M` on `X`; in particular the two
Euler characteristics over a field `k` (along compatible maps `k ⟶ Γ(𝒪)`) agree:

`χ(Y, N ⊗ M) = χ(X, j^*N ⊗ j^*M)`.

The proof passes through the scheme-theoretic support `i : Z ⟶ Y` of `N` (Stacks 05JU, 07U0):
`N ≅ i_*G`, and `Z` lies in `X` because its points are the support of `N`, so `i = j ∘ i'` with
`i' : Z ⟶ X` again a closed immersion, the square `(𝟙, i', i, j)` being cartesian. Then
`j^*N ≅ i'_*G` by affine base change (Stacks 07U8), and by the projection formula and
Stacks 0D2U both Euler characteristics are `χ(Z, G ⊗ i^*M)`.

## Main results

* `AlgebraicGeometry.Space.eulerCharacteristicAlong_tensor_modulePullback_of_isOpenImmersion`:
  `χ(Y, N ⊗ M) = χ(X, j^*N ⊗ j^*M)` for `N` supported in the open subspace `X`.

## References

* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Euler characteristic along a closed immersion, through the projection formula.** For a
closed immersion `i : Z ⟶ Y`, a quasi-coherent `𝒪_Z`-module `G` and a quasi-coherent
`𝒪_Y`-module `M`, `χ(Y, i_*G ⊗ M) = χ(Z, G ⊗ i^*M)`, along `φ ∘ α` on `Y` and `(i ≫ φ) ∘ α` on
`Z`. -/
theorem eulerCharacteristicAlong_tensor_modulePushforward_of_isClosedImmersion
    {Z Y : AlgebraicSpaces B S hS} (i : Z ⟶ Y) (hi : IsClosedImmersion B S hS i.hom)
    {V : BigFppfOver B S hS} (φ : Y.1 ⟶ yoneda.obj V) (k : Type u) [Field k]
    (α : k →+* Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V)))
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite) :
    eulerCharacteristicAlong B S hS Y.1 Y.2 k ((globalSectionsRingHom B S hS Y.1 Y.2 φ).comp α)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
            ((modulePushforward B S hS i).obj G)).obj M) =
      eulerCharacteristicAlong B S hS Z.1 Z.2 k
        ((globalSectionsRingHom B S hS Z.1 Z.2 (i.hom ≫ φ)).comp α)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj G).obj
            ((modulePullback B S hS i).obj M)) := by
  have haff := isAffineHom_of_isClosedImmersion B S hS i.hom hi
  have hrep := relativelyRepresentable_of_isAffineHom B S hS i haff
  have hMqc : ((modulePullback B S hS i).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS i M hM
  have hqc : (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj G).obj
        ((modulePullback B S hS i).obj M)).IsQuasicoherentOnSite :=
    @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite.{u + 1, u, u}
      _ _ (smallEtaleRingedSite B S hS Z.1 Z.2).J _ _ _
      (smallEtaleRingedSite B S hS Z.1 Z.2).O G ((modulePullback B S hS i).obj M) hG hMqc
  refine (eulerCharacteristicAlong_congr _ _ _ _ _ _ _
    (sheafTensorModulePushforwardIso B S hS i hi G M)).trans ?_
  exact (eulerCharacteristicAlong_modulePushforward_of_isAffineHom B S hS i hrep k _ _ haff
    (globalSectionRingHomsCompatible_globalSectionsRingHom B S hS i hrep φ α) _ hqc).symm

/-- **The Euler characteristic of a module supported in an open subspace.** Let `j : X ⟶ Y` be an
open immersion, `N` a quasi-coherent `𝒪_Y`-module of finite type whose support lies in `X` and
`M` a quasi-coherent `𝒪_Y`-module. Then `χ(Y, N ⊗ M) = χ(X, j^*N ⊗ j^*M)`, along `φ ∘ α` on `Y`
and `φX ∘ α` on `X`, for any `φX = j ≫ φ`. -/
theorem eulerCharacteristicAlong_tensor_modulePullback_of_isOpenImmersion
    {X Y : AlgebraicSpaces B S hS} (j : X ⟶ Y) (hj : IsOpenImmersion B S hS j.hom)
    {V : BigFppfOver B S hS} (φ : Y.1 ⟶ yoneda.obj V) (k : Type u) [Field k]
    (α : k →+* Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V)))
    (N : Modules.{u, u} B S hS Y.1 Y.2) (hN : N.IsQuasicoherentOnSite)
    (hNft : SheafOfModules.IsFiniteTypeOnSite N)
    (hsupp : supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj N) ⊆
      Set.range (pointsMap B S hS X.1 j.hom))
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (φX : X.1 ⟶ yoneda.obj V) (hφX : j.hom ≫ φ = φX) :
    eulerCharacteristicAlong B S hS Y.1 Y.2 k ((globalSectionsRingHom B S hS Y.1 Y.2 φ).comp α)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj N).obj M) =
      eulerCharacteristicAlong B S hS X.1 X.2 k
        ((globalSectionsRingHom B S hS X.1 X.2 φX).comp α)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj ((modulePullback B S hS j).obj N)).obj
            ((modulePullback B S hS j).obj M)) := by
  subst hφX
  have hft := Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite N hNft
  obtain ⟨hZ, G, hGqc, ⟨e⟩⟩ := exists_module_on_schemeTheoreticSupport B S hS Y N hN hft
  let Zc : ClosedSubspaces B S hS Y.1 := ⟨schemeTheoreticSupport B S hS Y N, hZ⟩
  let Z := closedSubspaceToSpace B S hS Y Zc
  let i : Z ⟶ Y := closedSubspaceInclusion B S hS Y Zc
  have hi : IsClosedImmersion B S hS i.hom := Zc.2.2
  have hrange : Set.range (pointsMap B S hS Z.1 i.hom) ⊆ Set.range (pointsMap B S hS X.1 j.hom) :=
    (supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS Y N hN hNft) ▸ hsupp
  obtain ⟨g, hg⟩ := (factorsThrough_isOpenImmersion_iff_points B S hS X.2 Y.2 Z.2 j.hom hj
    i.hom).2 hrange
  let i' : Z ⟶ X := ObjectProperty.homMk g
  have hi'j : i' ≫ j = i := ObjectProperty.hom_ext _ hg
  have hjmono : Mono j :=
    (ObjectProperty.ι _).mono_of_mono_map (mono_of_presheaf_isOpenImmersion hj)
  have sq : IsPullback (𝟙 Z) i' i j :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hi'j]⟩
  have hi' : IsClosedImmersion B S hS i'.hom := isClosedImmersion_of_isPullback B S hS sq hi
  have hiaff := isAffineHom_of_isClosedImmersion B S hS i.hom hi
  have hbc := isIso_moduleBaseChangeMap_app_of_isAffineHom sq hiaff G hGqc
  let eN : (modulePullback B S hS j).obj N ≅ (modulePushforward B S hS i').obj G :=
    (modulePullback B S hS j).mapIso e.symm ≪≫ @asIso _ _ _ _ _ hbc ≪≫
      (modulePushforward B S hS i').mapIso ((modulePullbackIdIso B S hS Z).app G)
  let eM : (modulePullback B S hS i').obj ((modulePullback B S hS j).obj M) ≅
      (modulePullback B S hS i).obj M :=
    (modulePullbackTriangle B S hS hi'j).symm.app M
  have hjM : ((modulePullback B S hS j).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS j M hM
  refine (eulerCharacteristicAlong_congr _ _ _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS Y.1 Y.2).O).mapIso e.symm).app M)).trans ?_
  refine (eulerCharacteristicAlong_tensor_modulePushforward_of_isClosedImmersion B S hS i hi φ k α
    G hGqc M hM).trans ?_
  refine Eq.trans ?_ (eulerCharacteristicAlong_congr _ _ _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS X.1 X.2).O).mapIso eN).app _)).symm
  refine Eq.trans ?_ (eulerCharacteristicAlong_tensor_modulePushforward_of_isClosedImmersion B S hS
    i' hi' (j.hom ≫ φ) k α G hGqc _ hjM).symm
  have hφ : i'.hom ≫ j.hom ≫ φ = i.hom ≫ φ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) hg)
  rw [hφ]
  exact eulerCharacteristicAlong_congr _ _ _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj G).mapIso eM.symm)

end AlgebraicGeometry.Space

end

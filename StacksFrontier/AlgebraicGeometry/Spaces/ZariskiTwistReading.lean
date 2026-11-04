module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceTwistFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwist
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict

/-!
# Twists, read on a scheme over an algebraic space

Let `p : h_U ⟶ X` be a morphism from (the space of) a scheme `U` to an algebraic space, `ℒ` an
`𝒪_X`-module and `M` an `𝒪_X`-module.  The iterated twist `M ⊗ ℒ^{⊗ d}` of
`AlgebraicGeometry.Space.twistPowFunctor` is compatible with inverse image along `p`, and, for
quasi-coherent modules, with the restriction to the Zariski site of `U`, where it becomes the
twist `(M|_U) ⊗ (ℒ|_U)^{⊗ d}` by the tensor powers `Stacks.Ample.tensorPowModule` of the
ampleness theory of schemes.

This is how the cohomology of the twists `𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ ⊗ ℒ^{⊗ d}` on `X` is read on the fibre `X_y`
in the proof of Stacks 0D39.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackTwistPowIso`: `p^*(M ⊗ ℒ^{⊗ d}) ≅ p^*M ⊗ (p^*ℒ)^{⊗ d}`.
* `AlgebraicGeometry.Space.zariskiModuleTwistPowSuccIso`:
  `(N ⊗ ℒ'^{⊗ (d+1)})|_U ≅ N|_U ⊗ (ℒ'|_U)^{⊗ (d+1)}` for quasi-coherent `N`, `ℒ'` on `h_U`
  with `ℒ'|_U` invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Inverse image -/

section Pullback

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (L : Modules.{u, u} B S hS Y.1 Y.2)

/-- Inverse image commutes with one twist. -/
def modulePullbackTwistIso (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).obj ((modulesTensorRightFunctor L).obj M) ≅
      (modulesTensorRightFunctor ((modulePullback B S hS f).obj L)).obj
        ((modulePullback B S hS f).obj M) :=
  (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS f)).app (M, L)

/-- **Inverse image commutes with the iterated twists.** -/
def modulePullbackTwistPowIso (M : Modules.{u, u} B S hS Y.1 Y.2) : ∀ d,
    (modulePullback B S hS f).obj ((twistPowFunctor L d).obj M) ≅
      (twistPowFunctor ((modulePullback B S hS f).obj L) d).obj ((modulePullback B S hS f).obj M)
  | 0 => Iso.refl _
  | d + 1 => eqToIso (congrArg (modulePullback B S hS f).obj (twistPowFunctor_obj_succ L M d)) ≪≫
      modulePullbackTwistIso f L ((twistPowFunctor L d).obj M) ≪≫
      (modulesTensorRightFunctor ((modulePullback B S hS f).obj L)).mapIso
        (modulePullbackTwistPowIso M d) ≪≫
      eqToIso (twistPowFunctor_obj_succ _ _ d).symm

end Pullback

/-! ### Restriction to the Zariski site of a scheme -/

section Zariski

variable (U : BigFppfOver B S hS)

/-- A twist of a quasi-coherent module by a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_twistFunctor_obj
    {X : AlgebraicSpaces B S hS} (N L' : Modules.{u, u} B S hS X.1 X.2)
    (hN : N.IsQuasicoherentOnSite) (hL : L'.IsQuasicoherentOnSite) :
    ((modulesTensorRightFunctor L').obj N).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_sheafTensor
    (X := smallEtaleRingedSite B S hS X.1 X.2) N L' hN hL

/-- Every iterated twist `N ⊗ ℒ'^{⊗ d}` of a quasi-coherent module `N` by a quasi-coherent
module `ℒ'` is quasi-coherent. -/
theorem isQuasicoherentOnSite_twistPowFunctor_obj
    {X : AlgebraicSpaces B S hS} (N L' : Modules.{u, u} B S hS X.1 X.2)
    (hN : N.IsQuasicoherentOnSite) (hL : L'.IsQuasicoherentOnSite) :
    ∀ d, ((twistPowFunctor L' d).obj N).IsQuasicoherentOnSite
  | 0 => hN
  | d + 1 => by
    rw [twistPowFunctor_obj_succ]
    exact isQuasicoherentOnSite_twistFunctor_obj _ L'
      (isQuasicoherentOnSite_twistPowFunctor_obj N L' hN hL d) hL

attribute [local instance] modulesMonoidalCategory

/-- The restriction to the Zariski site of `U` of a module on `h_U`, as a functor. -/
abbrev zariskiFunctor :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (idEtaleChart B S hS U)

/-- **One twist, read on the Zariski site of `U`**: for quasi-coherent `N` and `ℒ'` on `h_U`,
`(N ⊗ ℒ')|_U ≅ N|_U ⊗ ℒ'|_U`. -/
def zariskiModuleTwistIso
    (N L' : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) (hL : L'.IsQuasicoherentOnSite) :
    (zariskiFunctor U).obj
      ((modulesTensorRightFunctor (X := representedAlgebraicSpace B S hS U) L').obj N) ≅
      tensorModules ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U N)
        (zariskiModule U L') :=
  (zariskiFunctor U).mapIso
      (eqToIso (modulesTensorRightFunctor_obj (X := representedAlgebraicSpace B S hS U) L' N) ≪≫
        (modulesTensorObjIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) N L').symm) ≪≫
    restrictToChartSchemeIdEtaleChartTensorIso B S hS U N L' hN hL

/-- **The iterated twists, read on the Zariski site of `U`**: for quasi-coherent `N` and
`ℒ'` on `h_U` with `ℒ'|_U` invertible, `(N ⊗ ℒ'^{⊗ (d+1)})|_U ≅ N|_U ⊗ (ℒ'|_U)^{⊗ (d+1)}`. -/
def zariskiModuleTwistPowSuccIso
    (N L' : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) (hL : L'.IsQuasicoherentOnSite)
    [IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')] : ∀ d : ℕ,
    (zariskiFunctor U).obj
        ((twistPowFunctor (X := representedAlgebraicSpace B S hS U) L' (d + 1)).obj N) ≅
      tensorModules ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U N)
        (tensorPowModule ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')
          ((d + 1 : ℕ) : ℤ))
  | 0 =>
    (zariskiFunctor U).mapIso
        (eqToIso (twistPowFunctor_obj_succ (X := representedAlgebraicSpace B S hS U) L' N 0)) ≪≫
      zariskiModuleTwistIso U N L' hN hL ≪≫
      tensorModulesMapIso ((BigFppfOver.toScheme B S hS).obj U) (Iso.refl (zariskiModule U N))
        ((tensorPowModuleOneIso ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')).symm ≪≫
          tensorPowModuleCongr ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')
            (by norm_num : (1 : ℤ) = ((0 + 1 : ℕ) : ℤ)))
  | d + 1 =>
    (zariskiFunctor U).mapIso
        (eqToIso
          (twistPowFunctor_obj_succ (X := representedAlgebraicSpace B S hS U) L' N (d + 1))) ≪≫
      zariskiModuleTwistIso U _ L'
        (isQuasicoherentOnSite_twistPowFunctor_obj
          (X := representedAlgebraicSpace B S hS U) N L' hN hL (d + 1)) hL ≪≫
      tensorModulesMapIso ((BigFppfOver.toScheme B S hS).obj U)
        (zariskiModuleTwistPowSuccIso N L' hN hL d) (Iso.refl (zariskiModule U L')) ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator ((BigFppfOver.toScheme B S hS).obj U)
        (zariskiModule U N)
        (tensorPowModule ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')
          ((d + 1 : ℕ) : ℤ))
        (zariskiModule U L') ≪≫
      tensorModulesMapIso ((BigFppfOver.toScheme B S hS).obj U) (Iso.refl (zariskiModule U N))
        (tensorModulesMapIso ((BigFppfOver.toScheme B S hS).obj U) (Iso.refl _)
          (tensorPowModuleOneIso ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')).symm ≪≫
          tensorPowModuleAddIso ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')
            ((d + 1 : ℕ) : ℤ) 1 ≪≫
          tensorPowModuleCongr ((BigFppfOver.toScheme B S hS).obj U) (zariskiModule U L')
            (by push_cast; ring : ((d + 1 : ℕ) : ℤ) + 1 = ((d + 1 + 1 : ℕ) : ℤ)))

end Zariski

end AlgebraicGeometry.Space

end

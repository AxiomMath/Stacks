module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.FlatBaseChangeAcyclic

/-!
# Flat base change along an affine morphism of algebraic spaces

Let

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

be a cartesian square of algebraic spaces over a scheme `S` with `g` flat, and let `ℱ` be a
quasi-coherent `𝒪_X`-module with pullback `ℱ' = (g')^*ℱ`.  When `f` is affine, `ℱ` has no
higher direct images along `f` and `ℱ'` none along the affine morphism `f'` (**Stacks 073H**,
**Stacks 03WI**).  So both total direct images are computed by the ordinary ones, and the base
change map `g^*Rf_*ℱ ⟶ Rf'_*ℱ'` of **Stacks 0736** at `ℱ[0]` is invertible as soon as the
ordinary base change map `g^*f_*ℱ ⟶ f'_*ℱ'` is.  This is the case of **Stacks 073K**, part (1),
in which `f` is affine, reduced to degree zero.

## Main results

* `AlgebraicGeometry.Space.rightAcyclic_pushforwardModules_of_isAffineHom`: a quasi-coherent
  module is acyclic for the direct image along an affine morphism.
* `AlgebraicGeometry.Space.BaseChangeDiagram.isIso_baseChangeMap_app_single_of_isAffineHom`:
  for `f` affine, the base change map is invertible at `ℱ[0]` when the ordinary base change map
  is invertible at `ℱ`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules (pushforwardModules)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Along an affine morphism -/

/-- **A quasi-coherent module is acyclic for the direct image along an affine morphism**, in the
spelling of the direct image of the morphism of small étale ringed topoi that the base change
map consumes.  Its higher direct images vanish by **Stacks 073H**, and the two spellings of the
direct image are isomorphic by **Stacks 03LU**. -/
theorem rightAcyclic_pushforwardModules_of_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    (pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom).rightAcyclic F := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have := modulePushforward_additive B S hS f
  have hadd := additive_pushforwardModules_smallEtaleRingedToposHom B S hS f
  have hlim : PreservesFiniteLimits (pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom) :=
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).rightAdjoint_preservesLimits.{0, 0}
      |>.preservesFiniteLimits
  have hrep := relativelyRepresentable_of_isAffineHom B S hS f hf
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived
    (pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom) F).2 fun p hp => ?_
  have := Functor.additive_of_iso (modulePushforwardIso B S hS f)
  exact (isZero_rightDerived_modulePushforward_of_chartwise B S hS f hrep F p
    (chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f hf hrep F hF p hp)).of_iso
    ((Functor.rightDerivedIsoOfNatIso (modulePushforwardIso B S hS f) p).app F)

variable {B S hS}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-- **The base change map is invertible at the coefficient along an affine morphism, as soon as
the underived base change map is.**  For `f` affine the coefficient `ℱ` and its inverse image
`ℱ' = (g')^*ℱ`, both quasi-coherent, are acyclic for `f_*` and `f'_*` (**Stacks 073H**; `f'` is
affine by **Stacks 03WI**), so `Rf_*ℱ = f_*ℱ` and `Rf'_*ℱ' = f'_*ℱ'` and the base change map at
`ℱ[0]` is the underived one. -/
theorem isIso_baseChangeMap_app_single_of_isAffineHom (hg : IsFlat B S hS D.g.hom)
    (hf : IsAffineHom B S hS D.f.hom)
    (hτ : IsIso ((Stacks.Cohomology.ToposBaseChange.moduleBaseChange
      (smallEtaleRingedToposHom B S hS D.f) (smallEtaleRingedToposHom B S hS D.f')
      (smallEtaleRingedToposHom B S hS D.g) (smallEtaleRingedToposHom B S hS D.g')
      D.directImageSquareIso).app D.F)) :
    IsIso ((D.baseChangeMap hg).app
      ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS D.X.1 D.X.2) 0).obj D.F)) :=
  Stacks.Cohomology.ToposBaseChange.isIso_baseChangeMap_app_single_of_rightAcyclic
    (smallEtaleRingedToposHom B S hS D.f) (smallEtaleRingedToposHom B S hS D.f')
    (smallEtaleRingedToposHom B S hS D.g) (smallEtaleRingedToposHom B S hS D.g')
    D.directImageSquareIso (D.isFlat_smallEtaleRingedToposHom_base hg)
    (D.isFlat_smallEtaleRingedToposHom_source hg) D.F
    (rightAcyclic_pushforwardModules_of_isAffineHom B S hS D.f hf D.F inferInstance) hτ
    (rightAcyclic_pushforwardModules_of_isAffineHom B S hS D.f'
      (IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ D.isPullback) hf)
      D.pulledBack
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.g' D.F
        inferInstance))

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

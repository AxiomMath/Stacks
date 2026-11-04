module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartObstruction
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCoefficientOfIdeal
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.CoefficientMap
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningIdealTilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor

/-!
# The coefficient of the obstruction of an object of `Coh_{X/B}` over a chart

For an object `x` of `Coh_{X/Y}` over `Spec A`, with `Y` final, and a square-zero thickening
`A' → A` with kernel `I`, the obstruction to lifting `x` to `A'` lives, on `X_A`, in
`Ext²(ℱ, f̃^*t̃^*𝒥̃ ⊗ ℱ)`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningObstructionOnBase`). This file identifies
the coefficient `f̃^*t̃^*𝒥̃ ⊗ ℱ` with `ℱ ⊗ p^*Ĩ`, the coefficient of the groups
`AlgebraicGeometry.Space.CoherentSituation.extGroup`, through `f̃^*t̃^*𝒥̃ ≅ p^*t^*𝒥`
(`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`), `t^*𝒥 ≅ J^~`
(`AlgebraicGeometry.Space.thickeningIdealTildeIso`), `J ≅ I`
(`AlgebraicGeometry.Space.CoherentSituation.kernelModuleIso`) and the symmetry of `⊗`.

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (hY : IsTerminal D.Y)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  {A' : Type u} [CommRing A'] (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A')

/-- The pullback of modules along `X_T ⟶ T` of the relative square is the one along the
projection to the represented test scheme. -/
theorem projection_toModulesHom_eq_baseProjection (x : CoherentObject D) :
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection x.T)).toModulesHom =
      @id (Stacks.Sheaves.RingedToposModules.RingedToposHom
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)))
        (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom :=
  rfl

/-- The two readings of the pullback of modules along `X_T ⟶ T`. -/
theorem toRingedToposModulesHom_eq_baseProjection (x : CoherentObject D) :
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom =
      @id (Stacks.Sheaves.RingedToposModules.RingedToposHom
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)))
        (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom :=
  (smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom_eq_toModulesHom.trans
      (projection_toModulesHom_eq_baseProjection x)

/-- **The kernel of `Γ(Spec A') ⟶ Γ(Spec A)` is the kernel of `A' → A`**, as a module over the
ring of the test scheme of `x` read through `D.chartRingEquiv x hx`. -/
def chartKernelIso :
    testKernelModule hx T (D.isFirstOrderThickening_thickeningTestMap hY x hx T) ≅
      D.baseModule x (D.chartRingEquiv x hx) T.kernel :=
  kernelModuleIso hx T (D.isFirstOrderThickening_thickeningTestMap hY x hx T)

/-- The test scheme of a square-zero thickening is affine. -/
instance isAffine_thickeningTestScheme :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (D.thickeningTestScheme hY T).left) :=
  isAffine_thickeningOver T

/-- **`p^*t^*𝒥 ≅ p^*Ĩ`** for the thickening `Spec A ⊂ Spec A'` of test schemes. -/
def testSchemeIdealIso :=
  ((smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).mapIso
    (thickeningIdealTildeIso (D.thickeningTestMap hY x hx T).left
        (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T))
        (isFirstOrderThickening_range_yoneda_map B S hS _
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx T) ≪≫
      (representedAffineAssociated B S hS x.T.left).mapIso (chartKernelIso hY hx T))

/-- **`f̃^*t̃^*𝒥̃ ≅ p^*t^*𝒥`** (`relativeSquareBasePullbackIdealIso`), with `t^*𝒥` written as the
pulled-back ideal of the first order thickening of small étale ringed topoi of `Spec A ⊂ Spec A'`
(the spelling of `AlgebraicGeometry.Space.thickeningIdealTildeIso`). -/
def relativeSquareTestIdealIso :
    D.relativeSquareSituation.relativeSquareBasePullbackIdeal (D.thickeningTestMap hY x hx T)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx T) ≅
      ((smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).obj
        ((smallEtaleRingedToposHom B S hS
          ((schemeSpaceFunctor B S hS).map
            (D.thickeningTestMap hY x hx T).left)).toRingedToposModulesHom.pullbackModules.obj
          (smallEtaleRingedToposHomFirstOrderThickening B S hS
            ((schemeSpaceFunctor B S hS).map (D.thickeningTestMap hY x hx T).left)
            (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T))
            (isFirstOrderThickening_range_yoneda_map B S hS _
              (D.isFirstOrderThickening_thickeningTestMap hY x hx T))).idealOfThickening.I) :=
  D.relativeSquareSituation.relativeSquareBasePullbackIdealIso _ _

/-- **The coefficient of the obstruction is the coefficient of `extGroup`**:
`f̃^*t̃^*𝒥̃ ⊗ ℱ ≅ ℱ ⊗ p^*Ĩ`. -/
def chartObstructionCoefficientIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
        (objectToposModule x)).obj
        (D.relativeSquareSituation.relativeSquareBasePullbackIdeal (D.thickeningTestMap hY x hx T)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T)) ≅
      D.extCoefficient x (D.chartRingEquiv x hx) T.kernel :=
  D.coefficientIsoOfIdealAt x (D.chartRingEquiv x hx) _ _
    (toRingedToposModulesHom_eq_baseProjection x)
    (relativeSquareTestIdealIso hY hx T ≪≫ testSchemeIdealIso hY hx T)

section Obstruction

variable (hflat : IsFlat B S hS D.f.hom)
  [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx T))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))]
  [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS
      (D.relativeSquareSituation.space (D.thickeningTestScheme hY T))).O))]
  [HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)]

/-- **The obstruction to lifting `x` across `A' → A`, in `Ext²_{X_A}(ℱ, ℱ ⊗ f^*Ĩ)`.** -/
def chartObstruction : D.extGroup x (D.chartRingEquiv x hx) T.kernel 2 :=
  letI : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  letI : EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (EnoughInjectives (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) T.kernel 2).symm
    (extCompIsoAddEquiv (chartObstructionCoefficientIso hY hx T) 2
      (thickeningObstructionOnBase (D.thickeningTestMap hY x hx T)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx T)
        (D.isFlat_projection_of_isFlat hflat _)))

/-- **`x` lifts across `A' → A` exactly when its obstruction vanishes** (Stacks 08VW, part (1)). -/
theorem nonempty_fiber_iff_chartObstruction_eq_zero :
    Nonempty ((Under.post (coherentCFG D).val.p).Fiber (Under.mk (eqToHom hx ≫ T.arrow))) ↔
      chartObstruction hY hx T hflat = 0 := by
  let : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  let : EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (EnoughInjectives (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  refine (nonempty_fiber_iff_nonempty_thickeningLift hY).trans
    ((nonempty_thickeningLift_iff_thickeningObstructionOnBase_eq_zero _
      (D.isFirstOrderThickening_thickeningTestMap hY x hx T)
      (D.isFlat_projection_of_isFlat hflat _)).trans ?_)
  refine (map_eq_zero_iff (extCompIsoAddEquiv (chartObstructionCoefficientIso hY hx T) 2)
    (extCompIsoAddEquiv (chartObstructionCoefficientIso hY hx T) 2).injective).symm.trans ?_
  exact (map_eq_zero_iff (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) T.kernel 2).symm
    (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) T.kernel 2).symm.injective).symm

end Obstruction

end AlgebraicGeometry.Space.CoherentSituation

end

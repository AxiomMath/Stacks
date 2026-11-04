module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartData
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartCoefficientNaturality

/-!
# Naturality of the transport of obstruction classes over a chart

For an object `x = (Spec A, ℱ)` of `Coh_{X/B}` over a chart, the obstruction class
`o(A' → A) ∈ Ext²_{X_A}(ℱ, ℱ ⊗ f^*Ĩ)` of Stacks 08VW, part (1)
(`AlgebraicGeometry.Space.CoherentSituation.chartObstruction`) is the transport, through the
coefficient isomorphism `AlgebraicGeometry.Space.CoherentSituation.chartObstructionCoefficientIso`,
of an `Ext²` class with coefficients in the pulled-back ideal of the relative square of the test
map. This transport of `Ext²` classes is natural along morphisms of square-zero thickenings
`A₁' → A₂'`: the map `I₁ ⟶ I₂` carries the transport of a class to the transport of its image
under the map of pulled-back ideals.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.extGroupMap_obstructionTransport`: the naturality of
  the transport in the thickening.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

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
  {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
  {T₁ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₁}
  {T₂ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₂}
  (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂)

section Transport

variable [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O))]
  [HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)]

/-- **The transport of `Ext²` classes to the `Ext` groups of `x` is natural in the thickening.** -/
theorem extGroupMap_obstructionTransport
    (z : Abelian.Ext.{u + 1} (objectToposModule x)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
          (objectToposModule x)).obj (D.relativeSquareSituation.relativeSquareBasePullbackIdeal
            (D.thickeningTestMap hY x hx T₁)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))) 2) :
    D.extGroupMap x (D.chartRingEquiv x hx) f.kernelMap 2
        ((D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) T₁.kernel 2).symm
          (z.comp (Abelian.Ext.mk₀ (chartObstructionCoefficientIso hY hx T₁).hom) (add_zero 2))) =
      (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) T₂.kernel 2).symm
        ((z.comp (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
              (objectToposModule x)).map ((relativeSquareTestIdealIso hY hx T₁).hom ≫
                ((smallEtaleRingedToposHom B S hS
                  (D.relativeSquareSituation.projection
                    x.T)).toRingedToposModulesHom.pullbackModules).map
                (thickeningIdealMap (D.thickeningTestMap hY x hx T₁).left
                  (D.thickeningTestMap hY x hx T₂).left (D.thickeningTestSchemeMap hY f).left
                  (left_comp_left_eq_of_comp_eq (D.thickeningTestSchemeMap hY f)
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f))
                  (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₁)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
                  (isFirstOrderThickening_range_yoneda_map B S hS _
                    (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
                  (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₂)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
                  (isFirstOrderThickening_range_yoneda_map B S hS _
                    (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
                  (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
                  (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂)) ≫
                (relativeSquareTestIdealIso hY hx T₂).inv))) (add_zero 2)).comp
          (Abelian.Ext.mk₀ (chartObstructionCoefficientIso hY hx T₂).hom) (add_zero 2)) := by
  apply (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) T₂.kernel 2).injective
  refine (D.extGroupAbelianExtEquiv_extGroupMap x (D.chartRingEquiv x hx) f.kernelMap 2 _).trans ?_
  refine (congrArg (fun w => Abelian.Ext.comp w
    (Abelian.Ext.mk₀ (D.extCoefficientModuleMap x (D.chartRingEquiv x hx) f.kernelMap))
    (add_zero 2))
    (AddEquiv.apply_symm_apply _ _)).trans (Eq.trans ?_ (AddEquiv.apply_symm_apply _ _).symm)
  exact (Abelian.Ext.comp_mk₀_comp_mk₀_of_comp_eq z _ _ _ _
    ((chartObstructionCoefficientIso_hom_naturality hY hx f).trans
      (congrArg ((chartObstructionCoefficientIso hY hx T₁).hom ≫ ·)
        (sheafTensor_map_eq_extCoefficientModuleMap hx f.kernelMap)))).symm

end Transport

end AlgebraicGeometry.Space.CoherentSituation

end

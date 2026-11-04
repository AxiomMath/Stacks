module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.RetractionExt
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareIdeal
public import StacksFrontier.Homology.Ext.MapExactFunctorComp

/-!
# Lifts of an object of `Coh_{X/Y}` across a split first order thickening, as `Ext¹` on `X_T`

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` a first order
thickening of schemes over `Y` with a retraction `r : T' ⟶ T` (`h ≫ r = 𝟙`), and assume
`X_{T'} ⟶ T'` flat. By Stacks 08VW, part (2), the isomorphism classes of lifts of `ξ` across `h`
are a principal homogeneous set under `Ext¹(𝒢, f^*𝒥 ⊗ 𝒢)`, and measuring the difference from the
trivial lift `r^*𝒢` identifies them with that group. This file reads the group on `X_T` itself:
`Ext¹_{𝒪_{X_T}}(𝒢, 𝒢 ⊗ f_T^*𝒥)`. A lift `𝒢'` gives the extension
`0 ⟶ 𝒢 ⊗ f^*𝒥 ⟶ 𝒢' ⟶ 𝒢 ⟶ 0` of `𝒪_{X_{T'}}`-modules (Stacks 08MQ), and pushing it forward along
the retraction `ρ : X_{T'} ⟶ X_T` gives an extension of `𝒪_{X_T}`-modules; its class, minus the
class of the trivial lift, is the difference. This is the computation `T_x(M) = Ext¹(𝒢, 𝒢 ⊗ M)`
of the proofs of Stacks 08W8 and Stacks 08WA.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficient`: the module `𝒢 ⊗ f_T^*𝒥` on
  `X_T`.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass`: the class on `X_T` of the
  extension attached to a lift.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e u

namespace Stacks.Homology

universe w v₁ u₁

/-- Conjugating `Ext`-classes by isomorphisms is bijective: conjugation by the inverses undoes it
(`Stacks.Homology.extConj_extConj`). -/
theorem bijective_extConj_of_iso {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
    {X' X Y Y' : C} (a : X' ≅ X) (b : Y ≅ Y') (n : ℕ) :
    Function.Bijective (fun x : Abelian.Ext.{w} X Y n => extConj a.hom b.hom x) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y => extConj a.inv b.inv y, fun x => ?_, fun y => ?_⟩ <;>
  simp only [extConj_extConj, Iso.hom_inv_id, Iso.inv_hom_id, extConj_id]

/-- Conjugating the zero class gives zero. -/
theorem extConj_zero {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
    {X' X Y Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℕ) :
    extConj a b (0 : Abelian.Ext.{w} X Y n) = 0 :=
  (extConjHom a b n).map_zero

end Stacks.Homology

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- `T ⟶ T'` is an isomorphism onto its image subfunctor, for a first order thickening `h`. -/
theorem isIso_toRange_testSchemeMap {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left)) :
    IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h.left).hom) :=
  have : Mono ((schemeSpaceFunctor B S hS).map h.left).hom :=
    mono_yoneda_map_of_isClosedImmersion h.left hh.1
  inferInstance

/-- **The module `f_T^*𝒥`** on `X_T`: the ideal `𝒥` of the first order thickening `T ⊂ T'` of
small étale ringed topoi, pulled back to `T` and then along `X_T ⟶ T`. -/
abbrev thickeningTestIdeal (ξ : CoherentObject D) {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O) :=
  ((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection ξ.T)).toRingedToposModulesHom.pullbackModules).obj
    ((smallEtaleRingedToposHom B S hS
      ((schemeSpaceFunctor B S hS).map h.left)).toRingedToposModulesHom.pullbackModules.obj
      (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h.left)
        (isIso_toRange_testSchemeMap h hh)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh)).idealOfThickening.I)

/-- **The coefficient module `𝒢 ⊗ f_T^*𝒥`** on `X_T` of the deformations of `ξ = (T, 𝒢)` across a
first order thickening `h : T ⟶ T'` with ideal `𝒥`: the tensor product of `𝒢` with the pullback
`f_T^*𝒥` of `𝒥` along `X_T ⟶ T`. -/
abbrev thickeningCoefficient (ξ : CoherentObject D) {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
      (objectToposModule ξ)).obj (thickeningTestIdeal ξ h hh)

variable {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T') (r : T' ⟶ ξ.T)
  (hr : h ≫ r = 𝟙 ξ.T)
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hfl : IsFlat B S hS (D.projection T').hom)

/-- The module `𝒢`, read on `X_T` from its direct image `i_*𝒢`: `ρ_* i_* 𝒢 ≅ 𝒢`. -/
def thickenedModuleRetractionIso :
    (thickenedRetraction h r).obj (thickenedModule ξ h) ≅ objectToposModule ξ :=
  (thickenedRetractionIso h r hr).app (objectToposModule ξ)

/-- `f^*𝒥 ⊗ i_*𝒢 ≅ i_*(𝒢 ⊗ f^*𝒥)` (projection formula). -/
def thickeningKernelIsoB :=
  pushforwardModuleTensorIso (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (objectToposModule ξ) (D.relativeSquareSituation.relativeSquareBasePullbackIdeal h hh)

include hfl in
/-- `I ⊗ i_*𝒢 ≅ i_*(𝒢 ⊗ f^*𝒥)` on the thickened presentation. -/
def thickeningKernelThickenedIso :=
  (thickeningLiftDifferenceIso h hh hfl).symm ≪≫ thickeningKernelIsoB h hh

/-- `f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥`: the pulled-back ideal of the relative square is the pullback of the
ideal of `T ⊂ T'`
(`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`). -/
def relativeSquareThickeningTestIdealIso :
    D.relativeSquareSituation.relativeSquareBasePullbackIdeal h hh ≅ thickeningTestIdeal ξ h hh :=
  D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h hh

/-- `𝒢 ⊗ f^*𝒥 ≅ 𝒢 ⊗ f_T^*𝒥`, from the identification of the pulled-back ideal of the relative
square with the pullback of the ideal of `T ⊂ T'`. -/
def thickeningCoefficientIso :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
      (objectToposModule ξ)).mapIso (relativeSquareThickeningTestIdealIso h hh)

include hfl in
/-- **The kernel of the extension attached to a lift, read on `X_T`, is `𝒢 ⊗ f_T^*𝒥`.** On the
thickened presentation the kernel `I ⊗ i_*𝒢` is `f^*𝒥 ⊗ i_*𝒢` (Stacks 08MQ, through
`Deformation.ToposThickening.basePullbackIdealTensorIso`), which is `i_*(𝒢 ⊗ f^*𝒥)` (projection
formula, `Deformation.ToposThickening.pushforwardModuleTensorIso`); reading on `X_T` undoes `i_*`,
and `f^*𝒥` of the relative square is `f_T^*𝒥`
(`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`). -/
def thickeningKernelRetractionIso :
    (thickenedRetraction h r).obj (thickeningKernel h hh hfl) ≅ thickeningCoefficient ξ h hh :=
  (thickenedRetraction h r).mapIso (thickeningKernelThickenedIso h hh hfl) ≪≫
    (thickenedRetractionIso h r hr).app _ ≪≫ thickeningCoefficientIso h hh

variable [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

attribute [local instance] preservesFiniteColimits_structureRestrict_relativeMap
  preservesFiniteLimits_structureRestrict_relativeMap

/-- **The class on `X_T` of the extension attached to a lift**: the image under `ρ_*` of the
class of `0 ⟶ I ⊗ 𝒢 ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0`, read through `ρ_* i_* 𝒢 ≅ 𝒢` and
`ρ_*(I ⊗ 𝒢) ≅ 𝒢 ⊗ f_T^*𝒥`, in `Ext¹_{𝒪_{X_T}}(𝒢, 𝒢 ⊗ f_T^*𝒥)`. -/
def thickeningLiftExtClass (L : D.ThickeningLift ξ h) :
    Abelian.Ext.{e} (objectToposModule ξ) (thickeningCoefficient ξ h hh) 1 :=
  Stacks.Homology.extConj (thickenedModuleRetractionIso h r hr).inv
    (thickeningKernelRetractionIso h r hr hh hfl).hom
    (retractionExt h r hr hh (thickeningLiftExtensionClass h hh hfl L))

/-- **The group of Stacks 08VW, part (2), read on `X_T`**: a class `a` of
`Ext¹_{i_*𝒪_{X_T}}(i_*𝒢, f^*𝒥 ⊗ i_*𝒢)`, carried to `Ext¹(i_*𝒢, I ⊗ i_*𝒢)` along
`f^*𝒥 ⊗ 𝒢 = I ⊗ 𝒢` (Stacks 08MQ), read on `X_T` by the exact equivalence
`AlgebraicGeometry.Space.CoherentSituation.thickenedRetraction` and through `ρ_* i_* 𝒢 ≅ 𝒢` and
`ρ_*(I ⊗ 𝒢) ≅ 𝒢 ⊗ f_T^*𝒥`. It is the composite of three bijections. -/
def thickeningLiftDifferenceEquiv :
    type_of% (thickeningLiftDifferenceTopos h r hr hh hfl
      (Quotient.mk _ (trivialThickeningLift h r hr))) ≃
      Abelian.Ext.{e} (objectToposModule ξ) (thickeningCoefficient ξ h hh) 1 :=
  (extCompIsoAddEquiv (A := thickenedModule ξ h) (thickeningLiftDifferenceIso h hh hfl)
      1).toEquiv.trans
    ((Equiv.ofBijective _ (bijective_thickenedRetractionExt h r hr hh (thickenedModule ξ h)
      (thickeningKernel h hh hfl))).trans
      (Equiv.ofBijective _ (Stacks.Homology.bijective_extConj_of_iso
        (thickenedModuleRetractionIso h r hr).symm
        (thickeningKernelRetractionIso h r hr hh hfl) 1)))

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))] in
/-- The value of `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifferenceEquiv`. -/
theorem thickeningLiftDifferenceEquiv_apply
    (a : type_of% (thickeningLiftDifferenceTopos h r hr hh hfl
      (Quotient.mk _ (trivialThickeningLift h r hr)))) :
    thickeningLiftDifferenceEquiv h r hr hh hfl a =
      Stacks.Homology.extConj (thickenedModuleRetractionIso h r hr).inv
        (thickeningKernelRetractionIso h r hr hh hfl).hom
        (thickenedRetractionExt h r hr hh
          (a.comp (Abelian.Ext.mk₀ (thickeningLiftDifferenceIso h hh hfl).hom) (add_zero 1))) :=
  rfl

/-- The value of `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifferenceEquiv`, read
through restriction of scalars to `𝒪_{X_{T'}}` and `ρ_*`
(`AlgebraicGeometry.Space.CoherentSituation.retractionExt_mapExtAddHom`). -/
theorem thickeningLiftDifferenceEquiv_apply'
    (a : type_of% (thickeningLiftDifferenceTopos h r hr hh hfl
      (Quotient.mk _ (trivialThickeningLift h r hr)))) :
    thickeningLiftDifferenceEquiv h r hr hh hfl a =
      Stacks.Homology.extConj (thickenedModuleRetractionIso h r hr).inv
        (thickeningKernelRetractionIso h r hr hh hfl).hom
        (retractionExt h r hr hh
          ((structureRestrict (smallEtaleRingedToposHom B S hS
              (D.relativeSquareSituation.relativeMap h))).mapExtAddHom.{e, e} _ _ 1
            (a.comp (Abelian.Ext.mk₀ (thickeningLiftDifferenceIso h hh hfl).hom) (add_zero 1)))) :=
  (congrArg (Stacks.Homology.extConj (thickenedModuleRetractionIso h r hr).inv
    (thickeningKernelRetractionIso h r hr hh hfl).hom)
    (retractionExt_mapExtAddHom h r hr hh _)).symm

/-- **The class on `X_T` of a lift is that of the trivial lift plus the difference**, read on
`X_T` (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtensionClass_eq`). -/
theorem thickeningLiftExtClass_eq (L : D.ThickeningLift ξ h) :
    thickeningLiftExtClass h r hr hh hfl L =
      thickeningLiftDifferenceEquiv h r hr hh hfl
          (thickeningLiftDifferenceTopos h r hr hh hfl (Quotient.mk _ L)) +
        thickeningLiftExtClass h r hr hh hfl (trivialThickeningLift h r hr) := by
  refine (congrArg (fun x => Stacks.Homology.extConj (thickenedModuleRetractionIso h r hr).inv
    (thickeningKernelRetractionIso h r hr hh hfl).hom (retractionExt h r hr hh x))
    (thickeningLiftExtensionClass_eq h r hr hh hfl L)).trans ?_
  refine ((congrArg (Stacks.Homology.extConj (thickenedModuleRetractionIso h r hr).inv
    (thickeningKernelRetractionIso h r hr hh hfl).hom) (retractionExt_add h r hr hh _ _)).trans
    (Stacks.Homology.extConj_add _ _ _ _)).trans ?_
  exact congrArg (· + _) (thickeningLiftDifferenceEquiv_apply' h r hr hh hfl _).symm

/-- **The isomorphism classes of lifts of `ξ` across a split first order thickening are
`Ext¹_{𝒪_{X_T}}(𝒢, 𝒢 ⊗ f_T^*𝒥)`** (Stacks 08VW, part (2), read on `X_T`). The class of a lift
goes to its difference from the trivial lift `r^*𝒢`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifferenceTopos`), read on `X_T` through
the retraction; it is the class on `X_T` of its extension minus that of the trivial lift
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_mk`). -/
def thickeningLiftDifference :
    D.ThickeningLiftClass ξ h ≃
      Abelian.Ext.{e} (objectToposModule ξ) (thickeningCoefficient ξ h hh) 1 :=
  (thickeningLiftDifferenceTopos h r hr hh hfl).trans (thickeningLiftDifferenceEquiv h r hr hh hfl)

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))] in
/-- `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifferenceEquiv` sends `0` to `0`. -/
theorem thickeningLiftDifferenceEquiv_zero :
    thickeningLiftDifferenceEquiv h r hr hh hfl 0 = 0 := by
  rw [thickeningLiftDifferenceEquiv_apply, Abelian.Ext.zero_comp]
  unfold thickenedRetractionExt
  rw [Abelian.Ext.mapExactFunctor_zero, Stacks.Homology.extConj_zero]

/-- **The trivial lift goes to `0`.** -/
theorem thickeningLiftDifference_trivial :
    thickeningLiftDifference h r hr hh hfl (Quotient.mk _ (trivialThickeningLift h r hr)) = 0 :=
  (congrArg (thickeningLiftDifferenceEquiv h r hr hh hfl)
    (thickeningLiftDifferenceTopos_trivial h r hr hh hfl)).trans
    (thickeningLiftDifferenceEquiv_zero h r hr hh hfl)

/-- **The class of a lift goes to the class on `X_T` of its extension minus that of the trivial
lift.** -/
theorem thickeningLiftDifference_mk (L : D.ThickeningLift ξ h) :
    thickeningLiftDifference h r hr hh hfl (Quotient.mk _ L) =
      thickeningLiftExtClass h r hr hh hfl L -
        thickeningLiftExtClass h r hr hh hfl (trivialThickeningLift h r hr) :=
  eq_sub_of_add_eq (thickeningLiftExtClass_eq h r hr hh hfl L).symm

end AlgebraicGeometry.Space.CoherentSituation

end

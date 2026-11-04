module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Obstruction
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# The difference of a lift of an object of `Coh_{X/Y}` from the trivial lift

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and `h : T ⟶ T'` a first order
thickening of schemes over `Y` with a retraction `r : T' ⟶ T` over `Y`, `h ≫ r = 𝟙` (for instance
the thickening `Spec A ⊂ Spec A[M]` by a trivial square-zero extension), and assume `X_{T'} ⟶ T'`
flat. Then `ξ` has the *trivial lift* `r^*𝒢`, and by Stacks 08VW, part (2), the isomorphism
classes of lifts of `ξ` across `h` are a principal homogeneous set under
`Ext¹(𝒢, f^*𝒥 ⊗ 𝒢)`. Measuring the difference from the trivial lift identifies them with that
group: this is the computation `T_x(M) = Ext¹(𝒢, 𝒢 ⊗ M)` of the proofs of Stacks 08W8 and
Stacks 08WA.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.identityThickeningLift`: `ξ` as a lift of itself
  across the identity.
* `AlgebraicGeometry.Space.CoherentSituation.trivialThickeningLift`: the trivial lift `r^*𝒢`.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningFlatLiftTorsor`: the principal
  homogeneous structure of Stacks 08VW, part (2), on the flat lift classes.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifferenceTopos`: the bijection between
  lift classes and `Ext¹(𝒢, f^*𝒥 ⊗ 𝒢)` (on the thickened presentation), sending the trivial lift
  to `0`.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
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

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **`ξ` as a lift of itself across the identity of its test scheme**, the comparison being the
identity law of Stacks 03LU. -/
def identityThickeningLift (ξ : CoherentObject D) : D.ThickeningLift ξ (𝟙 ξ.T) where
  F := ξ.F
  quasicoherent := ξ.quasicoherent
  finitePresentation := ξ.finitePresentation
  flat := ξ.flat
  properSupport := ξ.properSupport
  fibre := (D.idComparison (modulePushforwardCoherence B S hS) ξ.T).hom.app ξ.F
  isIso_fibre := Iso.isIso_hom ((D.idComparison (modulePushforwardCoherence B S hS) ξ.T).app ξ.F)

variable {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T') (r : T' ⟶ ξ.T)
  (hr : h ≫ r = 𝟙 ξ.T)

/-- **The trivial lift** of `ξ` across a thickening `h` with retraction `r`: the pullback
`r^*𝒢`. -/
def trivialThickeningLift : D.ThickeningLift ξ h :=
  (identityThickeningLift ξ).pullback r hr

variable (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hfl : IsFlat B S hS (D.projection T').hom)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]

include hfl in
/-- **Stacks 08VW, part (2), on the relative square**: the principal homogeneous structure on the
isomorphism classes of flat lifts of `𝒢` across `X_T ⊂ X_{T'}`, with the action of the source
(`Deformation.ToposThickening.exists_addTorsor_flatLiftClass_basePullbackIdeal`); the trivial lift
shows that a lift exists. -/
abbrev exists_thickeningFlatLiftTorsor :=
  exists_addTorsor_flatLiftClass_basePullbackIdeal.{u, u + 1, u, u, u + 1, u, u + 1, u, u, u + 1,
      u, e}
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
    (D.relativeSquareSituation.relativeSquareThickening h)
    (D.relativeSquareSituation.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquare_comm h) (thickenedModule ξ h)
    (D.relativeSquareSituation.isStrict_relativeSquare h hh)
    (isFlat_relBaseRight_smallEtaleRingedToposHom (D.relativeSquareSituation.projection T') hfl)
    (isFlatOverBase_thickenedModule h hh) ⟨(trivialThickeningLift h r hr).toFlatLift h hh⟩

/-- **The principal homogeneous structure of Stacks 08VW, part (2)**, on the isomorphism classes
of flat lifts of `𝒢` across `X_T ⊂ X_{T'}`, with the action of the source
(`AlgebraicGeometry.Space.CoherentSituation.exists_thickeningFlatLiftTorsor`). -/
abbrev thickeningFlatLiftTorsor :=
  (exists_thickeningFlatLiftTorsor h r hr hh hfl).choose

/-- **The difference from the trivial lift**: the bijection between the isomorphism classes of
lifts of `ξ` across `h` and `Ext¹(𝒢, f^*𝒥 ⊗ 𝒢)` (on the presentation of `𝒪_{X_T}`-modules over
`X_{T'}`), the class of a lift going to its difference from the class of the trivial lift in the
principal homogeneous structure of Stacks 08VW, part (2). -/
def thickeningLiftDifferenceTopos :=
  letI := thickeningFlatLiftTorsor h r hr hh hfl
  (thickeningLiftClassEquiv h hh).trans
    (Equiv.vaddConst ((thickeningLiftClassEquiv h hh)
      (Quotient.mk _ (trivialThickeningLift h r hr)))).symm

/-- **The trivial lift differs from itself by `0`.** -/
theorem thickeningLiftDifferenceTopos_trivial :
    thickeningLiftDifferenceTopos h r hr hh hfl (Quotient.mk _ (trivialThickeningLift h r hr)) =
      0 :=
  @vsub_self _ _ _ (thickeningFlatLiftTorsor h r hr hh hfl) _

include hfl in
/-- **`f^*𝒥 ⊗ i_*𝒢 ≅ I ⊗ i_*𝒢`** (Stacks 08MQ), the identification through which Stacks 08VW,
part (2), lets `Ext¹(i_*𝒢, f^*𝒥 ⊗ i_*𝒢)` act
(`Deformation.ToposThickening.basePullbackIdealTensorIso`). -/
abbrev thickeningLiftDifferenceIso :=
  basePullbackIdealTensorIso.{u, u + 1, u, u, u + 1, u, u + 1, u, u, u + 1, u}
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
    (D.relativeSquareSituation.relativeSquareThickening h)
    (D.relativeSquareSituation.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquare_comm h)
    (isFlat_relBaseRight_smallEtaleRingedToposHom (D.relativeSquareSituation.projection T') hfl)
    (D.relativeSquareSituation.isStrict_relativeSquare h hh) (thickenedModule ξ h)

/-- The target of an isomorphism, to name an object by the isomorphism it is read from. -/
abbrev isoTarget {C : Type*} [Category C] {X Y : C} (_e : X ≅ Y) : C := Y

include hfl in
/-- **The kernel `I ⊗ i_*𝒢`** of the extension attached to a lift, over `i_*𝒪_{X_T}`: the target
of `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifferenceIso`. -/
abbrev thickeningKernel :=
  isoTarget (thickeningLiftDifferenceIso h hh hfl)

/-- **The extension attached to a lift**, `0 ⟶ I ⊗ 𝒢 ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` of `𝒪_{X_{T'}}`-modules
(Stacks 08MQ), the one with which Stacks 08VW, part (2), describes the action
(`Deformation.ToposThickening.FlatLift.fixedActionExtension`). -/
abbrev thickeningLiftExtension (L : D.ThickeningLift ξ h) :=
  (L.toFlatLift h hh).fixedActionExtension
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
    (D.relativeSquareSituation.relativeSquareThickening h)
    (D.relativeSquareSituation.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquare_comm h) (thickenedModule ξ h)
    ((isStrictPullbackIdealMap_iff_isStrict
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      (D.relativeSquareSituation.relativeSquareThickening h)
      (D.relativeSquareSituation.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquare_comm h)).mpr
      (D.relativeSquareSituation.isStrict_relativeSquare h hh))
    (isFlat_reducedBaseModule_of_isFlatOverBase
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      (D.relativeSquareSituation.relativeSquareThickening h)
      (D.relativeSquareSituation.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquare_comm h) (thickenedModule ξ h)
      (isFlatOverBase_thickenedModule h hh))

include hfl in
/-- The class in `Ext¹_{𝒪_{X_{T'}}}(i_*𝒢, I ⊗ 𝒢)` of the extension attached to a lift. -/
abbrev thickeningLiftExtensionClass (L : D.ThickeningLift ξ h) :=
  extensionClass.{u, u + 1, u, u, u + 1, u, e} (thickenedModule ξ h) (thickeningKernel h hh hfl)
    (thickeningLiftExtension h hh L)

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))] in
/-- Restriction of scalars along `𝒪_{X_{T'}} ⟶ i_*𝒪_{X_T}` is right exact
(`Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteColimits_restrictScalars`),
at the thickening `X_T ⊂ X_{T'}`. -/
theorem preservesFiniteColimits_structureRestrict_relativeMap :
    PreservesFiniteColimits
      (structureRestrict
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))) :=
  Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteColimits_restrictScalars _

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))] in
/-- Restriction of scalars along `𝒪_{X_{T'}} ⟶ i_*𝒪_{X_T}` is left exact
(`Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteLimits_restrictScalars`), at
the thickening `X_T ⊂ X_{T'}`. -/
theorem preservesFiniteLimits_structureRestrict_relativeMap :
    PreservesFiniteLimits
      (structureRestrict
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))) :=
  Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteLimits_restrictScalars _

attribute [local instance] preservesFiniteColimits_structureRestrict_relativeMap
  preservesFiniteLimits_structureRestrict_relativeMap

include hfl in
/-- **The relation of Stacks 08VW, part (2), with the trivial lift.** The extension class of a
lift is the class of the trivial lift plus the image in `Ext¹_{𝒪_{X_{T'}}}(i_*𝒢, I ⊗ 𝒢)` of the
difference of the two lifts: this is how the action of the principal homogeneous structure is
defined (`Deformation.ToposThickening.exists_addTorsor_flatLiftClass_basePullbackIdeal`). -/
theorem thickeningLiftExtensionClass_eq (L : D.ThickeningLift ξ h) :
    thickeningLiftExtensionClass h hh hfl L =
      (structureRestrict
          (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h))).mapExtAddHom.{e, e}
          _ _ 1
          ((thickeningLiftDifferenceTopos h r hr hh hfl (Quotient.mk _ L)).comp
            (Abelian.Ext.mk₀ (thickeningLiftDifferenceIso h hh hfl).hom) (add_zero 1)) +
        thickeningLiftExtensionClass h hh hfl (trivialThickeningLift h r hr) :=
  ((exists_thickeningFlatLiftTorsor h r hr hh hfl).choose_spec _
      ((trivialThickeningLift h r hr).toFlatLift h hh) (L.toFlatLift h hh)).1
    (@vsub_vadd _ _ _ (thickeningFlatLiftTorsor h r hr hh hfl) _ _)

end AlgebraicGeometry.Space.CoherentSituation

end

module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SectionsClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourcePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingInvertibleQuotients

/-!
# The conormal source `Ker(q) ⊗ ℒ^{⊗ -1}` read at an étale scheme point

Let `q : ℰ ⟶ ℒ` be an invertible quotient of a quasi-coherent module on an algebraic space `X`,
and let `x : T ⟶ X` be an étale scheme point.  The module `Ker(q) ⊗ ℒ^{⊗ -1}` is quasi-coherent
(Stacks 03M1, and invertible modules are quasi-coherent).  Its inverse image along `x` is
`Ker(x^*q) ⊗ (x^*ℒ)^{⊗ -1}`, since `x` is flat; the Zariski reading `R_T` to the scheme `T` is a
right adjoint, so preserves kernels, it is monoidal on quasi-coherent modules, so carries the
tensor inverse `(x^*ℒ)^{⊗ -1}`, characterised by its trivialisation against `x^*ℒ`, to the tensor
inverse of `R_T(x^*ℒ)`.  Together: the Zariski reading of `x^*(Ker(q) ⊗ ℒ^{⊗ -1})` is the source
`Ker(q_x) ⊗ ℒ_x^{⊗ -1}` of the conormal isomorphism of Stacks 0B3V for the invertible quotient
`q_x = R_T(x^*q)` of `(x^*ℰ)_Zar` on `T`, with the tensor product of
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor`.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingKernelIso`: `R_T(Ker g) ≅ Ker(R_T g)`.
* `AlgebraicGeometry.Space.zariskiReadingTensorObjIso`: `R_T(ℳ ⊗ 𝒩) ≅ R_T ℳ ⊗ R_T 𝒩` for
  quasi-coherent `ℳ`, `𝒩`.
* `AlgebraicGeometry.Space.zariskiReadingTensorPowerNegOneIso`:
  `R_T(ℒ^{⊗ -1}) ≅ (R_T ℒ)^{⊗ -1}`.
* `AlgebraicGeometry.Space.zariskiReadingKernelTensorInverseIso`:
  `R_T(Ker(q) ⊗ ℒ^{⊗ -1}) ≅ Ker(R_T q) ⊗ (R_T ℒ)^{⊗ -1}`.
* `AlgebraicGeometry.Space.conormalSourceReadingIso`:
  `R_T(x^*(Ker(q) ⊗ ℒ^{⊗ -1})) ≅ Ker(q_x) ⊗ ℒ_x^{⊗ -1}`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_tensor_tensorPower_neg_one`:
  `Ker(q) ⊗ ℒ^{⊗ -1}` is quasi-coherent.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Quasicoherence

variable (Z : AlgebraicSpaces B S hS)

/-- **The kernel of a map of quasi-coherent modules on an algebraic space is quasi-coherent**
(Stacks 03M1). -/
theorem isQuasicoherentOnSite_kernel_of_isQuasicoherentOnSite
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (q : M ⟶ N) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) : (kernel q).IsQuasicoherentOnSite :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS Z.1 Z.2
  ObjectProperty.prop_kernel _ q hM hN

/-- **Integral tensor powers of an invertible module on an algebraic space are
quasi-coherent.** -/
theorem isQuasicoherentOnSite_invertibleTensorPower (L : Modules.{u, u} B S hS Z.1 Z.2)
    [hL : IsInvertible (structureCommRings B S hS Z) (structureRingSheaf B S hS Z).property L]
    (n : ℤ) :
    (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Z)
      (structureRingSheaf B S hS Z).property L n).IsQuasicoherentOnSite :=
  have := (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  isQuasicoherentOnSite_of_isInvertible B S hS Z _
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _ L n))

/-- **`Ker(q) ⊗ ℒ^{⊗ -1}` is quasi-coherent** for a map `q : ℰ ⟶ ℒ` from a quasi-coherent
module to an invertible one. -/
theorem isQuasicoherentOnSite_kernel_tensor_tensorPower_neg_one
    {M L : Modules.{u, u} B S hS Z.1 Z.2} (q : M ⟶ L) (hM : M.IsQuasicoherentOnSite)
    [hL : IsInvertible (structureCommRings B S hS Z) (structureRingSheaf B S hS Z).property L] :
    (kernel q ⊗ Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Z)
      (structureRingSheaf B S hS Z).property L (-1)).IsQuasicoherentOnSite :=
  @isQuasicoherentOnSite_tensorObj B S hS Z.1 Z.2 _ _
    (isQuasicoherentOnSite_kernel_of_isQuasicoherentOnSite Z q hM
      (isQuasicoherentOnSite_of_isInvertible B S hS Z L hL))
    (isQuasicoherentOnSite_invertibleTensorPower Z L (-1))

end Quasicoherence

section Reading

variable (T : BigFppfOver B S hS)

/-- **The Zariski reading preserves kernels**: it is a direct image, hence a right adjoint. -/
def zariskiReadingKernelIso
    {M N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)} (g : M ⟶ N) :
    (zariskiReadingFunctor T).obj (kernel g) ≅ kernel ((zariskiReadingFunctor T).map g) :=
  haveI : PreservesLimitsOfSize.{0, 0} (zariskiReadingFunctor T) :=
    (zariskiReadingAdj T).rightAdjoint_preservesLimits
  haveI : (zariskiReadingFunctor T).PreservesZeroMorphisms :=
    haveI : (zariskiReadingFunctor T).IsRightAdjoint := (zariskiReadingAdj T).isRightAdjoint
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  PreservesKernel.iso (zariskiReadingFunctor T) g

/-- **The Zariski reading of a tensor product of quasi-coherent modules is the tensor product of
the readings**, for the tensor product sheaf on the scheme. -/
def zariskiReadingTensorObjIso
    (M N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (zariskiReadingFunctor T).obj
        (M ⊗ N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) ≅
      ((zariskiReadingFunctor T).obj M ⊗ (zariskiReadingFunctor T).obj N :
        ((BigFppfOver.toScheme B S hS).obj T).Modules) :=
  (zariskiReadingFunctor T).mapIso (modulesTensorObjIso B S hS _ _ M N) ≪≫
    zariskiReadingTensorIso T M N hM hN

/-- **The Zariski reading of the trivialisation `ℒ^{⊗ -1} ⊗ ℒ ≅ 𝒪`**, as a trivialisation of
`R_T(ℒ^{⊗ -1}) ⊗ R_T ℒ` on the scheme. -/
def zariskiReadingTensorPowerNegOnePairing
    (L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    [hL : IsInvertible (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
        ((zariskiReadingFunctor T).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS (yonedaSpace B S hS T))
          (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1)))).obj
        ((zariskiReadingFunctor T).obj L) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2) :=
  (zariskiReadingTensorIso T _ L
      (isQuasicoherentOnSite_invertibleTensorPower (yonedaSpace B S hS T) L (-1))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) L hL)).symm ≪≫
    (zariskiReadingFunctor T).mapIso
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
          (structureCommRings B S hS (yonedaSpace B S hS T))
          (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1) ≪≫
        Stacks.SheafOfModules.Invertible.tensorPowerReindex
          (structureCommRings B S hS (yonedaSpace B S hS T))
          (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L
          (show (-1 : ℤ) + 1 = 0 by omega)) ≪≫
    zariskiReadingUnitIso T

/-- **The Zariski reading of `ℒ^{⊗ -1}` is `(R_T ℒ)^{⊗ -1}`**: the reading of the
trivialisation of `ℒ^{⊗ -1} ⊗ ℒ` identifies `R_T(ℒ^{⊗ -1})` with the tensor inverse of
`R_T ℒ` (`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne`). -/
def zariskiReadingTensorPowerNegOneIso
    (L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    [hL : IsInvertible (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L] :
    haveI := isInvertible_zariskiReading T L
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL)
    (zariskiReadingFunctor T).obj (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS (yonedaSpace B S hS T))
        (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1)) ≅
      Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 ((zariskiReadingFunctor T).obj L)
        (-1) :=
  haveI := isInvertible_zariskiReading T L
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL)
  Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne
    ((BigFppfOver.toScheme B S hS).obj T).presheaf
    ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 _ _
    (zariskiReadingTensorPowerNegOnePairing T L)

/-- **`R_T(Ker(q) ⊗ ℒ^{⊗ -1}) ≅ Ker(R_T q) ⊗ (R_T ℒ)^{⊗ -1}`** for a map `q : ℳ ⟶ ℒ` from a
quasi-coherent module to an invertible one on the represented algebraic space. -/
def zariskiReadingKernelTensorInverseIso
    {M L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)} (q : M ⟶ L)
    (hM : M.IsQuasicoherentOnSite)
    [hL : IsInvertible (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L] :
    haveI := isInvertible_zariskiReading T L
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL)
    (zariskiReadingFunctor T).obj (kernel q ⊗ Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS (yonedaSpace B S hS T))
        (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1) :
          Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) ≅
      (kernel ((zariskiReadingFunctor T).map q) ⊗ Stacks.SheafOfModules.Invertible.tensorPower
        ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 ((zariskiReadingFunctor T).obj L)
        (-1) :
          ((BigFppfOver.toScheme B S hS).obj T).Modules) :=
  haveI := isInvertible_zariskiReading T L
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL)
  zariskiReadingTensorObjIso T _ _
      (isQuasicoherentOnSite_kernel_of_isQuasicoherentOnSite (yonedaSpace B S hS T) q hM
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) L hL))
      (isQuasicoherentOnSite_invertibleTensorPower (yonedaSpace B S hS T) L (-1)) ≪≫
    tensorIso (C := ((BigFppfOver.toScheme B S hS).obj T).Modules) (zariskiReadingKernelIso T q)
      (zariskiReadingTensorPowerNegOneIso T L)

end Reading

section Point

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)
  (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)

/-- The kernel of `x^*q` is the kernel of the quotient map of the base change of `Q` along `x`
read along the identity of `x^*ℰ`. -/
def kernelPointBaseChangeIso :
    kernel ((modulePullback B S hS (pointHom x)).map Q.q) ≅
      kernel (Q.baseChange (pointHom x) (Iso.refl _)).q :=
  kernelIsoOfEq (Category.id_comp _).symm

/-- **The conormal source `Ker(q) ⊗ ℒ^{⊗ -1}` read at an étale scheme point `x : T ⟶ X`**:
the Zariski reading of its pullback along `x` is the conormal source
`Ker(q_x) ⊗ ℒ_x^{⊗ -1}` of the invertible quotient `q_x` of `(x^*ℰ)_Zar` on the scheme `T`. -/
def conormalSourceReadingIso (hx : IsEtale B S hS x) :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
      Q.invertible.toAlgebraicGeometry
    haveI := (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE T x)
      (Q.baseChange (pointHom x) (Iso.refl _))).invertible
    (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
      (kernel Q.q ⊗ Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))) ≅
    (kernel (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE T x)
        (Q.baseChange (pointHom x) (Iso.refl _))).q ⊗
      Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
        (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE T x)
          (Q.baseChange (pointHom x) (Iso.refl _))).L (-1) :
        ((BigFppfOver.toScheme B S hS).obj T).Modules) :=
  haveI hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      Q.L :=
    Q.invertible.toAlgebraicGeometry
  haveI := isInvertible_modulePullback_obj B S hS (pointHom x) Q.L hQ
  haveI : IsInvertible (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
      (Q.baseChange (pointHom x) (Iso.refl _)).L :=
    isInvertible_modulePullback_obj B S hS (pointHom x) Q.L hQ
  (zariskiReadingFunctor T).mapIso
      (modulePullbackKernelTensorInverseIso (pointHom x)
          (isFlat_smallEtaleRingedToposHom_of_isEtale B S hS (pointHom x) hx) Q.q ≪≫
        tensorIso (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
          (kernelPointBaseChangeIso X E Q T x) (Iso.refl _)) ≪≫
    zariskiReadingKernelTensorInverseIso T (Q.baseChange (pointHom x) (Iso.refl _)).q
      (isQuasicoherentOnSite_pointPullback X E hE T x)

end Point

end AlgebraicGeometry.Space

end

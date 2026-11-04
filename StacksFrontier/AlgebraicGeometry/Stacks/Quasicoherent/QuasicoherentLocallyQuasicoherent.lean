module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentEtaleSheafClause

/-!
# Quasi-coherent modules are locally quasi-coherent

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` and let `F` be a
quasi-coherent module on its fppf site (**Stacks 06WG**).  This file proves that `F`, read on the
étale site, is locally quasi-coherent (**Stacks 06WJ**).  That is the forward direction of
clause (1) of **Stacks 06WK**, and the first of the two halves of the containment
`QCoh(𝒪_𝒳) ⊂ LQCoh^fbc(𝒪_𝒳)` (Stacks, Section 0GQG) which **Stacks 0778** uses to form its
inclusion functor; the second half, the flat base change property of **Stacks 0762**, is not
proved here.

## Main results

* `AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`: a
  quasi-coherent module is cartesian along every arrow of `𝒳` between objects lying over affine
  schemes: `Γ(y) ⊗_{Γ(y')} F(y') ⟶ F(y)` is an isomorphism.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite`: a quasi-coherent
  module is locally quasi-coherent.

## Implementation notes

The cartesian property is
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction`, stated with
`LinearMap.liftBaseChange`; it is transported to `Stacks.PresheafOfModules.restrictionBaseChange`,
the form in which local quasi-coherence is tested
(`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff`), by
checking that the two maps agree on pure tensors.

## References

* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

/-- **A quasi-coherent module is cartesian between affine objects.**  For an arrow `f : y ⟶ y'`
of `𝒳` between objects lying over affine schemes, the base-change comparison
`Γ(y) ⊗_{Γ(y')} F(y') ⟶ F(y)` of a quasi-coherent module `F` on the fppf site of `𝒳` is an
isomorphism.  This is `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction`
read through `Stacks.PresheafOfModules.restrictionBaseChange`. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) {y y' : 𝒳} (f : y ⟶ y')
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)))
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y'))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp .fppf).obj) M.val f.op) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let := objModule B S hS p hp M y'
  let := objModule B S hS p hp M y
  let := objAlgebra B S hS p f
  let : Module (objRing B S hS p y') (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p y') (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p y') (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let F1 := ConcreteCategory.hom (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp .fppf).obj) M.val f.op)
  let F2 := LinearMap.liftBaseChange (objRing B S hS p y) (restrictionLinear M f)
  have h (z) : F1 z = F2 z := by
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero F1).trans (map_zero F2).symm
    | tmul a s => rfl
    | add z z' hz hz' =>
      exact (map_add F1 z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add F2 z z').symm)
  rw [show (F1 : _ → _) = fun z => F2 z from funext h]
  exact bijective_liftBaseChange_of_eq_restriction M hM f hy' hy
    (restrictionLinear M f) (fun _ => rfl)

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A quasi-coherent module is locally quasi-coherent** (**Stacks 06WK**, forward direction of
clause (1)).  A quasi-coherent module `F` on the fppf site of `𝒳` (**Stacks 06WG**) is a sheaf
for the coarser étale topology, and at every object `x` of `𝒳` its restriction `x^*F|_{U_ét}` to
the small étale site of the scheme `U` below `x` (**Stacks 06WJ**) is quasi-coherent: it is
cartesian between affine objects, because the index functor of **Stacks 06W1** sends a morphism
of affine objects of `U_ét` to an arrow of `𝒳` between objects over affine schemes, along which
`F` is cartesian by
`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`; and a
cartesian sheaf on the small étale site is quasi-coherent (Descent, Proposition 03DX). -/
theorem isLocallyQuasicoherent_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasicoherent B E h S hS p hp M.val := by
  have hFet : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) M.val.presheaf :=
    isSheaf_etale_of_isQuasicoherent B S hS p hp M.val ⟨M.isSheaf, hM⟩
  refine ⟨hFet, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x M.val hFet, ?_⟩⟩
  refine SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines E _ _ _
    fun {T T'} g hT hT' => ?_
  refine (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff B E h S hS p hp M.val
    x g).2 ?_
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite M hM
      ((etaleIndex B E h S hS p hp x).map g)
      (isAffine_etaleIndex_obj B E h S hS p hp x T hT)
      (isAffine_etaleIndex_obj B E h S hS p hp x T' hT'))

end AlgebraicGeometry.Stack

end

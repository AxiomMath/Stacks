module

public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.TwistTrivialization

/-!
# The zeroth twist and the structure sheaf agree at a stalk

Let `S` be a nonnegatively graded ring, `X = Proj(S)`, and let `x` be a point of `X`, that is a
homogeneous prime `p` not containing the irrelevant ideal. A section of `𝒪_X(0)` near `x` is a
fraction `m / s` with `m` and `s` homogeneous of the *same* degree, which is exactly an element
of the local ring `S₍p₎`. So the degree-zero part of the localization of the zeroth twist at `x`
is `S₍p₎`, and hence **the stalk of `𝒪_X(0)` at `x` is the stalk of `𝒪_X` at `x`**.

This is the twist `0` case of the stalk comparison proved at twist `-1` in
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.twistingSheafMinusOneStalkEquiv`, and unlike
that case it needs no degree-one element outside `p`: the identification is the tautological one
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAtZeroEquiv`, read over the
structure-sheaf stalk through `AlgebraicGeometry.Proj.stalkIso'`. The passage from the stalk of
the twisting sheaf to the degree-zero part is
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkLinearEquiv` of
Stacks Tag 01M7.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.twistZeroStalkLinearEquiv`: the degree-zero
  part of the zeroth twist at `x` is the structure-sheaf stalk at `x`, linearly over that stalk.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.twistingSheafZeroStalkEquiv`: the stalk of
  `𝒪_X(0)` at `x` is the stalk of `𝒪_X` at `x`.

## Main results

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.val_twistingSheafZeroStalkEquiv_germ`: the
  germ of a section of `𝒪_X(0)` is sent to the element of the local ring whose fraction is the
  value of the section at `x`.

## Implementation notes

All the underlying equivalences are linear over `HomogeneousLocalization.AtPrime 𝒮 p`, the ring
`degreeZeroModuleAt` is a `Submodule` over; the stalk-level statements read them over the
structure-sheaf stalk, which acts through `AlgebraicGeometry.Proj.stalkIso'`. The module
structure in the type of `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAt`
is introduced by `letI` in that declaration's statement, so the two local instances
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.fiberModule` and
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.stalkModuleDegreeZeroModuleAt` are re-enabled
here rather than restated. The germ computation rule chains the existing equations with
`Eq.trans` rather than rewriting with them, which avoids rewriting inside the fibres.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The ideal underlying the homogeneous prime of a point of `Proj(S)` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

attribute [local instance] fiberModule stalkModuleDegreeZeroModuleAt

/-- The identification of the degree-zero part of `S(0)` at `x` with the local ring at `x`, read
over the structure-sheaf stalk: the stalk acts on both sides through
`AlgebraicGeometry.Proj.stalkIso'`. -/
def twistZeroStalkLinearEquiv (x : ProjectiveSpectrum.top 𝒮) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 0) x
      ≃ₗ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x where
  toFun z := (Proj.stalkIso' 𝒮 x).symm ((degreeZeroModuleAtZeroEquiv 𝒮 x).symm z)
  invFun c := degreeZeroModuleAtZeroEquiv 𝒮 x (Proj.stalkIso' 𝒮 x c)
  map_add' _ _ := by simp
  map_smul' c z := by
    change (Proj.stalkIso' 𝒮 x).symm
        ((degreeZeroModuleAtZeroEquiv 𝒮 x).symm ((Proj.stalkIso' 𝒮 x c) • z)) =
      c * (Proj.stalkIso' 𝒮 x).symm ((degreeZeroModuleAtZeroEquiv 𝒮 x).symm z)
    rw [map_smul]
    change (Proj.stalkIso' 𝒮 x).symm
      ((Proj.stalkIso' 𝒮 x c) * (degreeZeroModuleAtZeroEquiv 𝒮 x).symm z) = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  left_inv _ := by simp
  right_inv _ := by simp

/-- **The stalk of `𝒪(0)` at `x` is the stalk of `𝒪` at `x`.** A degree-zero fraction `m / s`
with `m` and `s` of the same degree is an element of the local ring at `x`, and that is already
the identification. -/
def twistingSheafZeroStalkEquiv (x : ProjectiveSpectrum.top 𝒮) :
    associatedModuleSheafStalk 𝒮 (twistGrading (S := S) 𝒮 0) x
      ≃ₗ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x :=
  (associatedModuleSheafStalkLinearEquiv 𝒮 (twistGrading (S := S) 𝒮 0) x).trans
    (twistZeroStalkLinearEquiv 𝒮 x)

/-- **The computation rule at a stalk**: if a section `a` of `𝒪(0)` over a neighbourhood of `x`
has value `z` at `x`, its germ is sent to the element of the local ring at `x` whose fraction is
`z`. -/
theorem val_twistingSheafZeroStalkEquiv_germ (x : ProjectiveSpectrum.top 𝒮)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (hxU : x ∈ U)
    (a : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮
      (twistGrading (S := S) 𝒮 0)).val.obj (op U))
    {z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x}
    (ha : ((ProjectiveSpectrum.Proj.associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 0) U).toFun a).1 ⟨x, hxU⟩ = z) :
    HomogeneousLocalization.val (Proj.stalkIso' 𝒮 x
        (twistingSheafZeroStalkEquiv 𝒮 x
          (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 0) x U hxU a))) = z := by
  have h : twistingSheafZeroStalkEquiv 𝒮 x
      (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 0) x U hxU a) =
      (Proj.stalkIso' 𝒮 x).symm ((degreeZeroModuleAtZeroEquiv 𝒮 x).symm
        (associatedModuleSheafStalkEquiv 𝒮 (twistGrading (S := S) 𝒮 0) x
          (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 0) x U hxU a))) := rfl
  rw [h, RingEquiv.apply_symm_apply]
  exact (val_degreeZeroModuleAtZeroEquiv_symm 𝒮 x _).trans
    ((associatedModuleSheafStalkEquiv_germ 𝒮 (twistGrading (S := S) 𝒮 0) x U hxU a).trans ha)

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections

end

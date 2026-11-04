module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaGlobal
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections

/-!
# The twist comparison at the tensor-power spelling the section module is graded by

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring covered in degree one, `X = Proj S`, and `d` a degree.
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaInt` compares the tensor powers of `𝒪_X(d)` with the
`d`-divisible twists at the spelling `Stacks.Ample.tensorPowModule`, which is
`AlgebraicGeometry.SheafOfModules.tensorPow`. The graded section ring and section module of Tag
01CV, and so the comparison map of Tag 0B5L and both parts of Tag 01PW, are instead graded by
`Stacks.SheafOfModules.TensorPower.tensorPower`, the image of the structure sheaf under the
`n`-th power of the right-tensor autoequivalence. The two are different constructions.

This file restates the comparison at that second spelling, by composing with the bridge
`Stacks.PowerFamilyBridge.tensorPowerModuleIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower` — **`𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` with the
  power taken at the spelling the section module of Tag 01CV is graded by**, in every integer
  degree.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample

namespace Stacks.AlgebraicGeometry.ThetaGlobal

universe u w

open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover)

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (hcover : DegreeOneCover 𝒮) (d : ℕ)
  [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))]

/-- Invertibility of the twist, at the spelling of the structure sheaf of the ringed space that
the section module is graded over. The two spellings are the same type, so the instance is the
one already in scope; instance search does not cross them, so it is named again here. -/
instance isInvertible_twist_sectionSite :
    Stacks.SheafOfModules.IsInvertible
      (Stacks.SheafOfModules.sectionSiteRing (AlgebraicGeometry.Proj 𝒮))
      (Stacks.SheafOfModules.sectionSiteSheaf (AlgebraicGeometry.Proj 𝒮))
      (twist 𝒮 (d : ℤ)) :=
  inferInstanceAs (IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)))

/-- Tensoring on the right by the twist is an autoequivalence, which is the hypothesis under
which Tag 01CU's powers are formed at this spelling. -/
instance isEquivalence_tensorRightFunctor_twist :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨(Stacks.SheafOfModules.sectionSiteRing (AlgebraicGeometry.Proj 𝒮)),
        Presheaf.isSheaf_of_isSheaf_comp _
          ((Stacks.SheafOfModules.sectionSiteRing (AlgebraicGeometry.Proj 𝒮)))
          (forget₂ CommRingCat RingCat)
          ((Stacks.SheafOfModules.sectionSiteSheaf (AlgebraicGeometry.Proj 𝒮)))⟩).flip.obj
        ((twist 𝒮 (d : ℤ))))).IsEquivalence :=
  Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _

/-- **The comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` with the tensor power taken at the spelling the
graded section module of Tag 01CV is graded by**, in every integer degree: the bridge of the two
constructions of Tag 01CU's powers, followed by
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaInt`. -/
def thetaSectionPower (n : ℤ) :
    Stacks.SheafOfModules.TensorPower.tensorPower
        (Stacks.SheafOfModules.sectionSiteRing (AlgebraicGeometry.Proj 𝒮))
        (Stacks.SheafOfModules.sectionSiteSheaf (AlgebraicGeometry.Proj 𝒮))
        (twist 𝒮 (d : ℤ)) n ≅
      twist 𝒮 ((d : ℤ) * n) :=
  Stacks.PowerFamilyBridge.tensorPowerModuleIso (AlgebraicGeometry.Proj 𝒮)
      (twist 𝒮 (d : ℤ)) n ≪≫
    thetaInt 𝒮 hcover d n

end Stacks.AlgebraicGeometry.ThetaGlobal

end

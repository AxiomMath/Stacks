module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceInverseImageExt
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFibreCriterion

/-!
# The pulled-back extension of an extension of `𝒪_X`, on the inverse-image ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `X_A = (X, f⁻¹𝒪_Y)` the
inverse-image ringed space and `ι : X ⟶ X_A` the factorization of `f`
(`AlgebraicGeometry.RingedSpace.inverseImageSourceInclusion`). A square-zero extension
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` whose identification of the ideal with `𝒢` is bijective is,
together with an algebra structure over the base of `X_A`, exactly the data of the second
construction of **Stacks 0GQ2** for `q = f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, with coefficients `ι_*𝒢`. This
file packages it as a `AlgebraicGeometry.RingedSpaceThickening.FibreExtensionData`, so that the
pulled-back extension `𝒪_{X'} ×_{𝒪_X} f⁻¹𝒪_Y` and the criterion of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionFibreCriterion.lean` apply to it.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.fibreExtensionData`: the
  data of **Stacks 0GQ2** attached to an extension of `𝒪_X` with bijective ideal identification.

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (presentationScalar)
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sites.SqZeroPullback
open AlgebraicGeometry.RingedSpace (inverseImage inverseImageSourceInclusion)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension

variable {X Y T₀ T : RingedSpace.{u, u}} (f : X ⟶ Y) {h : X ⟶ T₀}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : AlgebraSquareZeroExtension h G)
  (hP : ∀ U, Function.Bijective (P.ideal.app U))
  (g : inverseImage Y f.hom.base ⟶ T)

/-- For an extension with bijective ideal identification, the inclusion `P.idealIncl hP U` of
`𝒢(U)` into `𝒪_{X'}(U)` is injective. -/
theorem idealIncl_injective (U : (Opens X.carrier)ᵒᵖ) : Function.Injective (P.idealIncl hP U) :=
  fun n n' hn => (P.ideal_idealIncl hP U n).symm.trans
    ((congrArg (P.ideal.app U) (Subtype.ext hn)).trans (P.ideal_idealIncl hP U n'))

/-- The inclusion of `𝒢` into an extension with bijective ideal identification, as a realization
of `ι_*𝒢` as the kernel of the reduction `P.reduction`. -/
def fibreInrData : FibreInrData P.reduction
    ((modulePushforward (inverseImageSourceInclusion f)).obj G).val.presheaf where
  app U :=
    { toFun := P.idealIncl hP U
      map_zero' := P.idealIncl_zero hP U
      map_add' := P.idealIncl_add hP U }
  app_map k n := P.idealIncl_map hP k n
  app_injective U := P.idealIncl_injective hP U
  range U a := ⟨fun ha => ⟨P.ideal.app U ⟨a, ha⟩, P.idealIncl_ideal hP U ⟨a, ha⟩⟩,
    fun ⟨n, hn⟩ => hn ▸ P.reduction_idealIncl hP U n⟩

variable (v : inverseImageBaseRing g ⟶ P.sheaf)
  (hv : v ≫ P.reduction = structureRingMap g ≫ ringedSpaceStructureMap f)

/-- **The data of the second construction of Stacks 0GQ2** attached to a square-zero extension
`𝒪_{X'}` of `𝒪_X` by `𝒢` with bijective ideal identification and an algebra structure `v` over
the base of `X_A = (X, f⁻¹𝒪_Y)` lying over `f^♯`: the extension is pulled back along
`f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, with coefficients `ι_*𝒢`. -/
def fibreExtensionData :
    FibreExtensionData g ((modulePushforward (inverseImageSourceInclusion f)).obj G)
      (ringedSpaceStructureMap f) where
  B' := P.sheaf
  p := P.reduction
  locallySurjective_p := P.reduction_surjective
  ι := P.fibreInrData f hP
  inr_mul_inr U n m := P.idealIncl_mul_idealIncl hP U n m
  smul_inr U b a n hb := by
    refine (P.mul_idealIncl hP U b n).trans (congrArg (P.idealIncl hP U) ?_)
    let n₀ : ↥(G.val.obj U) := n
    exact congrArg (fun c : ↥((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf).obj.obj U) => c • n₀) hb
  v := v
  base_comm := hv

end AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension

end

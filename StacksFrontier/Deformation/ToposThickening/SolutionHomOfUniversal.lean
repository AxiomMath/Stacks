module

public import StacksFrontier.Deformation.AlgebraExtension.InducedKernelMap
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutAlgebraExtension
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism

/-!
# Morphisms of solutions when the prescribed map is universal

For the square-zero extension problem of [Stacks Project, Tag 08UF] with prescribed map
`c : f⁻¹𝒥 ⟶ 𝒢`, a morphism of solutions is a map of the thickened structure sheaves over `𝒪_X`,
under the thickened base, which is the identity on `𝒢`. When `c` is universal, in the sense that
an endomorphism `k` of `𝒢` with `c ≫ k = c` is the identity — as for `c` the unit of extension of
scalars, with `𝒢 = f^*𝒥` — the last condition is automatic: the map of kernels induced by such a
map of thickened structure sheaves restricts to the identity on the image of `c`.

## Main results
* `Deformation.ToposThickening.RingedToposExtensionProblem.kernel_comm_of_universal`: the
  identity on `𝒢` is automatic.
* `Deformation.ToposThickening.RingedToposExtensionProblem.isomorphic_of_hom_of_universal`: two
  solutions related by such a map are isomorphic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)

/-- The prescribed map `c` is universal on endomorphisms: an endomorphism `k` of `𝒢` with
`c ≫ k = c` is the identity. -/
def CIsUniversal : Prop :=
  ∀ k : S.G ⟶ S.G, S.c ≫ (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map k =
    S.c → k = 𝟙 _

variable {S}

/-- **The identity on `𝒢` is automatic** for a map of solutions over `𝒪_X` and under the
thickened base, when `c` is universal. -/
theorem kernel_comm_of_universal (hc : S.CIsUniversal) {P Q : S.CompatibleFirstOrderThickening}
    (φ : P.extension ⟶ Q.extension) (hr : φ ≫ Q.reduction = P.reduction)
    (hb : P.baseMap ≫ φ = Q.baseMap) (U : X.Cᵒᵖ) (g : S.G.val.obj U) :
    φ.hom.app U (show P.extension.obj.obj U from P.kernelInclusion.val.app U g) =
      (show Q.extension.obj.obj U from Q.kernelInclusion.val.app U g) := by
  let a₀ := (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
    S.f.fSharpInverseImage
  let P' := S.toAlgebraExtension (Iso.refl _) (Category.id_comp a₀) P
  let Q' := S.toAlgebraExtension (Iso.refl _) (Category.id_comp a₀) Q
  have hk : Deformation.AlgebraExtension.inducedKernelMap P' Q' φ hr = 𝟙 _ := by
    refine hc _ (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
      ModuleCat.hom_ext (LinearMap.ext fun a => ?_)))
    refine Deformation.AlgebraExtension.inducedKernelSection_eq P' Q' φ hr _ _ ?_
    have h1 := Q.baseMap_ideal V a
    have h2 := P.baseMap_ideal V a
    have h3 := congrArg (fun m => m.hom.app V
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj V from
        S.idealInclusion.val.app V a)) hb
    exact h1.symm.trans (h3.symm.trans (congrArg (φ.hom.app V) h2))
  have h := Deformation.AlgebraExtension.hom_incl P' Q' φ hr g
  rw [hk] at h
  exact h

/-- **Two solutions related by a map of thickened structure sheaves over `𝒪_X` and under the
thickened base are isomorphic**, when `c` is universal. -/
theorem isomorphic_of_hom_of_universal (hc : S.CIsUniversal)
    {P Q : S.CompatibleFirstOrderThickening} (φ : P.extension ⟶ Q.extension)
    (hr : φ ≫ Q.reduction = P.reduction) (hb : P.baseMap ≫ φ = Q.baseMap) :
    CompatibleFirstOrderThickening.Isomorphic P Q :=
  ⟨(CompatibleFirstOrderThickening.Hom.toIso
    { hom := φ
      reduction_comm := hr
      baseMap_comm := hb
      kernel_comm := kernel_comm_of_universal hc φ hr hb })⟩

end Deformation.ToposThickening.RingedToposExtensionProblem

end

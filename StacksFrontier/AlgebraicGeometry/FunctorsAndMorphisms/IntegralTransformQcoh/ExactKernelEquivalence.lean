module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernelOfFunctor
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelFullyFaithful

/-!
# Exact functors on quasi-coherent modules are integral transforms

Let `R` be a ring and let `X` and `Y` be schemes over `R` with `X` quasi-compact and with affine
diagonal. Sending a quasi-coherent kernel `K` on `X ×_R Y` to its integral transform
`F_K = pr_{2,*}(pr_1^*(-) ⊗ K)` is an equivalence from the full subcategory of the kernels which
are flat over `X` and satisfy `R^q pr_{2,*}(pr_1^*G ⊗ K) = 0` for `q > 0` and all quasi-coherent
`G` on `X`, onto the category of `R`-linear exact functors `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` commuting with
arbitrary direct sums ([Stacks, Tag 0FZH]).

## Main results

* `AlgebraicGeometry.exists_integralTransformExactKernel_iso`: every `R`-linear exact functor
  commuting with arbitrary direct sums is the integral transform of a kernel which is flat over `X`
  and has no positive higher direct images.
* `AlgebraicGeometry.isEquivalence_integralTransformExactKernelFunctor`: the integral transform
  functor `AlgebraicGeometry.integralTransformExactKernelFunctor` is an equivalence.
* `AlgebraicGeometry.integralTransformExactQcohEquivalence`: the equivalence, with
  `AlgebraicGeometry.integralTransformExactQcohEquivalence_functor_obj_obj` saying that it sends
  a kernel to its integral transform.

## References

* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [CompactSpace X.left]
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- **Every `R`-linear exact functor commuting with arbitrary direct sums is the integral
transform of a kernel which is flat over `X` and has no positive higher direct images.** -/
theorem exists_integralTransformExactKernel_iso
    (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
    (hF : exactLinearCoproductFunctor R X Y F) :
    ∃ K : Scheme.QuasicoherentModules (pullback X.hom Y.hom),
      integralTransformExactKernel R X Y K ∧
        Nonempty (F ≅ quasicoherentIntegralTransform R X Y K) := by
  have hF'' := exactLinearCoproductFunctor_le_rightExactLinearCoproductFunctor R X Y F hF
  have hF' := affineOpenRightExactLinearCoproductFunctor_of_rightExact R X Y F hF''
  have : PreservesFiniteLimits F := ((exactFunctor_iff F).mp hF.2.1).1
  have := isIso_kernelTransform_of_preservesFiniteLimits R X Y F hF'
  have hflat := isFlatOver_glued_of_exactFunctor R X Y F hF'' hF.2.1
  refine ⟨(openKernelSystem R X Y F hF').glued, ⟨hflat, fun G q hq => ?_⟩,
    ⟨asIso (kernelTransform R X Y F hF')⟩⟩
  exact isZero_rightDerived_integralTransformIntegrand_of_exactFunctor R X Y _ hflat
    ((exactFunctor _ _).prop_of_iso (asIso (kernelTransform R X Y F hF')) hF.2.1) G q hq

/-- Let `R` be a ring and let `X` and `Y` be schemes over `R` with `X` quasi-compact and with
affine diagonal. The functor sending a quasi-coherent kernel `K` on `X ×_R Y` to its integral
transform `F ↦ pr_{2,*}(pr_1^*F ⊗ K)` is an equivalence of categories between

1. the full subcategory of `QCoh(𝒪_{X ×_R Y})` of the kernels `K` which are flat over `X` and
   satisfy `R^q pr_{2,*}(pr_1^*F ⊗ K) = 0` for all quasi-coherent `F` on `X` and all `q > 0`
   (`AlgebraicGeometry.integralTransformExactKernel`), and
2. the category of `R`-linear exact functors `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` which commute with
   arbitrary direct sums (`AlgebraicGeometry.exactLinearCoproductFunctor`). -/
@[stacks 0FZH "the functor sending a kernel K on X ×_R Y to its integral transform is an \
equivalence from the kernels flat over X with vanishing higher direct images of pr_1^*F ⊗ K \
onto the R-linear exact functors QCoh(X) ⥤ QCoh(Y) commuting with arbitrary direct sums"]
theorem isEquivalence_integralTransformExactKernelFunctor :
    (integralTransformExactKernelFunctor R X Y).IsEquivalence := by
  have := faithful_integralTransformQcohFunctor R X Y
  have := full_integralTransformQcohFunctor R X Y
  have e := ObjectProperty.liftCompιIso (exactLinearCoproductFunctor R X Y)
    (ObjectProperty.ι (integralTransformExactKernel R X Y) ⋙ integralTransformQcohFunctor R X Y)
    (fun K => exactLinearCoproductFunctor_quasicoherentIntegralTransform R X Y K.obj K.property)
  have : (integralTransformExactKernelFunctor R X Y).Faithful := Functor.Faithful.of_comp_iso e
  have : (integralTransformExactKernelFunctor R X Y).Full := Functor.Full.of_comp_faithful_iso e
  have : (integralTransformExactKernelFunctor R X Y).EssSurj := ⟨fun F => by
    obtain ⟨K, hK, ⟨e⟩⟩ := exists_integralTransformExactKernel_iso R X Y F.obj F.property
    exact ⟨⟨K, hK⟩, ⟨ObjectProperty.isoMk _ e.symm⟩⟩⟩
  exact { }

/-- The equivalence `integralTransformExactKernelFunctor` between the kernels flat over `X` with
vanishing higher direct images and the `R`-linear exact functors commuting with arbitrary direct
sums. -/
def integralTransformExactQcohEquivalence :
    (integralTransformExactKernel R X Y).FullSubcategory ≌
      (exactLinearCoproductFunctor R X Y).FullSubcategory :=
  haveI := isEquivalence_integralTransformExactKernelFunctor R X Y
  (integralTransformExactKernelFunctor R X Y).asEquivalence

/-- The equivalence `integralTransformExactQcohEquivalence` sends a kernel `K` to its integral
transform `F ↦ pr_{2,*}(pr_1^*F ⊗ K)`. -/
theorem integralTransformExactQcohEquivalence_functor_obj_obj
    (K : (integralTransformExactKernel R X Y).FullSubcategory) :
    ((integralTransformExactQcohEquivalence R X Y).functor.obj K).obj =
      quasicoherentIntegralTransform R X Y K.obj := rfl

end AlgebraicGeometry

end

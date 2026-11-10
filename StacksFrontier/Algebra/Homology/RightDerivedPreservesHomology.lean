module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective

/-!
# Left exact functors preserving the homology of a short complex

Let `Q : B ⥤ D` be a left exact additive functor between abelian categories, `B` having enough
injectives. By the long exact sequence of right derived functors, `Q` takes a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `R¹Q X₁ = 0` to a short exact sequence. Consequently `Q` preserves
the homology of a short complex `X₁ ⟶ X₂ ⟶ X₃` as soon as `R¹Q X₁ = 0` and
`R¹Q`, `R²Q` vanish on the kernel of `X₁ ⟶ X₂`: writing `K` for the kernel of `X₂ ⟶ X₃` and `I`
for the image of `X₁ ⟶ K`, the sequences `0 ⟶ ker ⟶ X₁ ⟶ I ⟶ 0` and `0 ⟶ I ⟶ K ⟶ H ⟶ 0` stay
exact.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.preservesLeftHomologyOf_of_isZero_rightDerived`: `Q`
  preserves the left homology of a short complex under the vanishing above.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedDelta

variable {B : Type u₁} [Category.{v₁} B] [Abelian B]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

/-- The short exact sequence `0 ⟶ ker e ⟶ X ⟶ Y ⟶ 0` of an epimorphism `e : X ⟶ Y`. -/
theorem shortExact_kernel_of_epi {X Y : B} (e : X ⟶ Y) [Epi e] :
    (ShortComplex.mk (kernel.ι e) e (kernel.condition e)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel e)

/-- The short exact sequence `0 ⟶ I ⟶ K ⟶ coker f ⟶ 0` of the image `I` of `f : X ⟶ K`. -/
theorem shortExact_image_cokernel {X K : B} (f : X ⟶ K) :
    (ShortComplex.mk (image.ι f) (cokernel.π f)
      (by rw [← cancel_epi (factorThruImage f), image.fac_assoc, cokernel.condition,
        comp_zero])).ShortExact where
  exact := by
    refine ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ _ _
      (fun k hk ↦ cokernel.desc f k (by rw [← image.fac f, assoc, hk, comp_zero]))
      (fun k hk ↦ cokernel.π_desc _ _ _) (fun k hk m hm ↦ coequalizer.hom_ext ?_))
    simpa using hm

variable [EnoughInjectives B]

/-- **A left exact functor preserves the left homology of a short complex `X₁ ⟶ X₂ ⟶ X₃`** as
soon as `R¹Q X₁ = 0` and `R¹Q`, `R²Q` vanish on the kernel of `X₁ ⟶ X₂`. -/
theorem preservesLeftHomologyOf_of_isZero_rightDerived (S : ShortComplex B)
    (h₁ : IsZero ((Q.rightDerived 1).obj S.X₁))
    (hk₁ : IsZero ((Q.rightDerived 1).obj (kernel S.f)))
    (hk₂ : IsZero ((Q.rightDerived 2).obj (kernel S.f))) :
    Q.PreservesLeftHomologyOf S := by
  let hd := ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  let f' := hd.f'
  let e := factorThruImage f'
  let ek : kernel S.f ≅ kernel e :=
    kernelIsoOfEq hd.f'_i.symm ≪≫ kernelCompMono f' hd.i ≪≫
      kernelIsoOfEq (image.fac f').symm ≪≫ kernelCompMono e (image.ι f')
  have hS₁ := shortExact_kernel_of_epi e
  have hepi : Epi (Q.map e) := Stacks.Cohomology.epi_map_of_isZero_rightDerived_one Q hS₁
    (hk₁.of_iso ((Q.rightDerived 1).mapIso ek).symm)
  have hS₂ := Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one Q
    (shortExact_image_cokernel f')
    (isZero_rightDerived_X₃ hS₁ Q 1 h₁ (hk₂.of_iso ((Q.rightDerived 2).mapIso ek).symm))
  have := hS₂.epi_g
  have hc' := isCokernelEpiComp hS₂.exact.gIsCokernel (Q.map e) (h := Q.map f')
    (by dsimp only [ShortComplex.map_f]; rw [← Q.map_comp, image.fac])
  have : hd.IsPreservedBy Q :=
    { g := inferInstance
      f' := preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f')
        ((isColimitMapCoconeCoforkEquiv' Q (cokernel.condition f')).symm hc') }
  exact Functor.PreservesLeftHomologyOf.mk' Q hd

end Stacks.Cohomology.RightDerivedDelta

end

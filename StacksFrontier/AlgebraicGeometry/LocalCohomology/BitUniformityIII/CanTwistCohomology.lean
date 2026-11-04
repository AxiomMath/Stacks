module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistDown

/-!
# The twisted image, kernel and cokernel of a map of sheaves on the blowup

Let `p : X → Spec(A)` be the blowup of `Spec(A)` in `I`, with twists `𝒪_X(t)`, `t ∈ ℤ`, and let
`α : ℰ ⟶ 𝒟` be a map of `𝒪_X`-modules. The duality step of [Stacks, Tag 0GAC] works with the two
short exact sequences

`0 → ker(α) → ℰ → im(α) → 0` and `0 → im(α) → 𝒟 → coker(α) → 0`

twisted by `𝒪_X(t)`, at `α = can : p^*(M^∨) → (p^*M)^∨`. This file records everything about
them that does not depend on what `α` is: the twisted sequences are short exact (`𝒪_X(t)` is
flat), so their long exact cohomology sequences give the exactness of
`H⁰(im(α)(t)) → H⁰(𝒟(t)) → H⁰(coker(α)(t))` and of
`H⁰(ℰ(t)) → H⁰(im(α)(t)) → H¹(ker(α)(t))`; the maps are natural in the twist; if `I^c` kills
the kernel or the cokernel then the twisting maps `t ↦ t - c` vanish on its cohomology
([Stacks, Tag 0GA9], `whiskerLeft_blowupTwistLE_eq_zero`); and for `ℰ`, `𝒟` quasi-coherent the
cohomology of the twisted kernel vanishes above the fibre dimension `d(S)`.

The image is `CategoryTheory.Abelian.image α`, the kernel of the cokernel of `α`, through which
`α` factors as `Abelian.factorThruImage α ≫ Abelian.image.ι α`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.shortExact_kernel_factorThruImage`,
  `shortExact_image_cokernel`: the two short exact sequences, and their twists
  `shortExact_twist_kernel` and `shortExact_twist_image`.
* `Stacks.LocalCohomology.UniformityIII.exact_twist_image_cokernel`,
  `exact_twist_factorThruImage_δ`: exactness of the two segments of the long exact sequences.
* `Stacks.LocalCohomology.UniformityIII.blowupHmodMap_whiskerRight_comp_whiskerLeft`,
  `twist_kernel_δ_naturality`: naturality in the twist.
* `Stacks.LocalCohomology.UniformityIII.blowupHmodMap_whiskerLeft_blowupTwistLE_eq_zero`:
  Tag 0GA9 on cohomology.
* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupHmod_twist_kernel`: the vanishing
  above `d(S)`.

## References

* [Stacks Project, Tag 0GA9](https://stacks.math.columbia.edu/tag/0GA9)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter)

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The two short exact sequences of a map -/

section Sequences

variable {E D : (blowupScheme I).Modules} (α : E ⟶ D)

/-- The kernel of `α` followed by the projection onto its image is zero. -/
theorem kernel_ι_comp_factorThruImage :
    kernel.ι α ≫ Abelian.factorThruImage α = 0 := by
  rw [← cancel_mono (Abelian.image.ι α), Category.assoc, Abelian.image.fac, kernel.condition,
    zero_comp]

/-- **`0 → ker(α) → ℰ → im(α) → 0` is short exact.** -/
theorem shortExact_kernel_factorThruImage :
    (ShortComplex.mk (kernel.ι α) (Abelian.factorThruImage α)
      (kernel_ι_comp_factorThruImage I α)).ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) inferInstance
    inferInstance
  refine KernelFork.IsLimit.ofι _ _
    (fun k hk => kernel.lift α k (by rw [← Abelian.image.fac α, ← Category.assoc, hk,
      zero_comp]))
    (fun k hk => kernel.lift_ι _ _ _) (fun k hk m hm => ?_)
  rw [← cancel_mono (kernel.ι α), kernel.lift_ι]
  exact hm

/-- The inclusion of the image of `α` followed by the projection onto its cokernel is zero. -/
theorem image_ι_comp_cokernel_π : Abelian.image.ι α ≫ cokernel.π α = 0 :=
  kernel.condition _

/-- **`0 → im(α) → 𝒟 → coker(α) → 0` is short exact.** -/
theorem shortExact_image_cokernel :
    (ShortComplex.mk (Abelian.image.ι α) (cokernel.π α)
      (image_ι_comp_cokernel_π I α)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance inferInstance

/-- **The twisted kernel sequence `0 → ker(α)(t) → ℰ(t) → im(α)(t) → 0` is short exact**, the
twist being flat. -/
theorem shortExact_twist_kernel (t : ℤ) :
    (ShortComplex.mk (kernel.ι α ▷ blowupTwistInt I t)
      (Abelian.factorThruImage α ▷ blowupTwistInt I t)
      (whiskerRight_comp_whiskerRight_eq_zero I _ _ (kernel_ι_comp_factorThruImage I α)
        _)).ShortExact :=
  shortExact_whiskerRight_blowupTwistInt I _ _ _ (shortExact_kernel_factorThruImage I α) t

/-- **The twisted image sequence `0 → im(α)(t) → 𝒟(t) → coker(α)(t) → 0` is short exact.** -/
theorem shortExact_twist_image (t : ℤ) :
    (ShortComplex.mk (Abelian.image.ι α ▷ blowupTwistInt I t)
      (cokernel.π α ▷ blowupTwistInt I t)
      (whiskerRight_comp_whiskerRight_eq_zero I _ _ (image_ι_comp_cokernel_π I α)
        _)).ShortExact :=
  shortExact_whiskerRight_blowupTwistInt I _ _ _ (shortExact_image_cokernel I α) t

/-- **Left exactness of `Γ` on the twisted image sequence**: `H⁰(X, im(α)(t)) → H⁰(X, 𝒟(t)) →
H⁰(X, coker(α)(t))` is exact. -/
theorem exact_twist_image_cokernel (t : ℤ) :
    Function.Exact (blowupHmodMap I 0 (Abelian.image.ι α ▷ blowupTwistInt I t)).hom
      (blowupHmodMap I 0 (cokernel.π α ▷ blowupTwistInt I t)).hom :=
  exact_blowupHmodMap I _ _ _ (shortExact_twist_image I α t) 0

/-- `H⁰(X, im(α)(t)) → H⁰(X, 𝒟(t))` is injective. -/
theorem injective_twist_image_ι (t : ℤ) :
    Function.Injective (blowupHmodMap I 0 (Abelian.image.ι α ▷ blowupTwistInt I t)).hom :=
  injective_blowupHmodMap I _ _ _ (shortExact_twist_image I α t)

/-- **The long exact sequence of the twisted kernel sequence at `H⁰(X, im(α)(t))`**: the image
of `H⁰(X, ℰ(t))` is the kernel of the connecting map to `H¹(X, ker(α)(t))`. -/
theorem exact_twist_factorThruImage_δ (t : ℤ) :
    Function.Exact (blowupHmodMap I 0 (Abelian.factorThruImage α ▷ blowupTwistInt I t)).hom
      ((blowupDeltaMod I).δ (shortExact_twist_kernel I α t) 0).hom :=
  exact_blowupHmodMap_δ I _ _ _ (shortExact_twist_kernel I α t) 0

end Sequences

/-! ### Naturality in the twist -/

section Naturality

/-- **The twisting maps commute with every map of sheaves on cohomology**: for `f : F ⟶ G` and
`t' ≤ t`, `Hⁱ(f(t)) ≫ Hⁱ(G(t) → G(t')) = Hⁱ(F(t) → F(t')) ≫ Hⁱ(f(t'))`, by `whisker_exchange`. -/
theorem blowupHmodMap_whiskerRight_comp_whiskerLeft (i : ℕ) {F G : (blowupScheme I).Modules}
    (f : F ⟶ G) {t t' : ℤ} (h : t' ≤ t) :
    blowupHmodMap I i (f ▷ blowupTwistInt I t) ≫ blowupHmodMap I i (G ◁ blowupTwistLE I h) =
      blowupHmodMap I i (F ◁ blowupTwistLE I h) ≫ blowupHmodMap I i (f ▷ blowupTwistInt I t') := by
  refine (((blowupΓmod I).rightDerived i).map_comp _ _).symm.trans ?_
  refine Eq.trans ?_ (((blowupΓmod I).rightDerived i).map_comp _ _)
  exact congrArg (fun φ => ((blowupΓmod I).rightDerived i).map φ)
    (whisker_exchange f (blowupTwistLE I h)).symm

/-- The elementwise form of `blowupHmodMap_whiskerRight_comp_whiskerLeft`. -/
theorem blowupHmodMap_whiskerRight_whiskerLeft_apply (i : ℕ) {F G : (blowupScheme I).Modules}
    (f : F ⟶ G) {t t' : ℤ} (h : t' ≤ t) (x : blowupHmod I i (F ⊗ blowupTwistInt I t)) :
    blowupHmodMap I i (G ◁ blowupTwistLE I h) (blowupHmodMap I i (f ▷ blowupTwistInt I t) x) =
      blowupHmodMap I i (f ▷ blowupTwistInt I t') (blowupHmodMap I i (F ◁ blowupTwistLE I h) x) :=
  ConcreteCategory.congr_hom (blowupHmodMap_whiskerRight_comp_whiskerLeft I i f h) x

variable {E D : (blowupScheme I).Modules} (α : E ⟶ D)

/-- The twisting maps, as a morphism from the twist by `t` to the twist by `t'` of the kernel
sequence of `α`. -/
def twistKernelSeqMap {t t' : ℤ} (h : t' ≤ t) :
    ShortComplex.mk (kernel.ι α ▷ blowupTwistInt I t)
        (Abelian.factorThruImage α ▷ blowupTwistInt I t)
        (whiskerRight_comp_whiskerRight_eq_zero I _ _ (kernel_ι_comp_factorThruImage I α) _) ⟶
      ShortComplex.mk (kernel.ι α ▷ blowupTwistInt I t')
        (Abelian.factorThruImage α ▷ blowupTwistInt I t')
        (whiskerRight_comp_whiskerRight_eq_zero I _ _ (kernel_ι_comp_factorThruImage I α) _) where
  τ₁ := kernel α ◁ blowupTwistLE I h
  τ₂ := E ◁ blowupTwistLE I h
  τ₃ := Abelian.image α ◁ blowupTwistLE I h
  comm₁₂ := whisker_exchange (kernel.ι α) (blowupTwistLE I h)
  comm₂₃ := whisker_exchange (Abelian.factorThruImage α) (blowupTwistLE I h)

/-- **The connecting map of the twisted kernel sequence is natural in the twist**:
`H⁰(im(α)(t)) → H¹(ker(α)(t)) → H¹(ker(α)(t'))` is
`H⁰(im(α)(t)) → H⁰(im(α)(t')) → H¹(ker(α)(t'))`. -/
theorem twist_kernel_δ_naturality {t t' : ℤ} (h : t' ≤ t)
    (x : blowupHmod I 0 (Abelian.image α ⊗ blowupTwistInt I t)) :
    (blowupDeltaMod I).δ (shortExact_twist_kernel I α t') 0
        (blowupHmodMap I 0 (Abelian.image α ◁ blowupTwistLE I h) x) =
      blowupHmodMap I 1 (kernel α ◁ blowupTwistLE I h)
        ((blowupDeltaMod I).δ (shortExact_twist_kernel I α t) 0 x) :=
  ConcreteCategory.congr_hom ((blowupDeltaMod I).δ_naturality (shortExact_twist_kernel I α t)
    (shortExact_twist_kernel I α t') (twistKernelSeqMap I α h) 0) x

end Naturality

/-! ### Tag 0GA9 on cohomology, and the vanishing above the fibre dimension -/

/-- **Tag 0GA9 on cohomology.** If every `a ∈ I^c` kills `F`, then the map
`Hⁱ(X, F(t)) → Hⁱ(X, F(t'))` induced by the twisting map is zero whenever `t' + c ≤ t`. -/
theorem blowupHmodMap_whiskerLeft_blowupTwistLE_eq_zero (i : ℕ) (F : (blowupScheme I).Modules)
    {c : ℕ} (hF : ∀ a ∈ I ^ c, (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app F = 0)
    {t t' : ℤ} (h : t' ≤ t) (hc : t' + c ≤ t) :
    blowupHmodMap I i (F ◁ blowupTwistLE I h) = 0 := by
  rw [whiskerLeft_blowupTwistLE_eq_zero I F hF h hc]
  exact ((blowupΓmod I).rightDerived i).map_zero _ _

/-- **The cohomology of the twisted kernel vanishes above the fibre dimension**: for `ℰ` and `𝒟`
quasi-coherent, the kernel of `α : ℰ ⟶ 𝒟` and its twists are quasi-coherent, so
`Hⁱ(X, ker(α)(t)) = 0` for `i > d(S)`. -/
theorem subsingleton_blowupHmod_twist_kernel [IsNoetherianRing A]
    {E D : (blowupScheme I).Modules} [E.IsQuasicoherent] [D.IsQuasicoherent] (α : E ⟶ D)
    (t : ℤ) {i : ℕ} (hi : fibreDim I < i) :
    Subsingleton (blowupHmod I i (kernel α ⊗ blowupTwistInt I t)) := by
  have : (kernel α).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel α
  exact subsingleton_blowupHmod_of_fibreDim_lt I _ hi

end Stacks.LocalCohomology.UniformityIII

end

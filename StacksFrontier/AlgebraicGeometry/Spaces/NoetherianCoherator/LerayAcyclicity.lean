module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.MayerVietorisDegreeOne

/-!
# Higher direct images of a direct image along a morphism without higher direct images

For additive left exact functors `j : A' ⥤ A` preserving injective objects and `h : A ⥤ B`, and an
object `M` of `A'` with `R^q j(M) = 0` for `q ≥ 1`, the vanishing of `R^p(j ⋙ h)(M)` forces the
vanishing of `R^p h(j M)`, for every `p ≥ 1`.  This is the degenerate case of the Grothendieck
spectral sequence, proved here by dimension shifting along an injective embedding of `M`.

## Main results

* `CategoryTheory.Functor.isZero_rightDerived_map_of_comp`: the vanishing transfer.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_obj_of_isEtale`: its instance
  for the direct images along an étale morphism followed by any morphism of algebraic spaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace CategoryTheory.Functor

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B] [Abelian A] [Abelian A']
  [Abelian B] [EnoughInjectives A] [EnoughInjectives A']

/-- In a short exact sequence whose middle term is `F`-acyclic in degrees `p` and `p + 1`, the
vanishing of `R^p F` at the quotient and of `R^{p+1} F` at the subobject are equivalent. -/
theorem isZero_rightDerived_succ_iff_of_shortExact (F : A ⥤ B) [F.Additive]
    {S : ShortComplex A} (hS : S.ShortExact) (p : ℕ)
    (h₁ : IsZero ((F.rightDerived p).obj S.X₂)) (h₂ : IsZero ((F.rightDerived (p + 1)).obj S.X₂)) :
    IsZero ((F.rightDerived (p + 1)).obj S.X₁) ↔ IsZero ((F.rightDerived p).obj S.X₃) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard B
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F
  have hmono : Mono (D.δ hS p) := (D.exact_δ₁ hS p).mono_g (h₁.eq_of_src _ _)
  have hepi : Epi (D.δ hS p) := (D.exact_δ₂ hS p).epi_f (h₂.eq_of_tgt _ _)
  have : IsIso (D.δ hS p) := isIso_of_mono_of_epi _
  exact (asIso (D.δ hS p)).isZero_iff.symm

/-- **The degenerate Grothendieck spectral sequence, in vanishing form.**  For `j` additive, left
exact and preserving injective objects, `h` additive and left exact, and `M` with
`R^q j(M) = 0` for every `q ≥ 1`: if `R^p(j ⋙ h)(M) = 0` with `p ≥ 1` then `R^p h(j M) = 0`. -/
theorem isZero_rightDerived_map_of_comp (j : A' ⥤ A) [j.Additive] [PreservesFiniteLimits j]
    [j.PreservesInjectiveObjects] (h : A ⥤ B) [h.Additive] [PreservesFiniteLimits h] :
    ∀ (p : ℕ) (M : A'), (∀ q : ℕ, IsZero ((j.rightDerived (q + 1)).obj M)) →
      IsZero (((j ⋙ h).rightDerived (p + 1)).obj M) →
        IsZero ((h.rightDerived (p + 1)).obj (j.obj M)) := by
  intro p
  induction p with
  | zero => exact fun M _ hM => isZero_rightDerived_one_map_of_comp j h M hM
  | succ p ih =>
    intro M hj hM
    let := HasDerivedCategory.standard A'
    let := HasDerivedCategory.standard A
    let ι := Injective.ι M
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    -- the image sequence `0 ⟶ j M ⟶ j I ⟶ j Q ⟶ 0` is short exact, `R¹ j M` vanishing
    have hjS : (S.map j).ShortExact := by
      refine { exact := hS.exact.map_of_mono_of_preservesKernel j inferInstance inferInstance,
               mono_f := by dsimp; infer_instance, epi_g := ?_ }
      let Dj := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives j
      exact epi_map_of_epi_rightDerived_zero_map j S.g
        ((Dj.exact_δ₁ hS 0).epi_f ((hj 0).eq_of_tgt _ _))
    -- `R^q j` vanishes on the quotient
    have hjQ : ∀ q : ℕ, IsZero ((j.rightDerived (q + 1)).obj (cokernel ι)) := fun q =>
      (isZero_rightDerived_succ_iff_of_shortExact j hS (q + 1)
        (isZero_rightDerived_obj_injective_succ j q _)
        (isZero_rightDerived_obj_injective_succ j (q + 1) _)).1 (hj (q + 1))
    have hFQ : IsZero (((j ⋙ h).rightDerived (p + 1)).obj (cokernel ι)) :=
      (isZero_rightDerived_succ_iff_of_shortExact (j ⋙ h) hS (p + 1)
        ((j ⋙ h).isZero_rightDerived_obj_injective_succ p (Injective.under M))
        ((j ⋙ h).isZero_rightDerived_obj_injective_succ (p + 1) _)).1 hM
    have : Injective (S.map j).X₂ := j.injective_obj (Injective.under M)
    exact (isZero_rightDerived_succ_iff_of_shortExact h hjS (p + 1)
      (h.isZero_rightDerived_obj_injective_succ p _)
      (h.isZero_rightDerived_obj_injective_succ (p + 1) _)).2 (ih (cokernel ι) hjQ hFQ)

end CategoryTheory.Functor


namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  isGrothendieckAbelian_modules

attribute [local instance 5000] modulePushforward_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Leray for an étale morphism without higher direct images.**  If `j : Y ⟶ X` is étale and
`R^q j_*M = 0` for `q ≥ 1`, then `R^{p+1}(j ≫ f)_*M = 0` forces `R^{p+1} f_*(j_*M) = 0`. -/
theorem isZero_rightDerived_modulePushforward_obj_of_isEtale {X Y Z : AlgebraicSpaces B S hS}
    (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) (f : X ⟶ Z) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hj0 : ∀ q : ℕ, IsZero (((modulePushforward B S hS j).rightDerived (q + 1)).obj M)) (p : ℕ)
    (hp : IsZero (((modulePushforward B S hS (j ≫ f)).rightDerived (p + 1)).obj M)) :
    IsZero (((modulePushforward B S hS f).rightDerived (p + 1)).obj
      ((modulePushforward B S hS j).obj M)) := by
  have := preservesInjectiveObjects_modulePushforward_of_isEtale B S hS j hj
  have := preservesFiniteLimits_modulePushforward B S hS j
  have := preservesFiniteLimits_modulePushforward B S hS f
  exact Functor.isZero_rightDerived_map_of_comp _ _ p M hj0 <|
    hp.of_iso ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (modulePushforwardCompIso B S hS j f) (p + 1)).app M)

end AlgebraicGeometry.Space

end

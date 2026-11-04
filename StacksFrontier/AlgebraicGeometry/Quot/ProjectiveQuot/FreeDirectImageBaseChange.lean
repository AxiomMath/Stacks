module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FreeDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheafNaturality

/-!
# The direct image of `𝒪(m)^{⊕ r}` on `ℙⁿ_T` commutes with every base change

For every `g : T' ⟶ T` and `m ≥ 0` the base-change morphism
`g^* π_*(𝒪^{⊕ r}(m)) ⟶ π'_*((ℙⁿ_g)^* 𝒪^{⊕ r}(m))` is an isomorphism, with no flatness assumption on
`g`: on each summand `𝒪(m)` it is read off from the canonical isomorphism
`(𝒪_T[T₀, …, Tₙ])_m ≅ π_* 𝒪(m)` and its compatibility with base change
(`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.toPushforwardTwistOver_baseChange`).
This is the free half of the base-change step in the proof of Stacks 0DPA.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isIso_app_sigma_of_isIso`: a natural transformation between
  functors preserving a coproduct is invertible at the coproduct once it is at each summand.
* `AlgebraicGeometry.ProjectiveQuot.isIso_baseChangeNatTrans_twistingSheaf`.
* `AlgebraicGeometry.ProjectiveQuot.isIso_baseChangeNatTrans_twist_freeModule`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)

universe u

namespace AlgebraicGeometry.ProjectiveQuot

/-- **A natural transformation is invertible at a preserved coproduct** once it is invertible at
every summand: through the comparison isomorphisms it is the coproduct of its components. -/
theorem isIso_app_sigma_of_isIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (α : F ⟶ G) {J : Type*} (f : J → C) [HasCoproduct f]
    [HasCoproduct fun j => F.obj (f j)] [HasCoproduct fun j => G.obj (f j)]
    [PreservesColimit (Discrete.functor f) F] [PreservesColimit (Discrete.functor f) G]
    (h : ∀ j, IsIso (α.app (f j))) : IsIso (α.app (∐ f)) := by
  have key : sigmaComparison F f ≫ α.app (∐ f) =
      Limits.Sigma.map (fun j => α.app (f j)) ≫ sigmaComparison G f := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc, ι_comp_sigmaComparison]
    exact α.naturality (Sigma.ι f j)
  have hmap : IsIso (Limits.Sigma.map (fun j => α.app (f j))) :=
    ⟨Limits.Sigma.map (fun j => inv (α.app (f j))), by ext; simp, by ext; simp⟩
  have heq : α.app (∐ f) =
      inv (sigmaComparison F f) ≫ Limits.Sigma.map (fun j => α.app (f j)) ≫
        sigmaComparison G f := by
    rw [← key, IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

variable (n r : ℕ)

/-- **Base change for `π_* 𝒪(d)`, `d ≥ 0`, along any morphism.** The canonical morphism
`(𝒪_T[T₀, …, Tₙ])_d ⟶ π_* 𝒪(d)` is invertible over every base, and its base change, read through
the base-change morphism and the identification of the twists, is the canonical morphism over
`T'`; so the base-change morphism is invertible. -/
theorem isIso_baseChangeNatTrans_twistingSheaf {T' T : Scheme.{u}} (g : T' ⟶ T) {d : ℤ}
    (hd : 0 ≤ d) :
    IsIso ((baseChangeNatTrans (isPullback_projectiveSpaceOverMap n g).w).app
      (twistingSheaf n T d)) := by
  have hkey := toPushforwardTwistOver_baseChange n g d
  have h₂ : IsIso (toPushforwardTwistOver n T' d) := isIso_toPushforwardTwistOver n T' (Or.inl hd)
  have ha : IsIso ((Scheme.Modules.pullback g).map (toPushforwardTwistOver n T d)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_toPushforwardTwistOver n T (Or.inl hd))
  have hc : IsIso ((Scheme.Modules.pushforward (projectiveSpaceOver n T' ↘ T')).map
      (twistOverPullbackIso n g d).hom) := Functor.map_isIso _ _
  have hrhs : IsIso ((pullbackBaseDegreeSheafIso n g d).hom ≫ toPushforwardTwistOver n T' d) :=
    inferInstance
  rw [← hkey] at hrhs
  have := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ha hrhs
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hc this

/-- **Base change for `π_*(𝒪^{⊕ r}(m))` along any morphism**, `m ≥ 0`: the twist of the free
module is the sum of `r` copies of `𝒪(m)`, and both sides of the base-change morphism commute
with finite sums. -/
theorem isIso_baseChangeNatTrans_twist_freeModule {T' T : Scheme.{u}} (g : T' ⟶ T) (m : ℕ) :
    IsIso ((baseChangeNatTrans (isPullback_projectiveSpaceOverMap n g).w).app
      (twist (m : ℤ) (freeModule n r T))) := by
  rw [NatTrans.isIso_app_iff_of_iso _ (twistFreeModuleIso n r T m)]
  exact isIso_app_sigma_of_isIso _ _ fun _ =>
    isIso_baseChangeNatTrans_twistingSheaf n g (Int.natCast_nonneg m)

end AlgebraicGeometry.ProjectiveQuot

end

module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientReduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletion

/-!
# What the comparison map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` being invertible amounts to

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites and let `ℐ ⊂ 𝒪`, `ℐ' ⊂ 𝒪'` be
sheaves of ideals such that `f^♯` carries `f^{-1}ℐ` into `ℐ'`. [Stacks, Tag 0A0G] asserts that
`Rf_*` commutes with derived completion, i.e. that the canonical map
`(Rf_*K)^∧ ⟶ Rf_*(K^∧)` of
`AlgebraicGeometry.RingedSite.derivedCompletionPushforwardComparison` is invertible for *every*
`K ∈ D(𝒪')`. This file reformulates that assertion in two ways, complementing the
one-directional criterion of `PushforwardCommutesCompletion.lean`.

* The tag asserts that `Rf_*(K^∧)`, together with `Rf_*(K ⟶ K^∧)`, *is* a derived completion of
  `Rf_*K`. Since `Rf_*(K^∧)` is derived complete ([Stacks, Tag 099J]), the comparison map is
  invertible precisely when that object has the universal property that defines `(Rf_*K)^∧`:
  composition with `Rf_*(K ⟶ K^∧)` is a bijection `Hom(Rf_*(K^∧), N) ≃ Hom(Rf_*K, N)` for every
  derived-complete `N`. That is `isIso_derivedCompletionPushforwardComparison_iff_bijective`,
  and it is an equivalence: it is the tag's assertion rewritten as a statement about hom-sets.
* The criterion already available,
  `AlgebraicGeometry.RingedSite.isIso_derivedCompletionPushforwardComparison_of_isIso_map_unit`,
  assumes `Rf_*(K ⟶ K^∧)` invertible. `isIso_map_derivedCompletionUnit_iff` measures that
  hypothesis: it holds if and only if `Rf_*K` is *already* derived complete **and** the
  comparison map is invertible. So that criterion, and with it the registered case of a
  derived-complete `K`, covers exactly the objects whose derived direct image is already
  complete, and it cannot reach the general case of the tag by itself: the hypothesis is
  strictly stronger than the conclusion.

## Main results

* `AlgebraicGeometry.RingedSite.bijective_derivedCompletionUnit_comp`: the universal property of
  derived completion as a bijection of hom-sets — for derived-complete `N`, composition with
  `K ⟶ K^∧` is a bijection `Hom(K^∧, N) ≃ Hom(K, N)`.
* `AlgebraicGeometry.RingedSite.isIso_derivedCompletionPushforwardComparison_iff_bijective`: the
  comparison map of [Stacks, Tag 0A0G] is invertible at `K` if and only if composition with
  `Rf_*(K ⟶ K^∧)` is a bijection `Hom(Rf_*(K^∧), N) ≃ Hom(Rf_*K, N)` for every derived-complete
  `N`.
* `AlgebraicGeometry.RingedSite.isIso_map_derivedCompletionUnit_iff`: `Rf_*(K ⟶ K^∧)` is
  invertible if and only if `Rf_*K` is derived complete and the comparison map is invertible.

## Implementation notes

Neither statement is tagged with Tag 0A0G: the first is an equivalent rephrasing of the tag
and the second is a statement about the scope of a criterion.

`bijective_derivedCompletionUnit_comp` is a general fact about the reflector of
[Stacks, Tag 099F] and not about `Rf_*`. Its injectivity half is
`AlgebraicGeometry.RingedSite.derivedCompletion_hom_ext` of `AdicQuotientReduction.lean`.

## References

* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

section Reflector

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- **The universal property of derived completion as a bijection of hom-sets.** For a
derived-complete `N`, composition with the unit `K ⟶ K^∧` is a bijection
`Hom(K^∧, N) ≃ Hom(K, N)`. This is the hom-set bijection of the reflector adjunction of
[Stacks, Tag 099F], read through the fully faithful inclusion of the derived-complete
objects. -/
theorem bijective_derivedCompletionUnit_comp
    {K N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hN : IsDerivedComplete.{u, u, u, u} X I N) :
    Function.Bijective (fun g : (derivedCompletion X I).obj K ⟶ N ↦
      (derivedCompletionUnit X I).app K ≫ g) := by
  refine ⟨fun g g' e ↦ derivedCompletion_hom_ext X I hN e, fun h ↦ ⟨?_, ?_⟩⟩
  · exact (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map
      (((derivedCompletionAdjunction X I).homEquiv K
        (⟨N, hN⟩ : ObjectProperty.FullSubcategory
          (IsDerivedComplete.{u, u, u, u} X I))).symm h)
  · exact ((derivedCompletionAdjunction X I).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)

end Reflector

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
  (I' : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (hI : PushforwardIdealCompatible f I I')
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I')).IsRightAdjoint]
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} Y I)).IsRightAdjoint]

include hI

/-- **[Stacks, Tag 0A0G] as a universal property.** The comparison map
`(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible at `K` if and only if `Rf_*(K^∧)`, with the map
`Rf_*(K ⟶ K^∧)`, has the universal property of the derived completion of `Rf_*K`: composition
with `Rf_*(K ⟶ K^∧)` is a bijection `Hom(Rf_*(K^∧), N) ≃ Hom(Rf_*K, N)` for every
derived-complete `N`.

The two halves use nothing beyond the reflector adjunction: forwards, composition with
`Rf_*(K ⟶ K^∧)` is composition with the comparison map followed by composition with the unit
`Rf_*K ⟶ (Rf_*K)^∧`, by
`derivedCompletionUnit_comp_derivedCompletionPushforwardComparison`, and both of those are
bijections; backwards, the bijection at `N = (Rf_*K)^∧` produces the inverse, and the two
identities it has to satisfy are checked by the uniqueness halves of the two universal
properties, that of `(Rf_*K)^∧` and the assumed one of `Rf_*(K^∧)`. -/
theorem isIso_derivedCompletionPushforwardComparison_iff_bijective
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsIso ((derivedCompletionPushforwardComparison f I I' hI).app K) ↔
      ∀ N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))),
        IsDerivedComplete.{u, u, u, u} Y I N →
          Function.Bijective (fun φ : (derivedPushforward.{u} f.toRingedToposSiteHom).obj
              ((derivedCompletion X I').obj K) ⟶ N ↦
            (derivedPushforward.{u} f.toRingedToposSiteHom).map
              ((derivedCompletionUnit X I').app K) ≫ φ) := by
  refine ⟨fun hc N hN ↦ ?_, fun hb ↦ ?_⟩
  · have key : (fun φ : (derivedPushforward.{u} f.toRingedToposSiteHom).obj
          ((derivedCompletion X I').obj K) ⟶ N ↦
        (derivedPushforward.{u} f.toRingedToposSiteHom).map
          ((derivedCompletionUnit X I').app K) ≫ φ) =
        (fun ψ : (derivedCompletion Y I).obj
            ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) ⟶ N ↦
          (derivedCompletionUnit Y I).app
            ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) ≫ ψ) ∘
        (fun φ : (derivedPushforward.{u} f.toRingedToposSiteHom).obj
            ((derivedCompletion X I').obj K) ⟶ N ↦
          (derivedCompletionPushforwardComparison f I I' hI).app K ≫ φ) := by
      funext φ
      rw [Function.comp_apply, ← Category.assoc,
        derivedCompletionUnit_comp_derivedCompletionPushforwardComparison f I I' hI K]
    rw [key]
    exact (bijective_derivedCompletionUnit_comp Y I hN).comp
      ⟨fun _ _ e ↦ (cancel_epi ((derivedCompletionPushforwardComparison f I I' hI).app K)).mp e,
        fun ψ ↦ ⟨inv ((derivedCompletionPushforwardComparison f I I' hI).app K) ≫ ψ, by simp⟩⟩
  · have hc := isDerivedComplete_derivedCompletion_obj Y I
      ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K)
    obtain ⟨ψ, hψ⟩ := (hb _ hc).2
      ((derivedCompletionUnit Y I).app ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K))
    beta_reduce at hψ
    have hcomp := derivedCompletionUnit_comp_derivedCompletionPushforwardComparison f I I' hI K
    refine ⟨ψ, derivedCompletion_hom_ext Y I hc ?_, ?_⟩
    · rw [← Category.assoc, hcomp, hψ]; simp
    · refine (hb _ (isDerivedComplete_derivedPushforward_derivedCompletion f I I' hI K)).1 ?_
      beta_reduce
      rw [← Category.assoc, hψ, hcomp]; simp

/-- **The exact scope of the criterion
`isIso_derivedCompletionPushforwardComparison_of_isIso_map_unit`.** Its hypothesis, that
`Rf_*(K ⟶ K^∧)` be invertible, holds if and only if `Rf_*K` is *already* derived complete and
the comparison map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible.

So that criterion is strictly stronger than its conclusion, and the objects it covers are
exactly those with `Rf_*K` derived complete — for which the unit `Rf_*K ⟶ (Rf_*K)^∧` is
invertible anyway. In particular it cannot be used to reach the general case of
[Stacks, Tag 0A0G]. -/
theorem isIso_map_derivedCompletionUnit_iff
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsIso ((derivedPushforward.{u} f.toRingedToposSiteHom).map
        ((derivedCompletionUnit X I').app K)) ↔
      IsDerivedComplete.{u, u, u, u} Y I
          ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) ∧
        IsIso ((derivedCompletionPushforwardComparison f I I' hI).app K) := by
  refine ⟨fun h ↦ ⟨(isDerivedComplete_iff_of_iso Y I (asIso ((derivedPushforward.{u}
      f.toRingedToposSiteHom).map ((derivedCompletionUnit X I').app K)))).mpr
      (isDerivedComplete_derivedPushforward_derivedCompletion f I I' hI K),
    isIso_derivedCompletionPushforwardComparison_of_isIso_map_unit f I I' hI h⟩, ?_⟩
  rintro ⟨hcomplete, hc⟩
  have := isIso_derivedCompletionUnit_app Y I hcomplete
  rw [← derivedCompletionUnit_comp_derivedCompletionPushforwardComparison f I I' hI K]
  infer_instance

end AlgebraicGeometry.RingedSite

end

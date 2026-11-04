module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistSquare

/-!
# Assertion (i) of Stacks Tag 01QK against a bound comparison

In the situation of Stacks Tag 01QH — `X` a scheme, `𝓛` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, 𝓛)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism of Stacks Tag 01PZ — the
first assertion of Stacks Tag 01QK reads

> Note that the isomorphism `f^*𝒪_Y(n) → 𝓛^{⊗ n}` of Lemma 01QI is just `θ_{𝓛^{⊗ n}}`.

Here `θ_𝓕 : f^* M̃ ⟶ 𝓕` is Tag 01QJ's comparison. This file studies the assertion for the
comparison `Stacks.SectionRingProjQuasicoherent.pullbackComparison L hL c` obtained by
transposing a family `c : M̃ ⟶ f_*𝓕` as in Tag 0B5I, a function of `c` that is odd in `c`
(`Stacks.SectionRingProjQuasicoherent.TwistCompatibility.pullbackComparison_app_neg`).

An equation between `θ` and a `c`-free morphism `α` therefore cannot hold for every `c`:
evaluating at `c` and at `-c` gives `α = -α`. When `α` is an isomorphism, as Tag 01QI asserts,
cancelling it turns this into `𝟙 + 𝟙 = 0` on `𝓛^{⊗ n}`, a condition on the scheme rather than on
the candidate. So the assertion holds uniformly in the family only over a base where `2 = 0`.

On the other hand the assertion is consistent and pins the family: for each `𝓕` and each
candidate `α`, exactly one value of `c.app 𝓕` makes `θ_𝓕 = α`. In this sense assertion (i) is a
normalization of Tag 01QJ's comparison at the objects `𝓛^{⊗ n}`.

The two corners are `(pullbackTildeFunctor L hL).obj (𝓛^{⊗ n})`, i.e. `f^*(Γ_*(X, 𝓛, 𝓛^{⊗ n}))~`,
and `𝓛^{⊗ n}`. Every statement below quantifies over the morphism, respectively the isomorphism,
between them.

## Main results

All in the namespace `Stacks.SectionRingProjTheta`.

* `one_add_one_eq_zero_of_add_self_eq_zero`: an isomorphism of a preadditive category which is
  `2`-torsion forces `𝟙 + 𝟙 = 0` at its target.
* `add_self_eq_zero_of_app_eq`: if a morphism `α` equals `θ` for the family `c` and also for
  `-c`, then `α` is `2`-torsion.
* `not_forall_app_eq`: no morphism that is not `2`-torsion equals `θ` uniformly in the family.
* `not_forall_app_eq_of_iso`: if `𝟙 + 𝟙 ≠ 0` at `𝓕`, no isomorphism `f^*M̃ ≅ 𝓕` equals `θ_𝓕`
  uniformly in the family.
* `not_forall_app_natTensorPow_eq_of_iso`: the same at `𝓕 = 𝓛^{⊗ n}`.
* `existsUnique_binder_app_of_app_eq`: for every `𝓕` and every candidate `α` there is exactly one
  `γ : M̃ ⟶ f_*𝓕` with `θ_𝓕 = α` when `c.app 𝓕` is `γ`.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

open Stacks.Ample
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (tildeFunctor pullbackTildeFunctor restrictComparison
  pullbackComparison)

universe v₁ u₁ u

namespace Stacks.SectionRingProjTheta

/-! ### Cancelling a `2`-torsion isomorphism -/

section AbstractIso

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- **An isomorphism which is `2`-torsion forces `𝟙 + 𝟙 = 0` at its target.** -/
theorem one_add_one_eq_zero_of_add_self_eq_zero {A B : C} (α : A ≅ B)
    (h : α.hom + α.hom = 0) : 𝟙 B + 𝟙 B = 0 := by
  have h' : α.inv ≫ (α.hom + α.hom) = α.inv ≫ 0 := congrArg (α.inv ≫ ·) h
  rwa [Preadditive.comp_add, α.inv_hom_id, Limits.comp_zero] at h'

end AbstractIso

/-! ### The obstruction to assertion (i) of Stacks Tag 01QK -/

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : IsAmple X L)

/-- **Tag 01QJ's comparison cannot equal a `c`-free morphism for both signs of the binder.** If
`α` equals `θ` for Tag 0B5I's family `c` and also for `-c`, then `α = -α`. -/
theorem add_self_eq_zero_of_app_eq
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F : X.Modules) (α : (pullbackTildeFunctor L hL).obj F ⟶ F)
    (h : (pullbackComparison L hL c).app F = α)
    (hneg : (pullbackComparison L hL (-c)).app F = α) :
    α + α = 0 := by
  rw [Stacks.SectionRingProjQuasicoherent.TwistCompatibility.pullbackComparison_app_neg L hL c F,
    h] at hneg
  exact add_eq_zero_iff_neg_eq.mpr hneg

/-- **No morphism that is not `2`-torsion equals Tag 01QJ's comparison uniformly in Tag 0B5I's
binder.** -/
theorem not_forall_app_eq
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F : X.Modules) (α : (pullbackTildeFunctor L hL).obj F ⟶ F) (hne : α + α ≠ 0) :
    ¬ ∀ d : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL),
        (pullbackComparison L hL d).app F = α := fun h =>
  hne (add_self_eq_zero_of_app_eq L hL c F α (h c) (h (-c)))

/-- **The obstruction to assertion (i) of Stacks Tag 01QK.** If `𝟙 + 𝟙 ≠ 0` at `𝓕`, no
isomorphism `f^*M̃ ≅ 𝓕` equals Tag 01QJ's comparison uniformly in Tag 0B5I's binder. -/
theorem not_forall_app_eq_of_iso
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F : X.Modules) (α : (pullbackTildeFunctor L hL).obj F ≅ F) (hchar : 𝟙 F + 𝟙 F ≠ 0) :
    ¬ ∀ d : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL),
        (pullbackComparison L hL d).app F = α.hom :=
  not_forall_app_eq L hL c F α.hom fun h => hchar (one_add_one_eq_zero_of_add_self_eq_zero α h)

/-- **The obstruction at `𝓕 = 𝓛^{⊗ n}`**: if `𝟙 + 𝟙 ≠ 0` at `𝓛^{⊗ n}`, no isomorphism
`f^*(Γ_*(X, 𝓛, 𝓛^{⊗ n}))~ ≅ 𝓛^{⊗ n}` equals Tag 01QJ's comparison uniformly in Tag 0B5I's
binder. -/
theorem not_forall_app_natTensorPow_eq_of_iso
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL)) (n : ℕ)
    (α : (pullbackTildeFunctor L hL).obj (Stacks.TensorPowers.natTensorPow L n) ≅
      Stacks.TensorPowers.natTensorPow L n)
    (hchar : 𝟙 (Stacks.TensorPowers.natTensorPow L n) +
      𝟙 (Stacks.TensorPowers.natTensorPow L n) ≠ 0) :
    ¬ ∀ d : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL),
        (pullbackComparison L hL d).app (Stacks.TensorPowers.natTensorPow L n) = α.hom :=
  not_forall_app_eq_of_iso L hL c (Stacks.TensorPowers.natTensorPow L n) α hchar

/-! ### Assertion (i) as a normalization of Tag 01QJ's binder -/

section Restrict

variable [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- **Assertion (i) of Stacks Tag 01QK pins Tag 01QJ's binder, and pins it uniquely.** For every
`𝓕` and every candidate morphism `α`, there is exactly one `γ : M̃ ⟶ f_*𝓕` for which the
transposed morphism — which is `Stacks.SectionRingProjQuasicoherent.pullbackComparison`'s
component when Tag 0B5I's family takes the value `γ` at `𝓕`, by
`Stacks.SectionRingProjTheta.pullbackComparison_app` — equals `α`. -/
theorem existsUnique_binder_app_of_app_eq (F : X.Modules)
    (α : (pullbackTildeFunctor L hL).obj F ⟶ F) :
    ∃! γ : (tildeFunctor L).obj F ⟶
        (Scheme.Modules.pushforward (projHomOfIsAmple L hL)).obj F,
      (pullbackTildeCrossIso L hL F).hom ≫
          ((Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map γ ≫
            (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).counit.app F) = α := by
  have hsymm : ∀ γ : (tildeFunctor L).obj F ⟶
      (Scheme.Modules.pushforward (projHomOfIsAmple L hL)).obj F,
      ((Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).homEquiv
          ((tildeFunctor L).obj F) F).symm γ =
        (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map γ ≫
          (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).counit.app F :=
    fun γ => (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).homEquiv_counit _ _ γ
  have key : ∀ γ : (tildeFunctor L).obj F ⟶
      (Scheme.Modules.pushforward (projHomOfIsAmple L hL)).obj F,
      ((pullbackTildeCrossIso L hL F).hom ≫
          ((Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map γ ≫
            (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).counit.app F) = α) ↔
        γ = (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).homEquiv
          ((tildeFunctor L).obj F) F ((pullbackTildeCrossIso L hL F).inv ≫ α) := by
    intro γ
    rw [← hsymm, ← Iso.eq_inv_comp, Equiv.symm_apply_eq]
  exact ⟨_, (key _).mpr rfl, fun γ hγ => (key γ).mp hγ⟩

end Restrict

end Scheme

end Stacks.SectionRingProjTheta

end

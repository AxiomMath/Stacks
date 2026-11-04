module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutAssembly

/-!
# The closed fibre of a localization, and step 3 of Stacks 0AT8

The proof of Stacks 0AT8 chooses an element `s` of the multiplicative subset which absorbs every
other one modulo the closed fibre (that is step 2,
`AlgebraicGeometry.exists_mem_smul_mem_smul_top_of_isNoetherianRing_quotient`) and then needs the
consequence that *every* element of the multiplicative subset acts injectively on the closed fibre
of the module localized at `s`. This file supplies that consequence, together with the remaining
small inputs of steps 3 and 4 of the proof.

## Main results

* `Submodule.mem_smul_top_isLocalizedModule_iff`: **the closed fibre of a localization is the
  localization of the closed fibre.** For a localization `f : N₀ → M₁` at a submonoid `T` and an
  ideal `J`, an element of `M₁` lies in `J • ⊤` exactly when it is `mk' f n t` for some `n` in
  `J • ⊤` and `t ∈ T`.
* `AlgebraicGeometry.PureSpreadout.fibre_smul_mem_of_absorbing` is step 3 of the proof of Stacks
  0AT8, and `AlgebraicGeometry.PureSpreadout.fibre_smul_maximalIdeal_mem_of_absorbing` the same
  statement in the shape that `AlgebraicGeometry.PureSpreadout.nonempty_of_data` consumes.
* `IsLocalizedModule.of_comp_of_le` lets a localization at a submonoid be factored through a
  localization at a smaller submonoid: if `g ∘ f` is a localization at `S` and `f` one at
  `T ≤ S`, then `g` is a localization at `S`.
* `Algebra.FinitePresentation.of_isLocalization_away` is step 4: a localization away from one
  element of an algebra of finite presentation is again of finite presentation over the base.
* `Stacks.Flatness.small_of_module_finite_of_small` and
  `AlgebraicGeometry.PureSpreadout.mem_maximalIdeal_smul_top_quotient_iff` are the two remaining
  inputs of step 5: the smallness of the spreadout module, and the identification of the closed
  fibre over a quotient of a local ring with the closed fibre over the local ring itself.

## Implementation notes

`Submodule.mem_smul_top_isLocalizedModule_iff` is `Mathlib`'s `Submodule.localized₀_smul`
together with `Submodule.localized₀_top`: the localization of `J • ⊤` is `J • ⊤`, and membership
in a `Submodule.localized₀` unfolds to the stated existential.

`fibre_smul_maximalIdeal_mem_of_absorbing` states the hypothesis and the conclusion over the
*local base ring* rather than over the algebra, the form in which
`AlgebraicGeometry.PureSpreadout.nonempty_of_data` takes its closed-fibre hypothesis. The
translation is `AlgebraicGeometry.PureSpreadout.mem_maximalIdeal_smul_top_iff`.

## References

* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
-/

@[expose] public section

universe u v w

/-- **The closed fibre of a localization is the localization of the closed fibre.** If
`f : N₀ →ₗ[B] M₁` exhibits `M₁` as the localization of `N₀` at a submonoid `T` and `J` is an
ideal of `B`, then an element of `M₁` lies in `J • ⊤` exactly when it is a fraction `n / t` with
`n ∈ J • ⊤` and `t ∈ T`. -/
theorem Submodule.mem_smul_top_isLocalizedModule_iff {B : Type u} [CommRing B] (T : Submonoid B)
    {N₀ : Type v} {M₁ : Type w} [AddCommGroup N₀] [Module B N₀] [AddCommGroup M₁] [Module B M₁]
    (f : N₀ →ₗ[B] M₁) [IsLocalizedModule T f] (J : Ideal B) (y : M₁) :
    y ∈ J • (⊤ : Submodule B M₁) ↔
      ∃ n ∈ J • (⊤ : Submodule B N₀), ∃ t : T, IsLocalizedModule.mk' f n t = y := by
  rw [show J • (⊤ : Submodule B M₁) = Submodule.localized₀ T f (J • (⊤ : Submodule B N₀)) by
    rw [Submodule.localized₀_smul, Submodule.localized₀_top]]
  exact Submodule.mem_localized₀ T f _ y

/-- **A localization at a submonoid factors through a localization at a smaller submonoid.** If
`g ∘ f` exhibits a localization at `S` and `f` a localization at `T ≤ S`, then `g` itself is a
localization at `S`. -/
theorem IsLocalizedModule.of_comp_of_le {B : Type u} [CommRing B] {T S : Submonoid B} (hTS : T ≤ S)
    {N₀ : Type v} {M₁ : Type w} {M₂ : Type*} [AddCommGroup N₀] [Module B N₀] [AddCommGroup M₁]
    [Module B M₁] [AddCommGroup M₂] [Module B M₂] (f : N₀ →ₗ[B] M₁) (g : M₁ →ₗ[B] M₂)
    [IsLocalizedModule T f] [IsLocalizedModule S (g ∘ₗ f)] : IsLocalizedModule S g where
  map_units u := IsLocalizedModule.map_units (g ∘ₗ f) u
  surj y := by
    obtain ⟨⟨n, u⟩, hu⟩ := IsLocalizedModule.surj S (g ∘ₗ f) y
    exact ⟨⟨f n, u⟩, hu⟩
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨⟨n₁, a₁⟩, hx₁⟩ := IsLocalizedModule.mk'_surjective T f x₁
    obtain ⟨⟨n₂, a₂⟩, hx₂⟩ := IsLocalizedModule.mk'_surjective T f x₂
    simp only [Function.uncurry_apply_pair] at hx₁ hx₂
    subst hx₁ hx₂
    have h1 : ∀ (n : N₀) (a : T), (a : B) • IsLocalizedModule.mk' f n a = f n :=
      IsLocalizedModule.mk'_cancel' f
    have e : ∀ (n : N₀) (a b : T), ((b : B) * a) • IsLocalizedModule.mk' f n a = f ((b : B) • n) :=
      fun n a b ↦ by rw [mul_smul, h1, map_smul]
    have hgf : (g ∘ₗ f) ((a₂ : B) • n₁) = (g ∘ₗ f) ((a₁ : B) • n₂) := by
      simp only [LinearMap.comp_apply]
      rw [← e n₁ a₁ a₂, ← e n₂ a₂ a₁, mul_comm (a₁ : B), map_smul, map_smul, h]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) hgf
    have hthis : (c : B) • (a₂ : B) • f n₁ = (c : B) • (a₁ : B) • f n₂ := by
      simpa only [Submonoid.smul_def, map_smul] using congrArg f hc
    refine ⟨c * ⟨(a₂ : B) * a₁, S.mul_mem (hTS a₂.2) (hTS a₁.2)⟩, ?_⟩
    simp only [Submonoid.smul_def, mul_smul]
    rwa [h1, smul_comm (a₂ : B) (a₁ : B), h1]

/-- A finite module over a ring small relative to a universe is itself small relative to that
universe. This generalizes `Stacks.Flatness.small_of_module_finite`, which takes the universe of
the base ring. -/
theorem Stacks.Flatness.small_of_module_finite_of_small (A : Type v) [CommRing A]
    [Small.{u} A] (M : Type w) [AddCommGroup M] [Module A M]
    [Module.Finite A M] : Small.{u} M := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  exact small_of_surjective
    ((span_range_eq_top_iff_surjective_fintypeLinearCombination A s).mp hs)

/-- **Step 4 of the proof of Stacks 0AT8.** A localization away from one element of an algebra of
finite presentation is of finite presentation over the base. -/
theorem Algebra.FinitePresentation.of_isLocalization_away (A : Type u) [CommRing A] (B : Type v)
    [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (t : B) (C : Type w) [CommRing C]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C] [IsLocalization.Away t C] :
    Algebra.FinitePresentation A C :=
  have : Algebra.FinitePresentation B C := IsLocalization.Away.finitePresentation t
  Algebra.FinitePresentation.trans A B C

namespace AlgebraicGeometry

namespace PureSpreadout

/-- **Step 3 of the proof of Stacks 0AT8.** Let `S` be a multiplicative subset of `B`, let `J` be
an ideal of `B`, and let `s ∈ S` absorb every element of `S` modulo `J N₀`, as step 2 provides.
Then *every* element of `S` acts injectively on the closed fibre of the localization of `N₀` at
the powers of `s`. -/
theorem fibre_smul_mem_of_absorbing {B : Type u} [CommRing B] (S : Submonoid B) (J : Ideal B)
    {N₀ : Type v} {M₁ : Type w} [AddCommGroup N₀] [Module B N₀] [AddCommGroup M₁] [Module B M₁]
    {s : B} (hs : s ∈ S)
    (habs : ∀ u ∈ S, ∀ n : N₀, u • n ∈ J • (⊤ : Submodule B N₀) →
      s • n ∈ J • (⊤ : Submodule B N₀))
    (f : N₀ →ₗ[B] M₁) [IsLocalizedModule (Submonoid.powers s) f]
    {u : B} (hu : u ∈ S) (y : M₁) (hy : u • y ∈ J • (⊤ : Submodule B M₁)) :
    y ∈ J • (⊤ : Submodule B M₁) := by
  have hpow : Submonoid.powers s ≤ S := Submonoid.powers_le.2 hs
  obtain ⟨⟨n, t⟩, hy'⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers s) f y
  simp only [Function.uncurry_apply_pair] at hy'
  subst hy'
  rw [Submodule.mem_smul_top_isLocalizedModule_iff (Submonoid.powers s) f] at hy
  obtain ⟨z, hz, t', hzt⟩ := hy
  rw [show u • IsLocalizedModule.mk' f n t = IsLocalizedModule.mk' f (u • n) t from
    (IsLocalizedModule.mk'_smul (S := Submonoid.powers s) f u n t).symm,
    IsLocalizedModule.mk'_eq_mk'_iff] at hzt
  obtain ⟨c, hc⟩ := hzt
  have hc' : (c : B) • (t' : B) • u • n = (c : B) • (t : B) • z := by
    simpa only [Submonoid.smul_def] using hc
  have key : ((c : B) * (t' : B) * u) • n ∈ J • (⊤ : Submodule B N₀) := by
    rw [mul_smul, mul_smul, hc']
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)
  have hmem : (c : B) * (t' : B) * u ∈ S :=
    S.mul_mem (S.mul_mem (hpow c.2) (hpow t'.2)) hu
  rw [Submodule.mem_smul_top_isLocalizedModule_iff (Submonoid.powers s) f]
  exact ⟨s • n, habs _ hmem n key, ⟨s, Submonoid.mem_powers s⟩ * t,
    IsLocalizedModule.mk'_cancel_left f n ⟨s, Submonoid.mem_powers s⟩ t⟩

/-- **Step 3 of the proof of Stacks 0AT8, over the local base ring.** This is
`AlgebraicGeometry.PureSpreadout.fibre_smul_mem_of_absorbing` with both the hypothesis and the
conclusion written over the maximal ideal of the local base ring. -/
theorem fibre_smul_maximalIdeal_mem_of_absorbing {A : Type u} [CommRing A] [IsLocalRing A]
    {B : Type v} [CommRing B] [Algebra A B] (S : Submonoid B)
    {N₀ : Type w} {M₁ : Type*} [AddCommGroup N₀] [Module B N₀] [Module A N₀]
    [IsScalarTower A B N₀] [AddCommGroup M₁] [Module B M₁] [Module A M₁] [IsScalarTower A B M₁]
    {s : B} (hs : s ∈ S)
    (habs : ∀ u ∈ S, ∀ n : N₀, u • n ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N₀) →
      s • n ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N₀))
    (f : N₀ →ₗ[B] M₁) [IsLocalizedModule (Submonoid.powers s) f]
    {u : B} (hu : u ∈ S) (y : M₁)
    (hy : u • y ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M₁)) :
    y ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M₁) := by
  rw [mem_maximalIdeal_smul_top_iff (S := B)] at hy ⊢
  refine fibre_smul_mem_of_absorbing S
    (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) hs (fun v hv n hn ↦ ?_) f hu y hy
  rw [← mem_maximalIdeal_smul_top_iff (S := B)] at hn ⊢
  exact habs v hv n hn

/-- The closed fibre of a module over a quotient of a local ring by an ideal inside the maximal
ideal is the closed fibre over the local ring itself. -/
theorem mem_maximalIdeal_smul_top_quotient_iff {A : Type u} [CommRing A] [IsLocalRing A]
    (I : Ideal A) [IsLocalRing (A ⧸ I)] {M : Type v} [AddCommGroup M] [Module (A ⧸ I) M]
    [Module A M] [IsScalarTower A (A ⧸ I) M] (x : M) :
    x ∈ IsLocalRing.maximalIdeal (A ⧸ I) • (⊤ : Submodule (A ⧸ I) M) ↔
      x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
  have hmap : Ideal.map (algebraMap A (A ⧸ I)) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal (A ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [← hmap, ← mem_maximalIdeal_smul_top_iff (R := A) (S := A ⧸ I)]

end PureSpreadout

end AlgebraicGeometry

end

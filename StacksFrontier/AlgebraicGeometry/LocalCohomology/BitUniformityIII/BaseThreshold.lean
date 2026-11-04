module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientShortExact

/-!
# A threshold with the three defining properties of `q(S)` of [Stacks, Tag 0GA6]

Let `A` be a commutative Noetherian ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of
`Spec(A)` in `I`, with exceptional divisor `Y`. There is an integer `q₀` such that for `q ≥ q₀`:

* `Hⁱ(X, 𝒪_Y(q)) = 0` for `i ≥ 1`;
* `Iᑫ → H⁰(X, 𝒪_Y(q))` is surjective;
* a class in `Iᑫ` killed by that map lies in `I^{q+1}`.

These are the `n = 1` fields `q₀`, `base_vanishing`, `base_surjective` and `base_ker_le` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput`; the least such integer is
`Stacks.LocalCohomology.UniformityIII.qS`. They follow from two theorems of Serre on `X`:

* `Stacks.Blowup.exists_forall_isZero_Hgroup_twistingSheaf_reesGrading`: `Hⁱ(X, 𝒪_X(q)) = 0` for
  `i > 0` and `q` large, uniformly in `i`;
* `Stacks.Blowup.exists_forall_bijective_ambientSections`: `H⁰(X, 𝒪_X(q)) = Iᑫ` for `q` large
  ([Stacks, Tag 0AG6] part (3)).

`q₀` is the larger of the two thresholds, and each property is one segment of the long exact
cohomology sequence of `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`:

* `Hⁱ(X, 𝒪_X(q)) → Hⁱ(X, 𝒪_Y(q)) → H^{i+1}(X, 𝒪_X(q+1))` with both ends vanishing gives
  the vanishing;
* the same segment in degree `0`, whose right-hand end `H¹(X, 𝒪_X(q+1))` vanishes, gives the
  surjectivity;
* left exactness of `Γ(X, -)` gives the kernel statement.

## Implementation notes

**Degree zero of the δ-functor is not `Γ(X, -)` on the nose.** `blowupH I 0` is
`(secF _ ⊤).rightDerived 0` while `blowupΓ` is `secF _ ⊤` itself; they are identified by
`CategoryTheory.Abelian.Functor.rightDerivedZeroIsoSelf`, which applies because global sections
on `X` preserve finite limits. The surjectivity in degree `0` is therefore proved for the
derived functor and transported along that natural isomorphism; the transport is
`surjective_blowupΓMap_of_subsingleton_blowupH`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupH_X₃`:
  the squeeze in the long exact sequence.
* `Stacks.LocalCohomology.UniformityIII.surjective_blowupΓMap_of_subsingleton_blowupH`: the
  same squeeze in degree `0`, read on sections.
* `Stacks.LocalCohomology.UniformityIII.exists_baseThreshold`: the threshold `q₀` and its three
  properties.

## References

* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The segment of the long exact sequence adjacent to the connecting map -/

/-- **The long exact cohomology sequence at the third term.** For a short exact sequence of
sheaves of modules on the blowup, `Hⁱ(X, ℱ₂) → Hⁱ(X, ℱ₃) → H^{i+1}(X, ℱ₁)` is exact. -/
theorem exact_blowupHMap_δ {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)}
    (hS : S.ShortExact) (i : ℕ) :
    Function.Exact (blowupHMap I i S.g) ((blowupDelta I).δ hS i).hom := by
  have h := (blowupDelta I).exact_δ₁ hS i
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- If `H^{i+1}(X, ℱ₁)` vanishes then `Hⁱ(X, ℱ₂) → Hⁱ(X, ℱ₃)` is surjective. -/
private theorem surjective_blowupHMap_of_subsingleton
    {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)} (hS : S.ShortExact)
    (i : ℕ) (h1 : Subsingleton (blowupH I (i + 1) S.X₁)) :
    Function.Surjective (blowupHMap I i S.g) := fun y =>
  (exact_blowupHMap_δ I hS i y).1 (@Subsingleton.elim _ h1 _ _)

/-- **The squeeze**: if `Hⁱ(X, ℱ₂)` and `H^{i+1}(X, ℱ₁)` both vanish then so does
`Hⁱ(X, ℱ₃)`. -/
theorem subsingleton_blowupH_X₃
    {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)} (hS : S.ShortExact)
    (i : ℕ) (h2 : Subsingleton (blowupH I i S.X₂))
    (h1 : Subsingleton (blowupH I (i + 1) S.X₁)) :
    Subsingleton (blowupH I i S.X₃) :=
  (surjective_blowupHMap_of_subsingleton I hS i h1).subsingleton

/-- **The squeeze in degree `0`, read on sections.** If `H¹(X, ℱ₁)` vanishes then
`Γ(X, ℱ₂) → Γ(X, ℱ₃)` is surjective. -/
theorem surjective_blowupΓMap_of_subsingleton_blowupH
    {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)} (hS : S.ShortExact)
    (h1 : Subsingleton (blowupH I 1 S.X₁)) :
    Function.Surjective (blowupΓMap I S.g) := by
  have hsurj := surjective_blowupHMap_of_subsingleton I hS 0 h1
  set e := (secF (blowupScheme I).ringCatSheaf
    (⊤ : Opens ↥(blowupScheme I))).rightDerivedZeroIsoSelf with he
  intro y
  obtain ⟨x, hx⟩ := hsurj ((e.inv.app S.X₃).hom y)
  refine ⟨(e.hom.app S.X₂).hom x, ?_⟩
  have key : (e.hom.app S.X₂ ≫
        (secF (blowupScheme I).ringCatSheaf (⊤ : Opens ↥(blowupScheme I))).map S.g).hom x =
      (e.hom.app S.X₃).hom ((e.inv.app S.X₃).hom y) := by
    rw [← hx]
    exact (ConcreteCategory.congr_hom (e.hom.naturality S.g) x).symm
  exact key.trans (ConcreteCategory.congr_hom (e.inv_hom_id_app S.X₃) y)

/-! ### The threshold and its three properties -/

/-- **A threshold with the defining properties of `q(S)`.** There is a `q₀` such that for every
`q ≥ q₀`, `Hⁱ(X, 𝒪_Y(q)) = 0` for every `i ≥ 1`, the canonical map `Iᑫ → H⁰(X, 𝒪_Y(q))` is
surjective, and its kernel is contained in `I^{q+1}`. -/
theorem exists_baseThreshold [IsNoetherianRing A] :
    ∃ q₀ : ℕ,
      (∀ i q : ℕ, 1 ≤ i → q₀ ≤ q → Subsingleton (blowupH I i (thickeningTwist I 1 q))) ∧
      (∀ q : ℕ, q₀ ≤ q → Function.Surjective (thickeningSections I 1 q)) ∧
      (∀ q : ℕ, q₀ ≤ q → ∀ x : (I ^ q : Ideal A),
        thickeningSections I 1 q x = 0 → (x : A) ∈ I ^ (q + 1)) := by
  obtain ⟨N₁, hN₁⟩ := Stacks.Blowup.exists_forall_isZero_Hgroup_twistingSheaf_reesGrading I
  obtain ⟨N₂, hN₂⟩ := Stacks.Blowup.exists_forall_bijective_ambientSections I
  have hvanish : ∀ i q : ℕ, 1 ≤ i → max N₁ N₂ ≤ q →
      Subsingleton (blowupH I i (blowupTwist I q)) := fun i q hi hq =>
    AddCommGrpCat.isZero_iff_subsingleton.1 (hN₁ q (le_trans (le_max_left _ _) hq) i hi)
  refine ⟨max N₁ N₂, fun i q hi hq => ?_, fun q hq => ?_, fun q hq x hx => ?_⟩
  · exact subsingleton_blowupH_X₃ I (shortExact_ambientTwistMap I q) i
      (hvanish i q hi hq) (hvanish (i + 1) (q + 1) (by omega) (by omega))
  · intro y
    obtain ⟨w, hw⟩ := surjective_blowupΓMap_of_subsingleton_blowupH I
      (shortExact_ambientTwistMap I q) (hvanish 1 (q + 1) le_rfl (by omega)) y
    obtain ⟨z, hz⟩ := (hN₂ q (le_trans (le_max_right _ _) hq)).2 w
    refine ⟨z, ?_⟩
    show blowupΓMap I (thickeningTwistProj I 1 q) (ambientSections I q z) = y
    rw [hz]
    exact hw
  · obtain ⟨y, hy⟩ := (exact_blowupΓMap I (shortExact_ambientTwistMap I q)
      (ambientSections I q x)).1 hx
    obtain ⟨z, hz⟩ := (hN₂ (q + 1) (by omega)).2 y
    have hxz : ambientSections I q x =
        ambientSections I q ⟨(z : A), Ideal.pow_le_pow_right (Nat.le_succ q) z.2⟩ := by
      rw [← blowupΓMap_ambientTwistMap_ambientSections I q z, hz]
      exact hy.symm
    have hval := congrArg Subtype.val ((hN₂ q (le_trans (le_max_right _ _) hq)).1 hxz)
    rw [hval]
    exact z.2

end Stacks.LocalCohomology.UniformityIII

end

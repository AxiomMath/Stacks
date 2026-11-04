module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.RingTheory.Flat.TorsionAdicallyZero

/-!
# A closed immersion through which the pieces off and along `V(I)` factor

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `D` a flat `R`-algebra. A closed immersion
`e : E ⟶ Spec D` through which every `Spec D_g` (`g ∈ I`) and every `Spec (D / I ^ n D)` factor
is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_of_isClosedImmersion_of_factors_away_quotient`: the statement above.

## Implementation notes

By `AlgebraicGeometry.IsClosedImmersion.isIso_of_injective_of_isAffine` it suffices that the map
on global sections is injective. An element `x` of its kernel maps to zero in every `D_g`, so it
is killed by a power of each `g ∈ I`, hence (`I` being finitely generated) by a power of `I`;
and it maps to zero in every `D / I ^ n D`, so it lies in every `I ^ n D`. Such an element is
zero by `Ideal.eq_zero_of_mem_map_pow_of_pow_mul_eq_zero`.

This is used with `D = Â ⊗_A Â` for the `I`-adic completion `Â` of a Noetherian ring `A`, which
is not Noetherian; its flatness over `Â` replaces the Krull intersection theorem. It is a step
of the existence half of [Stacks, Tag 0GI3].

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A closed immersion into `Spec D` through which `D_g` (`g ∈ I`) and `D / I ^ n D` factor is
an isomorphism**, for `D` flat over a Noetherian ring `R` and an ideal `I ⊆ R`. -/
theorem isIso_of_isClosedImmersion_of_factors_away_quotient
    {R D : Type u} [CommRing R] [IsNoetherianRing R] [CommRing D] [Algebra R D]
    [Module.Flat R D] (I : Ideal R) {E : Scheme.{u}} (e : E ⟶ Spec (.of D))
    [IsClosedImmersion e]
    (haway : ∀ g ∈ I, ∃ s : Spec (.of (Localization.Away (algebraMap R D g))) ⟶ E,
      s ≫ e = Spec.map (CommRingCat.ofHom
        (algebraMap D (Localization.Away (algebraMap R D g)))))
    (hquot : ∀ n : ℕ, ∃ s : Spec (.of (D ⧸ (I ^ n).map (algebraMap R D))) ⟶ E,
      s ≫ e = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ n).map (algebraMap R D))))) :
    IsIso e := by
  refine IsClosedImmersion.isIso_of_injective_of_isAffine ?_
  rw [injective_iff_map_eq_zero]
  intro y hy
  -- transport the kernel element to `D`
  set x : D := (Scheme.ΓSpecIso (.of D)).hom y with hx
  have hkey : ∀ {T : CommRingCat.{u}} (φ : CommRingCat.of D ⟶ T)
      (s : Spec T ⟶ E), s ≫ e = Spec.map φ → φ x = 0 := by
    intro T φ s hs
    have h1 : (Spec.map φ).appTop y = 0 := by
      rw [← hs, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hy, map_zero]
    have h2 : (Scheme.ΓSpecIso T).hom ((Spec.map φ).appTop y) = 0 := by rw [h1, map_zero]
    rw [← h2, hx, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.ΓSpecIso_naturality]
  -- killed by a power of every element of `I`
  let J : Ideal R := (Submodule.span D {x}).annihilator.comap (algebraMap R D)
  have hJ : ∀ a : R, a ∈ J ↔ algebraMap R D a * x = 0 := fun a => by
    rw [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hrad : I ≤ J.radical := by
    intro g hg
    obtain ⟨s, hs⟩ := haway g hg
    obtain ⟨⟨m, ⟨k, rfl⟩⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R D g)) _ x).mp (hkey _ s hs)
    exact ⟨k, (hJ _).mpr (by rwa [map_pow])⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  have hmem : ∀ n : ℕ, x ∈ (I ^ n).map (algebraMap R D) := by
    intro n
    obtain ⟨s, hs⟩ := hquot n
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hkey _ s hs)
  simpa [hx] using congrArg (Scheme.ΓSpecIso (.of D)).inv
    (Ideal.eq_zero_of_mem_map_pow_of_pow_mul_eq_zero I hmem (k := k) fun a ha => (hJ a).mp (hk ha))

end AlgebraicGeometry

end

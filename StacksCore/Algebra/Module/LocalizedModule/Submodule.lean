module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
import StacksCore.Tactic.StacksAttribute

/-! ## Submodules of localized modules -/
add_to_stacks 02C8 localizedQuotientEquiv

@[expose] public section

variable {R : Type*} (S : Type*) {M N : Type*} [CommSemiring R] [CommSemiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Algebra R S]
  [Module S N] [IsScalarTower R S N] (p : Submonoid R) [IsLocalization p S]
  (f : M →ₗ[R] N) [IsLocalizedModule p f]

namespace Submodule

@[stacks 00CU]
theorem localized'_comap_restrictScalars (N' : Submodule S N) :
    ((N'.restrictScalars R).comap f).localized' S p f = N' :=
  (localized'gi S p f).l_u_eq N'

@[stacks 00CU "existence form"]
theorem localized'_surjective : Function.Surjective (localized' S p f) :=
  (localized'gi S p f).l_surjective

section EqTop

/-! ### When a submodule localizes to everything

`Submodule.localized₀_top` says `⊤` localizes to `⊤`. The converse question — which submodules
localize to `⊤` — has the expected answer: exactly those that every element of `M` can be pushed
into by some element of the submonoid. The immediate consequence is that localizing at a *larger*
submonoid preserves the property, which is what lets a spanning set of one localization be read
as a spanning set of a bigger one.
-/

/-- `M'` localizes onto everything exactly when every element of `M` is carried into `M'` by some
element of `p`.

The forward direction is the interesting one: `f m` lies in `M'.localized₀ p f`, so it is
`mk' f n u` with `n ∈ M'`; clearing the denominator gives `f (u • m) = f n`, and
`IsLocalizedModule.exists_of_eq` supplies the further `c ∈ p` making `(c * u) • m = c • n` hold
already in `M`. -/
theorem localized₀_eq_top_iff (M' : Submodule R M) :
    M'.localized₀ p f = ⊤ ↔ ∀ m : M, ∃ t : p, (t : R) • m ∈ M' := by
  constructor
  · intro h m
    obtain ⟨n, hn, u, hu⟩ : f m ∈ M'.localized₀ p f := h ▸ Submodule.mem_top
    have hum : f ((u : R) • m) = f n := by
      rw [map_smul, ← hu]; exact IsLocalizedModule.mk'_cancel' f n u
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p) (f := f) hum
    exact ⟨c * u, by rw [Submonoid.coe_mul, mul_smul]; exact hc ▸ M'.smul_mem c hn⟩
  · intro h
    rw [eq_top_iff]
    rintro x -
    obtain ⟨⟨m, u⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
    obtain ⟨t, ht⟩ := h m
    exact ⟨(t : R) • m, ht, t * u, IsLocalizedModule.mk'_cancel_left f m t u⟩

/-- The `localized'` form of `localized₀_eq_top_iff`. -/
theorem localized'_eq_top_iff (M' : Submodule R M) :
    M'.localized' S p f = ⊤ ↔ ∀ m : M, ∃ t : p, (t : R) • m ∈ M' := by
  rw [← Submodule.restrictScalars_eq_top_iff (S := R), restrictScalars_localized',
    localized₀_eq_top_iff]

/-- The span-level face of `localized'_eq_top_iff`: a set spans the localization exactly when
every element of `M` is carried into its `R`-span by some element of `p`.

This is the form that travels, because the right-hand side mentions neither the localized ring
nor the localization map — so a span statement about one localization can be moved to another
just by rewriting through it in both directions. -/
theorem span_image_eq_top_iff (t : Set M) :
    span S (f '' t) = ⊤ ↔ ∀ m : M, ∃ x : p, (x : R) • m ∈ span R t := by
  rw [← localized'_span S p f t, localized'_eq_top_iff]

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable (T : Type*) [CommSemiring T] [Algebra R T] [Module T P] [IsScalarTower R T P]
variable {q : Submonoid R} [IsLocalization q T] (g : M →ₗ[R] P) [IsLocalizedModule q g]

/-- Localizing at a larger submonoid preserves "localizes onto everything". -/
theorem localized'_eq_top_of_le (hpq : p ≤ q) {M' : Submodule R M}
    (h : M'.localized' S p f = ⊤) : M'.localized' T q g = ⊤ := by
  rw [localized'_eq_top_iff] at h ⊢
  exact fun m => let ⟨t, ht⟩ := h m; ⟨⟨t, hpq t.2⟩, ht⟩

/-- A set spanning the localization at `p` still spans the localization at any larger `q`.

Used for Stacks 0GLX, where the hypothesis is about `S⁻¹(M/IM)` but the argument runs over the
larger submonoid `S + I`. -/
theorem span_image_eq_top_of_le (hpq : p ≤ q) (s : Set M)
    (h : span S (f '' s) = ⊤) : span T (g '' s) = ⊤ := by
  rw [← localized'_span S p f s] at h
  rw [← localized'_span T q g s]
  exact localized'_eq_top_of_le _ _ _ _ _ hpq h

end EqTop

section Quotient

variable {A X Y : Type*} (B : Type*) [CommRing A] [CommRing B] [AddCommGroup X] [AddCommGroup Y]
  [Module A X] [Module A Y] [Algebra A B] [Module B Y] [IsScalarTower A B Y]
  (c : Submonoid A) [IsLocalization c B] (φ : X →ₗ[A] Y) [IsLocalizedModule c φ]

/-- The two ways of reaching the localized quotient agree on images: going
`X → X ⧸ K → c⁻¹(X ⧸ K)` lands on the same set as going `X → c⁻¹X → (c⁻¹X) ⧸ K_c`.

Both composites are `Submodule.Quotient.mk ∘ φ` after unfolding, so this is definitional; it is
worth a name only because the two spellings look different enough to block a rewrite. -/
theorem image_toLocalizedQuotient' (K : Submodule A X) (t : Set X) :
    K.toLocalizedQuotient' B c φ '' (Submodule.Quotient.mk '' t)
      = (K.localized' B c φ).mkQ '' (φ '' t) := by
  rw [Set.image_image, Set.image_image]; rfl

end Quotient

end Submodule

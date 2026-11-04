module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization at a maximal ideal is faithful above `𝔪 • X`

Let `A` be a commutative ring, `𝔪` a maximal ideal, and `X` an `A`-module. Localization at `𝔪`
loses no information about the submodules of `X` that contain `𝔪 • X`: if `N ≤ P` and the
localizations of `N` and `P` at `𝔪` agree, and `𝔪 • X ≤ N`, then `N = P`.

The reason is elementary. If `x ∈ P` then some `t ∉ 𝔪` has `t • x ∈ N`, and `𝔪` being maximal
there are `y` and `i ∈ 𝔪` with `y t + i = 1`; so `x = y • (t • x) + i • x`, whose first summand
is in `N` and whose second is in `𝔪 • X ≤ N`. Equivalently: `X / N` is a module over the field
`A / 𝔪`, and localizing such a module at `𝔪` does nothing.

The consequence recorded here is that *coatom-ness* of such a submodule descends from a single
localization — unlike `⊤`, `⊥` and equality, which Mathlib descends only from the localizations
at *all* maximal ideals (`Submodule.eq_of_localization_maximal` and its family). One maximal
ideal suffices here because the hypothesis `𝔪 • X ≤ N` already pins down what happens away from
`𝔪`: there the quotient `X / N` vanishes.

## Main results

* `Submodule.exists_smul_mem_of_mem_localized₀`: an element whose image lies in the localization
  of `N` is carried into `N` by an element of the submonoid.
* `Submodule.eq_of_localized₀_le_of_smul_top_le`, `Submodule.eq_of_localized'_le_of_smul_top_le`:
  faithfulness of localization at `𝔪` above `𝔪 • X`.
* `Submodule.isCoatom_of_isCoatom_localized'`: coatom-ness descends from the localization
  at `𝔪`.

## Implementation notes

`Submodule.exists_smul_mem_of_mem_localized₀` is the forward computation of the repository's
`Submodule.localized₀_eq_top_iff` separated from the `⊤` it was stated for, so that it applies
to a comparison of two submodules rather than only to a comparison with `⊤`.
-/

@[expose] public section

namespace Submodule

section Submonoid

variable {A X Y : Type*} [CommRing A] [AddCommGroup X] [AddCommGroup Y] [Module A X]
  [Module A Y] (p : Submonoid A) (f : X →ₗ[A] Y) [IsLocalizedModule p f]

/-- If the image of `x` lies in the localization of `N` at `p`, then some element of `p` carries
`x` into `N` already. -/
theorem exists_smul_mem_of_mem_localized₀ {N : Submodule A X} {x : X}
    (hx : f x ∈ N.localized₀ p f) : ∃ t : p, (t : A) • x ∈ N := by
  obtain ⟨n, hn, u, hu⟩ := hx
  have hum : f ((u : A) • x) = f n := by
    rw [map_smul, ← hu]; exact IsLocalizedModule.mk'_cancel' f n u
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p) (f := f) hum
  exact ⟨c * u, by rw [Submonoid.coe_mul, mul_smul]; exact hc ▸ N.smul_mem c hn⟩

end Submonoid

section Maximal

variable {A X Y : Type*} [CommRing A] [AddCommGroup X] [AddCommGroup Y] [Module A X]
  [Module A Y] (𝔪 : Ideal A) [𝔪.IsMaximal] (f : X →ₗ[A] Y)
  [IsLocalizedModule 𝔪.primeCompl f]

/-- **Localization at a maximal ideal is faithful above `𝔪 • X`**, `localized₀` form: two nested
submodules with the same localization at `𝔪` agree, provided the smaller one contains
`𝔪 • X`. -/
theorem eq_of_localized₀_le_of_smul_top_le {N P : Submodule A X}
    (hsmul : 𝔪 • (⊤ : Submodule A X) ≤ N) (hNP : N ≤ P)
    (h : P.localized₀ 𝔪.primeCompl f ≤ N.localized₀ 𝔪.primeCompl f) : N = P := by
  refine le_antisymm hNP fun x hx => ?_
  obtain ⟨t, ht⟩ := exists_smul_mem_of_mem_localized₀ 𝔪.primeCompl f
    (h (map_le_localized₀ 𝔪.primeCompl f P (mem_map_of_mem hx)))
  obtain ⟨y, i, hi, hyi⟩ := (‹𝔪.IsMaximal›).exists_inv t.2
  have hsplit : x = y • ((t : A) • x) + i • x := by
    rw [smul_smul, ← add_smul, hyi, one_smul]
  exact hsplit ▸ N.add_mem (N.smul_mem _ ht) (hsmul (smul_mem_smul hi mem_top))

variable (R : Type*) [CommRing R] [Algebra A R] [IsLocalization 𝔪.primeCompl R] [Module R Y]
  [IsScalarTower A R Y]

/-- **Localization at a maximal ideal is faithful above `𝔪 • X`**, `localized'` form. -/
theorem eq_of_localized'_le_of_smul_top_le {N P : Submodule A X}
    (hsmul : 𝔪 • (⊤ : Submodule A X) ≤ N) (hNP : N ≤ P)
    (h : P.localized' R 𝔪.primeCompl f ≤ N.localized' R 𝔪.primeCompl f) : N = P :=
  eq_of_localized₀_le_of_smul_top_le 𝔪 f hsmul hNP <| by
    rw [← restrictScalars_localized' R 𝔪.primeCompl f N,
      ← restrictScalars_localized' R 𝔪.primeCompl f P]
    exact fun _ hy => h hy

/-- **Coatom-ness descends from the localization at a maximal ideal**, for a submodule containing
`𝔪 • X`: if `N` contains `𝔪 • X` and the localization of `N` at `𝔪` is a coatom in the lattice
of submodules of the localized module, then `N` is a coatom in the lattice of submodules of `X`.

This is what lets a computation carried out at one local ring decide a global question: a
submodule of the form `(image of A) ⊔ 𝔪 • X` contains `𝔪 • X` by construction. -/
theorem isCoatom_of_isCoatom_localized' {N : Submodule A X}
    (hsmul : 𝔪 • (⊤ : Submodule A X) ≤ N)
    (h : IsCoatom (N.localized' R 𝔪.primeCompl f)) : IsCoatom N := by
  refine ⟨fun hNtop => h.1 (by rw [hNtop, localized'_top]), fun P hNP => ?_⟩
  have hle : N.localized' R 𝔪.primeCompl f ≤ P.localized' R 𝔪.primeCompl f :=
    (localized'gi R 𝔪.primeCompl f).gc.monotone_l hNP.le
  exact (eq_or_lt_of_le hle).elim
    (fun heq => absurd (eq_of_localized'_le_of_smul_top_le 𝔪 f R hsmul hNP.le heq.ge) hNP.ne)
    (fun hlt => eq_of_localized'_le_of_smul_top_le 𝔪 f R (hsmul.trans hNP.le) le_top
      (le_of_eq (by rw [localized'_top, h.2 _ hlt])))

end Maximal

end Submodule

end

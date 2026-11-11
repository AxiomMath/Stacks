module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.CompleteLocalRing.InverseLimitCharacterization

/-!
# Complete local rings

Let `(R, 𝔪)` be a local ring. The Stacks project calls `R` a *complete local ring* when the
canonical map `R ⟶ lim_n R / 𝔪ⁿ` to the `𝔪`-adic completion of `R` is an isomorphism; a footnote
stresses that this includes `⋂ₙ 𝔪ⁿ = (0)`.

## Main definitions and results

* `IsCompleteLocalRing`: the canonical ring map
  `algebraMap R (AdicCompletion (maximalIdeal R) R)` is bijective. Mathlib's
  `AdicCompletion 𝔪 R` is the inverse limit `lim_n R / 𝔪ⁿ`: the compatible families in
  `∀ n, R ⧸ (𝔪ⁿ • ⊤)`, where `𝔪ⁿ • ⊤ = 𝔪ⁿ`, with componentwise ring structure; the canonical
  map is `AdicCompletion.of 𝔪 R`, sending `r` to its family of residues.
* `IsCompleteLocalRing.ringEquiv`: the ring isomorphism `R ≃+* AdicCompletion 𝔪 R` it gives.
* `isCompleteLocalRing_iff_isAdicComplete`: the definition agrees with Mathlib's
  `IsAdicComplete (maximalIdeal R) R`, the conjunction of `IsHausdorff` (the footnote's
  `⋂ₙ 𝔪ⁿ = (0)`, injectivity) and `IsPrecomplete` (surjectivity). The later results of the
  Cohen structure theorem section state completeness in that form.
* `isCompleteLocalRing_iff_forall_compatible_existsUnique_mk_eq`: the definition restated with
  the source's truncations `R ⧸ 𝔪ⁿ` and transition maps `Ideal.Quotient.factor`, through
  `IsLocalRing.isAdicComplete_maximalIdeal_iff_forall_compatible_existsUnique_mk_eq`.
-/

@[expose] public section

universe u

open IsLocalRing

/-- **Complete local ring.** A local ring `(R, 𝔪)` is a *complete local ring* when the canonical
ring map `R ⟶ lim_n R / 𝔪ⁿ` to its `𝔪`-adic completion is an isomorphism. The completion is
Mathlib's `AdicCompletion (maximalIdeal R) R`, the inverse limit of the truncations `R / 𝔪ⁿ`, and
a ring map is an isomorphism exactly when it is bijective (`IsCompleteLocalRing.ringEquiv`).
Injectivity is the separatedness `⋂ₙ 𝔪ⁿ = (0)` of the source's footnote. -/
@[stacks 0324 "The source's definition: `(R, 𝔪)` local is a complete local ring when the \
canonical map `R ⟶ lim_n R / 𝔪ⁿ` is an isomorphism. The limit is Mathlib's \
`AdicCompletion (maximalIdeal R) R` (compatible families of residues modulo `𝔪ⁿ • ⊤ = 𝔪ⁿ`), the \
canonical map is `algebraMap R (AdicCompletion (maximalIdeal R) R)`, and the predicate is its \
bijectivity, which for a ring map is being an isomorphism; `IsCompleteLocalRing.ringEquiv` is \
the resulting ring isomorphism. The footnote's `⋂ 𝔪ⁿ = (0)` is the injectivity half. \
`isCompleteLocalRing_iff_isAdicComplete` identifies the predicate with \
`IsAdicComplete (maximalIdeal R) R`, the spelling used by the section's later results, and \
`isCompleteLocalRing_iff_forall_compatible_existsUnique_mk_eq` restates it with the source's \
truncations `R ⧸ 𝔪ⁿ` and transition maps. The footnote's references 05JC, 05GG, 05GH are \
separate tags.",
  stacks 0323 "Definition 0324 of the section, its opening notion: a complete local ring, a \
local ring `(R, 𝔪)` whose canonical map `R ⟶ lim_n R / 𝔪ⁿ` is an isomorphism. The section's \
main theorem, the Cohen structure theorem 032A, is also registered under 0323, on \
`IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries`."]
def IsCompleteLocalRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  Function.Bijective (algebraMap R (AdicCompletion (maximalIdeal R) R))

/-- A local ring is a complete local ring exactly when it is `𝔪`-adically complete in Mathlib's
sense, `IsAdicComplete (maximalIdeal R) R`. -/
theorem isCompleteLocalRing_iff_isAdicComplete (R : Type u) [CommRing R] [IsLocalRing R] :
    IsCompleteLocalRing R ↔ IsAdicComplete (maximalIdeal R) R :=
  AdicCompletion.of_bijective_iff

theorem IsCompleteLocalRing.isAdicComplete {R : Type u} [CommRing R] [IsLocalRing R]
    (h : IsCompleteLocalRing R) : IsAdicComplete (maximalIdeal R) R :=
  (isCompleteLocalRing_iff_isAdicComplete R).mp h

theorem IsCompleteLocalRing.of_isAdicComplete (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : IsCompleteLocalRing R :=
  (isCompleteLocalRing_iff_isAdicComplete R).mpr ‹_›

/-- The ring isomorphism `R ≃+* lim_n R / 𝔪ⁿ` of a complete local ring: the canonical map. -/
noncomputable def IsCompleteLocalRing.ringEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    (h : IsCompleteLocalRing R) : R ≃+* AdicCompletion (maximalIdeal R) R :=
  RingEquiv.ofBijective (algebraMap R (AdicCompletion (maximalIdeal R) R)) h

@[simp]
theorem IsCompleteLocalRing.ringEquiv_apply {R : Type u} [CommRing R] [IsLocalRing R]
    (h : IsCompleteLocalRing R) (r : R) :
    h.ringEquiv r = algebraMap R (AdicCompletion (maximalIdeal R) R) r :=
  rfl

/-- A local ring is a complete local ring exactly when every family of residues
`f n : R ⧸ 𝔪ⁿ`, compatible with the truncation maps `R ⧸ 𝔪ⁿ → R ⧸ 𝔪ᵏ` for `k ≤ n`, is the
family of residues of a unique `r : R`. -/
theorem isCompleteLocalRing_iff_forall_compatible_existsUnique_mk_eq
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsCompleteLocalRing R ↔
      ∀ f : (n : ℕ) → R ⧸ maximalIdeal R ^ n,
        (∀ (k n : ℕ) (h : k ≤ n),
            Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (f n) = f k) →
          ∃! r : R, ∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) r = f n :=
  (isCompleteLocalRing_iff_isAdicComplete R).trans
    (IsLocalRing.isAdicComplete_maximalIdeal_iff_forall_compatible_existsUnique_mk_eq R)

end

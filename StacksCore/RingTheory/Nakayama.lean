module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Nilpotent.Defs
import StacksCore.Tactic.StacksAttribute

/-! # Nakayama's lemma: the parts Mathlib omits

Stacks tag 00DV is a twelve-part statement. Mathlib proves and tags parts (1), (2), (3), (4)
and (8) at their own declarations, in `Mathlib.RingTheory.Nakayama` and
`Mathlib.RingTheory.Finiteness.Nakayama`. This file covers the other seven — (5), (6), (7), and
the whole nilpotent block (9)–(12) — completing the tag.

**Part (6)** is proved in Mathlib but goes untagged: `LinearMap.surjective_of_surjective_comp_mkQ`
sits after `end Submodule`, outside the block where the neighbouring parts carry their tags. Only
the tag is supplied here.

**Part (5)** is the localized form of (6): dropping `I ⊆ rad(R)` costs surjectivity everywhere,
but buys it after inverting a single `r ∈ 1 + I`. It is proved here, following the Stacks proof
exactly — "apply (3) to `M` and the submodules `Im(N → M)` and `M`", i.e. instantiate
`Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup` at `N := range φ` and `N' := P := ⊤`.
The passage from `r • ⊤ ≤ range φ` to surjectivity after localizing is
`Submodule.localized₀_le_localized₀_of_smul_le`, which is the bridge part (3)'s own `@[stacks]`
comment defers its second conclusion to.

Both parts take the hypothesis "`N/IN → M/IM` is surjective" in the form Mathlib uses for (6):
surjectivity of the composite `N → M ⧸ I • ⊤`. That is the same condition, because `N ↠ N/IN`
means precomposing with the quotient map changes neither the range nor its image. Mathlib also
names source and target the other way round from the tag — its `φ` runs `N →ₗ[R] M` with the
*target* `M` finite, where the tag writes `N → M` with `M` finite, so here the two agree.

**Part (7)** — a set generating `M/IM` generates `M_f` for some `f ∈ 1 + I` — is proved here too.
The Stacks proof obtains it from (5), applied to `R^n → M`, `(a₁, …, aₙ) ↦ ∑ aᵢxᵢ`; going back to
(3) directly is shorter, because the tag's conclusion is a statement about spans and
`Submodule.localized'_span` converts one into the other. Nothing forces the generating set to be
finite, so it is taken to be an arbitrary `s : Set M`; the tag's `x₁, …, xₙ` is `s := Set.range x`.

**Part (9)** opens the nilpotent block, where `I ⊆ rad(R)` is replaced by `I` nilpotent. These
need **no finiteness hypothesis at all**: `N ≤ I • N` gives `N ≤ Iᵏ • N` for every `k` by
induction, and `Iⁿ = 0` finishes it, so none of the finite-generation machinery that parts
(1)–(8) route through is involved. Accordingly it is stated for an arbitrary `N`, mirroring
part (2)'s `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` with the Jacobson hypothesis
swapped for nilpotence and the `N.FG` hypothesis dropped; the tag's own wording is the `N = ⊤`
case.

**Part (10)** is (9) read in `M ⧸ N`: `Submodule.mkQ_map_self` kills the `N` summand and
`Submodule.map_smul''` carries `I • N'` across, leaving (9)'s hypothesis on the quotient. It is
the workhorse of the block — **(11) and (12) are both just (10) at `N' := ⊤`**, taking `N` to be
`range φ` and `span R s`, which are the same two instantiations used for (5) and (7) above.

Each nilpotent part mirrors a Jacobson one with the same statement, `I ≤ jacobson ⊥` swapped for
`IsNilpotent I`, and the finiteness hypothesis dropped: (9) mirrors (2), (10) mirrors (4), (11)
mirrors (6), (12) mirrors (8). The naming follows suit wherever Mathlib names the sibling.
-/

@[expose] public section

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

add_to_stacks 00DV "(6): `N → M` with `N/IN → M/IM` surjective, `M` finite and
  `I ⊆ rad(R)` forces `N → M` surjective. Mathlib swaps the names of source and target."
  LinearMap.surjective_of_surjective_comp_mkQ

/-- If `N → M ⧸ I • ⊤` is surjective then `⊤ ≤ range φ ⊔ I • ⊤`. -/
private theorem top_le_range_sup_smul_top_of_surjective_comp_mkQ
    (I : Ideal R) (φ : N →ₗ[R] M)
    (hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ φ)) :
    (⊤ : Submodule R M) ≤ LinearMap.range φ ⊔ I • ⊤ := by
  rw [top_le_iff, sup_comm, ← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp]
  exact LinearMap.range_eq_top_of_surjective _ hsurj

/-- If `s` spans `M ⧸ I • ⊤` then `span R s ⊔ I • ⊤ = ⊤`. -/
private theorem span_sup_smul_top_eq_top_of_span_image_mk_eq_top
    (I : Ideal R) (s : Set M)
    (hs : Submodule.span R
      (Submodule.Quotient.mk '' s : Set (M ⧸ I • (⊤ : Submodule R M))) = ⊤) :
    Submodule.span R s ⊔ I • ⊤ = ⊤ := by
  rwa [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span]

open scoped Pointwise in
/-- **Stacks 00DV (5)**: if `φ : N →ₗ[R] M` has `N/IN → M/IM` surjective and `M` is finite, then
some `r ∈ 1 + I` makes `φ` surjective after localizing at the powers of `r`.

Stated against arbitrary localization witnesses `fN`, `fM`, so it applies to any model of
`N_r` and `M_r`. For the concrete `LocalizedModule` reading see
`LinearMap.exists_sub_one_mem_and_localizedMap_surjective_of_surjective_comp_mkQ`.

Dropping the hypothesis `I ≤ rad(R)` of `LinearMap.surjective_of_surjective_comp_mkQ` (part (6))
costs surjectivity of `φ` itself; inverting one element of `1 + I` recovers it. -/
@[stacks 00DV "(5)"]
theorem LinearMap.exists_sub_one_mem_and_map_surjective_of_surjective_comp_mkQ
    (I : Ideal R) (φ : N →ₗ[R] M) [Module.Finite R M]
    (hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ φ)) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ {Nᵣ Mᵣ : Type*} [AddCommGroup Nᵣ] [Module R Nᵣ]
      [AddCommGroup Mᵣ] [Module R Mᵣ] (fN : N →ₗ[R] Nᵣ) (fM : M →ₗ[R] Mᵣ)
      [IsLocalizedModule (Submonoid.powers r) fN] [IsLocalizedModule (Submonoid.powers r) fM],
      Function.Surjective (IsLocalizedModule.map (Submonoid.powers r) fN fM φ) := by
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.finite_def.mp ‹_›) le_rfl
    (top_le_range_sup_smul_top_of_surjective_comp_mkQ I φ hsurj)
  refine ⟨r, hr1, fun fN fM _ _ ↦ ?_⟩
  rw [← LinearMap.range_eq_top, LinearMap.range_localizedMap_eq_localized₀_range,
    ← top_le_iff, ← Submodule.localized₀_top (Submonoid.powers r) fM]
  exact Submodule.localized₀_le_localized₀_of_smul_le _ _ ⟨r, Submonoid.mem_powers r⟩ hr2

/-- **Stacks 00DV (5)**, in the concrete `LocalizedModule` model: the tag's literal
"`N_f → M_f` is surjective".

This is `LinearMap.exists_sub_one_mem_and_map_surjective_of_surjective_comp_mkQ` at the canonical
witnesses `LocalizedModule.mkLinearMap`. -/
@[stacks 00DV "(5)"]
theorem LinearMap.exists_sub_one_mem_and_localizedMap_surjective_of_surjective_comp_mkQ
    (I : Ideal R) (φ : N →ₗ[R] M) [Module.Finite R M]
    (hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ φ)) :
    ∃ r : R, r - 1 ∈ I ∧
      Function.Surjective (LocalizedModule.map (Submonoid.powers r) φ) := by
  obtain ⟨r, hr1, hr2⟩ :=
    LinearMap.exists_sub_one_mem_and_map_surjective_of_surjective_comp_mkQ I φ hsurj
  exact ⟨r, hr1, hr2 (LocalizedModule.mkLinearMap _ _) (LocalizedModule.mkLinearMap _ _)⟩

open scoped Pointwise in
/-- **Stacks 00DV (7)**: if `s` generates `M/IM` and `M` is finite, then some `r ∈ 1 + I` makes
`s` generate `M` after localizing at the powers of `r`.

"`s` generates `M/IM`" is taken literally, as `s` spanning the quotient `M ⧸ I • ⊤`. Internally
that is converted to the `Submodule.span R s ⊔ I • ⊤ = ⊤` form which part (3) consumes, by
`span_sup_smul_top_eq_top_of_span_image_mk_eq_top`. Stated against arbitrary localization
witnesses `S`, `fM`; for the concrete reading see
`Submodule.exists_sub_one_mem_and_span_image_mkLinearMap_eq_top`.

The tag writes a finite list `x₁, …, xₙ`, but finiteness of the generating set is not used —
only finiteness of `M`. Take `s := Set.range x` to recover the tag's form. -/
@[stacks 00DV "(7)"]
theorem Submodule.exists_sub_one_mem_and_span_image_eq_top
    (I : Ideal R) [Module.Finite R M] (s : Set M)
    (hs : Submodule.span R
      (Submodule.Quotient.mk '' s : Set (M ⧸ I • (⊤ : Submodule R M))) = ⊤) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ {S Mᵣ : Type*} [CommRing S] [Algebra R S]
      [AddCommGroup Mᵣ] [Module R Mᵣ] [Module S Mᵣ] [IsScalarTower R S Mᵣ]
      [IsLocalization (Submonoid.powers r) S] (fM : M →ₗ[R] Mᵣ)
      [IsLocalizedModule (Submonoid.powers r) fM],
      Submodule.span S (fM '' s) = ⊤ := by
  have hs' := span_sup_smul_top_eq_top_of_span_image_mk_eq_top I s hs
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := I) (N := Submodule.span R s) (N' := ⊤) (P := ⊤)
    (Module.finite_def.mp ‹_›) le_rfl hs'.ge
  refine ⟨r, hr1, fun {S Mᵣ} _ _ _ _ _ _ _ fM _ ↦ ?_⟩
  rw [← Submodule.localized'_span S (Submonoid.powers r) fM s, eq_top_iff,
    ← Submodule.localized'_top S (Submonoid.powers r) fM]
  exact Submodule.localized'_le_localized'_of_smul_le S (Submonoid.powers r) fM
    ⟨r, Submonoid.mem_powers r⟩ hr2

/-- **Stacks 00DV (7)**, in the concrete `LocalizedModule` model: the tag's literal
"`x₁, …, xₙ` generate `M_f` over `R_f`". -/
@[stacks 00DV "(7)"]
theorem Submodule.exists_sub_one_mem_and_span_image_mkLinearMap_eq_top
    (I : Ideal R) [Module.Finite R M] (s : Set M)
    (hs : Submodule.span R
      (Submodule.Quotient.mk '' s : Set (M ⧸ I • (⊤ : Submodule R M))) = ⊤) :
    ∃ r : R, r - 1 ∈ I ∧
      Submodule.span (Localization (Submonoid.powers r))
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M '' s) = ⊤ := by
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_span_image_eq_top I s hs
  exact ⟨r, hr1, hr2 (LocalizedModule.mkLinearMap _ _)⟩

/-- **Stacks 00DV (9)**: if `N ≤ I • N` and `I` is nilpotent, then `N = ⊥`. -/
@[stacks 00DV "(9)"]
theorem Submodule.eq_bot_of_le_smul_of_isNilpotent (I : Ideal R) (N : Submodule R M)
    (hI : IsNilpotent I) (hN : N ≤ I • N) : N = ⊥ := by
  obtain ⟨n, hn⟩ := hI
  simpa using (hn ▸ le_pow_smul hN n : _ ≤ (0 : Ideal R) • N)

open Submodule in
/-- **Stacks 00DV (10)**: if `N' ≤ N ⊔ I • N'` and `I` is nilpotent, then `N' ≤ N`.

The nilpotent counterpart of `Submodule.le_of_le_smul_of_le_jacobson_bot` (part (4)), which
assumes `I ≤ jacobson ⊥` and `N'.FG` instead; as everywhere in this block the finiteness goes.

This is (9) read in `M ⧸ N`: mapping the hypothesis through `N.mkQ` kills the `N` summand
(`Submodule.mkQ_map_self`) while `Submodule.map_smul''` carries `I • N'` across, leaving
`map N.mkQ N' ≤ I • map N.mkQ N'` — exactly (9)'s hypothesis on the quotient.

The tag words it as `M = N + I N'`; that is the case `N' := ⊤`, reached from the tag's hypothesis
via `I • N' ≤ I • ⊤`. Parts (11) and (12) are both this lemma at `N' := ⊤`, with `N` taken to be
`range φ` and `span R s` respectively. -/
@[stacks 00DV "(10)"]
theorem Submodule.le_of_le_smul_of_isNilpotent {I : Ideal R} {N N' : Submodule R M}
    (hI : IsNilpotent I) (hNN : N' ≤ N ⊔ I • N') : N' ≤ N := by
  rw [← Submodule.ker_mkQ N, LinearMap.le_ker_iff_map]
  refine Submodule.eq_bot_of_le_smul_of_isNilpotent I _ hI ?_
  grw [map_mono hNN, Submodule.map_sup, mkQ_map_self, bot_sup_eq, map_smul'']

open Submodule in
/-- **Stacks 00DV (11)**: if `φ : N →ₗ[R] M` has `N/IN → M/IM` surjective and `I` is nilpotent,
then `φ` is surjective. -/
@[stacks 00DV "(11)"]
theorem LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent
    (I : Ideal R) (φ : N →ₗ[R] M) (hI : IsNilpotent I)
    (hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ φ)) :
    Function.Surjective φ :=
  φ.range_eq_top.1 <| eq_top_iff.2 <| le_of_le_smul_of_isNilpotent hI <|
    top_le_range_sup_smul_top_of_surjective_comp_mkQ I φ hsurj

open Submodule in
/-- **Stacks 00DV (12)**: if `s` generates `M/IM` and `I` is nilpotent, then `s` generates `M`.

The nilpotent counterpart of part (8), and (10) at `N := span R s`, `N' := ⊤`. As in part (7) the
hypothesis is taken literally — `s` spans the quotient `M ⧸ I • ⊤` — and nothing requires `s` to
be finite, so the tag's `{xα}` is an arbitrary `s : Set M`. Unlike (7), `M` need not be finite
either. -/
@[stacks 00DV "(12)"]
theorem Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_isNilpotent
    (I : Ideal R) (hI : IsNilpotent I) (s : Set M)
    (hs : Submodule.span R
      (Submodule.Quotient.mk '' s : Set (M ⧸ I • (⊤ : Submodule R M))) = ⊤) :
    Submodule.span R s = ⊤ :=
  eq_top_iff.2 <| le_of_le_smul_of_isNilpotent hI
    (span_sup_smul_top_eq_top_of_span_image_mk_eq_top I s hs).ge

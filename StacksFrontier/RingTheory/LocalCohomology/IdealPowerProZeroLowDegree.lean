module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.DepthExtension.DegreeZero
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerSystems

/-!
# Pro-zero local cohomology of the ideal-power filtration in low degrees

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `M` a finite `A`-module and `T ⊆ Spec(A)` a
subset. This module complements `StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero`, which
sets up the inverse system `{IⁿM}` and the globalization steps of [Stacks, Tag 0EFX], with three
further pieces about the system `{H^i_T(IⁿM)}`:

* both assertions of Tag 0EFX in degrees `i ≤ 0`, with nothing assumed beyond the data of
  Situation [Stacks, Tag 0EFU]. In degree `0` the content is the Artin–Rees lemma: `H^0_T(IⁿM)`
  is `IⁿM ∩ Γ_T(M)`, the submodule `Γ_T(M)` of the finite module `M` is supported in `T ⊆ V(I)`
  and so killed by a power of `I`, and Artin–Rees makes the intersection land in a power of `I`
  times `Γ_T(M)` and hence vanish from some index on. Since the tag asserts pro-vanishing for
  `i ≤ s` and the stable-image property in degree `s + 1`, these cover the whole tag whenever
  `s < 0`;
* the Mittag-Leffler condition for `{H^i_{𝔭A_𝔭}((IⁿM)_𝔭)}`, which is the input the first
  paragraph of the source's proof of Tag 0EFX takes from Lemma [Stacks, Tag 0DX1];
* the globalization of the stable-image assertion of Tag 0EFX without the stability of the
  localized transition images, an engine carrying no tag.

## Main results

* `Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomology_localizedIdealPowerTower` —
  Lemma [Stacks, Tag 0DX1] at the system `{H^i_{𝔭A_𝔭}((IⁿM)_𝔭)}`.
* `exists_eventually_injective_image_idealPowerTower_of_local_image_injective` — the
  stable-image globalization of Tag 0EFX from the weaker per-prime input.
* `Stacks.LocalCohomology.exists_eventually_injective_image_idealPowerTower_of_neg` — the
  stable-image half of Tag 0EFX in negative degrees, with no hypothesis at all; the pro-zero half
  there is `Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_neg`.
* `Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_le_zero`,
  `Stacks.LocalCohomology.exists_eventually_injective_image_idealPowerTower_of_le_zero` — both
  halves of Tag 0EFX in degrees `i ≤ 0`, with nothing assumed but `A` Noetherian, `M` finite and
  `T ⊆ V(I)`, which are three of the data of Situation [Stacks, Tag 0EFU].
* `Stacks.LocalCohomology.exists_isZero_localCohomologyWithSupportIn_idealPowerTower_zero` — the
  engine of the degree-zero case: `H^0_T(IⁿM) = 0` for `n` large, by Artin–Rees.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFA](https://stacks.math.columbia.edu/tag/0EFA)
* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### Lemma 0DX1 at the localized ideal-power tower -/

/-- The localization at a prime of a term of `{IⁿM}` is a finite module over the local ring at
that prime: `IⁿM` is a submodule of the finite module `M`, hence finite over the Noetherian ring
`A`, and finiteness passes to localizations. -/
private theorem finite_localizedModule_idealPowerTower_obj [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{max u v} A) [Module.Finite A M] (p : PrimeSpectrum A) (n : ℕᵒᵖ) :
    Module.Finite (Localization p.asIdeal.primeCompl)
      ((ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl).obj
        ((idealPowerTower.{u, v} I M).obj n)) := by
  have : IsNoetherian A M := isNoetherian_of_isNoetherianRing_of_finite A M
  have : Module.Finite A ((idealPowerTower.{u, v} I M).obj n) := by
    change Module.Finite A ↥(I ^ n.unop • (⊤ : Submodule A M))
    exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  change Module.Finite (Localization p.asIdeal.primeCompl)
    (((idealPowerTower.{u, v} I M).obj n).localizedModule p.asIdeal.primeCompl)
  exact Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
    (((idealPowerTower.{u, v} I M).obj n).localizedModuleMkLinearMap p.asIdeal.primeCompl)

/-- **Lemma [Stacks, Tag 0DX1] at the localized ideal-power tower.** For a finite module `M` over
a Noetherian ring `A`, an ideal `I` and a prime `𝔭`, the inverse system
`n ↦ H^i_{𝔭A_𝔭}((IⁿM)_𝔭)` satisfies the Mittag-Leffler condition in every degree.

This is the Mittag-Leffler input of the first paragraph of the proof of [Stacks, Tag 0EFX],
where the source cites Lemma [Stacks, Tag 0DX1] for it. Each `(IⁿM)_𝔭` is a finite module over
the Noetherian local ring `A_𝔭`, so its local cohomology at the maximal ideal is Artinian, and
the images of the transition maps into a fixed term form a descending chain of submodules of an
Artinian module, which stabilizes. -/
theorem isMittagLefflerCategorical_localCohomology_localizedIdealPowerTower
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{max u v} A) [Module.Finite A M]
    (p : PrimeSpectrum A) (i : ℤ) :
    IsMittagLefflerCategorical
      (idealPowerTower.{u, v} I M ⋙
        ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i) :=
  isMittagLeffler_localCohomology (Localization p.asIdeal.primeCompl)
    (idealPowerTower.{u, v} I M ⋙
      ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl)
    (finite_localizedModule_idealPowerTower_obj.{u, v} I M p) i

/-! ### Tag 0EFX, the stable-image globalization without stable localized images -/

/-- **The globalization step in the proof of [Stacks, Tag 0EFX], the stable-image assertion.** If
for every `m` there is a `c ≥ m` such that at every `𝔭 ∈ T` and for every `k ≥ c` the transition
map of `{H^{i-1}_{𝔭A_𝔭}((IⁿM)_𝔭)}` vanishes and the transition image of
`{H^i_{𝔭A_𝔭}((IⁿM)_𝔭)}` injects into the zeroth term, then there is an `m₀` such that
for every `m ≥ m₀` the image of `H^i_T(IᵏM) → H^i_T(IᵐM)` injects into `H^i_T(I^{m₀}M)` for all
large `k`.

This is the reduction Lemma [Stacks, Tag 0EFA], applied to the tower `{IⁿM}`; in the source it is
applied in degree `i = s + 1`. Unlike `exists_eventually_injective_image_idealPowerTower_of_local`
it does not ask the localized transition images to be independent of `k`.

*What this assumes, and why it carries no `@[stacks 0EFX]`.* The hypothesis `hloc` is the
per-prime stable-image assertion, uniform in `𝔭 ∈ T`, which is the local-duality half of the
source's own proof — a step of that proof, not a restriction on the data `A, I, T, M`. So this
theorem is an engine, not a registration of the tag: a tag counts only on a declaration proved
under the source's hypotheses. `hloc` is discharged in Situation [Stacks, Tag 0EFU] by
`Stacks.Algebraization.exists_forall_localized_localCohomology_map_eq_zero` in degree `i - 1` and
`Stacks.Algebraization.exists_forall_localized_ker_le_ker_idealPowerTower` in degree `i`, and this
engine run on them is `Stacks.Algebraization.exists_hasStableImageIdealPowerCohomology`, which
carries the tag for the stable-image assertion at a general specialization-stable `T`. -/
theorem exists_eventually_injective_image_idealPowerTower_of_local_image_injective
    [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℕ)
    (hloc : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ p ∈ T, ∀ (k : ℕ) (hck : c ≤ k),
      ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
        p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
          (Localization p.asIdeal.primeCompl) ((i : ℤ) - 1)).map
            (homOfLE (hmc.trans hck)).op = 0) ∧
      (∀ x : (idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).obj (op k),
        ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map
              (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
            p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
              (Localization p.asIdeal.primeCompl) (i : ℤ)).map
                (homOfLE (Nat.zero_le m)).op).hom →
        ((idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map
              (homOfLE (hmc.trans hck)).op).hom x = 0)) :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).obj (op k),
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, v} I M ⋙
            localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0 :=
  eventually_injective_image_localCohomologyWithSupportIn_of_image_injective.{u, v} A hdim T hT
    (idealPowerTower.{u, v} I M) i hloc

/-! ### Tag 0EFX in negative degrees -/

/-- Any two elements of `H^i_T(IᵐM)` are equal if this module is zero. -/
private theorem eq_of_isZero_localCohomologyWithSupportIn_idealPowerTower
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ) (m : ℕ)
    (h : IsZero ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj
      ((idealPowerTower.{u, v} I M).obj (op m))))
    (x y : (idealPowerTower.{u, v} I M ⋙
      localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj (op m)) : x = y :=
  (ModuleCat.isZero_iff_subsingleton.mp h).elim x y

/-- **Stacks Project, Tag 0EFX**, the stable-image assertion, in negative degrees and with no
hypothesis. The assertion is that there is an `m₀` such that for every `m ≥ m₀` there is a
`c ≥ m` beyond which the image of `H^i_T(IᵏM) → H^i_T(IᵐM)` maps injectively to
`H^i_T(I^{m₀}M)`. For `i < 0` every term `H^i_T(IⁿM)` of the system vanishes, so `m₀ = 0` serves
and the injectivity is automatic.

This is the companion of `exists_map_idealPowerTower_eq_zero_of_neg`, and it covers the degree
`s + 1` at which the source states the stable-image assertion exactly when `s < -1`. The
conclusion is the conclusion of
`exists_eventually_injective_image_idealPowerTower_of_local` verbatim, so the two theorems prove
the same assertion in complementary ranges of the degree. -/
@[stacks 0EFX "the stable-image assertion in negative degrees, unconditionally"]
theorem exists_eventually_injective_image_idealPowerTower_of_neg (T : Set (PrimeSpectrum A))
    (I : Ideal A) (M : ModuleCat.{max u v} A) (i : ℤ) (hi : i < 0) :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj (op k),
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, v} I M ⋙
            localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
            (homOfLE (hmc.trans hck)).op).hom x = 0 := by
  refine ⟨0, fun m _ => ⟨m, le_rfl, fun k _ x _ => ?_⟩⟩
  exact eq_of_isZero_localCohomologyWithSupportIn_idealPowerTower.{u, v} T I M i m
    (isZero_localCohomologyWithSupportIn_single_of_neg.{u, v} A T
      ((idealPowerTower.{u, v} I M).obj (op m)) i hi) _ _

/-! ### Tag 0EFX in degree zero -/

/-- The `T`-supported sections of a finite module over a Noetherian ring are killed by a power of
`I` as soon as `T ⊆ V(I)`: `Γ_T(M)` is a submodule of `M`, hence finite, its support is contained
in `T` and therefore in `V(I)`, so `I` lies in the radical of its annihilator and a power of the
finitely generated `I` lies in the annihilator itself. -/
@[ega "I 9.3.4" "Affine case X = Spec A"]
private theorem exists_pow_smul_sectionsWithSupportIn_eq_bot [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (hT : T ⊆ PrimeSpectrum.zeroLocus (I : Set A)) (M : ModuleCat.{max u v} A)
    [Module.Finite A M] :
    ∃ a : ℕ, I ^ a • sectionsWithSupportIn A T M = ⊥ := by
  have hNoeth : IsNoetherian A M := isNoetherian_of_isNoetherianRing_of_finite A M
  have hfin : Module.Finite A ↥(sectionsWithSupportIn A T M) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hsupp : Module.support A ↥(sectionsWithSupportIn A T M) ⊆
      PrimeSpectrum.zeroLocus (I : Set A) :=
    (support_sectionsWithSupportIn_subset T M).trans hT
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsupp
  obtain ⟨a, ha⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hsupp (Ideal.fg_of_isNoetherianRing I)
  refine ⟨a, le_antisymm (Submodule.smul_le.2 fun r hr x hx => ?_) bot_le⟩
  have hzero := (Module.mem_annihilator.1 (ha hr)) (⟨x, hx⟩ : ↥(sectionsWithSupportIn A T M))
  have : r • x = 0 := congrArg Subtype.val hzero
  simp [this]

/-- A submodule meeting the `T`-supported sections of the ambient module only in `0` has no
nonzero `T`-supported section of its own: the annihilator of an element is unchanged by the
inclusion, so a `T`-supported section of `N` is a `T`-supported section of `M` lying in `N`. -/
private theorem subsingleton_sectionsWithSupportIn_of_inf_eq_bot
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (N : Submodule A M)
    (h : N ⊓ sectionsWithSupportIn A T M = ⊥) :
    Subsingleton ↥(sectionsWithSupportIn A T (ModuleCat.of A ↥N)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hx := (mem_sectionsWithSupportIn_iff A T ↥N x.1).1 x.2
  rw [torsionOf_submodule_eq] at hx
  have hmem : (x.1.1 : M) ∈ sectionsWithSupportIn A T M :=
    (mem_sectionsWithSupportIn_iff A T (M : Type (max u v)) x.1.1).2 hx
  have hbot : (x.1.1 : M) ∈ (⊥ : Submodule A M) := by
    rw [← h]; exact ⟨x.1.2, hmem⟩
  exact Subtype.ext (Subtype.ext (by simpa using hbot))

/-- **`H^0_T(IⁿM)` vanishes for `n` large.** For `M` finite over a Noetherian ring and
`T ⊆ V(I)`, there is a `c` with `H^0_T(IⁿM) = 0` for every `n ≥ c`.

The degree-zero local cohomology with support in `T` is the module of `T`-supported sections, and
a section of `IⁿM` is `T`-supported exactly when it is `T`-supported as a section of `M`, the
annihilator of an element being unchanged by an injective map. So `H^0_T(IⁿM)` is
`IⁿM ∩ Γ_T(M)`, and the Artin–Rees lemma makes that intersection `I^{n-k}(I^kM ∩ Γ_T(M))` for
`n ≥ k`, which lands inside `I^{n-k}Γ_T(M)` and hence vanishes once `n - k` exceeds the exponent
killing `Γ_T(M)`. -/
theorem exists_isZero_localCohomologyWithSupportIn_idealPowerTower_zero [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (hT : T ⊆ PrimeSpectrum.zeroLocus (I : Set A)) (M : ModuleCat.{max u v} A)
    [Module.Finite A M] :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      IsZero ((localCohomologyWithSupportInModuleFunctor.{u, v} A T 0).obj
        ((idealPowerTower.{u, v} I M).obj (op n))) := by
  obtain ⟨a, ha⟩ := exists_pow_smul_sectionsWithSupportIn_eq_bot.{u, v} T I hT M
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (sectionsWithSupportIn A T M)
  refine ⟨k + a, fun n hn => ?_⟩
  have hinf : (I ^ n • (⊤ : Submodule A M)) ⊓ sectionsWithSupportIn A T M = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [hk n (by omega)]
    calc I ^ (n - k) • ((I ^ k • (⊤ : Submodule A M)) ⊓ sectionsWithSupportIn A T M)
        ≤ I ^ (n - k) • sectionsWithSupportIn A T M :=
          Submodule.smul_mono le_rfl inf_le_right
      _ ≤ I ^ a • sectionsWithSupportIn A T M :=
          Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl
      _ = ⊥ := ha
  have hsub : Subsingleton
      ↥(sectionsWithSupportIn A T ((idealPowerTower.{u, v} I M).obj (op n))) :=
    subsingleton_sectionsWithSupportIn_of_inf_eq_bot.{u, v} T M
      (I ^ n • (⊤ : Submodule A M)) hinf
  obtain ⟨iso⟩ := nonempty_localCohomologyWithSupportIn_zero_iso.{u, v} T
    ((idealPowerTower.{u, v} I M).obj (op n))
  exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr hsub) iso

/-- **Stacks Project, Tag 0EFX**, the pro-zero assertion in degrees `i ≤ 0`, with no hypothesis
beyond the data of Situation [Stacks, Tag 0EFU]: `A` Noetherian, `M` finite and `T ⊆ V(I)`. For
`i < 0` every term of `{H^i_T(IⁿM)}` vanishes; in degree `0` the terms vanish from some index on,
by `exists_isZero_localCohomologyWithSupportIn_idealPowerTower_zero`. In either case a transition
map out of a vanishing term is zero.

Together with the stable-image companion
`exists_eventually_injective_image_idealPowerTower_of_le_zero` this proves both assertions of the
tag whenever `s < 0`: the pro-zero assertion is asserted for `i ≤ s` and the stable-image
assertion in degree `s + 1`. -/
@[stacks 0EFX "the pro-zero assertion in degrees i ≤ 0, for A Noetherian, M finite and T ⊆ V(I)"]
theorem exists_map_idealPowerTower_eq_zero_of_le_zero [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (hT : T ⊆ PrimeSpectrum.zeroLocus (I : Set A)) (M : ModuleCat.{max u v} A)
    [Module.Finite A M] (i : ℤ) (hi : i ≤ 0) (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        ((idealPowerTower.{u, v} I M).map (homOfLE h).op) = 0 := by
  rcases lt_or_eq_of_le hi with hneg | rfl
  · exact exists_map_idealPowerTower_eq_zero_of_neg.{u, v} T I M i hneg m
  · obtain ⟨c, hc⟩ := exists_isZero_localCohomologyWithSupportIn_idealPowerTower_zero.{u, v}
      T I hT M
    exact ⟨max m c, le_max_left _ _, (hc _ (le_max_right _ _)).eq_of_src _ _⟩

/-- **Stacks Project, Tag 0EFX**, the stable-image assertion in degrees `i ≤ 0`, with no
hypothesis beyond the data of Situation [Stacks, Tag 0EFU]: `A` Noetherian, `M` finite and
`T ⊆ V(I)`. The assertion is that there is an `m₀` such that for every `m ≥ m₀` there is a
`c ≥ m` beyond which the image of `H^i_T(IᵏM) → H^i_T(IᵐM)` maps injectively to `H^i_T(I^{m₀}M)`.

For `i < 0` every term vanishes and `m₀ = 0` serves. In degree `0` the terms vanish from the
index `c` of `exists_isZero_localCohomologyWithSupportIn_idealPowerTower_zero` on, so `m₀ = c`
serves: every class in a vanishing target is zero. The conclusion is the conclusion of
`exists_eventually_injective_image_idealPowerTower_of_local` verbatim.

This covers the degree `s + 1` at which the source states the stable-image assertion exactly
when `s < 0`. -/
@[stacks 0EFX "the stable-image assertion in degrees i ≤ 0, for A Noetherian, M finite and \
T ⊆ V(I)"]
theorem exists_eventually_injective_image_idealPowerTower_of_le_zero [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (hT : T ⊆ PrimeSpectrum.zeroLocus (I : Set A)) (M : ModuleCat.{max u v} A)
    [Module.Finite A M] (i : ℤ) (hi : i ≤ 0) :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj (op k),
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, v} I M ⋙
            localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, v} I M ⋙
          localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
            (homOfLE (hmc.trans hck)).op).hom x = 0 := by
  rcases lt_or_eq_of_le hi with hneg | rfl
  · exact exists_eventually_injective_image_idealPowerTower_of_neg.{u, v} T I M i hneg
  · obtain ⟨c, hc⟩ := exists_isZero_localCohomologyWithSupportIn_idealPowerTower_zero.{u, v}
      T I hT M
    refine ⟨c, fun m hcm => ⟨m, le_rfl, fun k _ x _ => ?_⟩⟩
    exact eq_of_isZero_localCohomologyWithSupportIn_idealPowerTower.{u, v} T I M 0 m
      (hc m hcm) _ _

end Stacks.LocalCohomology

end

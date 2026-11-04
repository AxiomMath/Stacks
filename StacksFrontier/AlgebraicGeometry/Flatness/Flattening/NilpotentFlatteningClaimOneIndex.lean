module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentFlatteningClaimOne

/-!
# Claim 1 of the proof of Stacks 05U9 at every index, and Stacks 05U9

Claim 1 of the proof of Stacks 05U9 says that in Situation 0AT0, with the local algebra
presented as the localization at a prime of a polynomial algebra over `A` and the module of
finite presentation over it, the reduction of `N` modulo the closure ideal `J_i` of a stratum
`S_i ∖ S_{i+1}` of a generic flatness stratification is flat over `A ⧸ J_i`. Its proof is an
induction on the length of the stratification, and this file is that induction, followed by the
three conclusions of Stacks 05U9.

The index step is not uniform in `i`. Three cases occur, and the first two are not instances of
the third:

* `S.ideal i.succ = ⊤`, the case the source calls immediate: the stratum is all of `S_i`, the
  flatness clause of the stratification covers it outright
  (`Stacks.FlatStratification.flat_quotient_ideal_of_succ_eq_top`) and no quotient situation is
  formed. A quotient situation could not be formed: the ideals `J_i ⊔ K_{i+1}ⁿ` the induction
  passes to are then `⊤`, which is not contained in the maximal ideal.
* `J_i = ⊤`. The base `A ⧸ J_i` is the zero ring and every module over it is flat. This happens
  independently of the previous case: `J_i` is the set of elements of `A` killed in every
  `(A ⧸ K_i)_{g j}`, which is all of `A` exactly when the stratum is empty, and that is tied
  neither way to `K_{i+1}` being the unit ideal.
* the generic case, where `A ⧸ J_i` is a nonzero local ring, the quotient situation over it
  exists, and the henselization core applies with the flatness modulo powers coming from the
  induction.

## Main results

* `AlgebraicGeometry.flat_quotient_of_flat_away_of_flat_quotient_sup`: the generic index of
  Claim 1, from the henselization core over the quotient situation.
* `AlgebraicGeometry.flat_quotient_of_flatStratification_quotient`: the induction step, which
  shortens the stratification over a quotient of the base.
* `AlgebraicGeometry.exists_fg_isNilpotent_flat_quotient_of_flatStratification`: **Claim 1**, by
  induction on the length of a generic flatness stratification.
* `AlgebraicGeometry.conclusion_of_presentation`: the three conclusions of Stacks 05U9 in the
  localized-polynomial case of Stacks 0AT2.
* `AlgebraicGeometry.conclusion_of_injectiveModuloMaximalIdeal`: **Stacks 05U9.**

## Implementation notes

Claim 1 mentions the data of Situation 0AT0 throughout, and must: by
`Stacks.not_forall_exists_fg_isNilpotent_flat_quotient` the same statement about `A`, `B` and
`N` alone is false, with `A = B = ℤ_[2]` and `N = ℤ_[2] ⧸ (2)`. What makes the difference is the
flat module `M` and the map `u : N → M` injective modulo `𝔪_A`, and every statement here is
about a situation, hence about those too.

The induction runs on the length of the stratification rather than on the index: the quotient
of a stratification by the ideal of its `s`-th closed subscheme is shorter by `s`
(`Stacks.FlatStratification.quotient`), which is how the proposition over the quotient base
becomes available at index `i > 0` and for the powers of the stratum ideal at index `i = 0`.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT2](https://stacks.math.columbia.edu/tag/0AT2)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-- **The generic index of Claim 1 of the proof of Stacks 05U9.** In Situation 0AT0 with a
presentation of `B` as a localization at a prime of a polynomial algebra over `A` and `N` of
finite presentation over `B`, let `E ⊆ A` be a proper ideal and `g` a finite family of elements
of `A` generating, together with `E`, a proper ideal. If `N ⧸ EN` is flat on each basic open
`D(ḡ j)` of `Spec (A ⧸ E)`, if `N ⧸ (E ⊔ (g)ⁿ)N` is flat over `A ⧸ (E ⊔ (g)ⁿ)` for every
`n > 0`, and if the union of the `D(ḡ j)` is scheme theoretically dense in `Spec (A ⧸ E)`, then
`N ⧸ EN` is flat over `A ⧸ E`.

This is `Stacks.flat_of_flat_away_of_flat_quotient_pow` applied over the quotient situation
`AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotient`: that situation's base is
`A ⧸ E`, its algebra is essentially of finite presentation by
`AlgebraicGeometry.essentiallyOfFinitePresentation_of_presentation` applied to the reduced
presentation, and its module is `N ⧸ EN` in the description
`N ⧸ (EB • ⊤ : Submodule B N)`, identified `A ⧸ E`-linearly with `N ⧸ (E • ⊤ : Submodule A N)`
by `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientNEquivBase`. The flatness
modulo the powers travels across that identification with
`Stacks.flat_quotient_map_of_flat_quotient_sup`, which turns flatness modulo the sum `E ⊔ (g)ⁿ`
over `A` into flatness modulo the extension of `(g)ⁿ` over `A ⧸ E`. -/
theorem flat_quotient_of_flat_away_of_flat_quotient_sup
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    (hfp : Module.FinitePresentation S.B S.N)
    (E : Ideal S.A) (hE : E ≤ maximalIdeal S.A)
    {ι : Type u₁} [Finite ι] (g : ι → S.A)
    (hgE : Ideal.span (Set.range g) ⊔ E ≠ ⊤)
    (hU : ∀ j, Module.Flat (Localization.Away (Ideal.Quotient.mk E (g j)))
      (Localization.Away (Ideal.Quotient.mk E (g j)) ⊗[S.A ⧸ E]
        (S.N ⧸ (E • (⊤ : Submodule S.A S.N)))))
    (hpow : ∀ n : ℕ, 0 < n →
      Module.Flat (S.A ⧸ (E ⊔ Ideal.span (Set.range g) ^ n))
        (S.N ⧸ ((E ⊔ Ideal.span (Set.range g) ^ n) • (⊤ : Submodule S.A S.N))))
    (hdense : ∀ x : S.A ⧸ E,
      (∀ j, ∃ n : ℕ, Ideal.Quotient.mk E (g j) ^ n * x = 0) → x = 0) :
    Module.Flat (S.A ⧸ E) (S.N ⧸ (E • (⊤ : Submodule S.A S.N))) := by
  have := hfp
  have hspan : (Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk E (g j)) : Ideal (S.A ⧸ E)) =
      (Ideal.span (Set.range g)).map (Ideal.Quotient.mk E) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hne : (Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk E (g j)) : Ideal (S.A ⧸ E)) ≠ ⊤ := by
    rw [hspan]
    intro htop
    obtain ⟨a, ha, hb⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk E)
      Ideal.Quotient.mk_surjective).mp ((Ideal.eq_top_iff_one _).mp htop)
    refine hgE ((Ideal.eq_top_iff_one _).mpr ?_)
    have h1 : (1 : S.A) - a ∈ E := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hb, map_one, sub_self]
    have h2 : (1 : S.A) = 1 - a + a := by ring
    rw [h2]
    exact Submodule.add_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left ha)
  have hU' : ∀ j, Module.Flat (Localization.Away (Ideal.Quotient.mk E (g j)))
      (Localization.Away (Ideal.Quotient.mk E (g j)) ⊗[S.A ⧸ E] (S.quotient E hE).N) := fun j ↦
    Stacks.flat_tensor_of_linearEquiv (S.quotientNEquivBase E hE).symm _ (hU j)
  have hpow' : ∀ n : ℕ, 0 < n → Module.Flat
      ((S.A ⧸ E) ⧸ (Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk E (g j))) ^ n)
      ((S.quotient E hE).N ⧸
        ((Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk E (g j))) ^ n •
          (⊤ : Submodule (S.A ⧸ E) (S.quotient E hE).N))) := by
    intro n hn
    have h := Stacks.flat_quotient_map_of_flat_quotient_sup E (Ideal.span (Set.range g) ^ n)
      (hpow n hn)
    rw [Ideal.map_pow, hspan.symm] at h
    exact Stacks.flat_quotient_smul_top_of_linearEquiv (S.quotientNEquivBase E hE).symm _ h
  exact S.flat_of_flat_quotient_N E hE
    (Stacks.flat_of_flat_away_of_flat_quotient_pow
      (A := (S.quotient E hE).A) (B := (S.quotient E hE).B) (N := (S.quotient E hE).N)
      (essentiallyOfFinitePresentation_of_presentation (S.quotient E hE)
        (S.quotientPresentation E hE P))
      (fun j ↦ Ideal.Quotient.mk E (g j)) hne hU' hpow' hdense)

/-- **The induction step in the proof of Claim 1 of Stacks 05U9.** In Situation 0AT0 with a
presentation and `N` of finite presentation over `B`, let `E ⊆ A` be a proper ideal and let `s`
be an index of a generic flatness stratification of `N` whose ideal `K_s` becomes nilpotent in
`A ⧸ E`. Then Claim 1 for stratifications of length `t - s` gives that `N ⧸ EN` is flat over
`A ⧸ E`.

The reduced data are Situation 0AT0 again with a presentation in the same number of variables
and a finitely presented module, the stratification of `N ⧸ EN` over `A ⧸ E` has length `t - s`
(`Stacks.FlatStratification.quotient`), and
`AlgebraicGeometry.conclusion_of_claim1_of_presentation` turns the nilpotent ideal Claim 1
produces there into flatness of the module of the quotient situation over its base, which
`AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.flat_of_flat_quotient_N` reads back as
flatness of `N ⧸ EN` over `A ⧸ E`. -/
theorem flat_quotient_of_flatStratification_quotient
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    (hfp : Module.FinitePresentation S.B S.N)
    (E : Ideal S.A) (hE : E ≤ maximalIdeal S.A)
    {t : ℕ} (strat : Stacks.FlatStratification S.A S.N t) (s : ℕ) (hs : s ≤ t)
    (hnil : (strat.ideal ⟨s, Nat.lt_succ_of_le hs⟩).map (Ideal.Quotient.mk E) ≤
      nilradical (S.A ⧸ E))
    (ih : ∀ T : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄},
      PolynomialLocalizationPresentation T.A T.B → Module.FinitePresentation T.B T.N →
      Stacks.FlatStratification T.A T.N (t - s) →
      ∃ I : Ideal T.A, I.FG ∧ IsNilpotent I ∧
        Module.Flat (T.A ⧸ I) (T.N ⧸ (I • (⊤ : Submodule T.A T.N)))) :
    Module.Flat (S.A ⧸ E) (S.N ⧸ (E • (⊤ : Submodule S.A S.N))) := by
  have := hfp
  obtain ⟨I, -, hInil, hIflat⟩ := ih (S.quotient E hE) (S.quotientPresentation E hE P)
    (S.finitePresentation_quotient_N E hE)
    ((strat.quotient E s hs hnil).ofLinearEquiv (S.quotientNEquivBase E hE).symm)
  exact S.flat_of_flat_quotient_N E hE
    (conclusion_of_claim1_of_presentation.{u₁, u₂, u₃, u₄, u₁} (S.quotient E hE)
      (S.quotientPresentation E hE P) (S.finitePresentation_quotient_N E hE)
      ⟨I, hInil, hIflat⟩).2.2

/-- **Claim 1 of the proof of Stacks 05U9.** In Situation 0AT0, with `B` presented as the
localization at a prime of a polynomial algebra over `A` and `N` of finite presentation over
`B`, a generic flatness stratification of `N` over `A` of length `t` gives a finitely generated
nilpotent ideal `I ⊆ A` with `N ⧸ IN` flat over `A ⧸ I`.

The proof is the source's induction on `t`. Claim 1 at an index `i` of the stratification —
flatness of `N ⧸ J_iN` over `A ⧸ J_i` for the closure ideal `J_i` of the stratum — is reached in
three ways, as described at the top of this file, and
`Stacks.exists_flat_quotient_le_of_isPrime` turns Claim 1 at every index into the statement that
every prime of `A` contains a flattening ideal, which
`AlgebraicGeometry.exists_fg_isNilpotent_flat_quotient_of_cover` turns into the nilpotent ideal
through the henselization. -/
theorem exists_fg_isNilpotent_flat_quotient_of_flatStratification :
    ∀ (t : ℕ) (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}),
      PolynomialLocalizationPresentation S.A S.B → Module.FinitePresentation S.B S.N →
      Stacks.FlatStratification S.A S.N t →
      ∃ I : Ideal S.A, I.FG ∧ IsNilpotent I ∧
        Module.Flat (S.A ⧸ I) (S.N ⧸ (I • (⊤ : Submodule S.A S.N))) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro S P hfp strat
  have := hfp
  refine exists_fg_isNilpotent_flat_quotient_of_cover S P hfp fun p hp ↦ ?_
  have := hp
  refine Stacks.exists_flat_quotient_le_of_isPrime strat ?_ p
  intro i ι _ g hspan
  by_cases hsucc : strat.ideal i.succ = ⊤
  · exact Stacks.flat_quotient_strataClosureIdeal_of_flat_quotient _ g
      (strat.flat_quotient_ideal_of_succ_eq_top i hsucc)
  have hsuccm : strat.ideal i.succ ≤ maximalIdeal S.A := IsLocalRing.le_maximalIdeal hsucc
  by_cases hJ : Stacks.strataClosureIdeal (strat.ideal i.castSucc) g = ⊤
  · have : Subsingleton (S.A ⧸ Stacks.strataClosureIdeal (strat.ideal i.castSucc) g) :=
      Ideal.Quotient.subsingleton_iff.mpr hJ
    have : Subsingleton (S.N ⧸ (Stacks.strataClosureIdeal (strat.ideal i.castSucc) g •
        (⊤ : Submodule S.A S.N))) :=
      Module.subsingleton (S.A ⧸ Stacks.strataClosureIdeal (strat.ideal i.castSucc) g) _
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofSubsingleton
      (S.N ⧸ (Stacks.strataClosureIdeal (strat.ideal i.castSucc) g • (⊤ : Submodule S.A S.N)))
      (S.A ⧸ Stacks.strataClosureIdeal (strat.ideal i.castSucc) g))
  have hJm : Stacks.strataClosureIdeal (strat.ideal i.castSucc) g ≤ maximalIdeal S.A :=
    IsLocalRing.le_maximalIdeal hJ
  refine flat_quotient_of_flat_away_of_flat_quotient_sup S P hfp _ hJm g
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal S.A).ne_top
      (sup_le (hspan ▸ hsuccm) hJm)) (fun j ↦ ?_) (fun n hn ↦ ?_)
    (Stacks.eq_zero_of_forall_pow_mul_eq_zero_quotient (strat.ideal i.castSucc) g)
  · have hmem : g j ∈ strat.ideal i.succ := hspan ▸ Ideal.subset_span ⟨j, rfl⟩
    exact Stacks.flat_tensorQuotient_of_flat_away_of_le _ (strat.ideal i.castSucc)
      (Stacks.le_strataClosureIdeal _ g) (g j) (strat.flat_away i (g j) hmem) _
  · set Ei := Stacks.strataClosureIdeal (strat.ideal i.castSucc) g ⊔
      Ideal.span (Set.range g) ^ n with hEi
    have hpowle : Ideal.span (Set.range g) ^ n ≤ strat.ideal i.succ :=
      (Ideal.pow_le_self hn.ne').trans (le_of_eq hspan)
    have hEm : Ei ≤ maximalIdeal S.A := by
      rw [hEi]
      exact sup_le hJm (hpowle.trans hsuccm)
    have hker : (Ideal.span (Set.range g) ^ n).map (Ideal.Quotient.mk Ei) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, hEi]
      exact le_sup_right
    have hnil : (strat.ideal i.succ).map (Ideal.Quotient.mk Ei) ≤ nilradical (S.A ⧸ Ei) := by
      refine (Ideal.FG.isNilpotent_iff_le_nilradical ((strat.fg i.succ).map _)).mp ⟨n, ?_⟩
      rw [← Ideal.map_pow, ← hspan]
      exact hker
    exact flat_quotient_of_flatStratification_quotient S P hfp Ei hEm strat (i.val + 1)
      i.isLt hnil fun T hP hfpT stratT ↦
        ih (t - (i.val + 1)) (by omega) T hP hfpT stratT

/-- **Stacks 05U9 in the localized-polynomial case of Stacks 0AT2.** In Situation 0AT0, with the
local algebra `B` presented as the localization at a prime of a polynomial algebra over `A` in
finitely many variables and `N` of finite presentation over `B`, all three conclusions of Stacks
05U9 hold: `u` is `A`-universally injective, `N` is of finite presentation over `B`, and `N` is
flat over `A`.

`AlgebraicGeometry.exists_flatStratification_of_presentation` produces a generic flatness
stratification of `N` over `A`, Claim 1 follows from it by
`AlgebraicGeometry.exists_fg_isNilpotent_flat_quotient_of_flatStratification`, and
`AlgebraicGeometry.conclusion_of_claim1_of_presentation` draws the three conclusions from it. -/
theorem conclusion_of_presentation
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    (hfp : Module.FinitePresentation S.B S.N) :
    InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} S := by
  have := hfp
  obtain ⟨t, ⟨strat⟩⟩ := exists_flatStratification_of_presentation S P hfp
  obtain ⟨I, -, hnil, hflat⟩ :=
    exists_fg_isNilpotent_flat_quotient_of_flatStratification t S P hfp strat
  exact conclusion_of_claim1_of_presentation S P hfp ⟨I, hnil, hflat⟩

/-- **Stacks Project, Tag 05U9.** Let `A → B` be a local homomorphism of local rings which is
essentially of finite type, let `M` be a flat `A`-module, let `N` be a finite `B`-module and let
`u : N → M` be an `A`-linear map whose reduction `ū : N ⧸ 𝔪_AN → M ⧸ 𝔪_AM` is injective. Then

1. `u` is `A`-universally injective,
2. `N` is of finite presentation over `B`, and
3. `N` is flat over `A`.

The hypotheses are the data of Situation 0AT0
(`AlgebraicGeometry.InjectiveModuloMaximalIdealSituation`) and the three conclusions are
`AlgebraicGeometry.InjectiveModuloMaximalIdealConclusion`.

Stacks 0AT2 reduces all three to the case where `B` is a localization at a prime of a
polynomial algebra over `A` in finitely many variables and `N` is of finite presentation over
`B`, and `AlgebraicGeometry.conclusion_of_presentation` settles that case through Claim 1 of the
source's proof. -/
@[stacks 05U9 "universal injectivity, finite presentation and flatness"]
theorem conclusion_of_injectiveModuloMaximalIdeal
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) :
    InjectiveModuloMaximalIdealConclusion.{u₅} S :=
  injectiveModuloMaximalIdealConclusion_of_rTensor_injective_cases S
    fun T _ P hfp Q _ _ ↦ (conclusion_of_presentation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄, u₅}
      T P hfp).1 Q

end AlgebraicGeometry

end

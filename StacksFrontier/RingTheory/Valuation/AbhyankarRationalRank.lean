module

public import StacksFrontier.RingTheory.Valuation.AbhyankarCounting
public import StacksFrontier.RingTheory.Valuation.AbhyankarAdjoin
public import StacksFrontier.RingTheory.Valuation.AbhyankarComposite
import StacksFrontier.RingTheory.Valuation.Localization
import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension

/-!
# Abhyankar's inequality: the rational rank is at most the dimension

Let `B` be a Noetherian local domain and `φ : B → V` an injective local homomorphism into a
valuation ring. If `x₁, …, x_r ∈ B` have `ℤ`-linearly independent values in `V`
(`Stacks.Abhyankar.MonomialIndependent`), then `r ≤ dim B`.

The proof is by induction on `dim B`. Let `f₁, …, f_d` be a system of parameters. If each
`v(φ(xᵢ))` is bounded by a multiple of each `v(φ(f_j))`, the counting step
(`Stacks.Abhyankar.card_le_card_of_forall_exists_pow_eq_mul`) gives `r ≤ d = dim B`. Otherwise
some `v(φ(x_{i₀}))` is infinitely large compared with `g = φ(f_{j₀})`, and `P = ⋂ₙ gⁿ V` is a
prime of `V` with `φ(x_{i₀}) ∈ P` and `g ∉ P`: the valuation ring `V` is the composite of `V_P`
and `V/P`. Choose, by linear algebra, `r₁` Laurent monomials `z_j` in the `xᵢ` whose values lie
in the value group of `V/P` and are independent there, and `r₂ = r - r₁` of the `xᵢ` whose values
stay independent modulo it; adjoining the `z_j` to `B` and localizing gives a Noetherian local
domain `C` with `dim C ≤ dim B` (Stacks 02IJ, the `z_j` being fractions). For `𝔭 = P ∩ C`, which
is neither `0` nor maximal, the induction hypothesis applied to `C_𝔭 → V_P` and to `C/𝔭 → V/P`
gives `r₂ ≤ ht 𝔭` and `r₁ ≤ dim C/𝔭`, and `ht 𝔭 + dim C/𝔭 ≤ dim C ≤ dim B`.

## Main results

* `Stacks.Abhyankar.card_le_height_maximalIdeal`: `r ≤ height 𝔪_B`.
* `Stacks.Abhyankar.card_le_ringKrullDim`: `r ≤ dim B`.

## References

* S. Abhyankar, *On the valuations centered in a local domain*, Amer. J. Math. 78 (1956),
  Theorem 1.
* O. Zariski, P. Samuel, *Commutative Algebra*, vol. II, Appendix 2.
-/

@[expose] public section

namespace Stacks.Abhyankar

open IsLocalRing

universe u v w

section Helpers

/-- The maximal ideal of the localization `C_𝔭` at a prime `𝔭` has the height of `𝔭`. -/
theorem height_maximalIdeal_localization {C : Type*} [CommRing C] (p : Ideal C) [p.IsPrime] :
    (maximalIdeal (Localization.AtPrime p)).height = p.height := by
  have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h1
  exact_mod_cast h1

/-- The quotient of a local ring by a prime ideal is a local ring. -/
theorem isLocalRing_quotient {C : Type*} [CommRing C] [IsLocalRing C] (p : Ideal C)
    [p.IsPrime] : IsLocalRing (C ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

/-- The image of the maximal ideal of a local ring `C` in `C ⧸ 𝔭` is the maximal ideal. -/
theorem maximalIdeal_quotient_eq {C : Type*} [CommRing C] [IsLocalRing C] (p : Ideal C)
    [p.IsPrime] [IsLocalRing (C ⧸ p)] :
    (maximalIdeal C).map (Ideal.Quotient.mk p) = maximalIdeal (C ⧸ p) := by
  have : ((maximalIdeal C).map (Ideal.Quotient.mk p)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  exact IsLocalRing.eq_maximalIdeal this

/-- The map `C/(P ∩ C) → V/P` induced by a local homomorphism `ψ : C → V` is local. -/
theorem isLocalHom_quotientMap {C : Type*} [CommRing C] [IsLocalRing C] {V : Type*}
    [CommRing V] [IsLocalRing V] (ψ : C →+* V) [IsLocalHom ψ] (P : Ideal V) [hP : P.IsPrime] :
    IsLocalHom (Ideal.quotientMap P ψ (le_refl (Ideal.comap ψ P))) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk] at ha
  obtain ⟨d', hd'⟩ := isUnit_iff_exists_inv.mp ha
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d'
  have hPm : P ≤ maximalIdeal V := IsLocalRing.le_maximalIdeal hP.ne_top
  have h1 : ψ c * d - 1 ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd', map_one, sub_self]
  have hψc : ψ c ∉ maximalIdeal V := by
    intro hm
    have : (1 : V) ∈ maximalIdeal V := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right d _ hm) (hPm h1)
      simp at this
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hc : IsUnit c := isUnit_of_map_unit ψ c (IsLocalRing.notMem_maximalIdeal.mp hψc)
  exact hc.map _

/-- Monomial independence is invariant under reindexing by an equivalence. -/
theorem MonomialIndependent.comp_equiv {V : Type*} [CommRing V] {ι κ : Type*} [Fintype ι]
    [Fintype κ] {x : ι → V} (hx : MonomialIndependent x) (e : κ ≃ ι) :
    MonomialIndependent (x ∘ e) := by
  intro α β h
  have key : ∀ γ : κ → ℕ, monom (x ∘ e) γ = monom x (γ ∘ e.symm) := by
    intro γ
    rw [monom, monom]
    exact (Fintype.prod_equiv e _ _ fun k => by simp).trans rfl
  rw [key, key] at h
  have := hx _ _ h
  funext k
  simpa using congrFun this (e k)

end Helpers

section Split

variable {V : Type v} [CommRing V] [IsDomain V] [ValuationRing V] (P : Ideal V) [P.IsPrime]
  {ι : Type} [Fintype ι]

/-- The exponent vectors `α - β ∈ ℚ^ι` of pairs of monomials in `y` with the same value modulo
the units of `V_P`. -/
def expDiffSet (y : ι → V) : Set (ι → ℚ) :=
  {v | ∃ α β : ι → ℕ, RelP P (monom y α) (monom y β) ∧ v = fun i => (α i : ℚ) - β i}

omit [ValuationRing V] in
/-- A subfamily `y ∘ a` whose coordinates support no nonzero vector of the span of
`expDiffSet P y` has independent values in `V_P`. -/
theorem monomialIndependent_localization (y : ι → V) {κ : Type} [Fintype κ] {a : κ → ι}
    (ha : Function.Injective a)
    (hsupp : ∀ v ∈ Submodule.span ℚ (expDiffSet P y), (∀ i, i ∉ Set.range a → v i = 0) → v = 0) :
    MonomialIndependent (algebraMap V (Localization.AtPrime P) ∘ y ∘ a) := by
  intro α' β' hass
  rw [← map_monom, ← map_monom] at hass
  have hR := relP_of_associated P hass
  rw [monom_comp_of_injective ha, monom_comp_of_injective ha] at hR
  set v : ι → ℚ := fun i => ((Function.extend a α' 0 i : ℕ) : ℚ) -
    ((Function.extend a β' 0 i : ℕ) : ℚ)
  have hvW : v ∈ Submodule.span ℚ (expDiffSet P y) := Submodule.subset_span ⟨_, _, hR, rfl⟩
  have hv0 : v = 0 := hsupp v hvW (by
    intro i hi
    have : ¬∃ k, a k = i := by rintro ⟨k, rfl⟩; exact hi ⟨k, rfl⟩
    simp [v, Function.extend_apply' _ _ _ this])
  funext k
  have := congrFun hv0 (a k)
  simp only [v, ha.extend_apply, Pi.zero_apply, sub_eq_zero] at this
  exact_mod_cast this

/-- Laurent monomials `z_j = y^{α_j - β_j}` outside `P` with linearly independent exponent
vectors have independent values in `V/P`. -/
theorem monomialIndependent_quotient {y : ι → V} (hy : MonomialIndependent y) {m : ℕ}
    (z : Fin m → V) (α β : Fin m → ι → ℕ) (hz : ∀ j, monom y (β j) * z j = monom y (α j))
    (hzP : ∀ j, z j ∉ P)
    (hli : LinearIndependent ℚ (fun j => fun i => (α j i : ℚ) - β j i)) :
    MonomialIndependent (Ideal.Quotient.mk P ∘ z) := by
  intro c c' hass
  rw [← map_monom, ← map_monom] at hass
  have hass' := associated_of_associated_quotient P (monom_notMem hzP c') hass
  have key : ∀ d d' : Fin m → ℕ, monom z d * (monom y (∑ j, d j • β j) * monom y (∑ j, d' j • β j))
      = monom y ((∑ j, d j • α j) + ∑ j, d' j • β j) := by
    intro d d'
    rw [monom_add, ← mul_assoc, monom_mul_monom_sum_eq y z α β hz d]
  have h1 := key c c'
  have h2 := key c' c
  rw [mul_comm (monom y (∑ j, c' j • β j))] at h2
  have hexp := hy ((∑ j, c j • α j) + ∑ j, c' j • β j) ((∑ j, c' j • α j) + ∑ j, c j • β j)
    (by
      rw [← h1, ← h2]
      exact hass'.mul_right _)
  have hsum : ∑ j, ((c j : ℚ) - c' j) • (fun i => (α j i : ℚ) - β j i) = 0 := by
    funext i
    have := congrFun hexp i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    have hq : (∑ j, (c j : ℚ) * α j i) + ∑ j, (c' j : ℚ) * β j i =
        (∑ j, (c' j : ℚ) * α j i) + ∑ j, (c j : ℚ) * β j i := by exact_mod_cast this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e : ∑ j, ((c j : ℚ) - c' j) * ((α j i : ℚ) - β j i) =
        ((∑ j, (c j : ℚ) * α j i) + ∑ j, (c' j : ℚ) * β j i) -
          ((∑ j, (c' j : ℚ) * α j i) + ∑ j, (c j : ℚ) * β j i) := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e, hq, sub_self]
  have hzero := Fintype.linearIndependent_iff.mp hli _ hsum
  funext j
  have := hzero j
  rw [sub_eq_zero] at this
  exact_mod_cast this

/-- **Splitting a family of independent values along the composite `V = V_P ∘ V/P`.** There
are a subfamily `y ∘ a` with independent values in `V_P` and Laurent monomials `z_j` in `y`,
outside `P`, with independent values in `V/P`, and `#κ + m = #ι`. -/
theorem exists_split (y : ι → V) (hy : MonomialIndependent y) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → ι) (m : ℕ) (z : Fin m → V),
      (∀ j, z j ∉ P) ∧ (∀ j, ∃ α β : ι → ℕ, monom y β * z j = monom y α) ∧
      MonomialIndependent (algebraMap V (Localization.AtPrime P) ∘ y ∘ a) ∧
      MonomialIndependent (Ideal.Quotient.mk P ∘ z) ∧
      Fintype.card κ + m = Fintype.card ι := by
  classical
  obtain ⟨κ, _, a, ha, hsupp, hcardκ⟩ :=
    exists_complement_coordinates (Submodule.span ℚ (expDiffSet P y))
  obtain ⟨b, hbD, hbli⟩ := exists_linearIndependent_fin (expDiffSet P y)
  have horient : ∀ j, ∃ α' β' : ι → ℕ, ∃ σ : ℚˣ,
      RelP P (monom y α') (monom y β') ∧ monom y β' ∣ monom y α' ∧
        (fun i => (α' i : ℚ) - β' i) = σ • b j := by
    intro j
    obtain ⟨α₀, β₀, hrel, hbeq⟩ := hbD j
    rcases ValuationRing.dvd_total (monom y β₀) (monom y α₀) with h | h
    · exact ⟨α₀, β₀, 1, hrel, h, by rw [hbeq, one_smul]⟩
    · refine ⟨β₀, α₀, -1, hrel.symm, h, ?_⟩
      rw [hbeq]
      funext i
      simp only [Units.neg_smul, one_smul, Pi.neg_apply]
      ring
  choose α β σ hrel hdiv hbα using horient
  have hli' : LinearIndependent ℚ (fun j => fun i => (α j i : ℚ) - β j i) := by
    convert hbli.units_smul σ using 1
    funext j
    exact hbα j
  choose z hz using hdiv
  have hz' : ∀ j, monom y (β j) * z j = monom y (α j) := fun j => (hz j).symm
  have hzP : ∀ j, z j ∉ P := by
    intro j hzj
    obtain ⟨c, d, hc, hd, hcd⟩ := hrel j
    apply hd
    have : c * z j = d := by
      apply mul_right_cancel₀ (hy.monom_ne_zero (β j))
      rw [mul_assoc, mul_comm (z j), hz' j, hcd]
    rw [← this]
    exact Ideal.mul_mem_left _ _ hzj
  exact ⟨κ, inferInstance, a, _, z, hzP, fun j => ⟨α j, β j, hz' j⟩,
    monomialIndependent_localization P y ha hsupp,
    monomialIndependent_quotient P hy z α β hz' hzP hli', hcardκ⟩

end Split

/-- The induction behind `card_le_height_maximalIdeal`, for families indexed by a type in
`Type`, by strong induction on `n = height 𝔪_B`. -/
theorem card_le_of_height_eq (n : ℕ) {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] (hB : (maximalIdeal B).height = n) {V : Type v} [CommRing V] [IsDomain V]
    [ValuationRing V] (φ : B →+* V) (hφ : Function.Injective φ) (hloc : IsLocalHom φ)
    {ι : Type} [Fintype ι] (x : ι → B) (hx : MonomialIndependent (φ ∘ x)) :
    Fintype.card ι ≤ n := by
  induction n using Nat.strong_induction_on generalizing B V ι with
  | _ n ih =>
  classical
  -- A system of parameters `s` of `B`.
  obtain ⟨s, hs, hcard⟩ := Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal B)
  have hrad : (Ideal.span (s : Set B)).radical = maximalIdeal B := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.radical_eq_sInf]
      exact sInf_le ⟨hs.1.2, (maximalIdeal.isMaximal B).isPrime⟩
    · rw [Ideal.radical_eq_sInf]
      exact le_sInf fun J hJ => hs.2 ⟨hJ.2, hJ.1⟩ (le_maximalIdeal hJ.2.ne_top)
  have hsn : s.card = n := by
    have : (s.card : ℕ∞) = n := hcard.trans hB
    exact_mod_cast this
  have hsm : ∀ f ∈ s, f ∈ maximalIdeal B := fun f hf => hs.1.2 (Ideal.subset_span hf)
  by_cases harch : ∀ i, ∀ f ∈ s, ∃ M : ℕ, ∃ c ∈ maximalIdeal V, φ f ^ M = φ (x i) * c
  · -- The archimedean case: the counting step.
    rw [← hsn]
    exact card_le_card_of_forall_exists_pow_eq_mul φ x hx s hrad harch
  -- The non-archimedean case.
  push Not at harch
  obtain ⟨i₀, f₀, hf₀, hna⟩ := harch
  set g := φ f₀ with hg
  have hdvd : ∀ M : ℕ, g ^ M ∣ φ (x i₀) := by
    intro M
    rcases ValuationRing.dvd_total (g ^ M) (φ (x i₀)) with h | ⟨c, hc⟩
    · exact h
    · by_cases hcm : c ∈ maximalIdeal V
      · exact absurd hc (hna M c hcm)
      · have hcu : IsUnit c := IsLocalRing.notMem_maximalIdeal.mp hcm
        exact ⟨↑hcu.unit⁻¹, by rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  have hx0 : φ (x i₀) ≠ 0 := hx.ne_zero i₀
  have hg0 : g ≠ 0 := by
    intro h
    apply hx0
    have := hdvd 1
    rwa [h, pow_one, zero_dvd_iff] at this
  have hgm : g ∈ maximalIdeal V := map_nonunit φ f₀ (hsm f₀ hf₀)
  have hgu : ¬IsUnit g := (IsLocalRing.mem_maximalIdeal _).mp hgm
  set P := powDvdIdeal g with hPdef
  have hP : P.IsPrime := powDvdIdeal_isPrime hgu
  have hgP : g ∉ P := notMem_powDvdIdeal_self hg0 hgu
  have hxP : φ (x i₀) ∈ P := hdvd
  -- Split the values along the composite `V = V_P ∘ V/P`.
  obtain ⟨κ, _, a, m, z, hzP, hzfrac, hx₁V, hx₂V, hcardκ⟩ := exists_split P (φ ∘ x) hx
  have hfrac : ∀ j, ∃ a' b' : B, a' ≠ 0 ∧ φ a' * z j = φ b' := by
    intro j
    obtain ⟨α, β, hαβ⟩ := hzfrac j
    refine ⟨monom x β, monom x α, ?_, ?_⟩
    · intro h0
      apply hx.monom_ne_zero β
      rw [← map_monom, h0, map_zero]
    · rw [map_monom, map_monom, hαβ]
  -- The ring `C = B[z]_𝔮`.
  set C := AdjoinLoc φ z
  set φC := adjoinLocHom φ z
  have hφC : Function.Injective φC := adjoinLocHom_injective φ z
  have hCle : (maximalIdeal C).height ≤ n :=
    (height_maximalIdeal_adjoinLoc_le φ z hφ hfrac).trans hB.le
  have hφCι : ∀ c : B, φC (algebraMap B C c) = φ c := adjoinLocHom_algebraMap φ z
  set p := Ideal.comap φC P with hpdef
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have hpm : p ≤ maximalIdeal C := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hp0 : p ≠ ⊥ := by
    intro h
    have hmem : algebraMap B C (x i₀) ∈ p := by
      rw [hpdef, Ideal.mem_comap, hφCι]
      exact hxP
    rw [h, Ideal.mem_bot] at hmem
    apply hx0
    rw [← hφCι, hmem, map_zero]
  have hf₀p : algebraMap B C f₀ ∉ p := by
    rw [hpdef, Ideal.mem_comap, hφCι]
    exact hgP
  -- The localization piece `C_𝔭 → V_P`.
  set C₁ := Localization.AtPrime p
  set V₁ := Localization.AtPrime P
  have : IsDomain V₁ := IsLocalization.isDomain_of_local_atPrime hP
  have : ValuationRing V₁ := ValuationRing.of_isLocalization P.primeCompl
  have : IsDomain C₁ := IsLocalization.isDomain_of_local_atPrime inferInstance
  have : IsNoetherianRing C₁ := IsLocalization.isNoetherianRing p.primeCompl C₁ inferInstance
  set g₁ : C →+* V₁ := (algebraMap V V₁).comp φC
  have hg₁ : Ideal.comap g₁ (maximalIdeal V₁) = p := by
    rw [← Ideal.comap_comap]
    congr 1
    exact Localization.AtPrime.comap_maximalIdeal
  have hg₁inj : Function.Injective g₁ :=
    (IsLocalization.injective V₁ P.primeCompl_le_nonZeroDivisors).comp hφC
  set ψ₁ := liftAtPrime g₁ p hg₁
  have hψ₁ : Function.Injective ψ₁ := liftAtPrime_injective g₁ p hg₁ hg₁inj
  have hψ₁loc : IsLocalHom ψ₁ := isLocalHom_liftAtPrime g₁ p hg₁
  set x₁ : κ → C₁ := fun k => algebraMap C C₁ (algebraMap B C (x (a k)))
  have hx₁eq : ψ₁ ∘ x₁ = algebraMap V V₁ ∘ ((φ ∘ x) ∘ a) := by
    funext k
    exact (liftAtPrime_algebraMap g₁ p hg₁ _).trans (by
      simp only [g₁, RingHom.comp_apply, hφCι, Function.comp_apply])
  have hx₁ : MonomialIndependent (ψ₁ ∘ x₁) := by
    rw [hx₁eq]
    exact hx₁V
  -- The quotient piece `C/𝔭 → V/P`.
  have : IsLocalRing (C ⧸ p) := isLocalRing_quotient p
  have : ValuationRing (V ⧸ P) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  set ψ₂ := Ideal.quotientMap P φC (le_refl (Ideal.comap φC P))
  have hψ₂ : Function.Injective ψ₂ := Ideal.quotientMap_injective' le_rfl
  have hψ₂loc : IsLocalHom ψ₂ := isLocalHom_quotientMap φC P
  set x₂ : Fin m → C ⧸ p := fun j => Ideal.Quotient.mk p (adjoinGen φ z j)
  have hx₂eq : ψ₂ ∘ x₂ = Ideal.Quotient.mk P ∘ z := by
    funext j
    simp only [Function.comp_apply, x₂, ψ₂]
    rw [Ideal.quotientMap_mk]
    exact congrArg _ (adjoinLocHom_adjoinGen φ z j)
  have hx₂ : MonomialIndependent (ψ₂ ∘ x₂) := by
    rw [hx₂eq]
    exact hx₂V
  -- Heights.
  have hheight := Stacks.Spectrum.LocalDimensionFormula.height_add_height_map_quotientMk_le p
    (maximalIdeal C) hpm
  rw [maximalIdeal_quotient_eq p] at hheight
  have hp1 : p.height ≠ 0 := fun h => hp0 (Ideal.height_eq_zero_iff_eq_bot.mp h)
  have hq1 : (maximalIdeal (C ⧸ p)).height ≠ 0 := by
    intro h
    have hbot := Ideal.height_eq_zero_iff_eq_bot.mp h
    have hmem : Ideal.Quotient.mk p (algebraMap B C f₀) ∈ maximalIdeal (C ⧸ p) := by
      rw [← maximalIdeal_quotient_eq p]
      refine Ideal.mem_map_of_mem _ ?_
      rw [← IsLocalRing.maximalIdeal_comap φC, Ideal.mem_comap, hφCι]
      exact hgm
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hf₀p hmem
  have htot : p.height + (maximalIdeal (C ⧸ p)).height ≤ n := hheight.trans hCle
  have hlift : ∀ k : ℕ∞, k ≤ n → ∃ a : ℕ, k = a := fun k hk =>
    ⟨k.toNat, (ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top n) hk)).symm⟩
  obtain ⟨a₁, ha₁⟩ := hlift _ (le_self_add.trans htot)
  obtain ⟨b₁, hb₁⟩ := hlift _ (le_add_self.trans htot)
  rw [ha₁, hb₁] at htot
  rw [ha₁] at hp1
  rw [hb₁] at hq1
  have htot' : a₁ + b₁ ≤ n := by exact_mod_cast htot
  have hp1' : a₁ ≠ 0 := by exact_mod_cast hp1
  have hq1' : b₁ ≠ 0 := by exact_mod_cast hq1
  have ha₁n : a₁ < n := by omega
  have hb₁n : b₁ < n := by omega
  have hC₁h : (maximalIdeal C₁).height = a₁ := by
    rw [height_maximalIdeal_localization, ha₁]
  have hκ : Fintype.card κ ≤ a₁ := ih a₁ ha₁n hC₁h ψ₁ hψ₁ hψ₁loc x₁ hx₁
  have hr₁ : Fintype.card (Fin m) ≤ b₁ := ih b₁ hb₁n hb₁ ψ₂ hψ₂ hψ₂loc x₂ hx₂
  rw [Fintype.card_fin] at hr₁
  rw [← hcardκ]
  omega

/-- **Abhyankar's inequality, rational rank part.** Let `B` be a Noetherian local domain and
`φ : B → V` an injective local homomorphism into a valuation ring. If the values of
`x₁, …, x_r ∈ B` in `V` are `ℤ`-linearly independent, then `r ≤ height 𝔪_B = dim B`. -/
theorem card_le_height_maximalIdeal {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] {V : Type v} [CommRing V] [IsDomain V] [ValuationRing V] (φ : B →+* V)
    (hφ : Function.Injective φ) [IsLocalHom φ] {ι : Type w} [Fintype ι] (x : ι → B)
    (hx : MonomialIndependent (φ ∘ x)) :
    (Fintype.card ι : ℕ∞) ≤ (maximalIdeal B).height := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (maximalIdeal B).height = n :=
    ⟨_, (ENat.coe_toNat (Ideal.height_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top)).symm⟩
  let e := Fintype.equivFin ι
  have h := card_le_of_height_eq n hn φ hφ inferInstance (x ∘ e.symm)
    (by
      have := hx.comp_equiv e.symm
      simpa [Function.comp_assoc] using this)
  rw [hn, Fintype.card_fin] at *
  exact_mod_cast h

/-- **Abhyankar's inequality, rational rank part**, in terms of the Krull dimension. -/
theorem card_le_ringKrullDim {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] {V : Type v} [CommRing V] [IsDomain V] [ValuationRing V] (φ : B →+* V)
    (hφ : Function.Injective φ) [IsLocalHom φ] {ι : Type w} [Fintype ι] (x : ι → B)
    (hx : MonomialIndependent (φ ∘ x)) :
    (Fintype.card ι : WithBot ℕ∞) ≤ ringKrullDim B := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast card_le_height_maximalIdeal φ hφ x hx

end Stacks.Abhyankar

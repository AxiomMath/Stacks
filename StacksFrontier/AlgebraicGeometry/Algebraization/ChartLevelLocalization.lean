module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkModuleComparison
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkModuleLevels

/-!
# The levels of a localized module over a completed chart ring, as localizations over the base

Let `A` be a ring, `f ∈ A`, `R = A_f`, `J ⊆ R` a finitely generated ideal contained in a prime
`𝔭` of `R`, `B = R^∧_J` the `J`-adic completion and `𝔮` the prime of `B` over `𝔭` containing `JB`
(`Stacks.Algebraization.adicPrimeOver`). For a `B`-module `N`, the level-`n` quotient
`N_𝔮 / Jⁿ N_𝔮` of its localization at `𝔮` is a localization of `N / JⁿN` at `B ∖ 𝔮`. When
moreover `N / JⁿN` is identified with the localization `L_f` of an `A`-module `L`, this file
shows that the composite `L → L_f ≅ N / JⁿN → N_𝔮 / Jⁿ N_𝔮` is a localization **over `A`** at
the complement of the prime of `A` under `𝔭`.

The point is that on a module annihilated by `JⁿB` every element of `B ∖ 𝔮` acts as an element
of `R ∖ 𝔭` (`Stacks.Algebraization.exists_notMem_algebraMap_sub_mem_map_pow`), and every element of
`R = A_f` is a fraction `a / fʲ` with `a ∈ A`.

This is the chart side of the comparison of the completed stalk of a finite module model at a
point `y` with the completion of the localization of the chart vertex at `𝔮`, the input needed
to read the depth hypotheses of Stacks 0EJ3 at `B_𝔮` (the per-point paragraph of the proof of
Stacks 0EHK).

## Main results

* `Stacks.Algebraization.isLocalizedModule_chartLevelMap` — the composite above is a
  localization at the complement of the prime of `A` under `𝔭`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Algebraization

section ChartLevel

variable {A : Type u} [CommRing A] (f : A)
  (J : Ideal (Localization.Away f)) (hJ : J.FG) {p : Ideal (Localization.Away f)} [p.IsPrime]
  (hJp : J ≤ p)
  {N : Type u} [AddCommGroup N] [Module (AdicCompletion J (Localization.Away f)) N]
  [Module A N] [Module (Localization.Away f) N]
  [IsScalarTower A (Localization.Away f) N]
  [IsScalarTower (Localization.Away f) (AdicCompletion J (Localization.Away f)) N]
  {L : Type u} [AddCommGroup L] [Module A L] (n : ℕ)
  (g : LocalizedModule (Submonoid.powers f) L ≃ₗ[Localization.Away f]
    (N ⧸ ((J.map (algebraMap (Localization.Away f) (AdicCompletion J (Localization.Away f)))) ^ n •
      (⊤ : Submodule (AdicCompletion J (Localization.Away f)) N))))

/-- The complement of the prime of `A` under `𝔭`. -/
abbrev chartBaseCompl : Submonoid A :=
  (p.comap (algebraMap A (Localization.Away f))).primeCompl

/-- `f` lies outside the prime of `A` under any prime of `A_f`. -/
theorem notMem_comap_of_away : f ∉ p.comap (algebraMap A (Localization.Away f)) := by
  intro h
  exact Ideal.IsPrime.ne_top ‹p.IsPrime› (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp h)
    (IsLocalization.Away.algebraMap_isUnit f))

include hJ in
/-- **An element of `B ∖ 𝔮` acts, after a power of `f`, as an element of `A ∖ 𝔭` on every module
annihilated by `JⁿB`.** -/
theorem exists_pow_smul_eq_of_notMem_adicPrimeOver
    {t : AdicCompletion J (Localization.Away f)} (ht : t ∉ (adicPrimeOver J hJp).asIdeal) :
    ∃ (a : A) (j : ℕ), a ∉ p.comap (algebraMap A (Localization.Away f)) ∧
      algebraMap A (AdicCompletion J (Localization.Away f)) (f ^ j) * t -
          algebraMap A (AdicCompletion J (Localization.Away f)) a ∈
        (J.map (algebraMap (Localization.Away f)
          (AdicCompletion J (Localization.Away f)))) ^ n := by
  obtain ⟨c, hc, hsub⟩ := exists_notMem_algebraMap_sub_mem_map_pow J hJ hJp n ht
  obtain ⟨⟨a, ⟨_, ⟨j, rfl⟩⟩⟩, hac⟩ := IsLocalization.surj (Submonoid.powers f) c
  refine ⟨a, j, ?_, ?_⟩
  · intro ha
    apply hc
    have hmem : c * algebraMap A (Localization.Away f) (f ^ j) ∈ p := by
      rw [hac]; exact ha
    rcases (‹p.IsPrime›.mem_or_mem hmem) with h | h
    · exact h
    · rw [map_pow] at h
      exact absurd (Ideal.mem_comap.mpr (‹p.IsPrime›.mem_of_pow_mem j h))
        (notMem_comap_of_away (p := p) f)
  · have hmem := Ideal.mul_mem_left _
      (algebraMap A (AdicCompletion J (Localization.Away f)) (f ^ j)) hsub
    rw [Ideal.map_pow] at hmem
    convert hmem using 1
    rw [mul_sub, IsScalarTower.algebraMap_apply A (Localization.Away f)
        (AdicCompletion J (Localization.Away f)) a,
      IsScalarTower.algebraMap_apply A (Localization.Away f)
        (AdicCompletion J (Localization.Away f)) (f ^ j), ← map_mul, ← hac, mul_comm c]

variable [IsScalarTower A (AdicCompletion J (Localization.Away f)) N]
  (Bq : Type u) [CommRing Bq] [Algebra (AdicCompletion J (Localization.Away f)) Bq]
  [Algebra A Bq] [IsScalarTower A (AdicCompletion J (Localization.Away f)) Bq]
  [IsLocalization (adicPrimeOver J hJp).asIdeal.primeCompl Bq]
  {Nq : Type u} [AddCommGroup Nq] [Module (AdicCompletion J (Localization.Away f)) Nq]
  [Module Bq Nq] [IsScalarTower (AdicCompletion J (Localization.Away f)) Bq Nq]
  [Module A Nq] [IsScalarTower A Bq Nq]
  [IsScalarTower A (AdicCompletion J (Localization.Away f)) Nq]
  (fq : N →ₗ[AdicCompletion J (Localization.Away f)] Nq)
  [IsLocalizedModule (adicPrimeOver J hJp).asIdeal.primeCompl fq]

/-- **The chart level map** `L → L_f ≅ N / JⁿN → N_𝔮 / Jⁿ N_𝔮`, as an `A`-linear map. -/
def chartLevelMap : L →ₗ[A] (Nq ⧸ ((J.map (algebraMap (Localization.Away f)
      (AdicCompletion J (Localization.Away f)))).map
        (algebraMap (AdicCompletion J (Localization.Away f)) Bq) ^ n • (⊤ : Submodule Bq Nq))) :=
  ((levelLocalizationMap (J.map (algebraMap (Localization.Away f)
      (AdicCompletion J (Localization.Away f)))) (adicPrimeOver J hJp).asIdeal.primeCompl Bq fq
        n).restrictScalars A) ∘ₗ (g.toLinearMap.restrictScalars A) ∘ₗ
    LocalizedModule.mkLinearMap (Submonoid.powers f) L

omit [Module A N] [Module (Localization.Away f) N] [IsScalarTower A (Localization.Away f) N]
  [IsScalarTower (Localization.Away f) (AdicCompletion J (Localization.Away f)) N]
  [IsScalarTower A (AdicCompletion J (Localization.Away f)) N] in
/-- An element of `JⁿB` acts as zero on `N / JⁿN`. -/
theorem smul_eq_zero_level {t : AdicCompletion J (Localization.Away f)}
    (ht : t ∈ (J.map (algebraMap (Localization.Away f)
      (AdicCompletion J (Localization.Away f)))) ^ n)
    (x : N ⧸ ((J.map (algebraMap (Localization.Away f)
      (AdicCompletion J (Localization.Away f)))) ^ n •
        (⊤ : Submodule (AdicCompletion J (Localization.Away f)) N))) : t • x = 0 :=
  smul_eq_zero_of_forall_smul_mem (A := AdicCompletion J (Localization.Away f))
    (B := AdicCompletion J (Localization.Away f)) _
    (fun _ => Submodule.smul_mem_smul ht Submodule.mem_top) x

omit [Algebra A Bq] [IsScalarTower A (AdicCompletion J (Localization.Away f)) Bq] [Module A Nq]
  [IsScalarTower A Bq Nq] [IsScalarTower A (AdicCompletion J (Localization.Away f)) Nq] in
/-- An element of `JⁿB` acts as zero on `N_𝔮 / Jⁿ N_𝔮`. -/
theorem smul_eq_zero_levelLocalized {t : AdicCompletion J (Localization.Away f)}
    (ht : t ∈ (J.map (algebraMap (Localization.Away f)
      (AdicCompletion J (Localization.Away f)))) ^ n)
    (x : Nq ⧸ ((J.map (algebraMap (Localization.Away f)
      (AdicCompletion J (Localization.Away f)))).map
        (algebraMap (AdicCompletion J (Localization.Away f)) Bq) ^ n • (⊤ : Submodule Bq Nq))) :
    t • x = 0 := by
  have hmap : algebraMap (AdicCompletion J (Localization.Away f)) Bq t ∈
      ((J.map (algebraMap (Localization.Away f) (AdicCompletion J (Localization.Away f)))).map
        (algebraMap (AdicCompletion J (Localization.Away f)) Bq)) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ht
  have := smul_eq_zero_of_forall_smul_mem (A := Bq) (B := Bq) _
    (fun y => Submodule.smul_mem_smul hmap Submodule.mem_top) x
  rwa [algebraMap_smul] at this

/-- If `(algebraMap f' * t - algebraMap a)` kills `x`, then `f' • t • x = a • x`. -/
private theorem smul_smul_eq_of_sub_smul_eq_zero {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    {f' a : R} {t : S} {x : M} (h : (algebraMap R S f' * t - algebraMap R S a) • x = 0) :
    f' • t • x = a • x := by
  rwa [sub_smul, mul_smul, sub_eq_zero, algebraMap_smul, algebraMap_smul] at h

/-- The prime of `B` over `𝔭` contracts to the prime of `A` under `𝔭`. -/
theorem algebraMap_mem_adicPrimeOver_iff (a : A) :
    algebraMap A (AdicCompletion J (Localization.Away f)) a ∈ (adicPrimeOver J hJp).asIdeal ↔
      a ∈ p.comap (algebraMap A (Localization.Away f)) := by
  rw [IsScalarTower.algebraMap_apply A (Localization.Away f)
    (AdicCompletion J (Localization.Away f)), ← Ideal.mem_comap, comap_adicPrimeOver,
    Ideal.mem_comap]

include hJ in
/-- **The chart level map is a localization at the complement of the prime of `A` under `𝔭`.** -/
theorem isLocalizedModule_chartLevelMap :
    IsLocalizedModule (chartBaseCompl f (p := p)) (chartLevelMap f J hJp n g Bq fq) := by
  set B := AdicCompletion J (Localization.Away f)
  set lev := levelLocalizationMap (J.map (algebraMap (Localization.Away f) B))
    (adicPrimeOver J hJp).asIdeal.primeCompl Bq fq n
  have hP : (p.comap (algebraMap A (Localization.Away f))).IsPrime := Ideal.comap_isPrime _ _
  have hfi : ∀ i : ℕ, f ^ i ∈ (p.comap (algebraMap A (Localization.Away f))).primeCompl :=
    fun i h => notMem_comap_of_away f (hP.mem_of_pow_mem i h)
  -- an element of `B ∖ 𝔮` acts, after a power of `f`, as an element of `A ∖ 𝔭`
  have key : ∀ t : (adicPrimeOver J hJp).asIdeal.primeCompl, ∃ (a : A) (j : ℕ),
      a ∉ p.comap (algebraMap A (Localization.Away f)) ∧
      (∀ x : N ⧸ ((J.map (algebraMap (Localization.Away f) B)) ^ n • (⊤ : Submodule B N)),
        (f ^ j) • (t : B) • x = a • x) ∧
      (∀ y : Nq ⧸ ((J.map (algebraMap (Localization.Away f) B)).map
          (algebraMap B Bq) ^ n • (⊤ : Submodule Bq Nq)), (f ^ j) • (t : B) • y = a • y) := by
    intro t
    obtain ⟨a, j, ha, hmem⟩ := exists_pow_smul_eq_of_notMem_adicPrimeOver f J hJ hJp n t.2
    refine ⟨a, j, ha, fun x => ?_, fun y => ?_⟩
    · exact smul_smul_eq_of_sub_smul_eq_zero (smul_eq_zero_level f J n hmem x)
    · exact smul_smul_eq_of_sub_smul_eq_zero (smul_eq_zero_levelLocalized f J n Bq hmem y)
  set h : LocalizedModule (Submonoid.powers f) L →ₗ[A] _ :=
    (lev.restrictScalars A) ∘ₗ (g.toLinearMap.restrictScalars A) with hh
  have hcl : ∀ l : L, chartLevelMap f J hJp n g Bq fq l = h (LocalizedModule.mk l 1) :=
    fun _ => rfl
  have hhapp : ∀ z, h z = lev (g z) := fun _ => rfl
  refine ⟨fun s => ?_, fun y => ?_, fun {l₁ l₂} e => ?_⟩
  · -- `s ∉ 𝔭` is a unit of `B_𝔮`
    have hs : algebraMap A B s ∈ (adicPrimeOver J hJp).asIdeal.primeCompl := fun h =>
      s.2 ((algebraMap_mem_adicPrimeOver_iff f J hJp s).mp h)
    obtain ⟨u, hu⟩ :=
      IsLocalization.map_units Bq (⟨_, hs⟩ : (adicPrimeOver J hJp).asIdeal.primeCompl)
    rw [Module.End.isUnit_iff]
    have hsm : ∀ z : Nq ⧸ ((J.map (algebraMap (Localization.Away f) B)).map
        (algebraMap B Bq) ^ n • (⊤ : Submodule Bq Nq)), (s : A) • z = (u : Bq) • z := by
      intro z
      rw [hu, ← IsScalarTower.algebraMap_apply, algebraMap_smul]
    refine ⟨fun z₁ z₂ hz => ?_, fun z => ⟨(↑u⁻¹ : Bq) • z, ?_⟩⟩
    · have h := congrArg (fun w => (↑u⁻¹ : Bq) • w) hz
      simp only [Module.algebraMap_end_apply, hsm] at h
      rwa [smul_smul, smul_smul, Units.inv_mul, one_smul, one_smul] at h
    · simp only [Module.algebraMap_end_apply, hsm]
      rw [smul_smul, Units.mul_inv, one_smul]
  · obtain ⟨⟨x, t⟩, hx⟩ := IsLocalizedModule.surj (adicPrimeOver J hJp).asIdeal.primeCompl lev y
    obtain ⟨a, j, ha, -, hay⟩ := key t
    obtain ⟨z, rfl⟩ := g.surjective x
    induction z using LocalizedModule.induction_on with
    | h l k =>
      obtain ⟨i, hi⟩ := k.2
      have hk : (k : A) ∈ (p.comap (algebraMap A (Localization.Away f))).primeCompl := by
        rw [← hi]; exact hfi i
      refine ⟨⟨f ^ j • l, ⟨(k : A) * a, mul_mem hk ha⟩⟩, ?_⟩
      dsimp only at hx ⊢
      rw [Submonoid.smul_def] at hx
      change ((k : A) * a) • y = h (LocalizedModule.mk (f ^ j • l) 1)
      have hmk : LocalizedModule.mk (f ^ j • l) (1 : Submonoid.powers f) =
          ((k : A) * f ^ j) • LocalizedModule.mk l k := by
        rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, smul_smul]
      rw [hmk, map_smul, hhapp, ← hx]
      simp only [mul_smul]
      rw [← hay y]
  · obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := (adicPrimeOver J hJp).asIdeal.primeCompl)
      (f := lev) (show lev (g (LocalizedModule.mk l₁ 1)) = lev (g (LocalizedModule.mk l₂ 1)) from e)
    obtain ⟨a, j, ha, hax, -⟩ := key t
    rw [Submonoid.smul_def, Submonoid.smul_def] at ht
    have h1 : g (a • LocalizedModule.mk l₁ 1) = g (a • LocalizedModule.mk l₂ 1) := by
      change (g.restrictScalars A) (a • _) = (g.restrictScalars A) (a • _)
      rw [map_smul, map_smul]
      change a • g _ = a • g _
      rw [← hax, ← hax, ht]
    have h2 := g.injective h1
    rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h2
    obtain ⟨⟨_, ⟨i, rfl⟩⟩, hi⟩ := h2
    refine ⟨⟨f ^ i * a, mul_mem (hfi i) ha⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul] at hi ⊢
    rw [mul_smul, mul_smul, hi]

end ChartLevel

end Stacks.Algebraization

end

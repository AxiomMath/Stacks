module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.KoszulTateComparison

/-! # The Koszul and Tate inverse systems are pro-isomorphic

Let `R` be a Noetherian ring and `f₁, …, f_r ∈ R`. Write `K_m` for the Koszul divided power
algebra `R⟨ξ₁, …, ξ_r⟩` with `ξᵢ` of degree one and `d(ξᵢ) = fᵢ^m`, and `K_M → K_m` for the
transition map `ξᵢ ↦ fᵢ^(M-m) ξᵢ`; these form an inverse system of differential graded
`R`-algebras with compatible divided powers. Tag 0GZ4 interpolates one Tate resolution between
two of them, and iterating it produces a sequence of exponents `1 = n₀ < n₁ < n₂ < ⋯` together
with divided power differential graded algebras `Aᵢ` and maps
`K_{nᵢ₊₁} → Aᵢ → R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁})` and `Aᵢ → K_{nᵢ}`. Taking `Aᵢ₊₁ → Aᵢ` to be the
composite `Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` makes the ladder of the two rows of Koszul algebras and the row
of Tate resolutions commute, and exhibits the two inverse systems as pro-isomorphic: the
composite `K_{nᵢ₊₁} → Aᵢ → K_{nᵢ}` is the Koszul transition map and the composite
`Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` is the Tate transition map, while the exponents `nᵢ` are cofinal in the
Koszul system. This is Tag 0GZ5.

The exponents and the resolutions are produced simultaneously by recursion on the index: the
exponent of the next stage is the exponent reached by the previous one, so a single witness of
Tag 0GZ4 is taken at each step. Applying Tag 0GZ4 to `nᵢ + 1` rather than to `nᵢ` and composing
the resulting map down with one more Koszul transition makes the sequence of exponents strictly
increasing, hence cofinal.

## Main definitions

* `DividedPowers.TateResolution.KoszulTateStage` — one factorization of a Koszul transition map
  through a divided power differential graded resolution, as in Tag 0GZ4.
* `DividedPowers.TateResolution.KoszulTateStage.proTransition` — the transition map of the Tate
  system, the composite of two consecutive stages through the Koszul algebra between them.
* `DividedPowers.TateResolution.koszulTatePower` and
  `DividedPowers.TateResolution.koszulTateProStage` — the sequence of exponents
  `1 = n₀ < n₁ < ⋯` and the stage over each of them.

## Main results

* `DividedPowers.TateResolution.KoszulTateStage.proTransition_up` and
  `DividedPowers.TateResolution.KoszulTateStage.down_proTransition` — the two squares of the
  ladder commute.
* `DividedPowers.TateResolution.exists_koszulTateProIso` — Tag 0GZ5.

## References

* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
* [Stacks Project, Tag 0GZ5](https://stacks.math.columbia.edu/tag/0GZ5)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

variable {R : Type u} [CommRing R] {r : ℕ}

/-- One stage of the Koszul--Tate ladder over the exponent `n`: a divided power differential
graded resolution `A` of `R/(f₁^N, …, f_r^N)` for an exponent `N > n`, together with the maps
`K_N → A → R/(f₁^N, …, f_r^N)` and `A → K_n` of Tag 0GZ4. -/
public structure KoszulTateStage (f : Fin r → R) (n : ℕ) where
  /-- The exponent resolved by the stage. -/
  topPower : ℕ
  /-- The resolved exponent is larger than the exponent mapped down to. -/
  lt : n < topPower
  /-- The divided power graded algebra of the stage. -/
  A : GradedDPAlgebra.{u, u} R
  /-- Its differential. -/
  d : A.carrier →ₗ[R] A.carrier
  /-- The identification of `R` with the degree-zero part of `A`. -/
  coeff : R →ₐ[R] A.carrier
  /-- The augmentation of `A` onto `R/(f₁^N, …, f_r^N)`. -/
  aug : A.carrier →ₐ[R] R ⧸ koszulPowerIdeal f topPower
  /-- The map `K_N → A`. -/
  up : ExteriorAlgebra R (Fin r → R) →ₐ[R] A.carrier
  /-- The map `A → K_n`. -/
  down : A.carrier →ₐ[R] ExteriorAlgebra R (Fin r → R)
  /-- The differential makes the grading of `A` a differential graded algebra. -/
  dga : IsDifferentialGradedAlgebra A.grade d
  /-- The divided powers of `A` are compatible with its differential. -/
  compatible : IsCompatibleWithDifferential A.gamma d
  /-- `A` is a graded divided power polynomial algebra, finitely generated in each degree. -/
  polynomial : ∃ P : GradedDividedPowerPolynomial A.grade A.gamma coeff,
    ∀ i : ℕ, Finite (P.indices i)
  /-- `R` embeds into `A`. -/
  coeff_injective : Function.Injective coeff
  /-- The degree-zero part of `A` is the image of `R`. -/
  mem_grade_zero : ∀ a : A.carrier, a ∈ A.grade 0 ↔ ∃ c : R, coeff c = a
  /-- The augmentation is the canonical surjection in degree zero. -/
  aug_coeff : ∀ c : R, aug (coeff c) = Ideal.Quotient.mk (koszulPowerIdeal f topPower) c
  /-- The augmentation is surjective. -/
  aug_surjective : Function.Surjective aug
  /-- The augmentation kills the positive degrees. -/
  aug_positive : ∀ (k : ℕ) (a : A.carrier), 0 < k → a ∈ A.grade k → aug a = 0
  /-- The augmentation kills the boundaries. -/
  aug_d : ∀ a : A.carrier, aug (d a) = 0
  /-- A degree-zero element killed by the augmentation is a boundary. -/
  exists_d_eq_of_aug_eq_zero : ∀ a : A.carrier, a ∈ A.grade 0 → aug a = 0 →
    ∃ b ∈ A.grade 1, d b = a
  /-- A cycle of positive degree is a boundary. -/
  exists_d_eq_of_cycle : ∀ (k : ℕ) (a : A.carrier), a ∈ A.grade (k + 1) → d a = 0 →
    ∃ b ∈ A.grade (k + 2), d b = a
  /-- The map `K_N → A` preserves degrees. -/
  up_grade : ∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
    x ∈ exteriorGrade R (Fin r → R) k → up x ∈ A.grade k
  /-- The map `K_N → A` is a chain map. -/
  up_d : ∀ x, up (koszulPowerDifferential f topPower x) = d (up x)
  /-- The map `K_N → A` preserves divided powers. -/
  up_dpow : ∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
    x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
      up ((exteriorDividedPowerStructure R r).dpow k x) = A.gamma.dpow k (up x)
  /-- The map `A → K_n` preserves degrees. -/
  down_grade : ∀ (k : ℕ) (a : A.carrier), a ∈ A.grade k →
    down a ∈ exteriorGrade R (Fin r → R) k
  /-- The map `A → K_n` is a chain map. -/
  down_d : ∀ a, down (d a) = koszulPowerDifferential f n (down a)
  /-- The map `A → K_n` preserves divided powers. -/
  down_dpow : ∀ (k : ℕ) (a : A.carrier), a ∈ positiveEvenPart A.grade →
    down (A.gamma.dpow k a) = (exteriorDividedPowerStructure R r).dpow k (down a)
  /-- The composite `K_N → A → R/(f₁^N, …, f_r^N)` is the canonical map. -/
  aug_up : ∀ x, aug (up x) = koszulPowerAugmentation f topPower x
  /-- The composite `K_N → A → K_n` is the Koszul transition map. -/
  down_up : ∀ x, down (up x) = koszulPowerTransitionHom f topPower n x
  /-- The map `A → K_n` is the identity of `R` in degree zero. -/
  down_coeff : ∀ c : R, down (coeff c) = algebraMap R (ExteriorAlgebra R (Fin r → R)) c
  /-- The map `A → K_n` induces `R/(f₁^N, …, f_r^N) → R/(f₁^n, …, f_r^n)` in degree-zero
  homology. -/
  down_homology : ∀ a : A.carrier, a ∈ A.grade 0 →
    koszulPowerAugmentation f n (down a) =
      Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f lt.le) (aug a)

section Existence

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}

/-- Over a Noetherian ring every exponent `n` is the bottom of a stage, that is, the Koszul
transition map out of some strictly larger exponent factors through a divided power differential
graded resolution. -/
public theorem nonempty_koszulTateStage (f : Fin r → R) (n : ℕ) :
    Nonempty (KoszulTateStage f n) := by
  obtain ⟨N, hN, A, d, coeff, aug, up, down, hdga, hcompat, hpoly, hinj, hzero, haugc, haugs,
    haugp, haugd, hbd0, hbd, hupg, hupd, hupdp, hdng, hdnd, hdndp, haugup, hdnup, hdnc, _⟩ :=
    exists_tateResolution_koszulPowers f (n + 1)
  have hle : n ≤ n + 1 := Nat.le_succ n
  have hlt : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) hN
  set down' := (koszulPowerTransitionHom f (n + 1) n).comp down with hdown'
  have hdng' : ∀ (k : ℕ) (a : A.carrier), a ∈ A.grade k →
      down' a ∈ exteriorGrade R (Fin r → R) k :=
    fun k a ha => koszulPowerTransitionHom_mem f (n + 1) n k (hdng k a ha)
  have hdnd' : ∀ a, down' (d a) = koszulPowerDifferential f n (down' a) := by
    intro a
    simp only [hdown', AlgHom.comp_apply, hdnd a]
    exact koszulPowerTransitionHom_differential f hle (down a)
  have hdndp' : ∀ (k : ℕ) (a : A.carrier), a ∈ positiveEvenPart A.grade →
      down' (A.gamma.dpow k a) = (exteriorDividedPowerStructure R r).dpow k (down' a) := by
    intro k a ha
    simp only [hdown', AlgHom.comp_apply, hdndp k a ha]
    exact koszulPowerTransitionHom_dpow f (n + 1) n k
      (algHom_mem_positiveEvenPart A.grade (exteriorGrade R (Fin r → R)) down hdng ha)
  have hdnup' : ∀ x, down' (up x) = koszulPowerTransitionHom f N n x := by
    intro x
    simp only [hdown', AlgHom.comp_apply, hdnup x]
    exact koszulPowerTransitionHom_comp f hle hN x
  have hdnc' : ∀ c : R, down' (coeff c) = algebraMap R (ExteriorAlgebra R (Fin r → R)) c := by
    intro c
    simp only [hdown', AlgHom.comp_apply, hdnc c]
    exact (koszulPowerTransitionHom f (n + 1) n).commutes c
  have hhom : ∀ a : A.carrier, a ∈ A.grade 0 →
      koszulPowerAugmentation f n (down' a) =
        Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f hlt.le) (aug a) := by
    intro a ha
    obtain ⟨c, rfl⟩ := (hzero a).1 ha
    rw [hdnc' c, haugc c, koszulPowerAugmentation_algebraMap, Ideal.Quotient.factor_mk]
  exact ⟨{ topPower := N, lt := hlt, A := A, d := d, coeff := coeff, aug := aug, up := up
           down := down', dga := hdga, compatible := hcompat, polynomial := hpoly
           coeff_injective := hinj, mem_grade_zero := hzero, aug_coeff := haugc
           aug_surjective := haugs, aug_positive := haugp, aug_d := haugd
           exists_d_eq_of_aug_eq_zero := hbd0, exists_d_eq_of_cycle := hbd
           up_grade := hupg, up_d := hupd, up_dpow := hupdp, aug_up := haugup
           down_grade := hdng', down_d := hdnd', down_dpow := hdndp'
           down_up := hdnup', down_coeff := hdnc', down_homology := hhom }⟩

/-- A stage over the exponent `n`: one witness of the factorization of Tag 0GZ4. -/
public noncomputable def koszulTateStageOf (f : Fin r → R) (n : ℕ) : KoszulTateStage f n :=
  (nonempty_koszulTateStage f n).some

/-- The chain of stages, built by recursion on the index: the exponent of a stage is the
exponent resolved by the previous one, starting from the exponent `1`. -/
public noncomputable def koszulTateChain (f : Fin r → R) : ℕ → (m : ℕ) × KoszulTateStage f m
  | 0 => ⟨1, koszulTateStageOf f 1⟩
  | i + 1 =>
    ⟨(koszulTateChain f i).2.topPower, koszulTateStageOf f (koszulTateChain f i).2.topPower⟩

/-- The sequence of exponents `1 = n₀ < n₁ < n₂ < ⋯` of the Koszul--Tate ladder. -/
public noncomputable def koszulTatePower (f : Fin r → R) (i : ℕ) : ℕ :=
  (koszulTateChain f i).1

/-- The stage of the Koszul--Tate ladder over the exponent `nᵢ`; it resolves `nᵢ₊₁`. -/
public noncomputable def koszulTateProStage (f : Fin r → R) (i : ℕ) :
    KoszulTateStage f (koszulTatePower f i) :=
  (koszulTateChain f i).2

/-- The sequence of exponents starts at `1`. -/
public theorem koszulTatePower_zero (f : Fin r → R) : koszulTatePower f 0 = 1 := rfl

/-- The exponent resolved by the `i`-th stage is the exponent of the next one. -/
public theorem koszulTateProStage_topPower (f : Fin r → R) (i : ℕ) :
    (koszulTateProStage f i).topPower = koszulTatePower f (i + 1) := rfl

/-- The sequence of exponents is strictly increasing. -/
public theorem koszulTatePower_lt_succ (f : Fin r → R) (i : ℕ) :
    koszulTatePower f i < koszulTatePower f (i + 1) :=
  (koszulTateProStage f i).lt

/-- The sequence of exponents is strictly monotone. -/
public theorem strictMono_koszulTatePower (f : Fin r → R) :
    StrictMono (koszulTatePower f) :=
  strictMono_nat_of_lt_succ (koszulTatePower_lt_succ f)

/-- The sequence of exponents is cofinal: every exponent is dominated by one of them. -/
public theorem le_koszulTatePower (f : Fin r → R) (k : ℕ) : k ≤ koszulTatePower f k :=
  (strictMono_koszulTatePower f).le_apply

end Existence

section Ladder

variable {f : Fin r → R} {m m' : ℕ}

/-- The transition map of the Tate system between two consecutive stages: the composite
`A' → K → A` through the Koszul algebra resolved by the lower stage. -/
public def KoszulTateStage.proTransition (t : KoszulTateStage f m') (s : KoszulTateStage f m) :
    t.A.carrier →ₐ[R] s.A.carrier :=
  s.up.comp t.down

/-- The upper square of the ladder: the Tate transition map precomposed with `K → A'` is the
Koszul transition map postcomposed with `K → A`. -/
public theorem KoszulTateStage.proTransition_up (t : KoszulTateStage f m')
    (s : KoszulTateStage f m) (x : ExteriorAlgebra R (Fin r → R)) :
    t.proTransition s (t.up x) = s.up (koszulPowerTransitionHom f t.topPower m' x) := by
  show s.up (t.down (t.up x)) = _
  rw [t.down_up]

/-- The lower square of the ladder: the Tate transition map postcomposed with `A → K` is the
Koszul transition map precomposed with `A' → K'`. -/
public theorem KoszulTateStage.down_proTransition (t : KoszulTateStage f m')
    (s : KoszulTateStage f m) (a : t.A.carrier) :
    s.down (t.proTransition s a) = koszulPowerTransitionHom f s.topPower m (t.down a) := by
  show s.down (s.up (t.down a)) = _
  rw [s.down_up]

/-- The Tate transition map preserves degrees. -/
public theorem KoszulTateStage.proTransition_grade (t : KoszulTateStage f m')
    (s : KoszulTateStage f m) (k : ℕ) (a : t.A.carrier) (ha : a ∈ t.A.grade k) :
    t.proTransition s a ∈ s.A.grade k :=
  s.up_grade k _ (t.down_grade k a ha)

/-- The Tate transition map between consecutive stages is a chain map. -/
public theorem KoszulTateStage.proTransition_d (t : KoszulTateStage f m')
    (s : KoszulTateStage f m) (h : m' = s.topPower) (a : t.A.carrier) :
    t.proTransition s (t.d a) = s.d (t.proTransition s a) := by
  subst h
  show s.up (t.down (t.d a)) = s.d (s.up (t.down a))
  rw [t.down_d, s.up_d]

/-- The Tate transition map preserves divided powers. -/
public theorem KoszulTateStage.proTransition_dpow (t : KoszulTateStage f m')
    (s : KoszulTateStage f m) (k : ℕ) (a : t.A.carrier)
    (ha : a ∈ positiveEvenPart t.A.grade) :
    t.proTransition s (t.A.gamma.dpow k a) = s.A.gamma.dpow k (t.proTransition s a) := by
  show s.up (t.down (t.A.gamma.dpow k a)) = s.A.gamma.dpow k (s.up (t.down a))
  rw [t.down_dpow k a ha,
    s.up_dpow k _ (algHom_mem_positiveEvenPart t.A.grade (exteriorGrade R (Fin r → R))
      t.down t.down_grade ha)]

end Ladder

section Main

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}

/-- **Tag 0GZ5.** Let `R` be a Noetherian ring and `f₁, …, f_r ∈ R`. Write `K_m` for the Koszul
divided power algebra of the `m`-th powers and `K_M → K_m` for its transition maps. Then there
is a sequence of exponents `1 = n₀ < n₁ < n₂ < ⋯`, cofinal in `ℕ`, and for each `i` maps
`K_{nᵢ₊₁} → Aᵢ → R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁})` and `Aᵢ → K_{nᵢ}` as in Tag 0GZ4, such that with
`Aᵢ₊₁ → Aᵢ` the composite `Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` the ladder commutes and the two inverse systems
`(K_n)` and `(Aᵢ)` are pro-isomorphic as differential graded `R`-algebras with compatible divided
powers: the composite `K_{nᵢ₊₁} → Aᵢ → K_{nᵢ}` is the Koszul transition map, and the composite
`Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` is the Tate transition map. -/
@[stacks 0GZ5]
public theorem exists_koszulTateProIso (f : Fin r → R) :
    ∃ (n : ℕ → ℕ) (stage : ∀ i : ℕ, KoszulTateStage f (n i)),
      n 0 = 1 ∧ StrictMono n ∧ (∀ k : ℕ, ∃ i : ℕ, k ≤ n i) ∧
      (∀ i : ℕ, (stage i).topPower = n (i + 1)) ∧
      -- the upper square of the ladder commutes
      (∀ (i : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        (stage (i + 1)).proTransition (stage i) ((stage (i + 1)).up x) =
          (stage i).up (koszulPowerTransitionHom f (n (i + 2)) (n (i + 1)) x)) ∧
      -- the lower square of the ladder commutes
      (∀ (i : ℕ) (a : (stage (i + 1)).A.carrier),
        (stage i).down ((stage (i + 1)).proTransition (stage i) a) =
          koszulPowerTransitionHom f (n (i + 1)) (n i) ((stage (i + 1)).down a)) ∧
      -- the composite `K_{nᵢ₊₁} → Aᵢ → K_{nᵢ}` is the transition map of the Koszul system
      (∀ (i : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        (stage i).down ((stage i).up x) =
          koszulPowerTransitionHom f (n (i + 1)) (n i) x) ∧
      -- the composite `Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` is the transition map of the Tate system
      (∀ i : ℕ, (stage (i + 1)).proTransition (stage i) =
        ((stage i).up).comp ((stage (i + 1)).down)) ∧
      -- the transition maps of the Tate system are maps of differential graded `R`-algebras
      -- with compatible divided powers
      (∀ (i k : ℕ) (a : (stage (i + 1)).A.carrier), a ∈ (stage (i + 1)).A.grade k →
        (stage (i + 1)).proTransition (stage i) a ∈ (stage i).A.grade k) ∧
      (∀ (i : ℕ) (a : (stage (i + 1)).A.carrier),
        (stage (i + 1)).proTransition (stage i) ((stage (i + 1)).d a) =
          (stage i).d ((stage (i + 1)).proTransition (stage i) a)) ∧
      (∀ (i k : ℕ) (a : (stage (i + 1)).A.carrier),
        a ∈ positiveEvenPart (stage (i + 1)).A.grade →
          (stage (i + 1)).proTransition (stage i) ((stage (i + 1)).A.gamma.dpow k a) =
            (stage i).A.gamma.dpow k ((stage (i + 1)).proTransition (stage i) a)) :=
  ⟨koszulTatePower f, koszulTateProStage f, koszulTatePower_zero f,
    strictMono_koszulTatePower f, fun k => ⟨k, le_koszulTatePower f k⟩,
    koszulTateProStage_topPower f,
    fun i x => (koszulTateProStage f (i + 1)).proTransition_up (koszulTateProStage f i) x,
    fun i a => (koszulTateProStage f (i + 1)).down_proTransition (koszulTateProStage f i) a,
    fun i x => (koszulTateProStage f i).down_up x,
    fun _ => rfl,
    fun i k a ha =>
      (koszulTateProStage f (i + 1)).proTransition_grade (koszulTateProStage f i) k a ha,
    fun i a =>
      (koszulTateProStage f (i + 1)).proTransition_d (koszulTateProStage f i) rfl a,
    fun i k a ha =>
      (koszulTateProStage f (i + 1)).proTransition_dpow (koszulTateProStage f i) k a ha⟩

end Main

end DividedPowers.TateResolution

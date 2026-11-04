module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.KoszulTateComparisonProregular
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.KoszulTateProSystem

/-! # The Koszul and Tate inverse systems of a weakly proregular sequence are pro-isomorphic

Let `R` be a ring and `f₁, …, f_r ∈ R` a weakly proregular sequence (Stacks 0H1E). Write `K_m` for
the Koszul divided power algebra `R⟨ξ₁, …, ξ_r⟩` with `ξᵢ` of degree one and `d(ξᵢ) = fᵢ^m`, and
`K_M → K_m` for the transition map `ξᵢ ↦ fᵢ^(M-m) ξᵢ`. Tag 0GZ5 is stated over a Noetherian ring,
where Tag 0GZ4 interpolates a degreewise finite Tate resolution between two Koszul algebras. For a
weakly proregular sequence
`DividedPowers.TateResolution.exists_tateResolution_koszulPowers_of_isWeaklyProregular` provides
the same interpolation, through a graded divided power polynomial algebra which need not be
finitely generated in each degree, and the construction of the pro-isomorphism goes through
unchanged: iterating it produces a sequence of exponents `1 = n₀ < n₁ < n₂ < ⋯` together with
divided power differential graded algebras `Aᵢ` and maps
`K_{nᵢ₊₁} → Aᵢ → R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁})` and `Aᵢ → K_{nᵢ}`, and with `Aᵢ₊₁ → Aᵢ` the
composite `Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` the ladder of Koszul algebras and Tate resolutions commutes and
exhibits the two inverse systems as pro-isomorphic.

## Main definitions

* `DividedPowers.TateResolution.KoszulTateFactorization` — one factorization of a Koszul
  transition map through a divided power differential graded resolution, as in Tag 0GZ4 but
  without finiteness in each degree.
* `DividedPowers.TateResolution.KoszulTateStage.toFactorization` — a stage of the Noetherian
  ladder, forgetting the finiteness.
* `DividedPowers.TateResolution.KoszulTateFactorization.proTransition` — the transition map of
  the Tate system.
* `DividedPowers.TateResolution.koszulTateFactorizationPower` and
  `DividedPowers.TateResolution.koszulTateFactorizationStage` — the sequence of exponents
  `1 = n₀ < n₁ < ⋯` and the factorization over each of them.

## Main results

* `DividedPowers.TateResolution.nonempty_koszulTateFactorization` — for a weakly proregular
  sequence every exponent is the bottom of a factorization.
* `DividedPowers.TateResolution.KoszulTateFactorization.proTransition_up` and
  `DividedPowers.TateResolution.KoszulTateFactorization.down_proTransition` — the two squares of
  the ladder commute.
* `DividedPowers.TateResolution.exists_koszulTateProIso_of_isWeaklyProregular` — Tag 0GZ5 for a
  weakly proregular sequence.

## References

* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
* [Stacks Project, Tag 0GZ5](https://stacks.math.columbia.edu/tag/0GZ5)
* [Stacks Project, Tag 0H1E](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

variable {R : Type u} [CommRing R] {r : ℕ}

/-- A factorization of the Koszul transition map `K_N → K_n`, for an exponent `N > n`, through a
divided power differential graded algebra `A` that is a graded divided power polynomial algebra
over `R` resolving `R/(f₁^N, …, f_r^N)`: maps `K_N → A → R/(f₁^N, …, f_r^N)` and `A → K_n`
compatible with the gradings, differentials, divided powers and augmentations. -/
public structure KoszulTateFactorization (f : Fin r → R) (n : ℕ) where
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
  /-- `A` is a graded divided power polynomial algebra over `R`. -/
  polynomial : Nonempty (GradedDividedPowerPolynomial A.grade A.gamma coeff)
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

/-- A stage of the Noetherian Koszul--Tate ladder is a factorization: forget that its polynomial
algebra has finitely many variables in each degree. -/
public def KoszulTateStage.toFactorization {f : Fin r → R} {n : ℕ} (s : KoszulTateStage f n) :
    KoszulTateFactorization f n where
  topPower := s.topPower
  lt := s.lt
  A := s.A
  d := s.d
  coeff := s.coeff
  aug := s.aug
  up := s.up
  down := s.down
  dga := s.dga
  compatible := s.compatible
  polynomial := let ⟨P, _⟩ := s.polynomial; ⟨P⟩
  coeff_injective := s.coeff_injective
  mem_grade_zero := s.mem_grade_zero
  aug_coeff := s.aug_coeff
  aug_surjective := s.aug_surjective
  aug_positive := s.aug_positive
  aug_d := s.aug_d
  exists_d_eq_of_aug_eq_zero := s.exists_d_eq_of_aug_eq_zero
  exists_d_eq_of_cycle := s.exists_d_eq_of_cycle
  up_grade := s.up_grade
  up_d := s.up_d
  up_dpow := s.up_dpow
  down_grade := s.down_grade
  down_d := s.down_d
  down_dpow := s.down_dpow
  aug_up := s.aug_up
  down_up := s.down_up
  down_coeff := s.down_coeff
  down_homology := s.down_homology

section Existence

/-- For a weakly proregular sequence every exponent `n` is the bottom of a factorization, that
is, the Koszul transition map out of some strictly larger exponent factors through a divided
power differential graded resolution. Tag 0GZ4 is applied to the exponent `n + 1`, which is at
least `1`, and the map down is composed with one more Koszul transition map. -/
public theorem nonempty_koszulTateFactorization (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) (n : ℕ) :
    Nonempty (KoszulTateFactorization f n) := by
  obtain ⟨N, hN, A, d, coeff, aug, up, down, hdga, hcompat, hpoly, hinj, hzero, haugc, haugs,
    haugp, haugd, hbd0, hbd, hupg, hupd, hupdp, hdng, hdnd, hdndp, haugup, hdnup, hdnc, _⟩ :=
    exists_tateResolution_koszulPowers_of_isWeaklyProregular f proregular (Nat.le_add_left 1 n)
  have hle : n ≤ n + 1 := Nat.le_succ n
  have hlt : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) hN
  set down' := (koszulPowerTransitionHom f (n + 1) n).comp down
  have hdng' : ∀ (k : ℕ) (a : A.carrier), a ∈ A.grade k →
      down' a ∈ exteriorGrade R (Fin r → R) k :=
    fun k a ha => koszulPowerTransitionHom_mem f (n + 1) n k (hdng k a ha)
  have hdnd' : ∀ a, down' (d a) = koszulPowerDifferential f n (down' a) := fun a =>
    (congrArg (koszulPowerTransitionHom f (n + 1) n) (hdnd a)).trans
      (koszulPowerTransitionHom_differential f hle (down a))
  have hdndp' : ∀ (k : ℕ) (a : A.carrier), a ∈ positiveEvenPart A.grade →
      down' (A.gamma.dpow k a) = (exteriorDividedPowerStructure R r).dpow k (down' a) :=
    fun k a ha => (congrArg (koszulPowerTransitionHom f (n + 1) n) (hdndp k a ha)).trans
      (koszulPowerTransitionHom_dpow f (n + 1) n k
        (algHom_mem_positiveEvenPart A.grade (exteriorGrade R (Fin r → R)) down hdng ha))
  have hdnup' : ∀ x, down' (up x) = koszulPowerTransitionHom f N n x := fun x =>
    (congrArg (koszulPowerTransitionHom f (n + 1) n) (hdnup x)).trans
      (koszulPowerTransitionHom_comp f hle hN x)
  have hdnc' : ∀ c : R, down' (coeff c) = algebraMap R (ExteriorAlgebra R (Fin r → R)) c :=
    fun c => (congrArg (koszulPowerTransitionHom f (n + 1) n) (hdnc c)).trans
      ((koszulPowerTransitionHom f (n + 1) n).commutes c)
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


/-- A factorization over the exponent `n`: one witness of the weakly proregular form of
Tag 0GZ4. -/
public noncomputable def koszulTateFactorizationOf (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) (n : ℕ) : KoszulTateFactorization f n :=
  (nonempty_koszulTateFactorization f proregular n).some

/-- The chain of factorizations, built by recursion on the index: the exponent of a factorization
is the exponent resolved by the previous one, starting from the exponent `1`. -/
public noncomputable def koszulTateFactorizationChain (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) : ℕ → (m : ℕ) × KoszulTateFactorization f m
  | 0 => ⟨1, koszulTateFactorizationOf f proregular 1⟩
  | i + 1 =>
    ⟨(koszulTateFactorizationChain f proregular i).2.topPower,
      koszulTateFactorizationOf f proregular
        (koszulTateFactorizationChain f proregular i).2.topPower⟩

/-- The sequence of exponents `1 = n₀ < n₁ < n₂ < ⋯` of the Koszul--Tate ladder of a weakly
proregular sequence. -/
public noncomputable def koszulTateFactorizationPower (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) (i : ℕ) : ℕ :=
  (koszulTateFactorizationChain f proregular i).1

/-- The factorization of the Koszul--Tate ladder over the exponent `nᵢ`; it resolves `nᵢ₊₁`. -/
public noncomputable def koszulTateFactorizationStage (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) (i : ℕ) :
    KoszulTateFactorization f (koszulTateFactorizationPower f proregular i) :=
  (koszulTateFactorizationChain f proregular i).2

/-- The sequence of exponents starts at `1`. -/
public theorem koszulTateFactorizationPower_zero (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) : koszulTateFactorizationPower f proregular 0 = 1 :=
  rfl

/-- The exponent resolved by the `i`-th factorization is the exponent of the next one. -/
public theorem koszulTateFactorizationStage_topPower (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) (i : ℕ) :
    (koszulTateFactorizationStage f proregular i).topPower =
      koszulTateFactorizationPower f proregular (i + 1) :=
  rfl

/-- The sequence of exponents is strictly increasing. -/
public theorem koszulTateFactorizationPower_lt_succ (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) (i : ℕ) :
    koszulTateFactorizationPower f proregular i <
      koszulTateFactorizationPower f proregular (i + 1) :=
  (koszulTateFactorizationStage f proregular i).lt

/-- The sequence of exponents is strictly monotone. -/
public theorem strictMono_koszulTateFactorizationPower (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) :
    StrictMono (koszulTateFactorizationPower f proregular) :=
  strictMono_nat_of_lt_succ (koszulTateFactorizationPower_lt_succ f proregular)

/-- The sequence of exponents is cofinal: every exponent is dominated by one of them. -/
public theorem le_koszulTateFactorizationPower (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) (k : ℕ) :
    k ≤ koszulTateFactorizationPower f proregular k :=
  (strictMono_koszulTateFactorizationPower f proregular).le_apply

end Existence

section Ladder

variable {f : Fin r → R} {m m' : ℕ}

/-- The transition map of the Tate system between two consecutive stages: the composite
`A' → K → A` through the Koszul algebra resolved by the lower stage. -/
public def KoszulTateFactorization.proTransition (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) :
    t.A.carrier →ₐ[R] s.A.carrier :=
  s.up.comp t.down

/-- The upper square of the ladder: the Tate transition map precomposed with `K → A'` is the
Koszul transition map postcomposed with `K → A`. -/
public theorem KoszulTateFactorization.proTransition_up (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (x : ExteriorAlgebra R (Fin r → R)) :
    t.proTransition s (t.up x) = s.up (koszulPowerTransitionHom f t.topPower m' x) :=
  congrArg s.up (t.down_up x)

/-- The lower square of the ladder: the Tate transition map postcomposed with `A → K` is the
Koszul transition map precomposed with `A' → K'`. -/
public theorem KoszulTateFactorization.down_proTransition (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (a : t.A.carrier) :
    s.down (t.proTransition s a) = koszulPowerTransitionHom f s.topPower m (t.down a) :=
  s.down_up (t.down a)

/-- The Tate transition map preserves degrees. -/
public theorem KoszulTateFactorization.proTransition_grade (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (k : ℕ) (a : t.A.carrier) (ha : a ∈ t.A.grade k) :
    t.proTransition s a ∈ s.A.grade k :=
  s.up_grade k _ (t.down_grade k a ha)

/-- The Tate transition map between consecutive stages is a chain map. -/
public theorem KoszulTateFactorization.proTransition_d (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (h : m' = s.topPower) (a : t.A.carrier) :
    t.proTransition s (t.d a) = s.d (t.proTransition s a) := by
  subst h
  show s.up (t.down (t.d a)) = s.d (s.up (t.down a))
  rw [t.down_d, s.up_d]

/-- The Tate transition map preserves divided powers. -/
public theorem KoszulTateFactorization.proTransition_dpow (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (k : ℕ) (a : t.A.carrier)
    (ha : a ∈ positiveEvenPart t.A.grade) :
    t.proTransition s (t.A.gamma.dpow k a) = s.A.gamma.dpow k (t.proTransition s a) := by
  show s.up (t.down (t.A.gamma.dpow k a)) = s.A.gamma.dpow k (s.up (t.down a))
  rw [t.down_dpow k a ha,
    s.up_dpow k _ (algHom_mem_positiveEvenPart t.A.grade (exteriorGrade R (Fin r → R))
      t.down t.down_grade ha)]

/-- Forgetting finiteness does not change the transition map of the Tate system. -/
public theorem KoszulTateStage.toFactorization_proTransition (t : KoszulTateStage f m')
    (s : KoszulTateStage f m) :
    t.toFactorization.proTransition s.toFactorization = t.proTransition s :=
  rfl

end Ladder

section Main

/-- **Tag 0GZ5 for a weakly proregular sequence.** Let `R` be a ring and let `f₁, …, f_r ∈ R` be
weakly proregular. Write `K_m` for the Koszul divided power algebra of the `m`-th powers and
`K_M → K_m` for its transition maps. Then there is a sequence of exponents `1 = n₀ < n₁ < n₂ < ⋯`,
cofinal in `ℕ`, and for each `i` maps `K_{nᵢ₊₁} → Aᵢ → R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁})` and
`Aᵢ → K_{nᵢ}` as in Tag 0GZ4, `Aᵢ` a graded divided power polynomial algebra over `R` resolving
`R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁})`, such that with `Aᵢ₊₁ → Aᵢ` the composite
`Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` the ladder commutes and the two inverse systems `(K_n)` and `(Aᵢ)` are
pro-isomorphic as differential graded `R`-algebras with compatible divided powers: the composite
`K_{nᵢ₊₁} → Aᵢ → K_{nᵢ}` is the Koszul transition map, and the composite
`Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` is the Tate transition map. -/
public theorem exists_koszulTateProIso_of_isWeaklyProregular (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) :
    ∃ (n : ℕ → ℕ) (stage : ∀ i : ℕ, KoszulTateFactorization f (n i)),
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
  ⟨koszulTateFactorizationPower f proregular, koszulTateFactorizationStage f proregular,
    koszulTateFactorizationPower_zero f proregular,
    strictMono_koszulTateFactorizationPower f proregular,
    fun k => ⟨k, le_koszulTateFactorizationPower f proregular k⟩,
    koszulTateFactorizationStage_topPower f proregular,
    fun i x => (koszulTateFactorizationStage f proregular (i + 1)).proTransition_up
      (koszulTateFactorizationStage f proregular i) x,
    fun i a => (koszulTateFactorizationStage f proregular (i + 1)).down_proTransition
      (koszulTateFactorizationStage f proregular i) a,
    fun i x => (koszulTateFactorizationStage f proregular i).down_up x,
    fun _ => rfl,
    fun i k a ha => (koszulTateFactorizationStage f proregular (i + 1)).proTransition_grade
      (koszulTateFactorizationStage f proregular i) k a ha,
    fun i a => (koszulTateFactorizationStage f proregular (i + 1)).proTransition_d
      (koszulTateFactorizationStage f proregular i) rfl a,
    fun i k a ha => (koszulTateFactorizationStage f proregular (i + 1)).proTransition_dpow
      (koszulTateFactorizationStage f proregular i) k a ha⟩

end Main

end DividedPowers.TateResolution

end

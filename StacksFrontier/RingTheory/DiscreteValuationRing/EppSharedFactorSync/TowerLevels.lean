module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.PrescribedFamily

/-!
# The levels of the family layer recursion

Mixed levels with terminal and carried members, prime-degree terminal layers, terminal bottom
layers, and the per-member trichotomy: carried, terminal, or splittable.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe u

section TowerFamily

open IsDiscreteValuationRing

/-- **A level of the recursion, mixed: one produced extension serves the terminal members and the
trivial ones at once.**

The proved consumer of `FamilyPrimeDegreeSolvable`, and the first place where the
producer form pays off at the *layer* level rather than the factor level.

Every member is assumed either trivial (`Module.finrank (L i) (M i) = 1`) or terminal in the sense
`FamilyPrimeDegreeSolvable` takes. O2's producer is applied to the **non-trivial sub-family only**,
and the trivial members are then *carried* against the `K₂` it returned — which is sound because at
a trivial member `A → C i` is already weakly unramified, and
`isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField` then makes **any** finite base
change a weak solution, that extension included.

So the two kinds are never solved separately and reconciled: one extension is produced, from bounds
over the whole terminal sub-family, and everything else is checked against it. Splitting the index
type is not the retracted `hmerge` — there is one resource here and partitioning indices does not
partition it. -/
theorem familyTowerSolvable_of_forall_terminal (p : ℕ) [Fact p.Prime]
    (hprime : FamilyPrimeDegreeSolvable.{u} p)
    (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)] [∀ i, Normal (L i) (M i)]
    (hepp : ∀ i, EppCondition A (B i) p)
    (halt : ∀ i, Module.finrank (L i) (M i) = 1 ∨
      (IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime)) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution := by
  classical
  obtain ⟨K₂, _, _, _, _, _, hsol⟩ :=
    hprime {i : ι // Module.finrank (L i) (M i) ≠ 1} A K (fun j => B j.1) (fun j => C j.1)
      (fun j => L j.1) (fun j => M j.1) (fun j => hweak j.1) (fun j => hepp j.1)
      (fun j => (halt j.1).resolve_left j.2)
  refine ⟨K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  by_cases h1 : Module.finrank (L i) (M i) = 1
  · exact ⟨canonicalBaseChange A (C i) K (M i) K₂,
      isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField A (C i) K (M i) K₂ _
        (isWeaklyUnramified_of_finrank_eq_one A (B i) (C i) K (L i) (M i) (hweak i) h1)⟩
  · exact hsol ⟨i, h1⟩

/-- Over a fraction field of `A`, a field `L` of the residue characteristic `p` of `A` has
characteristic zero or `p`. -/
private theorem charZero_or_charP_of_isFractionRing (A K L : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsFractionRing A K] [IsScalarTower A K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    CharZero L ∨ CharP L p :=
  charZero_or_charP_of_injective (algebraMap A L)
    (by rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K))
    (IsLocalRing.residue A) p

/-- **A normal layer of prime degree is terminal.**

The leaf of the four-branch reduction: for a normal `M / L` of prime degree `q`, the separable
closure is an intermediate field whose degree divides `q`, so it is `⊥` or `⊤`, and the two
cases are exactly the two disjuncts `Stacks.EppTheorem.FamilyPrimeDegreeSolvable` takes — purely
inseparable of degree `p`, or Galois of prime degree.

The work is in the first case, where the disjunct demands the degree be `p` and not merely prime.
`charP_of_finrank_eq_prime` reads `CharP L q` off the purely inseparable layer, and
`charZero_or_charP_of_injective` reads `CharZero L ∨ CharP L p` off the residue characteristic
of `A`; `p ∣ q` between two primes then forces `q = p`, the characteristic-zero alternative being
impossible because `(q : L) = 0` and `CharZero L` would make `q` zero. Note that this is where the
member's base field acquires a characteristic at all — `FamilyTowerSolvable` assumes one only of
`IsLocalRing.ResidueField A`. -/
theorem terminal_of_normal_of_finrank_prime
    (A K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra K L] [Algebra L M]
    [IsFractionRing A K] [IsScalarTower A K L]
    [Module.Finite L M] [Normal L M]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    {q : ℕ} (hq : q.Prime) (hdeg : Module.finrank L M = q) :
    IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
      IsGalois L M ∧ (Module.finrank L M).Prime := by
  classical
  have hmul := Module.finrank_mul_finrank L (separableClosure L M) M
  have hdvd : Module.finrank L (separableClosure L M) ∣ q :=
    ⟨Module.finrank (separableClosure L M) M, (hmul.trans hdeg).symm⟩
  rcases (hq.eq_one_or_self_of_dvd _ hdvd) with h1 | hqq
  · have hbot : separableClosure L M = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
    have hpi : IsPurelyInseparable L M := separableClosure.eq_bot_iff.mp hbot
    refine Or.inl ⟨hpi, ?_⟩
    have hcq : CharP L q := charP_of_finrank_eq_prime L M hq hdeg
    have hzero : ((q : ℕ) : L) = 0 := @CharP.cast_eq_zero L _ q hcq
    rcases charZero_or_charP_of_isFractionRing A K L p with hc | hc
    · let := hc
      rw [Nat.cast_eq_zero] at hzero
      exact absurd hzero hq.ne_zero
    · have hpq : p ∣ q := (@CharP.cast_eq_zero_iff L _ p hc q).mp hzero
      exact hdeg.trans
        (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp hpq).symm)
  · have h1 : Module.finrank (separableClosure L M) M = 1 := by
      have hx : Module.finrank L (separableClosure L M) *
          Module.finrank (separableClosure L M) M =
          Module.finrank L (separableClosure L M) * 1 := by
        rw [mul_one, hmul, hdeg, hqq]
      exact Nat.eq_of_mul_eq_mul_left (by rw [hqq]; exact hq.pos) hx
    have htop : separableClosure L M = ⊤ :=
      IntermediateField.finrank_eq_one_iff_eq_top.mp h1
    let : Algebra.IsSeparable L M := (separableClosure.eq_top_iff L M).mp htop
    exact Or.inr ⟨⟨⟩, hdeg ▸ hq⟩

/-- **A family every member of which is trivial or of prime degree is solved.**

The reduction composed with the mixed level: `terminal_of_normal_of_finrank_prime` turns each
prime-degree member into the terminal alternative, and `familyTowerSolvable_of_forall_terminal`
then runs O2's producer on the non-trivial sub-family and carries the trivial members against the
`K₂` it returns.

This is the first point at which an *arbitrary* member — one whose degree is only known to be
prime, with no terminal structure assumed — is reduced to what O2 solves. The general induction
needs the same reduction at composite degrees, which is a proper intermediate field and a recursion
rather than a case split, and is not here. -/
theorem familyTowerSolvable_of_forall_finrank_prime (p : ℕ) [Fact p.Prime]
    (hprime : FamilyPrimeDegreeSolvable.{u} p)
    (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)] [∀ i, Normal (L i) (M i)]
    (hepp : ∀ i, EppCondition A (B i) p)
    (hpr : ∀ i, Module.finrank (L i) (M i) = 1 ∨ (Module.finrank (L i) (M i)).Prime) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution := by
  refine familyTowerSolvable_of_forall_terminal p hprime ι A K B C L M hweak hepp ?_
  intro i
  rcases hpr i with h1 | hq
  · exact Or.inl h1
  · exact Or.inr (terminal_of_normal_of_finrank_prime A K (L i) (M i) p hq rfl)

/-- The degree bound of `FamilyTowerSolvable` is monotone: a proof at `n` serves every `m ≤ n`,
since the hypothesis `Module.finrank (L i) (M i) ≤ m` is then stronger. Used to start the strong
induction, where `familyTowerSolvable_one` covers `n = 0` as well as `n = 1`. -/
theorem familyTowerSolvable_mono (p : ℕ) [Fact p.Prime] {m n : ℕ} (hmn : m ≤ n)
    (h : FamilyTowerSolvable.{u} p n) : FamilyTowerSolvable.{u} p m := by
  intro ι _ A K B C L M
  intros
  rename_i hweak _ _ hepp hdegree
  exact h ι A K B C L M hweak hepp fun i => (hdegree i).trans hmn

/-- A nontrivial finite purely inseparable extension has a purely inseparable intermediate field
of degree `p`. -/
private theorem exists_isPurelyInseparable_finrank_eq (L M : Type u) [Field L] [Field M]
    [Algebra L M] [Module.Finite L M] [IsPurelyInseparable L M] (p : ℕ) [Fact p.Prime]
    [ExpChar L p] (h1 : 1 < Module.finrank L M) :
    ∃ E : IntermediateField L M, IsPurelyInseparable L E ∧ Module.finrank L E = p := by
  have hbot : (⊥ : IntermediateField L M) ≠ ⊤ := by
    intro hb
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one] at hb
    omega
  obtain ⟨y, -, hy⟩ :=
    IsDiscreteValuationRing.exists_intermediateField_finrank_eq_of_isPurelyInseparable L M p hbot
  exact ⟨IntermediateField.adjoin L {y}, IsPurelyInseparable.tower_bot L _ M, hy⟩

/-- **A terminal bottom layer, in the two branches whose splitting lemmas are field-theoretic.**

The first step of the layer assembly, for the two cases that need no
ring theory: a non-trivial extension that is purely inseparable, or Galois with solvable group, has
an intermediate field `E` such that `E / L` is **terminal** in the sense
`Stacks.EppTheorem.FamilyPrimeDegreeSolvable` takes, and `M / E` is of strictly smaller degree than
`M / L`.

The strict drop is not an extra hypothesis: `Module.finrank_mul_finrank` plus
`1 < Module.finrank L E` gives it, and both branches produce a bottom layer of degree at least two
— `p` in the inseparable case, a prime in the Galois one.

`ExpChar L p` is used only by the inseparable branch and is a hypothesis rather than derived: at a
member of `FamilyTowerSolvable` the base field carries no characteristic, only
`IsLocalRing.ResidueField A` does, and `charZero_or_charP_of_injective` is what a caller uses to
supply it — in the characteristic-zero alternative a purely inseparable extension is trivial and
this lemma is not reached. -/
theorem exists_terminal_bottomLayer (L M : Type u) [Field L] [Field M] [Algebra L M]
    [Module.Finite L M] (p : ℕ) [Fact p.Prime] [ExpChar L p]
    (h1 : 1 < Module.finrank L M)
    (hcase : IsPurelyInseparable L M ∨ (IsGalois L M ∧ Group.IsSolvable (M ≃ₐ[L] M))) :
    ∃ E : IntermediateField L M,
      (IsPurelyInseparable L E ∧ Module.finrank L E = p ∨
        IsGalois L E ∧ (Module.finrank L E).Prime) ∧
      Module.finrank E M < Module.finrank L M := by
  classical
  have hdrop : ∀ E : IntermediateField L M, 1 < Module.finrank L E →
      Module.finrank E M < Module.finrank L M := by
    intro E hE
    have hmul := Module.finrank_mul_finrank L E M
    have hpos : 0 < Module.finrank E M := Module.finrank_pos
    nlinarith
  rcases hcase with hpi | ⟨hgal, hsolv⟩
  · let := hpi
    obtain ⟨E, hEpi, hE⟩ := exists_isPurelyInseparable_finrank_eq L M p h1
    exact ⟨E, Or.inl ⟨hEpi, hE⟩, hdrop _ (by rw [hE]; exact (Fact.out : p.Prime).one_lt)⟩
  · let := hgal
    let := hsolv
    obtain ⟨E, hEgal, hEprime, -, hEdrop, -, -⟩ :=
      IsDiscreteValuationRing.exists_intermediateField_prime_finrank_of_isSolvable L M h1
    exact ⟨E, Or.inr ⟨hEgal, hEprime⟩, hEdrop⟩

/-- **The carried-member mechanism, at the shape the recursion's branches actually produce.**

`familyTowerSolvable_of_forall_terminal` takes the carried alternative as
`Module.finrank (L i) (M i) = 1`. Two of the recursion's four branches do not produce that: the
inertia branch, when the inertia group's fixed field is everything, concludes
`IsWeaklyUnramified A (C i)` with the degree unconstrained. So the hypothesis shape, not the
mechanism, was the restriction — `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField`
makes **any** finite base change a weak solution at a weakly unramified member, and the degree
plays no part in it.

This is that lemma with the first disjunct weakened to `IsWeaklyUnramified A (C i)`, which subsumes
the old one through `isWeaklyUnramified_of_finrank_eq_one`. Checked before writing the recursion,
because a carried mechanism that did not cover the inertia branch would have meant that branch
needed a second argument of its own inside the same theorem. It does cover it. -/
theorem familyTowerSolvable_of_forall_terminal_or_isWeaklyUnramified (p : ℕ) [Fact p.Prime]
    (hprime : FamilyPrimeDegreeSolvable.{u} p)
    (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)] [∀ i, Normal (L i) (M i)]
    (hepp : ∀ i, EppCondition A (B i) p)
    (halt : ∀ i, IsWeaklyUnramified A (C i) ∨
      (IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime)) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution := by
  classical
  obtain ⟨K₂, _, _, _, _, _, hsol⟩ :=
    hprime {i : ι // ¬ IsWeaklyUnramified A (C i)} A K (fun j => B j.1) (fun j => C j.1)
      (fun j => L j.1) (fun j => M j.1) (fun j => hweak j.1) (fun j => hepp j.1)
      (fun j => (halt j.1).resolve_left j.2)
  refine ⟨K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  by_cases hw : IsWeaklyUnramified A (C i)
  · exact ⟨canonicalBaseChange A (C i) K (M i) K₂,
      isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField A (C i) K (M i) K₂ _ hw⟩
  · exact hsol ⟨i, hw⟩

/-- **The per-member trichotomy of the layer recursion: carried, terminal, or splittable.**

For a member `A ⊆ B ⊆ C` over `K ⊆ L ⊆ M` with `M / L` finite and normal and `B / A` weakly
unramified, exactly one of three things is available:

* `IsWeaklyUnramified A C` — the member is **carried**, and is then solved over *any* finite
  extension of `K` by `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField`;
* `M / L` is **terminal** — purely inseparable of degree `p`, or Galois of prime degree — which is
  what `Stacks.EppTheorem.FamilyPrimeDegreeSolvable` consumes;
* there is a **proper normal intermediate field**, with both degrees `> 1` and hence both `<
  Module.finrank L M`, which is what the induction hypothesis consumes at two smaller degrees.

This is the branch analysis of Tag 09F8's `normalTowerSolvable` with the *solving* removed, and
removing it is what makes the statement separable from the rest of the recursion: nothing in the
conclusion mentions an integral closure, a weak-solution package, or a produced extension, so it
needs no `letI`-threaded existential bundle. One cannot
separate a *terminal bottom layer* instead, since that is **not** closed under its own
recursion; the third alternative here asks only for a proper normal intermediate field, and that
is.

Note what it does **not** need: no `hresidue`, no `IsAlgClosed`, no `PerfectField`, and no
cyclotomic parameter. Those are consumed by 09F8's solving steps, not by its case split, which is
why this holds over a merely perfect residue field — indeed over no hypothesis on the residue field
beyond the characteristic.

The proof is 09F8's, branch for branch: the degree-one case from
`ramificationIdx_dvd_finrank_of_isLocalRing`; the separable closure, being normal over `L`, is `⊥`
or `⊤` once there is no proper normal intermediate field; `⊥` gives purely inseparable of degree
`p`; `⊤` gives Galois, and then the fixed field of the inertia subgroup is normal
(`normal_inertia_maximalIdeal`), so it too is `⊥` or `⊤` — `⊥` makes the Galois group solvable
(`isSolvable_inertia`) and hence the degree prime, and `⊤` makes `B → C` formally unramified
(`formallyUnramified_integralClosure_fixedField_inertia`) and hence the member carried. -/
theorem isWeaklyUnramified_or_terminal_or_exists_properNormal (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharP (IsLocalRing.ResidueField A) p]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M] [Normal L M]
    (hweak : IsWeaklyUnramified A B) :
    IsWeaklyUnramified A C ∨
      (IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
        IsGalois L M ∧ (Module.finrank L M).Prime) ∨
      ∃ E : IntermediateField L M, Normal L E ∧
        1 < Module.finrank L E ∧ 1 < Module.finrank E M := by
  classical
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  let : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := isAdicComplete_of_finite B C
  -- the carried alternative, from weak unramifiedness of the upper step
  have hcarried (hBC : IsWeaklyUnramified B C) :
      IsWeaklyUnramified A C ∨
        (IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
          IsGalois L M ∧ (Module.finrank L M).Prime) ∨
        ∃ E : IntermediateField L M, Normal L E ∧
          1 < Module.finrank L E ∧ 1 < Module.finrank E M :=
    Or.inl (isWeaklyUnramified_trans A B C hweak hBC)
  by_cases h1 : Module.finrank L M = 1
  · refine hcarried ?_
    have hd := ramificationIdx_dvd_finrank_of_isLocalRing B C
    rw [← IsFractionRing.finrank_eq B L C M, h1] at hd
    exact (isWeaklyUnramified_iff_ramificationIdx_eq_one B C).mpr (Nat.dvd_one.mp hd)
  have hnontriv : 1 < Module.finrank L M := lt_of_le_of_ne Module.finrank_pos (Ne.symm h1)
  by_cases hproper : ∃ E : IntermediateField L M, Normal L E ∧ E ≠ ⊥ ∧ E ≠ ⊤
  · obtain ⟨E, hE, hbot, htop⟩ := hproper
    exact Or.inr (Or.inr ⟨E, hE,
      lt_of_le_of_ne Module.finrank_pos
        (Ne.symm fun h => hbot (IntermediateField.finrank_eq_one_iff.mp h)),
      lt_of_le_of_ne Module.finrank_pos
        (Ne.symm fun h => htop (IntermediateField.finrank_eq_one_iff_eq_top.mp h))⟩)
  have htriv (E : IntermediateField L M) [Normal L E] : E = ⊥ ∨ E = ⊤ := by
    by_contra h
    push Not at h
    exact hproper ⟨E, inferInstance, h⟩
  rcases htriv (separableClosure L M) with hsep | hsep
  · -- purely inseparable, and with no proper normal intermediate field the degree is `p`
    let : IsPurelyInseparable L M := separableClosure.eq_bot_iff.mp hsep
    have hchar : CharP L p := by
      rcases charZero_or_charP_of_isFractionRing A K L p with hc | hc
      · let := hc
        exact False.elim (h1 (Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
          (IsPurelyInseparable.bijective_algebraMap_of_isSeparable L M)))
      · exact hc
    let := hchar
    obtain ⟨E, hEpi, hE⟩ := exists_isPurelyInseparable_finrank_eq L M p hnontriv
    have hEtop : E = ⊤ := (htriv E).resolve_left fun h =>
      (Fact.out : p.Prime).ne_one (hE.symm.trans (IntermediateField.finrank_eq_one_iff.mpr h))
    have hdeg : Module.finrank L M = p := by
      have he : Module.finrank L E = Module.finrank L M := by rw [hEtop]; simp
      exact he.symm.trans hE
    exact Or.inr (Or.inl (Or.inl ⟨inferInstance, hdeg⟩))
  · -- Galois; split on the fixed field of the inertia subgroup, which is normal over `L`
    let : Algebra.IsSeparable L M := (separableClosure.eq_top_iff L M).mp hsep
    let : IsGalois L M := ⟨⟩
    let R := integralClosure B M
    let : IsDiscreteValuationRing R :=
      (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).1
    let := IsIntegralClosure.MulSemiringAction B L M R
    let P := IsLocalRing.maximalIdeal R
    let I := P.inertia Gal(M/L)
    let : I.Normal := normal_inertia_maximalIdeal Gal(M/L) R
    let E := IntermediateField.fixedField I
    rcases htriv E with hE | hE
    · -- the inertia group is everything, so the Galois group is solvable and the degree is prime
      have hI : I = ⊤ := by
        have h := IsGalois.fixedField_eq_iff_fixingSubgroup_eq.mp hE
        simpa only [IntermediateField.fixingSubgroup_bot] using h.symm
      let : CharP (IsLocalRing.ResidueField B) p := charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).injective p
      have hsolI : Group.IsSolvable I := isSolvable_inertia B L M p P
      rw [hI] at hsolI
      let := hsolI
      let : Group.IsSolvable Gal(M/L) := Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup Gal(M/L)) ≃* Gal(M/L)).toMonoidHom)
        Subgroup.topEquiv.surjective
      obtain ⟨E', hgal, hp, hcyc, -, -, -⟩ :=
        exists_intermediateField_prime_finrank_of_isSolvable L M hnontriv
      let := hgal
      have htopE : E' = ⊤ := (htriv E').resolve_left fun h =>
        hp.ne_one (IntermediateField.finrank_eq_one_iff.mpr h)
      have hp' : (Module.finrank L M).Prime := by
        have he := ((IntermediateField.equivOfEq htopE).trans
          (IntermediateField.topEquiv : (⊤ : IntermediateField L M) ≃ₐ[L]
            M)).toLinearEquiv.finrank_eq
        exact he ▸ hp
      exact Or.inr (Or.inl (Or.inr ⟨inferInstance, hp'⟩))
    · -- the inertia group is trivial, so `B → C` is formally unramified and the member is carried
      let eE : E ≃ₐ[L] M := (IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv
      let eR := (eE.restrictScalars B).mapIntegralClosure
      let : IsLocalRing (integralClosure B E) := eR.symm.toRingEquiv.isLocalRing
      let : Algebra.FormallyUnramified B (integralClosure B E) :=
        formallyUnramified_integralClosure_fixedField_inertia B L M inferInstance
      let : Algebra.FormallyUnramified B C := Algebra.FormallyUnramified.of_equiv
        (eR.trans (IsIntegralClosure.equiv B R M C))
      exact hcarried (isWeaklyUnramified_of_formallyUnramified B C)

end TowerFamily

end Stacks.EppTheorem

end

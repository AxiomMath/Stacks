module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.Sheaves.Flasque
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.QuasiCoherentPushforward.CharacterModuleInjective

/-!
# An injective module whose associated sheaf is not flasque

Let `k` be a field and let `A = k[x, y, z₀, z₁, …]/(xⁿ⁺¹ zₙ)`. The product `J = ∏_{n} A^∨`
of countably many copies of the character module of `A` is an injective `A`-module, and the
associated sheaf `J~` on `Spec A` is not flasque: the restriction map from `Spec A` to the
standard open `D(x)` is not surjective.

The witnessing section of `J~` over `D(x)` is `(χₙ)ₙ / x`, where `χₙ` is a character of `A`
not vanishing on `xⁿ zₙ`. Such a character exists because `xⁿ zₙ ≠ 0` in `A`, which is the
monomial computation `nonflasque_sectionExponent_not_relationDivides`. If the section came
from a global section `q`, then `xᴺ⁺¹ q = xᴺ (χ)` for some `N`, and comparing the `N`-th
coordinates against `z_N` gives `χ_N (xᴺ z_N) = 0`, a contradiction.

## Main results

* `Stacks.Examples.InjectiveTilde.exists_injective_tilde_not_flasque`: an injective module
  whose associated sheaf is not flasque exists.
* `Stacks.Examples.InjectiveTilde.exists_injective_tilde_basicOpen_restriction_not_surjective`:
  the failure is already witnessed by the restriction to a standard open.

## Implementation notes

The associated sheaf is viewed as a presheaf of abelian groups through
`AlgebraicGeometry.Scheme.Modules.presheaf`, and it is the underlying additive restriction map
that is tested for surjectivity. The coefficient field is pinned to `ULift ℚ` so that the ring
lives in the universe the `tilde` construction requires.

## References

* [Stacks Project, Tag 0274](https://stacks.math.columbia.edu/tag/0274)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Stacks.Examples.InjectiveTilde

universe u

/-- The relations `xⁿ⁺¹ zₙ = 0` in the polynomial ring `k[x, y, z₀, z₁, …]`, whose variables
are indexed by `Fin 2 ⊕ ℕ` with the two left indices standing for `x` and `y`. -/
noncomputable def nonflasqueRelations (k : Type u) [Field k] :
    Ideal (MvPolynomial (Fin 2 ⊕ ℕ) k) :=
  Ideal.span (Set.range fun n : ℕ =>
    MvPolynomial.X (Sum.inl (0 : Fin 2)) ^ (n + 1) * MvPolynomial.X (Sum.inr n))

/-- The ring `k[x, y, z₀, z₁, …]/(xⁿ⁺¹ zₙ)`. -/
abbrev nonflasqueRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2 ⊕ ℕ) k ⧸ nonflasqueRelations k

/-- The coordinate `x` of `k[x, y, z₀, z₁, …]/(xⁿ⁺¹ zₙ)`. -/
noncomputable def nonflasqueX (k : Type u) [Field k] : nonflasqueRing k :=
  Ideal.Quotient.mk (nonflasqueRelations k) (MvPolynomial.X (Sum.inl (0 : Fin 2)))

/-- The exponent vector of the relation monomial `xⁿ⁺¹ zₙ`. -/
private noncomputable def relationExponent (n : ℕ) : (Fin 2 ⊕ ℕ) →₀ ℕ :=
  Finsupp.single (Sum.inl (0 : Fin 2)) (n + 1) + Finsupp.single (Sum.inr n) 1

/-- The relation monomial `xⁿ⁺¹ zₙ`. -/
private noncomputable def relationMonomial (k : Type u) [Field k] (n : ℕ) :
    MvPolynomial (Fin 2 ⊕ ℕ) k :=
  MvPolynomial.X (Sum.inl (0 : Fin 2)) ^ (n + 1) * MvPolynomial.X (Sum.inr n)

/-- The relation monomial is the monomial with coefficient one on `relationExponent n`. -/
private theorem relationMonomial_eq (k : Type u) [Field k] (n : ℕ) :
    relationMonomial k n = MvPolynomial.monomial (relationExponent n) 1 := by
  unfold relationMonomial relationExponent
  rw [MvPolynomial.X_pow_eq_monomial]
  change (MvPolynomial.monomial (Finsupp.single (Sum.inl (0 : Fin 2)) (n + 1)) 1 *
    MvPolynomial.monomial (Finsupp.single (Sum.inr n) 1) 1) = _
  simp

/-- An exponent vector is divisible by a relation if it dominates some `relationExponent n`. -/
private def relationDivides (e : (Fin 2 ⊕ ℕ) →₀ ℕ) : Prop :=
  ∃ n : ℕ, relationExponent n ≤ e

/-- A polynomial is supported on the relations if every monomial in its support is divisible
by a relation monomial. -/
private def supportedOnRelations (k : Type u) [Field k]
    (p : MvPolynomial (Fin 2 ⊕ ℕ) k) : Prop :=
  ∀ e ∈ p.support, relationDivides e

/-- Every element of the relation ideal is supported on the relations: the ideal is generated
by monomials, so membership is detected monomial by monomial. -/
private theorem nonflasqueRelations_supported (k : Type u) [Field k]
    (p : MvPolynomial (Fin 2 ⊕ ℕ) k) (hp : p ∈ nonflasqueRelations k) :
    supportedOnRelations k p := by
  classical
  simp only [nonflasqueRelations] at hp
  change p ∈ Submodule.span (MvPolynomial (Fin 2 ⊕ ℕ) k)
    (Set.range (relationMonomial k)) at hp
  refine Submodule.span_induction (s := Set.range (relationMonomial k))
    (p := fun q _ => supportedOnRelations k q) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨n, rfl⟩ e he
    rw [relationMonomial_eq] at he
    exact ⟨n, (by simpa [MvPolynomial.support_monomial] using he) ▸ le_rfl⟩
  · simp [supportedOnRelations]
  · exact fun p q _ _ hp hq e he =>
      (Finset.mem_union.mp (MvPolynomial.support_add he)).elim (hp e) (hq e)
  · intro a p _ hp e he
    rcases Finset.mem_add.mp (MvPolynomial.support_mul a p he) with ⟨e₁, _, e₂, he₂, hsum⟩
    obtain ⟨n, hn⟩ := hp e₂ he₂
    exact ⟨n, hsum ▸ hn.trans le_add_self⟩

/-- The exponent vector of the monomial `xⁿ zₙ`, which just fails to be a relation. -/
private noncomputable def sectionExponent (n : ℕ) : (Fin 2 ⊕ ℕ) →₀ ℕ :=
  Finsupp.single (Sum.inl (0 : Fin 2)) n + Finsupp.single (Sum.inr n) 1

/-- The monomial `xⁿ zₙ` has `sectionExponent n` in its support. -/
private theorem sectionMonomial_mem_support (k : Type u) [Field k] (n : ℕ) :
    sectionExponent n ∈
      (MvPolynomial.X (Sum.inl (0 : Fin 2)) ^ n * MvPolynomial.X (Sum.inr n) :
        MvPolynomial (Fin 2 ⊕ ℕ) k).support := by
  rw [MvPolynomial.mem_support_iff]
  simp [sectionExponent, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_X_pow]

/-- No relation divides the exponent vector of `xⁿ zₙ`: the only candidate relation is the
`n`-th one, and it needs one more factor of `x`. -/
private theorem sectionExponent_not_relationDivides (n : ℕ) :
    ¬ relationDivides (sectionExponent n) := by
  rintro ⟨j, hj⟩
  by_cases h : j = n
  · subst j
    have hx := (Finsupp.le_def.mp hj) (Sum.inl (0 : Fin 2))
    simp [relationExponent, sectionExponent] at hx
  · have hz := (Finsupp.le_def.mp hj) (Sum.inr j)
    simp [relationExponent, sectionExponent, h] at hz

/-- The element `xⁿ zₙ` of `k[x, y, z₀, z₁, …]/(xⁿ⁺¹ zₙ)` is nonzero. -/
private theorem nonflasqueX_pow_mul_z_ne_zero (k : Type u) [Field k] (n : ℕ) :
    nonflasqueX k ^ n *
      Ideal.Quotient.mk (nonflasqueRelations k)
        (MvPolynomial.X (Sum.inr n) : MvPolynomial (Fin 2 ⊕ ℕ) k) ≠ 0 := by
  change Ideal.Quotient.mk (nonflasqueRelations k)
    ((MvPolynomial.X (Sum.inl (0 : Fin 2)) : MvPolynomial (Fin 2 ⊕ ℕ) k) ^ n *
      MvPolynomial.X (Sum.inr n)) ≠ 0
  exact fun h => sectionExponent_not_relationDivides n
    (nonflasqueRelations_supported k _ ((Ideal.Quotient.eq_zero_iff_mem).mp h)
      (sectionExponent n) (sectionMonomial_mem_support k n))

/-- Since `xⁿ zₙ` is nonzero, some character of the ring does not vanish on it. -/
private theorem diagonalCharacter_exists (k : Type u) [Field k] (n : ℕ) :
    ∃ χ : CharacterModule (nonflasqueRing k),
      χ (nonflasqueX k ^ n *
        Ideal.Quotient.mk (nonflasqueRelations k)
          (MvPolynomial.X (Sum.inr n) : MvPolynomial (Fin 2 ⊕ ℕ) k)) ≠ 0 := by
  by_contra! h
  exact nonflasqueX_pow_mul_z_ne_zero k n (CharacterModule.eq_zero_of_character_apply h)

/-- The injective module of the example: countably many copies of the character module of
`k[x, y, z₀, z₁, …]/(xⁿ⁺¹ zₙ)`. -/
private abbrev DiagonalProduct (k : Type u) [Field k] :=
  ∀ _ : ℕ, CharacterModule (nonflasqueRing k)

/-- The element of `DiagonalProduct k` whose `n`-th coordinate is a character not vanishing
on `xⁿ zₙ`. -/
private noncomputable def diagonalProduct (k : Type u) [Field k] : DiagonalProduct k :=
  fun n => Classical.choose (diagonalCharacter_exists k n)

/-- Rearranging a nested scalar multiplication of a difference. -/
private theorem smul_nested_sub {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    (a b : R) (m n : M) :
    a • (b • m - n) = (a * b) • m - a • n := by
  rw [smul_sub, ← mul_smul]

/-- Sections of `M~` over a standard open `D(x)` form the localization of `M` at `x`. This is
Mathlib's instance, named so that it can be supplied by hand where the ring and the module are
given by local definitions. -/
private theorem isLocalizedModule_away_toOpen (A : CommRingCat.{u}) (J : ModuleCat.{u} A)
    (x : A) : IsLocalizedModule.Away x (tilde.toOpen J (PrimeSpectrum.basicOpen x)).hom :=
  inferInstance

/-- Restricting from `Spec A` to the standard open `D(x)` is not surjective on the associated
sheaf of the product of character modules: the section `(χₙ)ₙ / x` is not the restriction of a
global section. -/
private theorem diagonalProduct_restriction_not_surjective (k : Type u) [Field k] :
    ¬ Function.Surjective
      ((tilde (ModuleCat.of (CommRingCat.of (nonflasqueRing k))
        (DiagonalProduct k))).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen (nonflasqueX k) ≤ ⊤)).op) := by
  classical
  let R := nonflasqueRing k
  let A : CommRingCat := CommRingCat.of R
  let J : ModuleCat A := ModuleCat.of A (DiagonalProduct k)
  let x : A := nonflasqueX k
  let U : (Spec A).Opens := PrimeSpectrum.basicOpen x
  let S := Submonoid.powers x
  have : IsLocalizedModule.Away x (tilde.toOpen J U).hom := isLocalizedModule_away_toOpen A J x
  let isoU := IsLocalizedModule.iso S (tilde.toOpen J U).hom
  let num : DiagonalProduct k := diagonalProduct k
  let den : S := ⟨x, Submonoid.mem_powers x⟩
  let sec := isoU (LocalizedModule.mk num den)
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj sec
  let q := (tilde.isoTop J).inv.hom t
  have htop : (tilde.toOpen J ⊤).hom q = t := Iso.inv_hom_id_apply (tilde.isoTop J) t
  have hlocal : (tilde.toOpen J U).hom q = sec :=
    (congrArg ((tilde J).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom htop).trans ht
  have hmk : LocalizedModule.mk q (1 : S) = LocalizedModule.mk num den :=
    isoU.injective (by simpa [sec, isoU] using hlocal)
  obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.mp hmk
  obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff _ _).mp v.property
  have hkill : (x ^ N) • (x • q - num) = 0 := by
    have hv' : (x ^ N * x) • q = x ^ N • num := by
      simpa [den, Submonoid.smul_def, one_smul, hN, mul_smul] using hv
    rw [smul_nested_sub, hv', sub_self]
  let z := Ideal.Quotient.mk (nonflasqueRelations k)
    (MvPolynomial.X (Sum.inr N) : MvPolynomial (Fin 2 ⊕ ℕ) k)
  have hrel : x ^ (N + 1) * z = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨N, rfl⟩)
  have harg : x • (x ^ N • z) = 0 := by
    simpa [x, smul_eq_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hrel
  have heval := DFunLike.congr_fun (congr_fun hkill N) z
  change q N (x • (x ^ N • z)) - (diagonalProduct k N) (x ^ N • z) = 0 at heval
  rw [harg, map_zero, zero_sub, neg_eq_zero] at heval
  exact Classical.choose_spec (diagonalCharacter_exists k N)
    (by simpa [z, smul_eq_mul, diagonalProduct] using heval)

/-- Over the spectrum of `ULift ℚ[x, y, z₀, z₁, …]/(xⁿ⁺¹ zₙ)`, the associated sheaf of the
injective module `∏ₙ A^∨` has a non-surjective restriction map to a standard open. -/
@[sga "6 II AppI.0.1" "partial"]
private theorem nonflasque_witness_with_basicOpen_failure :
    ∃ (A : CommRingCat.{u}) (J : ModuleCat.{u} A) (f : A),
      Injective J ∧
        ¬ Function.Surjective
          ((tilde J).presheaf.map
            (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op) := by
  let k := ULift.{u} ℚ
  let R := nonflasqueRing k
  exact ⟨CommRingCat.of R, ModuleCat.of R (DiagonalProduct k), nonflasqueX k,
    injective_pi_characterModule R ℕ, diagonalProduct_restriction_not_surjective k⟩

/-- **Stacks Project, Tag 0274.** An injective module can have a nonflasque associated sheaf
on its affine spectrum. -/
@[stacks 0274 "nonflasque associated sheaf",
  sga "6 II AppI.0.1" "not flasque",
  sga "6 II AppI.1.2" "Ĩ not flasque"]
theorem exists_injective_tilde_not_flasque :
    ∃ (A : CommRingCat) (J : ModuleCat A),
      Injective J ∧ ¬ TopCat.Presheaf.IsFlasque (tilde J).presheaf := by
  obtain ⟨A, J, f, hJ, hns⟩ := nonflasque_witness_with_basicOpen_failure
  exact ⟨A, J, hJ, fun hfl => hns ((AddCommGrpCat.epi_iff_surjective _).mp
    (hfl.epi (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op))⟩

/-- **Stacks Project, Tag 0274.** Even restriction to a standard open can fail to be
surjective for the associated sheaf of an injective module. -/
@[stacks 0274 "basic-open restriction not surjective",
  sga "6 II AppI.0.1" "not flasque (std open)",
  sga "6 II AppI.1.2" "Ĩ not flasque"]
theorem exists_injective_tilde_basicOpen_restriction_not_surjective :
    ∃ (A : CommRingCat) (J : ModuleCat A) (f : A),
      Injective J ∧
        ¬ Function.Surjective
          ((tilde J).presheaf.map
            (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op) :=
  nonflasque_witness_with_basicOpen_failure

end Stacks.Examples.InjectiveTilde

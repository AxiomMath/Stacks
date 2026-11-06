module

public import Mathlib.Order.Zorn
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealResidueFibre

/-!
# A maximal prime failing a property which spreads out over a closed subset

Let `A` be a commutative ring and let `Good` be a property of the prime ideals of `A`. Suppose
that whenever a prime `𝔭` is good there is a *finitely generated* ideal
`𝔞 ⊆ 𝔭 A_𝔭` such that every prime of `A_𝔭` containing `𝔞` is good — that is, goodness of a
prime spreads out over a closed subset of `Spec (A_𝔭)` cut out by finitely many equations.
Then every prime which is not good is dominated by a prime which is not good and all of whose
strict specializations are good.

## Main results

* `Ideal.isPrime_sSup_of_isChain`: the supremum of a nonempty chain of prime ideals is prime.
* `Ideal.exists_mem_le_map_of_fg_of_isChain`: a finitely generated ideal below the extension of
  the supremum of a nonempty chain of ideals lies below the extension of one member of the
  chain.
* `Stacks.BadPrime.exists_maximal_not_good`: a non-good prime is dominated by a non-good prime
  all of whose strict specializations are good.
* `Stacks.BadPrime.forall_good`: consequently, if in addition a prime all of whose strict
  specializations are good is itself good, then every prime is good.
* `AlgebraicGeometry.rTensor_residueField_injective_of_spreadout_of_step`: for a map `u : N → M`
  injective modulo the maximal ideal, `u ⊗ id_{κ(𝔭)}` is injective at every prime `𝔭` as soon as
  this injectivity spreads out and passes from the strict specializations of a prime to the prime.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT7](https://stacks.math.columbia.edu/tag/0AT7)
* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace Ideal

variable {A : Type u₁} [CommRing A]

/-- The supremum of a nonempty chain of prime ideals is prime. -/
theorem isPrime_sSup_of_isChain {C : Set (Ideal A)} (hne : C.Nonempty)
    (hchain : IsChain (· ≤ ·) C) (hprime : ∀ p ∈ C, p.IsPrime) : (sSup C).IsPrime := by
  have hmem : ∀ x : A, x ∈ sSup C ↔ ∃ p ∈ C, x ∈ p := fun _ =>
    Submodule.mem_sSup_of_directed hne hchain.directedOn
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨p, hp, h1⟩ := (hmem 1).mp (htop ▸ Submodule.mem_top)
    exact (hprime p hp).ne_top ((Ideal.eq_top_iff_one p).mpr h1)
  · obtain ⟨p, hp, hmul⟩ := (hmem (x * y)).mp hxy
    rcases (hprime p hp).mem_or_mem hmul with h | h
    · exact Or.inl ((hmem x).mpr ⟨p, hp, h⟩)
    · exact Or.inr ((hmem y).mpr ⟨p, hp, h⟩)

/-- A finitely generated ideal below the extension of the supremum of a nonempty chain of ideals
already lies below the extension of one member of the chain. -/
theorem exists_mem_le_map_of_fg_of_isChain {C : Set (Ideal A)} (hne : C.Nonempty)
    (hchain : IsChain (· ≤ ·) C) {B : Type u₂} [CommRing B] (f : A →+* B) {a : Ideal B}
    (hfg : a.FG) (hle : a ≤ (sSup C).map f) : ∃ p ∈ C, a ≤ p.map f := by
  have hdir : DirectedOn (· ≤ ·) ((fun p : Ideal A => p.map f) '' C) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rcases hchain.total hp hq with h | h
    · exact ⟨q.map f, ⟨q, hq, rfl⟩, Ideal.map_mono h, le_rfl⟩
    · exact ⟨p.map f, ⟨p, hp, rfl⟩, le_rfl, Ideal.map_mono h⟩
  rw [Ideal.map_sSup, ← sSup_image] at hle
  obtain ⟨_, ⟨p, hp, rfl⟩, hab⟩ :=
    (isCompactElement_iff_le_of_directed_sSup_le a).mp
      ((Submodule.fg_iff_compact a).mp hfg) _ (hne.image _) hdir hle
  exact ⟨p, hp, hab⟩

end Ideal

namespace Stacks.BadPrime

variable {A : Type u₁} [CommRing A]

/-- Let `Good` be a property of the primes of `A` which *spreads out*: whenever `𝔭` is good there
is a finitely generated ideal `𝔞 ⊆ 𝔭 A_𝔭` such that every prime `𝔮 ⊆ 𝔭` of `A` with
`𝔞 ⊆ 𝔮 A_𝔭` is good. Then every prime which is not good is contained in a prime which is not
good and all of whose strict specializations are good. -/
theorem exists_maximal_not_good (Good : ∀ p : Ideal A, p.IsPrime → Prop)
    (hspread : ∀ (p : Ideal A) [hp : p.IsPrime], Good p hp →
      ∃ a : Ideal (Localization.AtPrime p), a.FG ∧
        a ≤ p.map (algebraMap A (Localization.AtPrime p)) ∧
        ∀ (q : Ideal A) [hq : q.IsPrime], q ≤ p →
          a ≤ q.map (algebraMap A (Localization.AtPrime p)) → Good q hq)
    {p₀ : Ideal A} (hp₀ : p₀.IsPrime) (hbad : ¬ Good p₀ hp₀) :
    ∃ (p : Ideal A) (hp : p.IsPrime), ¬ Good p hp ∧ p₀ ≤ p ∧
      ∀ (q : Ideal A) [hq : q.IsPrime], p < q → Good q hq := by
  classical
  set S : Set (Ideal A) := {p | ∃ hp : p.IsPrime, ¬ Good p hp}
  have hub : ∀ C ⊆ S, IsChain (· ≤ ·) C → ∀ y ∈ C, ∃ ub ∈ S, ∀ z ∈ C, z ≤ ub := by
    intro C hCS hchain y hy
    have hne : C.Nonempty := ⟨y, hy⟩
    have hprime : ∀ p ∈ C, p.IsPrime := fun p hp => (hCS hp).choose
    have hsup : (sSup C).IsPrime := Ideal.isPrime_sSup_of_isChain hne hchain hprime
    refine ⟨sSup C, ⟨hsup, fun hgood => ?_⟩, fun z hz => le_sSup hz⟩
    obtain ⟨a, hfg, hale, hVa⟩ := hspread (sSup C) (hp := hsup) hgood
    obtain ⟨p, hp, hap⟩ :=
      Ideal.exists_mem_le_map_of_fg_of_isChain hne hchain
        (algebraMap A (Localization.AtPrime (sSup C))) hfg hale
    exact (hCS hp).choose_spec (hVa p (hq := hprime p hp) (le_sSup hp) hap)
  obtain ⟨m, hp₀m, hmem, hmax⟩ := zorn_le_nonempty₀ S hub p₀ ⟨hp₀, hbad⟩
  refine ⟨m, hmem.choose, hmem.choose_spec, hp₀m, fun q hq hlt => ?_⟩
  by_contra hqbad
  exact not_le_of_gt hlt (hmax ⟨hq, hqbad⟩ hlt.le)

/-- If `Good` spreads out as in `Stacks.BadPrime.exists_maximal_not_good`, and if moreover a prime
all of whose strict specializations are good is itself good, then every prime is good. -/
theorem forall_good (Good : ∀ p : Ideal A, p.IsPrime → Prop)
    (hspread : ∀ (p : Ideal A) [hp : p.IsPrime], Good p hp →
      ∃ a : Ideal (Localization.AtPrime p), a.FG ∧
        a ≤ p.map (algebraMap A (Localization.AtPrime p)) ∧
        ∀ (q : Ideal A) [hq : q.IsPrime], q ≤ p →
          a ≤ q.map (algebraMap A (Localization.AtPrime p)) → Good q hq)
    (hstep : ∀ (p : Ideal A) [hp : p.IsPrime],
      (∀ (q : Ideal A) [hq : q.IsPrime], p < q → Good q hq) → Good p hp)
    (p : Ideal A) [hp : p.IsPrime] : Good p hp := by
  by_contra hbad
  obtain ⟨m, hm, hmbad, -, hmmax⟩ := exists_maximal_not_good Good hspread hp hbad
  exact hmbad (hstep m (hp := hm) hmmax)

end Stacks.BadPrime

namespace AlgebraicGeometry

open Stacks.BadPrime

/-- Let `A → B` be a local homomorphism of local rings essentially of finite type, `M` a flat
`A`-module, `N` a finite `B`-module and `u : N → M` an `A`-linear map injective modulo the
maximal ideal of `A`. Say that a prime `𝔭` of `A` is *good* if `u ⊗ id_{κ(𝔭)}` is injective.
Then every prime is good as soon as

* goodness spreads out: a good `𝔭` admits a finitely generated ideal `𝔞 ⊆ 𝔭 A_𝔭` with every
  prime of `A_𝔭` containing `𝔞` good; and
* a prime all of whose strict specializations are good is good. -/
theorem rTensor_residueField_injective_of_spreadout_of_step
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hspread : ∀ (p : Ideal S.A) [p.IsPrime],
      Function.Injective (S.u.rTensor p.ResidueField) →
        ∃ a : Ideal (Localization.AtPrime p), a.FG ∧
          a ≤ p.map (algebraMap S.A (Localization.AtPrime p)) ∧
          ∀ (q : Ideal S.A) [q.IsPrime], q ≤ p →
            a ≤ q.map (algebraMap S.A (Localization.AtPrime p)) →
              Function.Injective (S.u.rTensor q.ResidueField))
    (hstep : ∀ (p : Ideal S.A) [p.IsPrime],
      (∀ (q : Ideal S.A) [q.IsPrime], p < q →
        Function.Injective (S.u.rTensor q.ResidueField)) →
          Function.Injective (S.u.rTensor p.ResidueField))
    (p : Ideal S.A) [p.IsPrime] : Function.Injective (S.u.rTensor p.ResidueField) :=
  forall_good (fun q hq => Function.Injective (S.u.rTensor (@Ideal.ResidueField S.A _ q hq)))
    (fun q _ => hspread q) (fun q _ => hstep q) p

end AlgebraicGeometry

end

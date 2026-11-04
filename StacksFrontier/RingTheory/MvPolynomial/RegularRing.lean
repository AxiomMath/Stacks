module

public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.RingTheory.MvPolynomial.MaximalIdeal
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# A polynomial algebra over a field is regular of global dimension the number of variables

Let `k` be a field and let `ι` be a finite index type, `n = Nat.card ι`. This file proves
Stacks 00OQ: the polynomial algebra `k[x_i : i ∈ ι]` is a regular ring, its global dimension is
`n`, and every localization of `k[x_i : i ∈ ι]` at a maximal ideal is a regular local ring of
dimension `n`.

The argument is the source's. By Lemma 00OP every localization of `k[x_i : i ∈ ι]` at a maximal
ideal is a regular local ring of dimension exactly `n`; a Noetherian ring with that property is
regular of global dimension `n`, by the equivalence of items (3), (2) and (1) of Lemma 00OE.

## Main results

* `Stacks.PolynomialRing.GlobalDimension.solution`: the three assertions of Stacks 00OQ.

## Implementation notes

The uniform dimension `n` at every maximal ideal is stronger than item (3) of Lemma 00OE, which
asks for the bound `≤ n` together with one maximal ideal attaining it; the private lemma
`isRegularRing_and_iSup_projectiveDimension_eq_of_forall_isMaximal` records the resulting form of
Lemma 00OE, for an arbitrary Noetherian ring and an arbitrary `n`, since the existential is then
witnessed by any maximal ideal at all. It is where Lemma 00OE enters, and the rest of the file
supplies its hypothesis.

Lemma 00OP is used through the library file
`StacksFrontier/RingTheory/MvPolynomial/MaximalIdeal.lean`
(`isRegularLocalRing_localization_atPrime`, `ringKrullDim_localization_atPrime_eq`), which states
it for the concrete `Localization.AtPrime 𝔪` of `k[x_1, …, x_n]`, whereas 00OQ is indexed by an
arbitrary finite `ι` and quantifies over an arbitrary localization `A` of `k[x_i : i ∈ ι]` at `𝔪`.
The private lemma `isRegularLocalRing_and_ringKrullDim_eq_of_isLocalization_atPrime` bridges both
gaps at once, transporting the two conclusions along the ring equivalence
`IsLocalization.ringEquivOfRingEquiv` induced by the renaming `MvPolynomial.renameEquiv` of the
variables along `ι ≃ Fin (Nat.card ι)`; it is at once the third assertion of 00OQ and, read at
`A = Localization.AtPrime 𝔪`, the hypothesis of the previous paragraph.

## References

* [StacksProject 00OQ](https://stacks.math.columbia.edu/tag/00OQ)
-/

@[expose] public section



open CategoryTheory

namespace Stacks.PolynomialRing.GlobalDimension

/-- **Lemma 00OP for an arbitrary index type and an arbitrary model of the localization.** Any
localization `A` of `k[x_i : i ∈ ι]` at a maximal ideal `𝔪` is a regular local ring of Krull
dimension the number of variables. Lemma 00OP is stated for the concrete `Localization.AtPrime`
of `k[x_1, …, x_n]`, so the variables are first renamed along `ι ≃ Fin (Nat.card ι)` by
`MvPolynomial.renameEquiv`, and `IsLocalization.ringEquivOfRingEquiv` turns that renaming into a
ring equivalence between `Localization.AtPrime (𝔪.comap …)` and `A` — one equivalence absorbing
both the change of index type and the change of model. `IsRegularLocalRing` transports along it by
`IsRegularLocalRing.of_ringEquiv` and `ringKrullDim` by `ringKrullDim_eq_of_ringEquiv`. -/
private theorem isRegularLocalRing_and_ringKrullDim_eq_of_isLocalization_atPrime
    {k : Type u} [Field k] {ι : Type v} [Finite ι] (𝔪 : Ideal (MvPolynomial ι k)) [𝔪.IsMaximal]
    (A : Type w) [CommRing A] [Algebra (MvPolynomial ι k) A] [IsLocalization.AtPrime A 𝔪] :
    IsRegularLocalRing A ∧ ringKrullDim A = (Nat.card ι : WithBot ℕ∞) :=
  have E : MvPolynomial (Fin (Nat.card ι)) k ≃+* MvPolynomial ι k :=
    (MvPolynomial.renameEquiv k (Finite.equivFin ι).symm).toRingEquiv
  have hm : (𝔪.comap E).IsMaximal := inferInstance
  have : (𝔪.comap E).IsPrime := hm.isPrime
  have e := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (𝔪.comap E)) A E (E.map_primeCompl_comap_eq 𝔪)
  have : IsRegularLocalRing (Localization.AtPrime (𝔪.comap E)) :=
    isRegularLocalRing_localization_atPrime (Nat.card ι) (𝔪.comap E) hm
  ⟨.of_ringEquiv e,
    (ringKrullDim_eq_of_ringEquiv e).symm.trans
      (ringKrullDim_localization_atPrime_eq (Nat.card ι) (𝔪.comap E) hm)⟩

/-- **A Noetherian ring all of whose localizations at maximal ideals are regular local of the same
dimension `n` is regular of global dimension `n`.** This is Lemma 00OE for a ring whose
localizations have uniform dimension: the hypothesis gives both halves of item (3) at once, the
bound `≤ n` at every maximal ideal and a maximal ideal attaining it — any one will do, and one
exists because `R` is nontrivial — and items (2) and (1) are the conclusion. -/
@[ega "III 6.5.5" "partial"]
private theorem isRegularRing_and_iSup_projectiveDimension_eq_of_forall_isMaximal
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R] (n : ℕ)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], IsRegularLocalRing (Localization.AtPrime 𝔪) ∧
      ringKrullDim (Localization.AtPrime 𝔪) = (n : WithBot ℕ∞)) :
    IsRegularRing R ∧ (⨆ M : ModuleCat.{u} R, projectiveDimension M) = (n : WithBot ℕ∞) := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  have h3 : (∀ 𝔫 : Ideal R, ∀ _ : 𝔫.IsMaximal, IsRegularLocalRing (Localization.AtPrime 𝔫) ∧
        ringKrullDim (Localization.AtPrime 𝔫) ≤ (n : WithBot ℕ∞)) ∧
      ∃ 𝔫 : Ideal R, ∃ _ : 𝔫.IsMaximal,
        ringKrullDim (Localization.AtPrime 𝔫) = (n : WithBot ℕ∞) :=
    ⟨fun 𝔫 _ => ⟨(h 𝔫).1, (h 𝔫).2.le⟩, 𝔪, h𝔪, (h 𝔪).2⟩
  have tfae := isRegularRing_tfae (R := R) n
  have h2 := (tfae.out 3 2).mp h3
  exact ⟨h2.1, (tfae.out 3 1).mp h3⟩

/-- **Stacks 00OQ.** The polynomial algebra `k[x_i : i ∈ ι]` over a field `k` in finitely many
variables is a regular ring of global dimension `n = Nat.card ι`, and each of its localizations at
a maximal ideal is a regular local ring of Krull dimension `n`. -/
public theorem solution (k : Type u) [Field k] (ι : Type v) [Finite ι] :
    IsRegularRing (MvPolynomial ι k) ∧
      (⨆ M : ModuleCat.{max u v} (MvPolynomial ι k), projectiveDimension M) =
        (Nat.card ι : WithBot ℕ∞) ∧
      ∀ (𝔪 : Ideal (MvPolynomial ι k)) [𝔪.IsMaximal] (A : Type w) [CommRing A]
          [Algebra (MvPolynomial ι k) A] [IsLocalization.AtPrime A 𝔪],
        IsRegularLocalRing A ∧ ringKrullDim A = (Nat.card ι : WithBot ℕ∞) :=
  have h := isRegularRing_and_iSup_projectiveDimension_eq_of_forall_isMaximal
    (R := MvPolynomial ι k) (Nat.card ι)
    fun 𝔪 => isRegularLocalRing_and_ringKrullDim_eq_of_isLocalization_atPrime 𝔪 _
  ⟨h.1, h.2, fun 𝔪 _ A _ _ _ =>
    isRegularLocalRing_and_ringKrullDim_eq_of_isLocalization_atPrime 𝔪 A⟩

end Stacks.PolynomialRing.GlobalDimension

end

/-!
# A polynomial algebra over a field is regular of global dimension the number of variables

Let `k` be a field and let `ι` be a finite set of variables, `n = #ι`. Then the polynomial
algebra `k[ι]` is a regular ring, its global dimension is `n`, and for every maximal ideal `𝔪`
of `k[ι]` the localization `k[ι]_𝔪` is a regular local ring of dimension `n`.

The last assertion is Lemma 00OP: by the Hilbert Nullstellensatz the residue field at a maximal
ideal is finite over `k`, which produces `n` elements generating `𝔪`, while `dim k[ι]_𝔪 = n`
because `dim k[ι] = n` and `𝔪` is maximal; a local ring whose maximal ideal is generated by
`dim`-many elements is regular local. Regularity of `k[ι]` at every prime, and hence the value of
the global dimension, then follows from Lemma 00OE, which reads the global dimension of a
Noetherian ring off the dimensions of its localizations at maximal ideals.

## Main results

* `MvPolynomial.isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization`:
  the three assertions of the source, for `k[ι]` with `ι` finite.

## Implementation notes

Mathlib has no predicate or numerical invariant for the global dimension of a ring. Since the
source asserts the *value* `n` and not merely the bound `≤ n`, the global dimension is spelled as
the supremum `⨆ M : ModuleCat.{max u v} k[ι], projectiveDimension M` of the projective dimensions
of all modules, taken in `WithBot ℕ∞` (`CategoryTheory.projectiveDimension`, whose value at a
zero object is `⊥`). This is the definition of the global dimension in Definition 00O6, and it is
sharper than the form `∀ M, HasProjectiveDimensionLE M n` in which the neighbouring tags 00O7 and
00O9 state a bound. Modules are quantified in the universe of the ring; by Lemma 065T a bound on
the projective dimensions of the cyclic modules already bounds them all, so the supremum does not
depend on the universe it is read in.

Following the source's `n` variables by an arbitrary finite index type `ι`, with `n = Nat.card ι`,
costs nothing and matches the shape of `MvPolynomial.ringKrullDim_of_isNoetherianRing`; the
source's `k[x_1, …, x_n]` is `ι = Fin n`.

The localization at `𝔪` is an abstract `IsLocalization.AtPrime A 𝔪` rather than the concrete
`Localization.AtPrime 𝔪`, so that a reader holding any other model of `k[ι]_𝔪` applies the lemma
without transporting along `IsLocalization.algEquiv`; the concrete family is one instantiation.
For the same reason `A` is allowed its own universe.

The first conjunct is already Mathlib's instance `MvPolynomial.isRegularRing_of_isRegularRing`,
and `IsRegularLocalRing A` for `A = Localization.AtPrime 𝔪` is then
`IsRegularRing.isRegularLocalRing_localization`; the mathematical content of the tag that Mathlib
does not have is the value of the global dimension and the dimension of the localizations. All
three assertions are carried by one theorem, since none of them is an instance of another.

Faithfulness. (1) No hypothesis is dead: `Field k` is used by all three conjuncts — over a
Noetherian regular base of positive dimension the localizations at maximal ideals of `k[ι]` no
longer all have dimension `Nat.card ι`, and `Finite ι` is used by each, the global dimension of
`k[ι]` being infinite for infinite `ι`. (2) The scalars and base are the source's: the ring is
`MvPolynomial ι k` itself, the projective dimensions are computed in `ModuleCat (MvPolynomial ι k)`
and the Krull dimension is that of the localization of `MvPolynomial ι k`; no base change occurs.
(3) The map the source names is pinned: `IsLocalization.AtPrime A 𝔪` pins `A` as the localization
of `MvPolynomial ι k` at the complement of `𝔪` through the canonical `algebraMap`, rather than
positing the existence of some regular local ring of dimension `n`. (4) The instantiation is not
degenerate: for `k = ℚ`, `ι = Fin 2` and `𝔪 = (x, y)` the conclusion says that `ℚ[x, y]` is
regular of global dimension `2` — witnessed by the residue field `ℚ[x, y]/(x, y)`, whose
projective dimension is `2` — and that `ℚ[x, y]_(x, y)` is regular local of dimension `2`. For
`ι` empty the ring is `k` itself and the global dimension is `0`, so no conjunct is vacuous.

## References

* [StacksProject 00OQ](https://stacks.math.columbia.edu/tag/00OQ)

## Tags

polynomial ring, regular ring, regular local ring, global dimension, projective dimension,
Krull dimension, maximal ideal, localization
-/

@[expose] public section



namespace MvPolynomial

open CategoryTheory in
/-- **Stacks 00OQ.** A polynomial algebra `k[ι]` in finitely many variables over a field is a
regular ring; its global dimension, the supremum of the projective dimensions of its modules, is
the number `Nat.card ι` of variables; and every localization of `k[ι]` at a maximal ideal is a
regular local ring of dimension `Nat.card ι`. -/
@[stacks 00OQ "The number of variables is `Nat.card ι` for an arbitrary finite index type `ι`,
the global dimension is the supremum of the projective dimensions of all modules (Mathlib has no
name for it), and the localization at a maximal ideal is an abstract `IsLocalization.AtPrime`.
See the module docstring.", sga "6 VI 1.5.2" "more general"]
public theorem isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization
    (k : Type u) [Field k] (ι : Type v) [Finite ι] :
    IsRegularRing (MvPolynomial ι k) ∧
      (⨆ M : ModuleCat.{max u v} (MvPolynomial ι k), projectiveDimension M) =
        (Nat.card ι : WithBot ℕ∞) ∧
      ∀ (𝔪 : Ideal (MvPolynomial ι k)) [𝔪.IsMaximal] (A : Type w) [CommRing A]
          [Algebra (MvPolynomial ι k) A] [IsLocalization.AtPrime A 𝔪],
        IsRegularLocalRing A ∧ ringKrullDim A = (Nat.card ι : WithBot ℕ∞) :=
  Stacks.PolynomialRing.GlobalDimension.solution k ι

end MvPolynomial

end

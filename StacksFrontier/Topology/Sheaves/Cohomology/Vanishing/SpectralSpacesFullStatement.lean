module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSupportVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological dimension of a spectral space: the three clauses together

Let `X` be a spectral space of Krull dimension `d` and let `F` be an abelian sheaf on `X`. Then

1. `H^q(X, F) = 0` for `q > d`;
2. `H^d(X, F) ⟶ H^d(U, F)` is surjective for every quasi-compact open `U ⊆ X`;
3. `H^q_Z(X, F) = 0` for `q > d` and every constructible closed `Z ⊆ X`.

The three clauses are proved separately in
`StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSpaces.lean` (clauses (1) and (2)) and
`StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSupportVanishing.lean` (clause (3)),
each under the weaker hypothesis that `d` only bounds the dimension. This file states the
proposition as one theorem, with the three clauses conjoined and under the source's own
hypothesis that the dimension *equals* `d`, and certifies that the hypotheses and the data the
conclusion quantifies over have inhabitants which are not degenerate.

## Main results

* `Stacks.CohomologyVanishing`
  `.subsingleton_sheafH_and_surjective_and_subsingleton_supported_of_topologicalKrullDim_eq`:
  the whole proposition — all three clauses, under exactly the source's hypotheses.
* `Stacks.CohomologyVanishing.nontrivial_sheafH_zero_skyscraperInt`: the cohomology the
  proposition speaks about is not identically zero. On `Spec ℤ` the skyscraper sheaf at the prime
  `(2)` with value `ℤ` has `H^0 ≠ 0`, while the proposition kills `H^q` for every `q ≥ 2`.
* `Stacks.CohomologyVanishing.nondegenerate_spectral_cohomologicalDimension`: every binder of the
  proposition instantiated at once, by terms which assume nothing — `Spec ℤ` in dimension exactly
  one, the skyscraper sheaf, the quasi-compact open `D(2)`, which is neither empty nor everything,
  and the closed constructible set `V(2)`, which is neither empty nor everything.

## The non-degeneracy certificate

A vanishing theorem can be true and say nothing: if the space were forced to be a point, if the
dimension bound were only ever attained at zero, if the quasi-compact open had to be the whole
space, if the closed constructible set had to be empty or everything, or if every abelian sheaf
on such a space had vanishing cohomology in all degrees, then the proposition would carry no
content. None of those happens, and each is checked here rather than argued:

* `Spec ℤ` is a spectral space of Krull dimension exactly `1`
  (`Stacks.CohomologyVanishing.topologicalKrullDim_primeSpectrum_int`) which is not discrete
  (`Stacks.CohomologyVanishing.not_discreteTopology_primeSpectrum_int`), so the bound is attained
  and the space is not a finite discrete one.
* `D(2) ⊆ Spec ℤ` is a quasi-compact open containing the generic point and missing `(2)`, so it is
  neither `⊥` nor `⊤` (`basicOpen_two_ne_bot`, `basicOpen_two_ne_top`).
* `V(2) ⊆ Spec ℤ` is closed and constructible — its complement is the quasi-compact open `D(2)` —
  contains `(2)` and misses the generic point, so it is neither empty nor everything.
* The skyscraper sheaf at `(2)` with value `ℤ` has `H^0 = ℤ`, so the cohomology functor the
  proposition vanishes above degree `d` is not the zero functor.

## References

* [Stacks Project, Proposition 20.33.5 (Tag 0A3G)](https://stacks.math.columbia.edu/tag/0A3G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Stacks.Cohomology.SupportedComplexes

universe u

namespace Stacks.CohomologyVanishing

/-- **[Stacks, Tag 0A3G].** Let `X` be a spectral space of Krull dimension `d` and let `F` be an
abelian sheaf on `X`. Then

1. `H^q(X, F) = 0` for `q > d`;
2. `H^d(X, F) ⟶ H^d(U, F)` is surjective for every quasi-compact open `U ⊆ X`;
3. `H^q_Z(X, F) = 0` for `q > d` and every constructible closed subset `Z ⊆ X`.

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant abelian
sheaf `ℤ` on the site of opens; cohomology over an open is the value of
`CategoryTheory.Sheaf.cohomologyPresheaf`, so that clause (2) is a statement about the restriction
map of that presheaf; and cohomology with support in `Z` is the right derived functor of the
sections over `X` of the subsheaf of sections supported on `Z`.

Each clause is proved in the file named beside it below, where it is proved under the weaker
hypothesis that `d` bounds the dimension rather than equalling it. Here they are put together
under the source's hypothesis. -/
@[stacks 0A3G "the whole proposition: (1) sheaf cohomology on a spectral space of Krull \
  dimension d vanishes above degree d, (2) restriction to a quasi-compact open is surjective in \
  degree d, and (3) cohomology with support in a constructible closed subset vanishes above \
  degree d"]
theorem subsingleton_sheafH_and_surjective_and_subsingleton_supported_of_topologicalKrullDim_eq
    {X : TopCat.{u}} [SpectralSpace X]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ)
    (hdim : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    (∀ q : ℕ, d < q → Subsingleton (Sheaf.H.{u, u, u, u} F q)) ∧
      (∀ U : Opens X, IsCompact (U : Set X) → Function.Surjective
        ((F.cohomologyPresheaf d).map (homOfLE (show U ≤ ⊤ from le_top)).op)) ∧
      (∀ Z : Set X, IsClosed Z → IsConstructible Z → ∀ q : ℕ, d < q →
        Subsingleton (((supportedSectionsEvaluation Z ⊤).rightDerived q).obj F)) :=
  ⟨-- clause (1), `SpectralSpaces.lean`
    fun q hq => subsingleton_sheafH_of_topologicalKrullDim_le d ↥X inferInstance inferInstance F q
      (le_of_eq hdim) hq,
    -- clause (2), `SpectralSpaces.lean`
    fun U hU => surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le F d
      (le_of_eq hdim) U hU,
    -- clause (3), `SpectralSupportVanishing.lean`
    fun Z hZ hZc q hq => subsingleton_rightDerived_supportedSections_of_topologicalKrullDim_le F d
      q (le_of_eq hdim) Z hZ hZc hq⟩

/-! ### The non-degeneracy certificate

Everything below instantiates the proposition. Nothing below is part of the statement of
[Stacks, Tag 0A3G], so nothing below carries the tag. -/

section Nondegeneracy

attribute [local instance] Classical.propDecidable

/-- The prime `(2)` of `ℤ`, a closed point of `Spec ℤ`. -/
def primeTwoInt : PrimeSpectrum ℤ :=
  ⟨Ideal.span {(2 : ℤ)}, (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two⟩

/-- The prime `(0)` of `ℤ`, the generic point of `Spec ℤ`. -/
def primeZeroInt : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩

/-- `Spec ℤ` as a topological space in the bundled sense. -/
abbrev primeSpectrumInt : TopCat.{0} := TopCat.of (PrimeSpectrum ℤ)

theorem mem_zeroLocus_two_primeTwoInt :
    primeTwoInt ∈ PrimeSpectrum.zeroLocus {(2 : ℤ)} := by
  simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
  exact Ideal.mem_span_singleton_self _

theorem notMem_zeroLocus_two_primeZeroInt :
    primeZeroInt ∉ PrimeSpectrum.zeroLocus {(2 : ℤ)} := by
  simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
  intro h
  simp [primeZeroInt] at h

/-- A prime lies in `D(2)` exactly when it does not lie in `V(2)`. -/
private theorem mem_basicOpen_two_iff (P : PrimeSpectrum ℤ) :
    P ∈ PrimeSpectrum.basicOpen (2 : ℤ) ↔ P ∉ PrimeSpectrum.zeroLocus {(2 : ℤ)} := by
  rw [← SetLike.mem_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  rfl

/-- `V(2) ⊆ Spec ℤ` is constructible: its complement is the basic open `D(2)`, which is
quasi-compact, and `Spec ℤ` is quasi-compact. -/
theorem isConstructible_zeroLocus_two :
    IsConstructible (PrimeSpectrum.zeroLocus {(2 : ℤ)}) := by
  refine IsConstructible.of_compl ?_
  rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact (PrimeSpectrum.isCompact_basicOpen _).isConstructible (PrimeSpectrum.basicOpen _).isOpen

/-- `D(2)` is not the whole of `Spec ℤ`: it misses the closed point `(2)`. -/
theorem basicOpen_two_ne_top :
    PrimeSpectrum.basicOpen (2 : ℤ) ≠ (⊤ : Opens (PrimeSpectrum ℤ)) := fun h =>
  (mem_basicOpen_two_iff _).1 (h ▸ trivial) mem_zeroLocus_two_primeTwoInt

/-- `D(2)` is not empty: it contains the generic point `(0)`. -/
theorem basicOpen_two_ne_bot :
    PrimeSpectrum.basicOpen (2 : ℤ) ≠ (⊥ : Opens (PrimeSpectrum ℤ)) := fun h => by
  have hmem := (mem_basicOpen_two_iff _).2 notMem_zeroLocus_two_primeZeroInt
  rw [h] at hmem
  simp at hmem

/-- The skyscraper sheaf on `Spec ℤ` at the prime `(2)` with value `ℤ`. -/
abbrev skyscraperInt : Sheaf (Opens.grothendieckTopology primeSpectrumInt) AddCommGrpCat.{0} :=
  skyscraperSheaf (X := primeSpectrumInt) primeTwoInt (AddCommGrpCat.of ℤ)

/-- The global sections of the skyscraper sheaf at `(2)` are `ℤ`: the open `⊤` contains `(2)`. -/
theorem sections_top_skyscraperInt :
    skyscraperInt.obj.obj (op (⊤ : Opens primeSpectrumInt)) = AddCommGrpCat.of ℤ := by
  change (if primeTwoInt ∈ (⊤ : Opens primeSpectrumInt) then AddCommGrpCat.of ℤ
    else terminal _) = _
  exact ite_eq_left trivial

/-- **The cohomology of [Stacks, Tag 0A3G] is not identically zero.** The skyscraper sheaf at the
prime `(2)` on `Spec ℤ` has nontrivial `H^0`, because `H^0` is global sections and those are `ℤ`.
Together with `topologicalKrullDim_primeSpectrum_int` this says that the proposition's conclusion
is a vanishing statement about a functor which does not vanish: on `Spec ℤ`, where `d = 1`, it
kills every degree `≥ 2` and degree `0` survives. -/
theorem nontrivial_sheafH_zero_skyscraperInt :
    Nontrivial (Sheaf.H.{0, 0, 0, 0} skyscraperInt 0) := by
  have hsections : Nontrivial (skyscraperInt.obj.obj (op (⊤ : Opens primeSpectrumInt))) := by
    rw [sections_top_skyscraperInt]
    exact inferInstanceAs (Nontrivial ℤ)
  exact (Sheaf.H.equiv₀ (T := (⊤ : Opens primeSpectrumInt)) skyscraperInt
    Stacks.Cohomology.TerminalCohomology.topIsTerminal).toEquiv.nontrivial

/-- **Every binder of [Stacks, Tag 0A3G] instantiated at once**, by terms which assume nothing:
the space is `Spec ℤ`, spectral of Krull dimension exactly `1`; the sheaf is the skyscraper at
`(2)`, whose `H^0` is nontrivial; the quasi-compact open is `D(2)`, neither empty nor everything;
the constructible closed subset is `V(2)`, neither empty nor everything; and the degree is `2`.

This is the positive non-degeneracy test: the proposition is satisfiable, and satisfiable at data
none of which is zero, empty or terminal. -/
theorem nondegenerate_spectral_cohomologicalDimension :
    Subsingleton (Sheaf.H.{0, 0, 0, 0} skyscraperInt 2) ∧
      Function.Surjective ((skyscraperInt.cohomologyPresheaf 1).map
        (homOfLE (show PrimeSpectrum.basicOpen (2 : ℤ) ≤ ⊤ from le_top)).op) ∧
      Subsingleton (((supportedSectionsEvaluation
        (PrimeSpectrum.zeroLocus {(2 : ℤ)}) ⊤).rightDerived 2).obj skyscraperInt) := by
  have hdim : topologicalKrullDim ↥primeSpectrumInt = ((1 : ℕ) : WithBot ℕ∞) := by
    have := topologicalKrullDim_primeSpectrum_int
    exact_mod_cast this
  obtain ⟨h1, h2, h3⟩ :=
    subsingleton_sheafH_and_surjective_and_subsingleton_supported_of_topologicalKrullDim_eq
      skyscraperInt 1 hdim
  exact ⟨h1 2 (by omega), h2 _ (PrimeSpectrum.isCompact_basicOpen _),
    h3 _ (PrimeSpectrum.isClosed_zeroLocus _) isConstructible_zeroLocus_two 2 (by omega)⟩

end Nondegeneracy

end Stacks.CohomologyVanishing

end

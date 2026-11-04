module

public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init

public import StacksFrontier.Algebra.MittagLeffler.Descent
public import StacksFrontier.Algebra.MittagLeffler.ProjectiveCharacterization
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe uR uS uM uT

/-!
# Faithfully flat descent of countably generated projective modules

Let `R → S` be a faithfully flat ring map and let `M` be an `R`-module whose base change
`S ⊗[R] M` is a countably generated projective `S`-module. Then `M` is countably generated and
projective.

The argument is the source's. Countable generation descends on its own (Lemma 0GVD). For
projectivity, Theorem 059Z characterizes projective modules as the flat Mittag-Leffler modules
which are direct sums of countably generated modules. Applied over `S` it turns the projectivity
of `S ⊗[R] M` into flatness and the Mittag-Leffler condition for `S ⊗[R] M`; flatness descends
(Lemma 03C4 (3), which is Mathlib's `Module.Flat.of_flat_tensorProduct`) and so does the
Mittag-Leffler condition (Lemma 05A5). The remaining condition of 059Z is met by the one-term
decomposition `{⊤}` of the countably generated `M`, and 059Z read backwards over `R` gives
projectivity.

## Main results

* `Stacks.Projective.CountablyGeneratedDescent.solution`: the proof of
  `Module.countablyGenerated_and_projective_of_faithfullyFlat_baseChange`.

## Implementation notes

Theorem 059Z and Lemma 05A5 both spell the Mittag-Leffler condition in the intrinsic form 059E (1),
whose quantifiers range over test modules in one fixed universe: 059Z is stated for a ring `R` and
a module `M : Type v` with `Small.{v} R`, and 05A5 for `R`, an algebra `S : Type v` and a module
`M : Type v`, again with `Small.{v} R`. Lemma 05A6 puts its ring, its algebra and its module in
three unrelated universes, so the descent is proved first in the form the two imported statements
have — `projective_of_countablyGenerated_of_projective_tensorProduct_of_small` below, for `S` and
`M` in one universe containing a copy of `R` — and then transported along the universe lifts of `S`
and `M` into a common universe.

The transport of projectivity is an instance of a general fact,
`projective_tensorProduct_of_equiv`: projectivity of a base change `A ⊗[R] M` over `A` depends on
the pair `(A, M)` only up to an `R`-algebra equivalence of the base and an `R`-linear equivalence
of the module, because `e ⊗ f` is then a bijection `A ⊗[R] M → B ⊗[R] N` semilinear over `e`.
Taking `e` and `f` to be `ULift.algEquiv` and `ULift.moduleEquiv` moves both factors up;
`Module.Projective.of_ulift` brings the conclusion back down. Countable generation goes up the lift
by `countablyGenerated_ulift`, read off the characterization
`Module.CountablyGenerated.iff_exists_surjective` proved with 0GVD. Nothing about the mathematics
changes.

## References

* [StacksProject 05A6](https://stacks.math.columbia.edu/tag/05A6)
-/



open scoped TensorProduct

namespace Stacks.Projective.CountablyGeneratedDescent

/-- Countable generation passes to a universe lift: a countable generating set is the image of one
under the surjection `M → ULift M`. -/
private theorem countablyGenerated_ulift {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] (hM : Module.CountablyGenerated R M) :
    Module.CountablyGenerated R (ULift.{uT} M) := by
  obtain ⟨I, hI, f, hf⟩ := (Module.CountablyGenerated.iff_exists_surjective R M).mp hM
  exact (Module.CountablyGenerated.iff_exists_surjective R _).mpr
    ⟨I, hI, ULift.moduleEquiv.symm.toLinearMap ∘ₗ f, ULift.moduleEquiv.symm.surjective.comp hf⟩

/-- Projectivity of a base change is carried along an isomorphism of the base and of the module:
if `e : A ≃ₐ[R] B` and `f : M ≃ₗ[R] N` then `e ⊗ f` is an `e`-semilinear bijection
`A ⊗[R] M → B ⊗[R] N`, so `Module.Projective.of_equiv` turns projectivity of `A ⊗[R] M` over `A`
into projectivity of `B ⊗[R] N` over `B`. -/
private theorem projective_tensorProduct_of_equiv {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {B : Type*} [CommRing B] [Algebra R B] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : A ≃ₐ[R] B) (f : M ≃ₗ[R] N)
    [Module.Projective A (A ⊗[R] M)] : Module.Projective B (B ⊗[R] N) := by
  have := RingHomInvPair.of_ringEquiv e.toRingEquiv
  have := RingHomInvPair.of_ringEquiv e.toRingEquiv.symm
  have key : ∀ (a : A) (x : A ⊗[R] M), TensorProduct.congr e.toLinearEquiv f (a • x) =
      e a • TensorProduct.congr e.toLinearEquiv f x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a' m => simp [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  exact Module.Projective.of_equiv (σ := (e.toRingEquiv : A →+* B))
    { TensorProduct.congr e.toLinearEquiv f with map_smul' := key }

/-- **Stacks 05A6**, second conjunct, in the universes the imported statements 059Z and 05A5 are stated
in: the ring `R` is small in the universe of the algebra `S` and of the module `M`, which is where
the Mittag-Leffler condition's test modules live. -/
@[sga "3 VIB 11.8.1" "(ii), special case",
  sga "3 VIB 11.8.2" "special case",
  sga "3 VIB 11.9.1" "special case"]
private theorem projective_of_countablyGenerated_of_projective_tensorProduct_of_small {R : Type uR}
    [CommRing R] [Small.{uS} R] {S : Type uS} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type uS} [AddCommGroup M] [Module R M]
    (hP : Module.Projective S (S ⊗[R] M)) (hM : Module.CountablyGenerated R M) :
    Module.Projective R M := by
  obtain ⟨hflat, hML, -⟩ :=
    (Module.projective_iff_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span S
      (S ⊗[R] M)).mp hP
  refine (Module.projective_iff_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span R M).mpr
    ⟨Module.Flat.of_flat_tensorProduct R M S,
      Module.mittagLeffler_of_mittagLeffler_tensorProduct hML, {⊤},
      sSupIndep_singleton _, sSup_singleton, ?_⟩
  rintro N rfl
  exact hM

/-- **Stacks 05A6**, second conjunct, with the ring, the algebra and the module in unrelated
universes: replace `S` and `M` by their lifts to `max uR uS uM`, where the previous lemma applies,
and bring the conclusion back down. -/
@[sga "3 VIB 11.8.1" "(ii), special case",
  sga "3 VIB 11.8.2" "special case",
  sga "3 VIB 11.9.1" "special case"]
private theorem projective_of_countablyGenerated_of_projective_tensorProduct (R : Type uR)
    [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (M : Type uM) [AddCommGroup M] [Module R M] [Module.Projective S (S ⊗[R] M)]
    (hM : Module.CountablyGenerated R M) : Module.Projective R M := by
  have hFF : Module.FaithfullyFlat R (ULift.{max uR uS uM} S) :=
    Module.FaithfullyFlat.of_linearEquiv R S ULift.moduleEquiv
  have hP : Module.Projective (ULift.{max uR uS uM} S)
      (ULift.{max uR uS uM} S ⊗[R] ULift.{max uR uS uM} M) :=
    projective_tensorProduct_of_equiv ULift.algEquiv.symm ULift.moduleEquiv.symm
  have : Module.Projective R (ULift.{max uR uS uM} M) :=
    projective_of_countablyGenerated_of_projective_tensorProduct_of_small hP
      (countablyGenerated_ulift hM)
  exact Module.Projective.of_ulift

public theorem solution {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {M : Type uM} [AddCommGroup M] [Module R M]
    [Module.Projective S (S ⊗[R] M)] (hM : Module.CountablyGenerated S (S ⊗[R] M)) :
    Module.CountablyGenerated R M ∧ Module.Projective R M :=
  have hCG : Module.CountablyGenerated R M :=
    countablyGenerated_of_faithfullyFlat_baseChange R S M hM
  ⟨hCG, projective_of_countablyGenerated_of_projective_tensorProduct R S M hCG⟩

end Stacks.Projective.CountablyGeneratedDescent

/-!
# Faithfully flat descent of countably generated projective modules

Let `R → S` be a faithfully flat ring map and let `M` be an `R`-module. If the base change of `M`
to `S` is countably generated and projective as an `S`-module, then `M` is countably generated and
projective as an `R`-module.

The two conjuncts of the conclusion have separate sources. Countable generation descends on its
own (Lemma 0GVD): a countable generating family of `M ⊗_R S` is a family of finite sums of
elementary tensors, so the countably many `R`-module elements occurring in those sums span a
submodule `M' ⊆ M` with `M' ⊗_R S → M ⊗_R S` surjective, whence `M' = M` by faithful flatness.
Projectivity is then read off Theorem 059Z, which for a countably generated module identifies
projectivity with the conjunction of flatness and the Mittag-Leffler condition: flatness descends
(Lemma 03C4) and so does the Mittag-Leffler condition (Lemma 05A5), and both hold for `M ⊗_R S`
because it is projective. This is the countably generated case of Theorem 05A9, which removes the
countable generation hypothesis by a Kaplansky dévissage — the dévissage being built out of the
present lemma.

## Main results

* `Module.countablyGenerated_and_projective_of_faithfullyFlat_baseChange`: for `R → S` faithfully
  flat, an `R`-module whose base change to `S` is a countably generated projective `S`-module is
  itself countably generated and projective.

## Implementation notes

Countable generation is `Module.CountablyGenerated`, the predicate introduced with Lemma 0GVD in
`StacksFrontier/RingTheory/Flat/FaithfullyFlat/Descent.lean`: a set of elements of the module which is
at most countable and spans it. It is used by its name there rather than restated, so that this
lemma and 0GVD speak of the same notion; the companion statements 05A3 and 058W spell the same condition
inline as `∃ t : Set M, t.Countable ∧ Submodule.span R t = ⊤`, which is that definition unfolded.
The `Prop`-valued `Module.CountablyGenerated` is an explicit hypothesis and the class-valued
`Module.Projective` an instance hypothesis, each in the form its own API is phrased in, matching
Mathlib's `Module.Flat.of_flat_tensorProduct`; the conclusion is their conjunction, the source's
conjunctive consequent.

The source's base change is `M ⊗_R S`; the statement writes `S ⊗[R] M`, Mathlib's convention for a
base change (`Module.Flat.baseChange`, `Module.Flat.of_flat_tensorProduct`) and the only one of the
two orders carrying an `S`-module structure in Mathlib, as in 0GVD, 05A3 and 05A5. The two are
identified by `TensorProduct.comm`, and since the hypotheses are statements about the `S`-action,
having that action be the pinned canonical one — the `S`-action on the left factor — is what makes
them the source's hypotheses rather than statements about an unspecified action. The faithfully
flat ring map is `[Module.FaithfullyFlat R S]` for `[Algebra R S]`, Mathlib's spelling. The three
types are `Type*`, so they lie in three unrelated universes, nothing in the mathematics forcing a
relation between them: `Module.CountablyGenerated` quantifies over subsets of the module and
`Module.Projective` over `Finsupp` splittings, neither reaching outside the module's own universe.

The name mutates that of its sibling in this repository, 0GVD's
`countablyGenerated_of_faithfullyFlat_baseChange`, by adjoining the second conjunct; the namespace
is `Module`, where both predicates of the conclusion live.

Faithfulness. (1) No hypothesis is dead. Countable generation of `S ⊗[R] M` is what gives the
first conjunct and is not implied by the second hypothesis: over `R = S = ℤ` the module `⨁_{i : I}
ℤ` on an uncountable `I` is projective and not countably generated. Projectivity of `S ⊗[R] M`
gives the second conjunct and is not implied by the first: over `R = S = ℤ` the module `ℚ` is
countably generated and not projective. Faithful flatness cannot be weakened to flatness: for
`R = ℤ`, `S = ℚ` and `M = ℚ` the flat map `ℤ → ℚ` has `ℚ ⊗_ℤ ℚ ≅ ℚ` free of rank one over `ℚ`,
hence countably generated and projective, while `ℚ` is not a projective `ℤ`-module (Theorem 059Z).
The countable generation hypothesis is not needed for the second conjunct alone — that is Theorem
05A9 — but it is the source's hypothesis here and it is live for the first conjunct, so the
statement is 05A6 and not a decorated 05A9. (2) The scalars and the base are the source's: the
hypotheses are conditions on `S ⊗[R] M` over `S`, the spans and the projectivity being over `S`,
the conclusion conditions on `M` over `R`, and the tensor product is over `R` along
`algebraMap R S`. (3) Where the source names a canonical map the statement pins it: the `S`-action
on `S ⊗[R] M` is the canonical one on the left factor rather than an abstract module structure
making `S ⊗[R] M` a base change, and countable generation is spanning by a countable set of
elements of the module itself rather than the existence of a surjection from a countably generated
free module (the two agree by `Module.CountablyGenerated.iff_exists_surjective`). (4) The
instantiation is not degenerate: for `R = ℤ`, `S = ℤ[X]` (free, hence faithfully flat) and
`M = ⨁_{n : ℕ} ℤ` the base change `S ⊗_ℤ M` is free on a countable basis over `S`, so both
hypotheses hold and the conclusion says something non-vacuous about `M`; and the conclusion holds
for no reason of generality, `ℚ` over `ℤ` being countably generated and not projective, so the
implication is not vacuously true either. `S = 0` cannot make the hypotheses vacuously true over a
nontrivial `R`: faithful flatness forbids `I • ⊤ = ⊤` for `I` maximal.

## References

* [StacksProject 05A6](https://stacks.math.columbia.edu/tag/05A6)
-/

@[expose] public section

open scoped TensorProduct

namespace Module

/-- **Stacks 05A6.** Let `R → S` be a faithfully flat ring map and let `M` be an `R`-module. If the
`S`-module `S ⊗_R M` is countably generated and projective, then `M` is countably generated and
projective. -/
@[stacks 05A6 "Countable generation is `Module.CountablyGenerated`, the predicate introduced with 0GVD.
  The base change is written `S ⊗[R] M`, Mathlib's order, the source writing `M ⊗_R S`.",
  sga
    "3 VIB 11.8.2" "countably generated case",
  sga "3 VIB 11.8.2" "countably generated case",
  sga "3 VIB 11.8.1" "(ii), special case"]
public theorem countablyGenerated_and_projective_of_faithfullyFlat_baseChange {R : Type*}
    [CommRing R] {S : Type*} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Projective S (S ⊗[R] M)]
    (hM : Module.CountablyGenerated S (S ⊗[R] M)) :
    Module.CountablyGenerated R M ∧ Module.Projective R M :=
  Stacks.Projective.CountablyGeneratedDescent.solution (S := S) hM

end Module

end
end

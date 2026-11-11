module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGrading
public import StacksCore.Tactic.StacksAttribute

/-!
# The two numerical invariants of the associated graded ring

Let `A` be a commutative ring and `I ⊆ A` an ideal, and let `S = Gr_I(A) = ⨁_{n ≥ 0} Iⁿ/Iⁿ⁺¹` be
the associated graded ring (`AssociatedGraded.gradedRing`), graded internally by
`AssociatedGraded.grading`. Section 51.22 of the chapter *Local Cohomology*
([Stacks, Tag 0GA6]) attaches to `S` two numerical invariants, used throughout that section and
by the uniform lifting lemma [Stacks, Tag 0GAQ]:

* `d(S)`, the maximum of the dimensions of the fibres of `Proj(S) → Spec(S₀)`;
* `q(S)`, the smallest `q₀ ≥ 0` such that for every `q ≥ q₀` one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for
  `1 ≤ i ≤ d(S)` and `H⁰(Y, 𝒪_Y(q)) = I^q/I^{q+1}`, where `Y = Proj(S)`.

Here `Y = Proj(S)` is the scheme `AlgebraicGeometry.Proj (AssociatedGraded.grading I)`, the
structure morphism `Y → Spec(S₀)` is `AlgebraicGeometry.Proj.toSpecZero`, and `S₀ = A/I` by
`AssociatedGraded.gradeZeroEquiv`. The twists `𝒪_Y(q)` are
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`, their cohomology is the right derived
functor of global sections `Stacks.Cohomology.sectionsFunctor`, their global sections are
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGlobalSections`, and the canonical map
`S_q → H⁰(Y, 𝒪_Y(q))` of [Stacks, Tag 0AG2] is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`.

## Main definitions

* `AssociatedGraded.projGr`: the scheme `Y = Proj(Gr_I(A))`.
* `AssociatedGraded.toSpecGradeZero`: its structure morphism `Y → Spec(S₀)`.
* `AssociatedGraded.dInvariant`: the invariant `d(S)`.
* `AssociatedGraded.projTwistCohomology`: `Hⁱ(Y, 𝒪_Y(q))`.
* `AssociatedGraded.pieceToSections`: the canonical map `I^q/I^{q+1} → H⁰(Y, 𝒪_Y(q))`.
* `AssociatedGraded.IsRegularDegree`: the conjunction of the two displayed conditions at a
  single degree `q`.
* `AssociatedGraded.qInvariant`: the invariant `q(S)`.

## Main results

* `AssociatedGraded.qInvariant_le`: `q(S)` is a lower bound for every degree past which the two
  conditions hold — one half of "smallest".
* `AssociatedGraded.isRegularDegree_of_qInvariant_le`: the other half, that the two conditions do
  hold for every `q ≥ q(S)`, given some bound (which exists for `A` Noetherian, see the
  implementation notes).
* `AssociatedGraded.dInvariant_eq_zero_of_eq_top` and
  `AssociatedGraded.qInvariant_eq_zero_of_eq_top`: in the degenerate case `I = A`, where `S = 0`,
  both invariants are `0`. The second goes through
  `AssociatedGraded.isRegularDegree_of_eq_top`, which exhibits a degree past which the two
  conditions hold and so also shows `AssociatedGraded.IsRegularDegree` is satisfiable.

## Implementation notes

`d(S)` is valued in `ℕ∞`, not in `ℕ`. The source treats it as a natural number; that it is
finite rests on properness of the blowup over a Noetherian base, so it is proved downstream, in
`Stacks.LocalCohomology.UniformityIII.dInvariant_eq_fibreDim`
(`BitUniformityIII/FibreDimensionAssociatedGraded.lean`), which identifies `d(S)` with the natural
number `Stacks.LocalCohomology.UniformityIII.fibreDim`. A fibre with empty underlying space has
`topologicalKrullDim = ⊥`, which is sent to `0` by `WithBot.unbotD 0`; this is the source's
convention "`d = 0` if `X = ∅`".

`q(S)` is `sInf` of the set of valid bounds, taken in `ℕ`. The source knows this set is nonempty
by Cohomology of Schemes, Lemmas [Stacks, Tag 0AG6] and [Stacks, Tag 0AG7]; for `A` Noetherian
this is `Stacks.LocalCohomology.UniformityIII.exists_forall_isRegularDegree`
(`BitUniformityIII/UniformityInvariants.lean`), which transports Serre's two theorems on the blowup
to `Y = Proj(S)` along the closed immersion `Y → X`. This file states
`isRegularDegree_of_qInvariant_le` for an arbitrary ring, so there nonemptiness is an argument;
`Nat.sInf` of the empty set is `0`.

`dInvariant` formalizes clause (2) of the paragraph of [Stacks, Tag 0GA6] that introduces `d`,
namely the description as the maximal fibre dimension of `Proj(S) → Spec(S₀)`, which is the
description that exhibits `d` as an invariant of the isomorphism class of `S` and justifies the
notation `d(S)`. The paragraph's primary phrasing is the maximal fibre dimension of the blowup
`p : X → Spec(A)` — in this repository `Stacks.Blowup.toSpec` on
`Stacks.Blowup.blowUpSpec I = Proj (Stacks.Blowup.reesGrading I)` — and the two agree by
`Stacks.LocalCohomology.UniformityIII.dInvariant_eq_fibreDim`.

The full content of the section, for `A` Noetherian, is
`Stacks.LocalCohomology.UniformityIII.dInvariant_qInvariant_spec`, which carries the tag.

The `d(S)`-dependent range `1 ≤ i ≤ d` of the vanishing clause is read in `ℕ∞`; since the two
conditions are indexed by `i : ℕ`, the hypothesis is `(i : ℕ∞) ≤ dInvariant I`.

## References

* [Stacks Project, Section 51.22 (0GA6)](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Lemma 51.22.1 (0GA7)](https://stacks.math.columbia.edu/tag/0GA7) — the four
  conclusions drawn from these two invariants.
* [Stacks Project, Lemma 30.14.2 (0AG6)](https://stacks.math.columbia.edu/tag/0AG6) and
  [Lemma 30.14.3 (0AG7)](https://stacks.math.columbia.edu/tag/0AG7) — what makes the set of
  bounds defining `q(S)` nonempty.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGlobalSections degreeSection)

attribute [local instance] HasDerivedCategory.standard

namespace AssociatedGraded

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The scheme `Y = Proj(Gr_I(A))`.** In the situation of [Stacks, Tag 0GA6] this is the
exceptional divisor of the blowup of `Spec(A)` in `I`. -/
abbrev projGr : Scheme.{u} := AlgebraicGeometry.Proj (grading I)

/-- **The structure morphism `Proj(S) → Spec(S₀)`.** Its target is `Spec(A/I)` by
`AssociatedGraded.gradeZeroEquiv`. -/
def toSpecGradeZero : projGr I ⟶ Spec (.of (grading I 0)) :=
  AlgebraicGeometry.Proj.toSpecZero (grading I)

/-- **The invariant `d(S) = d(Gr_I(A))`**: the maximum of the dimensions of the fibres of
`Proj(S) → Spec(S₀)`, a fibre with empty underlying space contributing `0`.

This is clause (2) of the paragraph of [Stacks, Tag 0GA6] that introduces `d`; for `A` Noetherian
it equals the maximal fibre dimension of the blowup by
`Stacks.LocalCohomology.UniformityIII.dInvariant_eq_fibreDim`, and the section's statements about
it are `Stacks.LocalCohomology.UniformityIII.dInvariant_qInvariant_spec`. -/
def dInvariant : ℕ∞ :=
  ⨆ y : Spec (.of (grading I 0)),
    (topologicalKrullDim (Scheme.Hom.fiber (toSpecGradeZero I) y)).unbotD 0

/-- **`Hⁱ(Y, 𝒪_Y(q))` for `Y = Proj(Gr_I(A))`**: the `i`-th right derived functor of global
sections, applied to the `q`-th twist of the structure sheaf. -/
abbrev projTwistCohomology (i : ℕ) (q : ℤ) :=
  ((Stacks.Cohomology.sectionsFunctor (projGr I) ⊤).rightDerived i).obj
    (twistingSheaf (grading I) q)

/-- **The canonical map `I^q/I^{q+1} → H⁰(Y, 𝒪_Y(q))`**: the map of [Stacks, Tag 0AG2] from the
degree-`q` homogeneous elements of `S` to the global sections of `𝒪_Y(q)`, precomposed with the
identification of `S_q` with `I^q/I^{q+1}`. -/
def pieceToSections (q : ℕ) :
    piece (M := A) I q → twistGlobalSections (grading I) q :=
  fun z => degreeSection (grading I) q (gradingEquivPiece I q z)

theorem bijective_pieceToSections_iff (q : ℕ) :
    Function.Bijective (pieceToSections I q) ↔
      Function.Bijective (degreeSection (grading I) q) :=
  Function.Bijective.of_comp_iff _ (gradingEquivPiece I q).bijective

/-- **The two conditions of [Stacks, Tag 0GA6] at a single degree `q`**: the vanishing of
`Hⁱ(Y, 𝒪_Y(q))` for `1 ≤ i ≤ d(S)`, and the bijectivity of the canonical map
`I^q/I^{q+1} → H⁰(Y, 𝒪_Y(q))`. -/
def IsRegularDegree (q : ℕ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → (i : ℕ∞) ≤ dInvariant I → IsZero (projTwistCohomology I i (q : ℤ))) ∧
    Function.Bijective (pieceToSections I q)

/-- **The invariant `q(S) = q(Gr_I(A))`**: the smallest `q₀ ≥ 0` such that
`AssociatedGraded.IsRegularDegree` holds at every `q ≥ q₀`.

That the set of such `q₀` is nonempty is Cohomology of Schemes, Lemmas [Stacks, Tag 0AG6] and
[Stacks, Tag 0AG7]; for `A` Noetherian it is
`Stacks.LocalCohomology.UniformityIII.exists_forall_isRegularDegree`, and
`Stacks.LocalCohomology.UniformityIII.dInvariant_qInvariant_spec` states that `q(S)` is the least
such bound. -/
def qInvariant : ℕ := sInf {q₀ : ℕ | ∀ q : ℕ, q₀ ≤ q → IsRegularDegree I q}

/-- `q(S)` is at most any degree past which the two conditions hold. -/
theorem qInvariant_le {q₀ : ℕ} (h : ∀ q : ℕ, q₀ ≤ q → IsRegularDegree I q) :
    qInvariant I ≤ q₀ :=
  Nat.sInf_le h

/-- The two conditions hold at every degree `≥ q(S)`, provided some degree past which they hold
exists at all; for `A` Noetherian one does, by
`Stacks.LocalCohomology.UniformityIII.exists_forall_isRegularDegree`. -/
theorem isRegularDegree_of_qInvariant_le
    (h : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → IsRegularDegree I q) {q : ℕ} (hq : qInvariant I ≤ q) :
    IsRegularDegree I q :=
  Nat.sInf_mem h q hq

/-- **In the degenerate case `I = A` one has `d(S) = 0`.** Then `S = 0` by
`AssociatedGraded.subsingleton_gradedRing_iff`, so `S₀` is the zero ring and `Spec(S₀)` has no
points at all. This is the case with which [Stacks, Tag 0GA6] qualifies `d`, and with which the
proof of [Stacks, Tag 0GA7] opens. -/
theorem dInvariant_eq_zero_of_eq_top (h : I = ⊤) : dInvariant I = 0 := by
  have hs := subsingleton_gradeZero_of_eq_top I h
  have : IsEmpty (Spec (.of (grading I 0))) :=
    ⟨fun x => (inferInstance : IsEmpty (PrimeSpectrum (grading I 0))).elim x⟩
  simp [dInvariant]

/-- If `I = A` then `S = 0`, and the homogeneous spectrum of the zero ring is empty: a point of
it would carry a homogeneous prime ideal, and every ideal of the zero ring is the unit ideal. -/
theorem isEmpty_projGr_of_eq_top (h : I = ⊤) : IsEmpty (ProjectiveSpectrum (grading I)) := by
  have h' := (subsingleton_gradedRing_iff I).mpr h
  refine ⟨fun x => x.isPrime.ne_top ?_⟩
  rw [Submodule.eq_top_iff']
  intro a
  rw [h'.elim a 0]
  exact Submodule.zero_mem _

/-- If `I = A` then `Y = Proj(S)` is empty, so `H⁰(Y, 𝒪_Y(q)) = 0`: a global section of the
sheaf associated to a graded module is a dependent function on the points of `Y`, and there are
none. -/
theorem subsingleton_twistGlobalSections_of_eq_top (h : I = ⊤) (q : ℕ) :
    Subsingleton (twistGlobalSections (grading I) q) := by
  have he := isEmpty_projGr_of_eq_top I h
  exact ⟨fun s t => Subtype.ext (funext fun x => False.elim (he.false x.1))⟩

/-- **In the degenerate case `I = A` both conditions of [Stacks, Tag 0GA6] hold at every
degree.** The vanishing clause is vacuous because `d(S) = 0` leaves no `i` with `1 ≤ i ≤ d(S)`,
and the comparison map is a map between zero groups. Together with
`AssociatedGraded.qInvariant_le` this gives `q(S) = 0`, the source's parenthetical "if `S = 0`
then `q(S) = 0`"; it also shows `AssociatedGraded.IsRegularDegree` is satisfiable. -/
theorem isRegularDegree_of_eq_top (h : I = ⊤) (q : ℕ) : IsRegularDegree I q := by
  refine ⟨fun i hi hid => ?_, ?_⟩
  · exfalso
    rw [dInvariant_eq_zero_of_eq_top I h] at hid
    have h1 : (1 : ℕ∞) ≤ (i : ℕ∞) := by exact_mod_cast hi
    simpa using h1.trans hid
  · have hs := subsingleton_twistGlobalSections_of_eq_top I h q
    refine ⟨fun a b _ => ?_, fun y => ⟨0, hs.elim _ _⟩⟩
    exact (subsingleton_piece_of_eq_top I h q a).trans (subsingleton_piece_of_eq_top I h q b).symm

/-- **In the degenerate case `I = A` one has `q(S) = 0`.** -/
theorem qInvariant_eq_zero_of_eq_top (h : I = ⊤) : qInvariant I = 0 :=
  Nat.le_zero.mp (qInvariant_le I fun q _ => isRegularDegree_of_eq_top I h q)

end AssociatedGraded

end

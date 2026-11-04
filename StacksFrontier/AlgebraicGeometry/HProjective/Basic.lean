module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace

/-!
# H-projective and H-quasi-projective morphisms, and the formal half of Stacks Tag 087S

Stacks Tag 087S says that over a base carrying an ample invertible sheaf every projective
morphism is H-projective and every quasi-projective morphism is H-quasi-projective. This file
sets up the two target predicates over the repository's `ℙⁿ_S` and proves everything in
the source's argument that does not need the projective bundle — which is the whole
of the argument's *shape*, and no part of its geometric input.

## The two predicates

`Stacks.HProjective.IsHProjective` and `Stacks.HProjective.IsHQuasiProjective` are Tag 0C61's
`IsProjectiveMorphism` and Tag 01VW's `IsHQuasiProjective` with Tag 01NF's relative projective
space spelled by its library name `AlgebraicGeometry.projectiveSpaceOver` and nothing else changed.
Those statements write the structure morphism of `ℙⁿ_S` in two different ways —
`projectiveSpaceOver n S ↘ S` in the H-projective predicate and `CategoryTheory.Limits.pullback.fst
(terminal.from S) (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse n))` in the
H-quasi-projective one — and `Stacks.HProjective.over_projectiveSpaceOver` records that these are
the same morphism, by `rfl`, so that one spelling serves both.

## Separatedness, which is the one non-formal input that *is* available

`Stacks.HProjective.isSeparated_over` is the separatedness of `ℙⁿ_S` over `S`. It is Stacks Tag
01MC — separatedness of `Proj` of a graded ring, which Mathlib carries as
`AlgebraicGeometry.Scheme.IsSeparated (Proj 𝒜)` — transported along the base change that defines
`ℙⁿ_S`. **This is strictly weaker than the separatedness of `S` that the source's proof opens with,
and it is what the argument actually consumes**: the source appeals to Properties Lemma 28.27.11
(Tag 01Q1) and Constructions Lemma 27.8.8 (Tag 01MC) to make `S` itself separated, but it needs
that only in order to apply Morphisms Lemma 29.44.12 (Tag 07RM). The quasi-compactness cancellation
inside the argument needs only `ℙⁿ_S ⟶ S` to be quasi-separated, and that comes from Tag 01MC by
base change with no reference to `S` and no reference to ampleness. Tag 01Q1 is not available in
this repository — `StacksFrontier/AlgebraicGeometry/AmpleTheory/Basic.lean` records that the
`Proj Γ_*(X, L)` route does not exist at this pin — so this is the stronger statement of the two to
have.

## Main definitions

* `Stacks.HProjective.IsHProjective`: H-projectivity, a closed immersion into `ℙⁿ_S` over `S`.
* `Stacks.HProjective.IsHQuasiProjective`: H-quasi-projectivity, a quasi-compact immersion into
  `ℙⁿ_S` over `S`.
* `Stacks.HProjective.HasHProjectiveClosedImmersion`,
  `Stacks.HProjective.HasHProjectiveImmersion`: factorisation through an *arbitrary* H-projective
  `S`-scheme, which is the form in which the source's reduction step is stated here; see the
  implementation notes.

## Main results

* `Stacks.HProjective.isSeparated_over`,
  `Stacks.HProjective.isSeparated_projectiveSpaceAtUniverse`: `ℙⁿ_S` is separated over `S`, and the
  integral model is separated. Stacks Tag 01MC.
* `Stacks.HProjective.isHProjective_iff_hasHProjectiveClosedImmersion`: **the reduction step of the
  source's proof, as an equivalence.** A morphism is H-projective exactly when it factors as a
  closed immersion into an H-projective `S`-scheme. This is the content of "by our definition of
  projective morphisms it suffices to show that `𝐏(E) ⟶ S` is H-projective", with nothing lost:
  the two conditions are equivalent, not merely one-way.
* `Stacks.HProjective.isHQuasiProjective_iff_hasHProjectiveImmersion`: the same for immersions,
  which is the content of "Lemma 29.44.12 applies and we see that (1) implies (2)". Here the
  quasi-compactness of the composite immersion is the step that consumes separatedness.
* `Stacks.HProjective.IsHProjective.isHQuasiProjective`: H-projective implies H-quasi-projective.
* `Stacks.HProjective.IsHProjective.isSeparated`,
  `Stacks.HProjective.IsHQuasiProjective.isSeparated`: both are separated morphisms. This is the
  property of `𝐏(E) ⟶ S` that the proof of [Stacks, Tag 07RM] uses.
* `Stacks.HProjective.isHProjective_over`: `ℙⁿ_S ⟶ S` is itself H-projective, which is what makes
  the two equivalences above equivalences rather than implications.

## Implementation notes

**The projective bundle is generalised away, as in
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean`.** Tag 01W8's `IsProjective`
asserts a closed immersion over `S` into `𝐏(E)` for a finite-type quasi-coherent `E`, and
Tag 01OB's projective bundle has no unconditional form at this pin:
`Stacks.ProjectiveBundle.projectiveBundle` is relative to a `Stacks.ProjectiveBundle.Situation`,
whose relative-`Proj` axioms are unproved, and which rests on a symmetric algebra of a sheaf of
modules that is itself not constructed. The only property of the bundle
the source's reduction uses is that it is *some* `S`-scheme that the given closed immersion lands
in, so the reduction is stated over an arbitrary `S`-scheme instead, and is then independent of
how the bundle is eventually built.

**`IsHProjective` and `IsHQuasiProjective` are `def`s, not `abbrev`s**, matching
Tag 0C61's `IsProjectiveMorphism` (a `def`) rather than Tag 01VW's `IsHQuasiProjective` (an
`abbrev`). The existential data is reached through the lemmas below instead of by projection, so
no consumer depends on the unfolding.

**The structure morphism is written `↘ S` throughout.** `AlgebraicGeometry.projectiveSpaceOver`
is an `abbrev` for a `CategoryTheory.Limits.pullback`, and its
`AlgebraicGeometry.Scheme.CanonicallyOver` instance has `hom := pullback.fst _ _`, so `↘` is the
first projection by `rfl`. Writing `↘` rather than `pullback.fst` keeps the pullback out of the
statements, where it would otherwise invite instance search to unfold it.

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01MC](https://stacks.math.columbia.edu/tag/01MC)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.HProjective

/-! ### Separatedness of relative projective space -/

/-- **The integral model of projective space is separated.** This is Stacks Tag 01MC,
separatedness of `Proj` of a graded ring, at the polynomial ring in `n + 1` variables with its
grading by total degree.

The grading instance is supplied locally, exactly as in the definition of
`AlgebraicGeometry.projectiveSpaceAtUniverse`, because `MvPolynomial.gradedAlgebra` is not a
global instance; without it Mathlib's instance has nothing to match. -/
instance isSeparated_projectiveSpaceAtUniverse (n : ℕ) :
    Scheme.IsSeparated (projectiveSpaceAtUniverse.{u} n) := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact inferInstanceAs (Scheme.IsSeparated
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))))

/-- The canonical structure morphism of `ℙⁿ_S` is the first projection of the pullback defining
it. The two spellings both occur in the statements of Tags 0C61 and 01VW; they are the same morphism
by `rfl`. -/
theorem over_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    (projectiveSpaceOver n S ↘ S) =
      pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  rfl

/-- **`ℙⁿ_S` is separated over `S`.** Stacks Tag 01MC, transported along the base change from the
integers that defines `AlgebraicGeometry.projectiveSpaceOver`. -/
instance isSeparated_over (n : ℕ) (S : Scheme.{u}) :
    IsSeparated (projectiveSpaceOver n S ↘ S) := by
  change IsSeparated (pullback.fst (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} n)))
  infer_instance

/-! ### The two predicates -/

/-- **H-projectivity**: a closed immersion into some relative projective space over the base,
compatible with the structure morphisms. This is Tag 0C61's `IsProjectiveMorphism`, with the
relative projective space spelled by its library name. -/
def IsHProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
    IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = f

/-- **H-quasi-projectivity**: a quasi-compact immersion into some relative projective space over
the base, compatible with the structure morphisms. This is Tag 01VW's `IsHQuasiProjective`, with
the relative projective space spelled by its library name. -/
def IsHQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = f

/-- The structure morphism of `ℙⁿ_S` is H-projective: the identity is a closed immersion over
`S`. Recorded because it is what turns the two reductions below into equivalences. -/
theorem isHProjective_over (n : ℕ) (S : Scheme.{u}) :
    IsHProjective (projectiveSpaceOver n S ↘ S) :=
  ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩

/-! ### The reduction step -/

/-- **The hypothesis of Stacks Tag 087S part (1) with `𝐏(E)` generalised away.** There is a
scheme `P` over `S` and a closed immersion `X ⟶ P` over `S` with `P ⟶ S` H-projective.

Tag 01W8's `IsProjective` is the case `P = 𝐏(E)`; it implies this condition as soon as the
projective bundle is built and shown H-projective, and those are the only two properties of the
bundle the source's argument uses. The projective bundle has no library form at this pin — see
the module documentation — so this is the form in which the reduction is proved. -/
def HasHProjectiveClosedImmersion {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (P : Scheme.{u}) (p : P ⟶ S) (i : X ⟶ P),
    IsClosedImmersion i ∧ i ≫ p = f ∧ IsHProjective p

/-- The same with the closed immersion weakened to an immersion. Tag 07RM's conclusion — an open
immersion followed by a projective morphism — is an instance of this once the projective
morphism is known H-projective. -/
def HasHProjectiveImmersion {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (P : Scheme.{u}) (p : P ⟶ S) (i : X ⟶ P),
    IsImmersion i ∧ i ≫ p = f ∧ IsHProjective p

/-- **A closed immersion into an H-projective `S`-scheme is H-projective.** The composite of the
given closed immersion with the one into `ℙⁿ_S` is a closed immersion, and the structure
morphisms compose. -/
theorem IsHProjective.comp_isClosedImmersion {X S P : Scheme.{u}} (i : X ⟶ P)
    [IsClosedImmersion i] {p : P ⟶ S} (hp : IsHProjective p) : IsHProjective (i ≫ p) := by
  obtain ⟨n, j, hj, hjp⟩ := hp
  have := hj
  exact ⟨n, i ≫ j, inferInstance, by rw [Category.assoc, hjp]⟩

/-- **The reduction step of Stacks Tag 087S part (1), as an equivalence.** A morphism is
H-projective exactly when it factors as a closed immersion into an H-projective `S`-scheme.

The backward direction is the source's "by our definition of projective morphisms it suffices to
show that `𝐏(E) ⟶ S` is H-projective". The forward direction holds because `ℙⁿ_S ⟶ S` is itself
H-projective, so the condition is *equivalent* to H-projectivity and the reduction loses
nothing. -/
theorem isHProjective_iff_hasHProjectiveClosedImmersion {X S : Scheme.{u}} (f : X ⟶ S) :
    IsHProjective f ↔ HasHProjectiveClosedImmersion f := by
  constructor
  · rintro ⟨n, i, hi, hif⟩
    exact ⟨projectiveSpaceOver n S, _, i, hi, hif, isHProjective_over n S⟩
  · rintro ⟨P, p, i, hi, hip, hp⟩
    have := hi
    exact hip ▸ hp.comp_isClosedImmersion i

/-! ### H-quasi-projectivity -/

/-- **An immersion into an H-projective `S`-scheme with quasi-compact structure morphism is
H-quasi-projective.** The composite with the closed immersion into `ℙⁿ_S` is an immersion, and it
is quasi-compact because `f` is and `ℙⁿ_S ⟶ S` is separated, hence quasi-separated:
`AlgebraicGeometry.QuasiCompact.of_comp` cancels the structure morphism. -/
theorem isHQuasiProjective_of_hasHProjectiveImmersion {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : QuasiCompact f) (h : HasHProjectiveImmersion f) : IsHQuasiProjective f := by
  obtain ⟨P, p, i, hi, hip, n, j, hj, hjp⟩ := h
  have := hi
  have := hj
  have heq : (i ≫ j) ≫ (projectiveSpaceOver n S ↘ S) = f := by
    rw [Category.assoc, hjp, hip]
  have : QuasiCompact ((i ≫ j) ≫ (projectiveSpaceOver n S ↘ S)) := by rw [heq]; exact hf
  exact ⟨n, i ≫ j, inferInstance,
    QuasiCompact.of_comp (i ≫ j) (projectiveSpaceOver n S ↘ S), heq⟩

/-- **H-projective implies H-quasi-projective.** A closed immersion is affine, hence
quasi-compact, and is an immersion. -/
theorem IsHProjective.isHQuasiProjective {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsHProjective f) :
    IsHQuasiProjective f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have := hi
  exact ⟨n, i, inferInstance, inferInstance, hif⟩

/-- **An H-projective morphism is separated.** It factors as a closed immersion, which is a
monomorphism and hence separated, followed by the structure morphism of `ℙⁿ_S`, which is
separated by `Stacks.HProjective.isSeparated_over`.

This is the fact the proof of [Stacks, Tag 07RM] uses about `𝐏(E) ⟶ S` (through Schemes Lemma
26.21.14, [Stacks, Tag 03GI]), and it is the separatedness half of "projective implies
proper". -/
theorem IsHProjective.isSeparated {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsHProjective f) :
    IsSeparated f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have := hi
  exact hif ▸ inferInstance

/-- **An H-quasi-projective morphism is separated.** An immersion is a monomorphism, hence
separated, and `ℙⁿ_S ⟶ S` is separated. -/
theorem IsHQuasiProjective.isSeparated {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsHQuasiProjective f) : IsSeparated f := by
  obtain ⟨n, i, hi, -, hif⟩ := hf
  have := hi
  exact hif ▸ inferInstance

/-- **The reduction step for H-quasi-projectivity, as an equivalence.** A quasi-compact morphism
is H-quasi-projective exactly when it factors as an immersion into an H-projective `S`-scheme.

This is the content of the source's "Lemma 29.44.12 applies and we see that (1) implies (2)":
Tag 07RM factors a quasi-projective morphism as an open immersion followed by a projective
morphism, and part (1) of Tag 087S makes the second factor H-projective, at which point this
equivalence delivers H-quasi-projectivity. -/
theorem isHQuasiProjective_iff_hasHProjectiveImmersion {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : QuasiCompact f) : IsHQuasiProjective f ↔ HasHProjectiveImmersion f := by
  constructor
  · rintro ⟨n, i, hi, -, hif⟩
    exact ⟨projectiveSpaceOver n S, _, i, hi, hif, isHProjective_over n S⟩
  · exact isHQuasiProjective_of_hasHProjectiveImmersion hf

/-- **The factorisation Tag 07RM produces, turned into H-quasi-projectivity.** An immersion `j`
over `S` onto an H-projective morphism `p`, with `j ≫ p` quasi-compact, makes `j ≫ p`
H-quasi-projective. Stated separately from
`Stacks.HProjective.isHQuasiProjective_of_hasHProjectiveImmersion` because this is the shape a
factorisation is produced in, with no existential to introduce. -/
theorem isHQuasiProjective_comp_of_isHProjective {X S X' : Scheme.{u}} (j : X ⟶ X')
    [IsImmersion j] {p : X' ⟶ S} (hp : IsHProjective p) (hqc : QuasiCompact (j ≫ p)) :
    IsHQuasiProjective (j ≫ p) :=
  isHQuasiProjective_of_hasHProjectiveImmersion hqc ⟨X', p, j, ‹_›, rfl, hp⟩

end Stacks.HProjective

end

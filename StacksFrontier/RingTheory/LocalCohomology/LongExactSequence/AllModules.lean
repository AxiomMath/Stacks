module

public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension

/-!
# Vanishing of local cohomology for every module

Let `I` be a finitely generated ideal of a commutative ring `A` and `Y = V(I)`. The first two of
the three equivalent conditions of [Stacks, Tag 0DX7] are

1. `H^i_Y(A) = 0` for all `i > d`;
2. `H^i_Y(M) = 0` for all `i > d`, for every `A`-module `M`.

This file proves that they are equivalent. That (2) implies (1) is immediate up to a change of
universe, and the other direction is the descending induction of the source: local cohomology
has finite cohomological dimension, so the vanishing holds for every module in degrees above the
number of generators of `I`, and from there one descends. The induction step fits an arbitrary
module `M` into a short exact sequence `0 → N → F → M → 0` with `F` free, notes that `H^i_Y(F) = 0`
because local cohomology commutes with direct sums, and reads `H^i_Y(M) = 0` off the long exact
sequence together with `H^{i+1}_Y(N) = 0`, which is the inductive hypothesis one degree up.

Three inputs make this work, and all three are recent additions:

* `Stacks.LocalCohomology.isZero_homology_localCohomology_directSum` — local cohomology commutes
  with direct sums, which for `RΓ_Y` a *right* adjoint is not formal and comes from the Čech
  model.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_of_shortExact` — the long exact
  sequence.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_uliftModule_iff` — the comparison
  between local cohomology in `ModuleCat.{u} A` and in `ModuleCat.{max u v} A`, needed because
  condition (1) is about the module `A` itself while condition (2) quantifies over a larger
  universe, and the free module of the induction is a direct sum of copies of `ULift.{v} A`.

## Main results

* `Stacks.LocalCohomology.exists_shortExact_freePresentation` — every module is a quotient of a
  direct sum of copies of `A`.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_free` — local cohomology of such a
  direct sum vanishes in a degree as soon as it does for `A`.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_of_isZero_homology_self` — **(1) implies
  (2)**: the descending induction of Tag 0DX7.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_forall_iff` — **(1) ⇔ (2) of Tag
  0DX7**.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_of_isLocalCohomologyBound` — the same
  statement phrased through `Stacks.LocalCohomology.IsLocalCohomologyBound`, the predicate the
  cohomological dimension of Tag 0DX8 is defined from.

## Implementation notes

No `@[stacks 0DX7]` attribute is placed: the tagged statement is a three-way equivalence, and the
third condition — a vanishing of sheaf cohomology of quasi-coherent modules on `Spec A \ V(I)` —
is not proved here. What is proved is the equivalence of the first two, which is the part of the
source's proof that rests on the algebra of local cohomology.

The free presentation is built inside the existence statement rather than exposed as a definition,
because `DirectSum.toModule` needs a `DecidableEq` instance on the index type and nothing
downstream depends on which one is chosen.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- **Every module is a quotient of a free module.** For an `A`-module `M` the direct sum of one
copy of `A` for every element of `M`, sending the copy indexed by `m` to `m`, is surjective; the
resulting short exact sequence `0 → N → F → M → 0` is the one the induction of
[Stacks, Tag 0DX7] uses. The copies of `A` are universe-lifted so that the free module lies in the
same universe as `M`. -/
theorem exists_shortExact_freePresentation (M : ModuleCat.{max u v} A) :
    ∃ (J : Type (max u v)) (S : ShortComplex (ModuleCat.{max u v} A)),
      S.ShortExact ∧
      S.X₂ = ModuleCat.of A (DirectSum J fun _ : J => ULift.{v} A) ∧ S.X₃ = M := by
  classical
  set π : (DirectSum (M : Type (max u v)) fun _ => ULift.{v} A) →ₗ[A] M :=
    DirectSum.toModule A _ _ fun m =>
      (LinearMap.toSpanSingleton A M m).comp
        (ULift.moduleEquiv : ULift.{v} A ≃ₗ[A] A).toLinearMap with hπ
  have hsurj : Function.Surjective π := by
    intro m
    refine ⟨DirectSum.lof A _ _ m (ULift.up 1), ?_⟩
    rw [hπ, DirectSum.toModule_lof]
    simp
  exact ⟨_, π.shortComplexKer, LinearMap.shortExact_shortComplexKer hsurj, rfl, rfl⟩

/-- **Local cohomology of a free module.** If the local cohomology of `ULift.{v} A` vanishes in
degree `i`, so does that of any direct sum of copies of it. This is
`Stacks.LocalCohomology.isZero_homology_localCohomology_directSum` for a constant family. -/
theorem isZero_homology_localCohomology_free
    {r : ℕ} (f : Fin r → A) (I : Ideal A) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I)
    (J : Type (max u v)) (i : ℤ)
    (h : IsZero (localCohomologyModule A I hI (ModuleCat.of A (ULift.{v} A)) i)) :
    IsZero (localCohomologyModule A I hI
      (ModuleCat.of A (DirectSum J fun _ : J => ULift.{v} A)) i) :=
  isZero_homology_localCohomology_directSum f (fun _ : J => ULift.{v} A) I hI hIf i fun _ => h

/-- **(1) implies (2) of [Stacks, Tag 0DX7].** Let `I` be a finitely generated ideal of `A` and
`Y = V(I)`. If `H^i_Y(A) = 0` for every `i > d`, then `H^i_Y(M) = 0` for every `i > d` and every
`A`-module `M`, in any universe.

This is the descending induction of the source. Local cohomology vanishes above the number `r` of
generators of `I` for every module, which starts the induction; the step writes `M` as a quotient
of a free module `F`, where `H^i_Y(F) = 0` because local cohomology commutes with direct sums, and
reads `H^i_Y(M) = 0` off the long exact sequence using `H^{i+1}_Y(N) = 0`. Degrees `i < 0` are
immediate, so no lower bound on `d` is needed. -/
theorem isZero_homology_localCohomology_of_isZero_homology_self
    (I : Ideal A) (hI : I.FG) (d : ℤ)
    (h₁ : ∀ i : ℤ, d < i → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i))
    (M : ModuleCat.{max u v} A) (i : ℤ) (hi : d < i) :
    IsZero (localCohomologyModule A I hI M i) := by
  classical
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  have hU : ∀ j : ℤ, d < j →
      IsZero (localCohomologyModule A I hI (ModuleCat.of A (ULift.{v} A)) j) := fun j hj =>
    (isZero_homology_localCohomology_uliftModule_iff f I hI hf (ModuleCat.of A A) j).1 (h₁ j hj)
  have key : ∀ k : ℕ, ∀ (N : ModuleCat.{max u v} A) (j : ℤ), d < j → (r : ℤ) + 1 - k ≤ j →
      IsZero (localCohomologyModule A I hI N j) := by
    intro k
    induction k with
    | zero =>
        intro N j _ hj
        refine isZero_homology_localCohomology_of_outside_range f N I hI hf j (Or.inr ?_)
        push_cast at hj
        omega
    | succ k ih =>
        intro N j hjd hj
        obtain ⟨J, S, hS, hX₂, hX₃⟩ := exists_shortExact_freePresentation.{v} N
        have hF : IsZero (localCohomologyModule A I hI S.X₂ j) := by
          rw [hX₂]
          exact isZero_homology_localCohomology_free f I hI hf J j (hU j hjd)
        have hN : IsZero (localCohomologyModule A I hI S.X₁ (j + 1)) := by
          refine ih S.X₁ (j + 1) (by omega) ?_
          push_cast at hj ⊢
          omega
        have hM := isZero_homology_localCohomology_of_shortExact f S I hI hf hS j hF hN
        rwa [hX₃] at hM
  rcases lt_or_ge i 0 with hneg | hpos
  · exact isZero_homology_localCohomology_of_outside_range f M I hI hf i (Or.inl hneg)
  · refine key (r + 1) M i hi ?_
    push_cast
    omega

/-- **(1) ⇔ (2) of [Stacks, Tag 0DX7].** For a finitely generated ideal `I` of `A` and
`Y = V(I)`, the local cohomology `H^i_Y(A)` vanishes for all `i > d` if and only if `H^i_Y(M)`
does for every `A`-module `M`.

The two sides are statements about two different derived categories: the left about
`ModuleCat.{u} A`, the right about `ModuleCat.{max u v} A`. The implication from right to left is
obtained by applying the right-hand side to `ULift.{v} A` and comparing universes. -/
theorem isZero_homology_localCohomology_forall_iff
    (I : Ideal A) (hI : I.FG) (d : ℤ) :
    (∀ i : ℤ, d < i → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i)) ↔
      ∀ (M : ModuleCat.{max u v} A) (i : ℤ), d < i →
        IsZero (localCohomologyModule A I hI M i) := by
  refine ⟨fun h₁ M i hi =>
    isZero_homology_localCohomology_of_isZero_homology_self I hI d h₁ M i hi, fun h₂ i hi => ?_⟩
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  exact (isZero_homology_localCohomology_uliftModule_iff f I hI hf (ModuleCat.of A A) i).2
    (h₂ (ModuleCat.of A (ULift.{v} A)) i hi)

/-- **(1) implies (2) of [Stacks, Tag 0DX7], phrased through
`Stacks.LocalCohomology.IsLocalCohomologyBound`.** A vanishing bound for the local cohomology of
`A` is a vanishing bound for the local cohomology of every `A`-module; in particular the
cohomological dimension of Tag 0DX8 bounds the vanishing degrees for all modules at once. -/
theorem isZero_homology_localCohomology_of_isLocalCohomologyBound
    (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : IsLocalCohomologyBound A I hI d)
    (M : ModuleCat.{max u v} A) (i : ℤ) (hi : d < i) :
    IsZero (localCohomologyModule A I hI M i) :=
  isZero_homology_localCohomology_of_isZero_homology_self I hI d hd.2 M i hi

end Stacks.LocalCohomology

end

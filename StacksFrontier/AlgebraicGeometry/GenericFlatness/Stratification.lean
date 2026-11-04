module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.RingTheory.Flat.GenericFlatness

/-!
# Towards the generic flatness stratification

Stacks 0H3Z asks, for a morphism `f : X ⟶ S` of finite presentation between quasi-compact and
quasi-separated schemes, for a chain of closed subschemes
`S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`, each cut out by a finite type ideal sheaf, with `S₀ ⊆ S` a
thickening and `X ×_S (S_i ∖ S_{i+1})` flat over `S_i ∖ S_{i+1}`. It is the special case
`ℱ = 𝒪_X` of Stacks 0ASY.

This file collects the two ingredients of the 0ASY argument that are available from the material
already in the library, namely the *flatness* form of generic flatness over a reduced base
(Stacks 051Z) and the *termination* of the stratification induction over a Noetherian space.

## Main results

* `Algebra.IsFinitePresentationFreeAway.flat` and
  `Algebra.IsFinitePresentationFreeAway.flat_tensor`: after inverting a good `f`, the ring and the
  module are flat, not merely free, over `R_f`.
* `Algebra.exists_isOpen_dense_flat`: the flatness form of Stacks 051Z — a dense open
  `U ⊆ Spec R` each of whose points has a standard open neighbourhood `D(f) ⊆ U` over which `S`
  and `M` become flat.
* `Stacks.GenericFlatness.exists_strata`: the stratification induction. Over a Noetherian space,
  removing from a closed set an open set that meets it, and iterating, reaches the empty set in
  finitely many steps. This is the "we continue in this way; because `S` is Noetherian any
  descending chain of closed subsets stabilizes" step of the proof of Stacks 0ASY, with the
  generic flatness input abstracted into the open set `U Z` removed at the stratum `Z`.

## Implementation notes

The stratification induction is stated for an abstract assignment `U : Closeds α → Opens α` of an
open set to each closed set, with the single hypothesis that `U Z` meets `Z` whenever `Z` is
nonempty. Density of `U Z` in `Z`, which is what generic flatness supplies, is not needed for the
chain to terminate — only nonemptiness is — and the conclusion records the strata as the iterates
of `Z ↦ Z ∖ U Z`, so that the properties of `U` transfer to them.

## Where Stacks 0H3Z is proved

Both remaining inputs of Stacks 0ASY are in the library: Stacks 052B is proved and tagged in
`StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness`, and the absolute
Noetherian approximation by which 0ASY reduces a quasi-compact quasi-separated base to one of
finite type over `ℤ` is carried out in
`StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationQcqs`. The tag itself is
`AlgebraicGeometry.HasFlatStratification.of_finitePresentation`, and the conclusion it produces
is `AlgebraicGeometry.HasFlatStratification`.

## References

* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 051Z](https://stacks.math.columbia.edu/tag/051Z)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
-/

@[expose] public section

open TensorProduct TopologicalSpace

namespace Algebra

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]
  {f : R}

/-- If `f` satisfies the condition of Stacks 051U then `S_f` is flat over `R_f`. -/
theorem IsFinitePresentationFreeAway.flat (h : IsFinitePresentationFreeAway R S M f) :
    Module.Flat (Localization.Away f)
      (Localization (algebraMapSubmonoid S (Submonoid.powers f))) :=
  have := h.2.2.1
  Module.Flat.of_free

/-- If `f` satisfies the condition of Stacks 051U then `M_f = S_f ⊗[S] M` is flat over `R_f`. -/
theorem IsFinitePresentationFreeAway.flat_tensor (h : IsFinitePresentationFreeAway R S M f) :
    Module.Flat (Localization.Away f)
      (Localization (algebraMapSubmonoid S (Submonoid.powers f)) ⊗[S] M) :=
  have := h.2.2.2
  Module.Flat.of_free

/-- **The flatness form of Stacks 051Z.** Let `R → S` be of finite type with `R` reduced and let
`M` be a finite `S`-module. Then there is a dense open `U ⊆ Spec R` such that every point of `U`
has a standard open neighbourhood `D(f) ⊆ U` over which both `S` and `M` become flat.

This is the input that Stacks 052B globalizes; `Algebra.exists_isOpen_dense_flat` discards the
finite presentation half of `Algebra.exists_isOpen_dense_isFinitePresentationFreeAway` and
weakens its freeness half to flatness. -/
theorem exists_isOpen_dense_flat [IsReduced R] [Algebra.FiniteType R S] [Module.Finite S M] :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ Dense U ∧
      ∀ u ∈ U, ∃ f : R, u ∈ PrimeSpectrum.basicOpen f ∧
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ U ∧
        Module.Flat (Localization.Away f)
          (Localization (algebraMapSubmonoid S (Submonoid.powers f))) ∧
        Module.Flat (Localization.Away f)
          (Localization (algebraMapSubmonoid S (Submonoid.powers f)) ⊗[S] M) := by
  obtain ⟨U, hUopen, hUdense, hU⟩ :=
    exists_isOpen_dense_isFinitePresentationFreeAway (R := R) (S := S) (M := M)
  refine ⟨U, hUopen, hUdense, fun u hu => ?_⟩
  obtain ⟨f, hfu, hfU, hf⟩ := hU u hu
  exact ⟨f, hfu, hfU, hf.flat, hf.flat_tensor⟩

end Algebra

namespace Stacks.GenericFlatness

variable {α : Type*} [TopologicalSpace α]

/-- One step of the stratification: remove from a closed set the open set assigned to it. -/
private def stratumStep (U : Closeds α → Opens α) (Z : Closeds α) : Closeds α :=
  Z ⊓ (U Z).compl

private theorem coe_stratumStep (U : Closeds α → Opens α) (Z : Closeds α) :
    (stratumStep U Z : Set α) = (Z : Set α) \ (U Z : Set α) :=
  rfl

/-- **The stratification induction of Stacks 0ASY.** Let `α` be a Noetherian space and assign to
every closed subset `Z` an open subset `U Z` which meets `Z` whenever `Z` is nonempty. Then
iterating `Z ↦ Z ∖ U Z` from any closed set reaches the empty set after finitely many steps.

In Stacks 0ASY the space is the base `S`, the closed sets are the strata `S_i` and `U Z` is the
dense open of `Z` over which the given module becomes flat, supplied by generic flatness; the
conclusion is the chain `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`. -/
theorem exists_strata [NoetherianSpace α] (U : Closeds α → Opens α)
    (hU : ∀ Z : Closeds α, Z ≠ ⊥ → ((Z : Set α) ∩ (U Z : Set α)).Nonempty) (Z₀ : Closeds α) :
    ∃ (t : ℕ) (Z : ℕ → Closeds α), Z 0 = Z₀ ∧ Z t = ⊥ ∧ Antitone Z ∧
      ∀ i, (Z (i + 1) : Set α) = (Z i : Set α) \ (U (Z i) : Set α) := by
  have hlt : ∀ Z : Closeds α, Z ≠ ⊥ → stratumStep U Z < Z := by
    intro Z hZ
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    obtain ⟨x, hxZ, hxU⟩ := hU Z hZ
    have hx : x ∈ (stratumStep U Z : Set α) := by rw [heq]; exact hxZ
    rw [coe_stratumStep] at hx
    exact hx.2 hxU
  have key : ∀ Z : Closeds α, ∃ t, (stratumStep U)^[t] Z = ⊥ := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | _ Z ih =>
      by_cases hZ : Z = ⊥
      · exact ⟨0, hZ⟩
      · obtain ⟨t, ht⟩ := ih _ (hlt Z hZ)
        exact ⟨t + 1, by rw [Function.iterate_succ_apply, ht]⟩
  have hstep : ∀ j, ((stratumStep U)^[j + 1] Z₀ : Set α)
      = ((stratumStep U)^[j] Z₀ : Set α) \ (U ((stratumStep U)^[j] Z₀) : Set α) := by
    intro j
    rw [Function.iterate_succ_apply', coe_stratumStep]
  obtain ⟨t, ht⟩ := key Z₀
  refine ⟨t, fun i => (stratumStep U)^[i] Z₀, rfl, ht, ?_, fun i => hstep i⟩
  refine antitone_nat_of_succ_le fun i => ?_
  rw [Function.iterate_succ_apply']
  exact inf_le_left

end Stacks.GenericFlatness

end

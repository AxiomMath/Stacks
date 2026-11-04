module

public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.ClosedPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's criterion for affineness, reduced to its two cohomological inputs

Serre's criterion [Stacks, Tag 01XF] says that a quasi-compact scheme `X` with
`H¹(X, 𝓘) = 0` for every quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X` is affine. Its proof uses the
vanishing hypothesis in exactly two places:

1. to produce, for a closed point `x` and an affine open `U ∋ x`, a global section
   `r ∈ Γ(X, 𝓘)` with `x ∈ X_r ⊆ U` — whence `X_r` is a basic open of the affine `U` and so
   affine. This uses `H¹(X, 𝓘') = 0` for `𝓘'` the ideal sheaf of the reduced closed subscheme
   `(X ∖ U) ∪ {x}`;
2. to pass from a *cover* `X = X_{r_1} ∪ … ∪ X_{r_n}` by affine basic opens to the stronger
   statement that `r_1, …, r_n` generate the unit ideal of `Γ(X, ⊤)`. This uses
   `H¹(X, ℱ) = 0` for `ℱ` the kernel of `𝒪_X^{⊕n} → 𝒪_X`, which is filtered by quasi-coherent
   sheaves of ideals.

Everything else in that proof is topology and Mathlib's
`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`. This file carries out all of it, taking
the two consequences above as hypotheses. No cohomology occurs, and the file is therefore
available at a pin where `H¹` of a quasi-coherent sheaf on a scheme is not yet connected to
affineness.

## Main results

* `Stacks.SerreAffinenessCriterion.exists_finset_isAffineOpen_basicOpen`: a quasi-compact scheme
  covered by affine basic opens of global sections is covered by *finitely many* of them.
* `Stacks.SerreAffinenessCriterion.isQuasiAffine_of_forall_isClosed_singleton`: input (1) alone
  makes `X` quasi-affine.
* `Stacks.SerreAffinenessCriterion.isAffine_of_forall_isClosed_singleton_of_span_eq_top`: inputs
  (1) and (2) together make `X` affine. This is Serre's criterion with the cohomology extracted.

## What is not done

**[Stacks, Tag 01XF] is not proved here, and is not stated here.** The two hypotheses `H₁` and
`H₂` below are *consequences* of the vanishing hypothesis of that lemma, not substitutes for it,
and deriving either of them is the open work; see the module documentation of
`StacksDraft.AlgebraicGeometry.F3.Tag01YQ.Chevalley` for the precise missing declarations. In
particular no `@[stacks]` attribute is attached in this file: the covering set of 01XF is not
proved by it.

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 01QF](https://stacks.math.columbia.edu/tag/01QF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SerreAffinenessCriterion

variable (X : Scheme.{u})

/-- **A quasi-compact scheme covered by affine basic opens of global sections is covered by
finitely many of them.** -/
theorem exists_finset_isAffineOpen_basicOpen [CompactSpace X]
    (H : ∀ x : X, ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) :
    ∃ s : Finset Γ(X, ⊤), (∀ r ∈ s, IsAffineOpen (X.basicOpen r)) ∧
      (⨆ r ∈ s, X.basicOpen r) = ⊤ := by
  classical
  have hcov : (Set.univ : Set X) ⊆
      ⋃ t : {r : Γ(X, ⊤) // IsAffineOpen (X.basicOpen r)}, (X.basicOpen t.1 : Set X) := by
    intro x _
    obtain ⟨r, hr, hx⟩ := H x
    exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hx⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun u : {r : Γ(X, ⊤) // IsAffineOpen (X.basicOpen r)} ↦ (X.basicOpen u.1 : Set X))
    (fun u ↦ (X.basicOpen u.1).2) hcov
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro r hr
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hr
    exact hu ▸ u.2
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨u, hu, hxu⟩ : ∃ u ∈ t, x ∈ (X.basicOpen u.1 : Set X) := by
      simpa using ht (Set.mem_univ x)
    exact Opens.mem_iSup.mpr ⟨u.1, Opens.mem_iSup.mpr ⟨Finset.mem_image_of_mem _ hu, hxu⟩⟩

variable {X} in
/-- **A basic open of a global section contained in an affine open is affine.** This is the step
that turns the output of the first paragraph of [Stacks, Tag 01XF] — a global section `r` with
`x ∈ X_r ⊆ U` for an affine open `U` — into the hypothesis `H₁` below: `X_r` is cut out inside
`U` by the restriction of `r`, hence is a basic open of an affine open. -/
theorem isAffineOpen_basicOpen_of_le {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, ⊤))
    (hrU : X.basicOpen r ≤ U) : IsAffineOpen (X.basicOpen r) := by
  have h := hU.basicOpen (X.presheaf.map (homOfLE (le_top (a := U))).op r)
  rwa [X.basicOpen_res, inf_eq_right.mpr hrU] at h

/-- **The hypothesis `H₁` in the shape [Stacks, Tag 01XF] produces it.** If every closed point of
a quasi-compact scheme lies in a basic open of a global section which is *contained in some
affine open*, then every point of `X` lies in an affine basic open of a global section. -/
@[ega "II 5.1.2" "d) ⇒ d')"]
theorem exists_isAffineOpen_basicOpen_mem_of_le [CompactSpace X]
    (H : ∀ x : X, IsClosed ({x} : Set X) → ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧
      ∃ U : X.Opens, IsAffineOpen U ∧ X.basicOpen r ≤ U) (x : X) :
    ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r :=
  exists_isAffineOpen_basicOpen_mem X
    (fun y hy ↦ (H y hy).imp fun r ⟨hyr, _U, hU, hrU⟩ ↦
      ⟨isAffineOpen_basicOpen_of_le hU r hrU, hyr⟩) x

/-- **Input (1) of Serre's criterion makes `X` quasi-affine.** If every closed point of a
quasi-compact scheme lies in an affine basic open of a global section, then `X ⟶ Spec Γ(X, ⊤)` is
an open immersion. -/
@[ega "II 5.1.2" "d') ⇒ a)"]
theorem isQuasiAffine_of_forall_isClosed_singleton [CompactSpace X]
    (H₁ : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) :
    X.IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X
    (exists_isAffineOpen_basicOpen_mem X H₁)

/-- **Serre's criterion for affineness with its two cohomological inputs as hypotheses.** A
quasi-compact scheme is affine as soon as

* `H₁`: every closed point lies in an affine basic open of a global section, and
* `H₂`: whenever finitely many global sections whose basic opens are affine cover `X`, those
  sections generate the unit ideal.

Both hypotheses follow from the vanishing of `H¹(X, 𝓘)` on quasi-coherent sheaves of ideals;
neither is proved here. -/
theorem isAffine_of_forall_isClosed_singleton_of_span_eq_top [CompactSpace X]
    (H₁ : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r)
    (H₂ : ∀ s : Finset Γ(X, ⊤), (∀ r ∈ s, IsAffineOpen (X.basicOpen r)) →
      (⨆ r ∈ s, X.basicOpen r) = ⊤ → Ideal.span (s : Set Γ(X, ⊤)) = ⊤) :
    IsAffine X := by
  obtain ⟨s, hs, hcov⟩ :=
    exists_finset_isAffineOpen_basicOpen X (exists_isAffineOpen_basicOpen_mem X H₁)
  exact isAffine_of_isAffineOpen_basicOpen (s : Set Γ(X, ⊤)) (H₂ s hs hcov) hs

/-- The converse of hypothesis `H₂` of
`Stacks.SerreAffinenessCriterion.isAffine_of_forall_isClosed_singleton_of_span_eq_top` is
unconditional: a spanning family of global sections has covering basic opens. Recorded so that `H₂`
is visibly an equivalence on an affine scheme and is therefore not a disguised extra assumption. -/
theorem iSup_basicOpen_eq_top_of_span_eq_top {s : Finset Γ(X, ⊤)}
    (hs : Ideal.span (s : Set Γ(X, ⊤)) = ⊤) : (⨆ r ∈ s, X.basicOpen r) = ⊤ :=
  iSup_basicOpen_of_span_eq_top _ _ hs

end Stacks.SerreAffinenessCriterion

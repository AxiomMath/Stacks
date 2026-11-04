module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The induction principle for quasi-compact opens of a scheme

Let `X` be a scheme and let `P` be a property of the open subsets of `X`. Suppose that

* `P U` holds for every affine open `U`, and
* `P (U ⊔ V)` holds whenever `U` is a quasi-compact open, `V` is an affine open, and `P U`,
  `P V` and `P (U ⊓ V)` hold.

Then `P U` holds for every quasi-compact open `U` of `X`, provided `X` is quasi-separated. This
is [Stacks, Tag 08DR], the induction principle that organises the proof of quasi-coherence of
higher direct images [Stacks, Tag 01XJ].

Mathlib already has `AlgebraicGeometry.compact_open_induction_on`, which is the same induction
with the *weaker* hypothesis `P U → P (U ⊔ V)`; that form is not strong enough for the
applications, which produce `P (U ⊔ V)` only from a Mayer–Vietoris sequence relating all three
of `U`, `V` and `U ⊓ V`. The extra work is therefore entirely in supplying `P (U ⊓ V)`, and the
proof is the two-step argument of the source:

* `of_le_isAffineOpen`: if `S` is a quasi-compact open contained in an affine open `W`, then
  `P S` holds. Here `S` is a *finite union of basic opens of `W`*, and basic opens are closed
  under intersection, `D(f) ⊓ D(g) = D(f * g)`, so the intersections appearing in the induction
  are again finite unions of basic opens of `W` and the induction closes on itself. This replaces
  the source's appeal to [Stacks, Tag 01KP] (two affine opens of a separated scheme meet in an
  affine open): the only separated schemes it is applied to there are affine, and inside an
  affine scheme the basic opens already suffice.
* `of_isCompact`: the general case. For `S` quasi-compact and `U` affine, `S ⊓ U` is a
  quasi-compact open — this is exactly where quasi-separatedness of `X` enters — contained in the
  affine open `U`, so the previous step applies.

## Main results

* `Stacks.AlgebraicGeometry.CompactOpenInduction.of_iSup_basicOpen`: `P` holds for a finite
  union of basic opens of an affine open.
* `Stacks.AlgebraicGeometry.CompactOpenInduction.of_le_isAffineOpen`: `P` holds for a
  quasi-compact open contained in an affine open.
* `Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact`: **[Stacks, Tag 08DR]**, `P`
  holds for every quasi-compact open of a quasi-separated scheme.
* `Stacks.AlgebraicGeometry.CompactOpenInduction.top`: `P ⊤` for a quasi-compact quasi-separated
  scheme.
* `Stacks.AlgebraicGeometry.CompactOpenInduction.top_of_qcqs_over_affine`: `P ⊤` for the source
  of a quasi-compact quasi-separated morphism to an affine scheme. This is the form in which
  [Stacks, Tag 01XJ] consumes the principle, after its reduction to an affine base.

## Implementation notes

The induction in `of_iSup_basicOpen` is on a natural number bounding the cardinality of the
indexing finite set, rather than directly on the finite set: the inductive step is applied not
only to a smaller set but also, for the intersection, to a *different family of sections* over
the same smaller set, which `Finset.induction_on` cannot supply. The index type is held fixed
and only the family `g : ι → Γ(X, W)` varies, which avoids taking images of finite sets.

## References

* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CompactOpenInduction

variable {X : Scheme.{u}} {P : X.Opens → Prop}
  (h₁ : ∀ U : X.Opens, IsAffineOpen U → P U)
  (h₂ : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
    P U → P V → P (U ⊓ V) → P (U ⊔ V))

include h₁ h₂ in
/-- **The affine step of [Stacks, Tag 08DR].** If `P` holds for affine opens and is stable under
the Mayer–Vietoris union step, then `P` holds for every finite union of basic opens
`X.basicOpen (g i)` of an affine open `W`.

The point is that this class of opens is stable under the intersections the induction creates:
`(⨆ i ∈ s, D (g i)) ⊓ D (g a) = ⨆ i ∈ s, D (g i * g a)`. -/
theorem of_iSup_basicOpen {W : X.Opens} (hW : IsAffineOpen W) {ι : Type*} :
    ∀ (n : ℕ) (s : Finset ι) (g : ι → Γ(X, W)), s.card ≤ n →
      P (⨆ i ∈ s, X.basicOpen (g i)) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s g hs
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simpa using h₁ ⊥ (isAffineOpen_bot X)
    · have hcard : (s.erase a).card < n := by
        have := Finset.card_erase_of_mem ha
        have := Finset.card_pos.mpr ⟨a, ha⟩
        omega
      have key : (⨆ i ∈ s, X.basicOpen (g i))
          = (⨆ i ∈ s.erase a, X.basicOpen (g i)) ⊔ X.basicOpen (g a) := by
        conv_lhs => rw [← Finset.insert_erase ha]
        rw [Finset.iSup_insert, sup_comm]
      rw [key]
      refine h₂ _ _ ?_ (hW.basicOpen _) (ih _ hcard _ _ le_rfl) (h₁ _ (hW.basicOpen _)) ?_
      · simp only [Opens.coe_iSup]
        exact Set.Finite.isCompact_biUnion (s.erase a).finite_toSet
          fun i _ => (hW.basicOpen (g i)).isCompact
      · have e : (⨆ i ∈ s.erase a, X.basicOpen (g i)) ⊓ X.basicOpen (g a)
            = ⨆ i ∈ s.erase a, X.basicOpen (g i * g a) := by
          simp only [iSup_inf_eq, ← Scheme.basicOpen_mul]
        rw [e]
        exact ih _ hcard _ _ le_rfl

include h₁ h₂ in
/-- **The separated case of [Stacks, Tag 08DR].** `P` holds for every quasi-compact open `S`
contained in an affine open `W`: such an `S` is a finite union of basic opens of `W`, so
`of_iSup_basicOpen` applies. -/
theorem of_le_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) (S : X.Opens)
    (hS : IsCompact (S : Set X)) (hSW : S ≤ W) : P S := by
  classical
  choose F hF₁ hF₂ using fun x : S => hW.exists_basicOpen_le (V := S) x (hSW x.2)
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun x : S => (X.basicOpen (F x) : Set X))
    (fun x => (X.basicOpen (F x)).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hF₂ ⟨x, hx⟩⟩)
  have hSeq : S = ⨆ i ∈ s, X.basicOpen (F i) := by
    refine le_antisymm (fun x hx => ?_) (iSup_le fun i => iSup_le fun _ => hF₁ i)
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Opens.mem_iSup.2 ⟨i, Opens.mem_iSup.2 ⟨hi, hxi⟩⟩
  rw [hSeq]
  exact of_iSup_basicOpen h₁ h₂ hW s.card s F le_rfl

include h₁ h₂ in
/-- **[Stacks, Tag 08DR], the induction principle.** Let `X` be a quasi-separated scheme and let
`P` be a property of its open subsets such that `P` holds for every affine open, and such that
`P (U ⊔ V)` holds whenever `U` is quasi-compact open, `V` is affine open and `P U`, `P V`,
`P (U ⊓ V)` hold. Then `P` holds for every quasi-compact open of `X`.

Only the hypothesis `P (U ⊓ V)` has to be produced beyond what
`AlgebraicGeometry.compact_open_induction_on` already supplies, and `U ⊓ V` is a quasi-compact
open of the affine open `V`, so `of_le_isAffineOpen` produces it. -/
@[stacks 08DR "induction on quasi-compact opens"]
theorem of_isCompact [QuasiSeparatedSpace X] (S : X.Opens) (hS : IsCompact (S : Set X)) : P S := by
  refine compact_open_induction_on S hS (h₁ ⊥ (isAffineOpen_bot X)) ?_
  intro T hT U hTP
  have hcpt : IsCompact ((T ⊓ (U : X.Opens) : X.Opens) : Set X) :=
    QuasiSeparatedSpace.inter_isCompact (T : Set X) (U : X.Opens) T.isOpen hT
      (U : X.Opens).isOpen U.2.isCompact
  exact h₂ T U hT U.2 hTP (h₁ _ U.2)
    (of_le_isAffineOpen h₁ h₂ U.2 (T ⊓ (U : X.Opens)) hcpt inf_le_right)

include h₁ h₂ in
/-- **[Stacks, Tag 08DR], the conclusion at `X` itself.** For a quasi-compact quasi-separated
scheme, `P ⊤` holds. -/
@[stacks 08DR "induction on quasi-compact opens"]
theorem top [QuasiSeparatedSpace X] [CompactSpace X] : P ⊤ :=
  of_isCompact h₁ h₂ ⊤ (by rw [Opens.coe_top]; exact isCompact_univ)

include h₁ h₂ in
/-- The form in which [Stacks, Tag 01XJ] uses the induction principle: after the reduction to an
affine base, `f : X ⟶ S` is a quasi-compact quasi-separated morphism onto an affine scheme, so
`X` is itself quasi-compact and quasi-separated and `P ⊤` holds. -/
theorem top_of_qcqs_over_affine {S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] : P ⊤ :=
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).1 inferInstance
  top h₁ h₂

end Stacks.AlgebraicGeometry.CompactOpenInduction

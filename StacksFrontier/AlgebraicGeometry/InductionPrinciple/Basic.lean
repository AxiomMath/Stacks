module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute

/-!
# The induction principle for quasi-compact quasi-separated schemes

Let `X` be a quasi-separated scheme and let `P` be a property of the opens of `X`. [Stacks,
Tag 08DR] asserts that `P` holds for every quasi-compact open of `X` as soon as

* `P` holds for every affine open, and
* `P` holds for `U ⊔ V` whenever `U` is a quasi-compact open, `V` is an affine open, and `P`
  holds for `U`, for `V` and for `U ⊓ V`.

Mathlib's `AlgebraicGeometry.compact_open_induction_on` is a strictly weaker principle: its
induction step has to produce `P (U ⊔ V)` from `P U` alone, with no access to `P V` or to
`P (U ⊓ V)`. The strengthening here is what the cohomological arguments of Chapter 30 use,
where the induction step is a Mayer–Vietoris sequence and therefore needs all three.

The proof is the one in the source, organized so that no separatedness hypothesis has to be
introduced. The source argues first for separated quasi-compact opens, where the intersection
of two affine opens is affine. That step is replaced here by an induction over finite families
of *basic* opens of one fixed affine open: such a family is closed under intersection, because
`X.basicOpen g ⊓ X.basicOpen h = X.basicOpen (g * h)`, and every member is affine. The general
case then follows by induction on the number of affine opens needed to cover the given
quasi-compact open, the intersections that arise being quasi-compact opens of a single affine
open and hence finite unions of basic opens of it. Quasi-separatedness enters exactly once, to
know that those intersections are quasi-compact.

## Main results

* `Stacks.AlgebraicGeometry.InductionPrinciple.isCompact_biSup`: a finite union of
  quasi-compact opens is quasi-compact.
* `Stacks.AlgebraicGeometry.InductionPrinciple.exists_finset_basicOpen_of_isCompact`: a
  quasi-compact open contained in an affine open `A` is a finite union of basic opens of `A`.
* `Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open` is **[Stacks, Tag
  08DR]**: the induction principle, for every quasi-compact open of a quasi-separated scheme.
* `Stacks.AlgebraicGeometry.InductionPrinciple.induction_top` is the clause "and in particular
  for `X`" of the same tag.

## Implementation notes

The source states the principle for a property of the quasi-compact opens of `X`; it is stated
here for a property of all opens, which is equivalent, since the hypotheses and the conclusion
only ever mention quasi-compact opens and any property of those extends arbitrarily. The
hypothesis that `X` itself is quasi-compact is not needed for the conclusion about an arbitrary
quasi-compact open, so it is dropped; `induction_top` reinstates it.

## References

* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

open TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.InductionPrinciple

variable {X : Scheme.{u}}

/-! ### Finite unions of quasi-compact opens -/

/-- A finite union of quasi-compact opens of a scheme is quasi-compact. -/
theorem isCompact_biSup {ι : Type*} (f : ι → X.Opens) :
    ∀ (t : Finset ι), (∀ i ∈ t, IsCompact (f i : Set X)) →
      IsCompact ((⨆ i ∈ t, f i : X.Opens) : Set X) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | @insert a t _ ih =>
      intro hf
      simp only [Finset.iSup_insert, Opens.coe_sup]
      exact (hf a (Finset.mem_insert_self a t)).union
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ### Quasi-compact opens of an affine open -/

/-- A quasi-compact open contained in an affine open `A` of a scheme is the union of a finite
family of basic opens of `A`. The basic opens of `A` form a basis of the opens contained in
`A`, so the given open is covered by them, and quasi-compactness extracts a finite
subcover. -/
theorem exists_finset_basicOpen_of_isCompact {A W : X.Opens} (hA : IsAffineOpen A)
    (hW : IsCompact (W : Set X)) (hWA : W ≤ A) :
    ∃ s : Finset Γ(X, A), W = ⨆ g ∈ s, X.basicOpen g := by
  classical
  have hlocal : ∀ x : W, ∃ g : Γ(X, A), X.basicOpen g ≤ W ∧ (x : X) ∈ X.basicOpen g :=
    fun x => hA.exists_basicOpen_le x (hWA x.2)
  choose g hgle hgmem using hlocal
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun x : W => (X.basicOpen (g x) : Set X))
    (fun x => (X.basicOpen (g x)).isOpen) fun x hx =>
      Set.mem_iUnion.2 ⟨⟨x, hx⟩, hgmem ⟨x, hx⟩⟩
  refine ⟨t.image g, le_antisymm ?_ ?_⟩
  · rw [Finset.iSup_finset_image]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact le_iSup₂ (f := fun (y : W) (_ : y ∈ t) => X.basicOpen (g y)) y hy hxy
  · exact iSup_le fun k => iSup_le fun hk => by
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hk
      exact hgle y

/-! ### The induction principle -/

section Induction

variable (P : X.Opens → Prop)
  (haffine : ∀ U : X.Opens, IsAffineOpen U → P U)
  (hsup : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
    P U → P V → P (U ⊓ V) → P (U ⊔ V))

include haffine hsup

/-- Adding one affine open to a finite family of quasi-compact opens preserves `P`, provided `P`
holds for the family and for its intersection with the new open. -/
private theorem of_insert_iSup {ι : Type*} [DecidableEq ι] (f : ι → X.Opens) (t : Finset ι)
    (a : ι) (hc : ∀ i ∈ t, IsCompact (f i : Set X)) (ha : IsAffineOpen (f a))
    (ih : P (⨆ i ∈ t, f i)) (h : P ((⨆ i ∈ t, f i) ⊓ f a)) : P (⨆ i ∈ insert a t, f i) := by
  rw [Finset.iSup_insert, sup_comm]
  exact hsup _ _ (isCompact_biSup _ _ hc) ha ih (haffine _ ha) h

/-- The induction principle for finite families of basic opens of one affine open `A`: the
property holds for the union of any such family. This is the step for which the source passes
to separated opens; here it is an induction on the size of the family, available because the
basic opens of `A` are affine and closed under intersection. -/
private theorem of_finset_basicOpen {A : X.Opens} (hA : IsAffineOpen A) :
    ∀ (n : ℕ) (s : Finset Γ(X, A)), s.card ≤ n → P (⨆ g ∈ s, X.basicOpen g) := by
  classical
  have hbot : P (⨆ g ∈ (∅ : Finset Γ(X, A)), X.basicOpen g) := by
    simpa using haffine ⊥ (isAffineOpen_bot X)
  intro n
  induction n with
  | zero =>
      intro s hs
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs)]
      exact hbot
  | succ n ih =>
      intro s hs
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨g, hg⟩
      · exact hbot
      · have hcard : (s.erase g).card ≤ n := by
          have h1 := Finset.card_erase_of_mem hg
          have h2 : 1 ≤ s.card := Finset.card_pos.mpr ⟨g, hg⟩
          omega
        have hinter : (⨆ x ∈ s.erase g, X.basicOpen x) ⊓ X.basicOpen g
            = ⨆ k ∈ (s.erase g).image (· * g), X.basicOpen k := by
          rw [Finset.iSup_finset_image]
          simp only [iSup_inf_eq, ← Scheme.basicOpen_mul]
        rw [← Finset.insert_erase hg]
        refine of_insert_iSup P haffine hsup _ _ g (fun h _ => (hA.basicOpen h).isCompact)
          (hA.basicOpen g) (ih _ hcard) ?_
        rw [hinter]
        exact ih _ (le_trans Finset.card_image_le hcard)

/-- **[Stacks, Tag 08DR], the Induction Principle.** Let `X` be a quasi-separated scheme and
let `P` be a property of the opens of `X` which holds for every affine open and which, given a
quasi-compact open `U` and an affine open `V`, passes from `U`, `V` and `U ⊓ V` to `U ⊔ V`.
Then `P` holds for every quasi-compact open of `X`.

The source assumes in addition that `X` is quasi-compact; that hypothesis is not used for the
conclusion about an arbitrary quasi-compact open, and `induction_top` records the clause of the
source that does use it. -/
@[stacks 08DR]
theorem induction_isCompact_open [QuasiSeparatedSpace X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) : P W := by
  classical
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  have key : ∀ t : Finset X.affineOpens, P (⨆ i ∈ t, (i : X.Opens)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using haffine ⊥ (isAffineOpen_bot X)
    | @insert a t _ ih =>
        have hB : ∀ i : X.affineOpens, ∃ u : Finset Γ(X, (a : X.Opens)),
            ((i : X.Opens) ⊓ (a : X.Opens)) = ⨆ g ∈ u, X.basicOpen g := by
          intro i
          refine exists_finset_basicOpen_of_isCompact a.2 ?_ inf_le_right
          rw [Opens.coe_inf]
          exact i.2.isCompact.inter_of_isOpen a.2.isCompact
            (i : X.Opens).isOpen (a : X.Opens).isOpen
        choose u hu using hB
        have hinter : (⨆ i ∈ t, (i : X.Opens)) ⊓ (a : X.Opens)
            = ⨆ g ∈ t.biUnion u, X.basicOpen g := by
          rw [Finset.iSup_biUnion]
          simp only [iSup_inf_eq]
          exact iSup_congr fun i => iSup_congr fun _ => hu i
        refine of_insert_iSup P haffine hsup _ _ a (fun i _ => i.2.isCompact) a.2 ih ?_
        rw [hinter]
        exact of_finset_basicOpen P haffine hsup a.2 _ _ le_rfl
  have hfin : (⨆ i ∈ s, (i : X.Opens)) = ⨆ i ∈ hs.toFinset, (i : X.Opens) := by
    simp [Set.Finite.mem_toFinset]
  rw [hfin]
  exact key _

/-- **[Stacks, Tag 08DR], the clause "and in particular for `X`".** On a quasi-compact
quasi-separated scheme the induction principle applies to the whole space. -/
@[stacks 08DR "in particular for X"]
theorem induction_top [CompactSpace X] [QuasiSeparatedSpace X] : P ⊤ :=
  induction_isCompact_open P haffine hsup ⊤ (by simpa using isCompact_univ (X := X))

end Induction

end Stacks.AlgebraicGeometry.InductionPrinciple

end

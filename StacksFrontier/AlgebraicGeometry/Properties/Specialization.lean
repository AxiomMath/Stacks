module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute

/-!
# Infinite subsets of Noetherian schemes without specializations

Every infinite set of points of a Noetherian scheme contains an infinite subset in which no
distinct points specialize to one another. The mechanism is that coheight is a finite rank
function on a locally Noetherian scheme which strictly decreases along a nontrivial
specialization, so an infinite subset has an infinite subset of constant coheight.

## Main results

* `AlgebraicGeometry.coheight_lt_top_of_isLocallyNoetherian`: points of a locally Noetherian
  scheme have finite coheight.
* `AlgebraicGeometry.coheight_lt_coheight_of_specializes`: a nontrivial specialization on a
  locally Noetherian scheme strictly decreases coheight.
* `AlgebraicGeometry.exists_infinite_subset_pairwise_not_specializes` extracts an infinite
  subset without nontrivial specializations.

## Implementation notes

The specialization relation is Mathlib's `Specializes`; distinctness excludes the trivial
specialization of a point to itself.

The coheight of a point of a scheme is the Krull dimension of the local ring there
(`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`), so finiteness of coheight needs only that
the stalks are Noetherian and is stated under `IsLocallyNoetherian`; the main result is about
a Noetherian scheme because it also uses well-foundedness of strict generalization.

## References

* [Stacks Project, Tag 0CXG](https://stacks.math.columbia.edu/tag/0CXG)
-/

public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On a Noetherian scheme, strict generalization is a well-founded relation. -/
private lemma flip_strictSpecializes_wf (S : Scheme) [IsNoetherian S] :
    WellFounded (fun x y : S => y ⤳ x ∧ x ≠ y) := by
  let f : S → Closeds S := fun x => ⟨closure ({x} : Set S), isClosed_closure⟩
  apply WellFounded.mono (InvImage.wf f wellFounded_lt)
  intro x y ⟨hxy, hne⟩
  have hneq : f x ≠ f y := by
    intro heq
    have heq' : closure ({x} : Set S) = closure ({y} : Set S) :=
      congrArg (fun C : Closeds S => (C : Set S)) heq
    exact hne ((specializes_iff_closure_subset.mpr (by simp [heq'])).antisymm hxy).eq
  exact lt_of_le_of_ne (specializes_iff_closure_subset.mp hxy) hneq

/-- Every point of a locally Noetherian scheme has finite coheight, the coheight of a point
being the Krull dimension of the local ring there. -/
lemma coheight_lt_top_of_isLocallyNoetherian (S : Scheme) [IsLocallyNoetherian S] (x : S) :
    Order.coheight x < ⊤ := by
  apply WithBot.coe_lt_coe.mp
  rw [← ringKrullDim_stalk_eq_coheight]
  exact ringKrullDim_lt_top

/-- On a locally Noetherian scheme a nontrivial specialization strictly decreases coheight. -/
lemma coheight_lt_coheight_of_specializes (S : Scheme) [IsLocallyNoetherian S]
    {x y : S} (hxy : x ⤳ y) (hne : x ≠ y) : Order.coheight x < Order.coheight y := by
  have hyx : y < x := by
    show y ≤ x ∧ ¬ x ≤ y
    exact ⟨Scheme.le_iff_specializes.mpr hxy, fun hrev => hne
      (hxy.antisymm (Scheme.le_iff_specializes.mp hrev)).eq⟩
  exact Order.coheight_strictAnti hyx (coheight_lt_top_of_isLocallyNoetherian S x)

/-- Every point of a subset specializes to one admitting no further nontrivial
specialization inside the subset. -/
private lemma exists_terminal_specialization (S : Scheme) [IsNoetherian S]
    (T : Set S) (x : S) (hx : x ∈ T) :
    ∃ y ∈ T, x ⤳ y ∧ ∀ z ∈ T, y ⤳ z → z = y := by
  induction x using (flip_strictSpecializes_wf S).induction with
  | h x ih =>
      by_cases hterm : ∀ z ∈ T, x ⤳ z → z = x
      · exact ⟨x, hx, specializes_refl x, hterm⟩
      · push Not at hterm
        obtain ⟨z, hz, hxz, hzx⟩ := hterm
        obtain ⟨y, hy, hzy, hyterm⟩ := ih z ⟨hxz, hzx⟩ hz
        exact ⟨y, hy, hxz.trans hzy, hyterm⟩

/-- An infinite set of points on a Noetherian scheme contains an infinite subset with no
nontrivial specializations among its points. -/
@[stacks 0CXG]
theorem exists_infinite_subset_pairwise_not_specializes (S : Scheme.{u}) [IsNoetherian S]
    {T : Set S} (hT : T.Infinite) :
    ∃ T' : Set S, T' ⊆ T ∧ T'.Infinite ∧
      ∀ ⦃x y : S⦄, x ∈ T' → y ∈ T' → x ≠ y → ¬ x ⤳ y := by
  classical
  let T₀ : Set S := {x | x ∈ T ∧ ∀ y ∈ T, x ⤳ y → y = x}
  by_cases hT₀ : T₀.Infinite
  · exact ⟨T₀, fun x hx => hx.1, hT₀, fun x y hx hy hne hxy => hne (hx.2 _ hy.1 hxy).symm⟩
  · have hT₀fin : T₀.Finite := Set.not_infinite.mp hT₀
    have hT₀ne : T₀.Nonempty := by
      obtain ⟨x, hx⟩ := hT.nonempty
      obtain ⟨y, hy, -, hyterm⟩ := exists_terminal_specialization S T x hx
      exact ⟨y, hy, hyterm⟩
    let F : Set ℕ∞ := Order.coheight '' T₀
    let d : ℕ∞ := sSup F
    have hdgreat : IsGreatest F d := (hT₀ne.image _).isGreatest_csSup (hT₀fin.image _)
    have hdtop : d < ⊤ := by
      obtain ⟨x, hx, heq⟩ := hdgreat.1
      rw [← heq]
      exact coheight_lt_top_of_isLocallyNoetherian S x
    have hbound : ∀ x ∈ T, Order.coheight x ≤ d := by
      intro x hx
      obtain ⟨y, hy, hxy, hyterm⟩ := exists_terminal_specialization S T x hx
      have hy₀ : y ∈ T₀ := ⟨hy, hyterm⟩
      rcases eq_or_ne x y with rfl | hne
      · exact hdgreat.2 ⟨_, hy₀, rfl⟩
      · exact (coheight_lt_coheight_of_specializes S hxy hne).le.trans
          (hdgreat.2 ⟨y, hy₀, rfl⟩)
    have : Infinite T := Set.infinite_coe_iff.mpr hT
    let rank : T → Set.Iic d.toNat := fun x =>
      ⟨(Order.coheight x.1).toNat, ENat.toNat_le_toNat (hbound x.1 x.2) hdtop.ne⟩
    obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber rank
    let Fv : Set T := rank ⁻¹' {v}
    let T' : Set S := (fun x : T => (x : S)) '' Fv
    have hT'inf : T'.Infinite :=
      (Set.infinite_coe_iff.mp hv).image fun _ _ _ _ h => Subtype.val_injective h
    refine ⟨T', ?_, hT'inf, ?_⟩
    · rintro x ⟨a, -, rfl⟩
      exact a.2
    · intro x y hx hy hne hxy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      have hnat : (Order.coheight (a : S)).toNat = (Order.coheight (b : S)).toNat :=
        congrArg Subtype.val ((ha : rank a = v).trans (hb : rank b = v).symm)
      have hax : Order.coheight (a : S) = Order.coheight (b : S) :=
        (ENat.natCast_toNat (coheight_lt_top_of_isLocallyNoetherian S a).ne).symm.trans
          ((congrArg Nat.cast hnat).trans
            (ENat.natCast_toNat (coheight_lt_top_of_isLocallyNoetherian S b).ne))
      exact lt_irrefl _ (hax ▸ coheight_lt_coheight_of_specializes S hxy hne)

end AlgebraicGeometry

end

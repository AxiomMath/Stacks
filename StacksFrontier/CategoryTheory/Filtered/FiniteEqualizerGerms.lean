module

public import Mathlib.Data.Set.Finite.Lattice

/-!
# Germs of sections commute with finite equalizers

Let `I` be a directed set, thought of as the levels of an inverse system, and let `E i`, `P i a`,
`Q i a b` be, at each level `i` and at the limit, the sets of sections of a sheaf over an object,
over the members `a` of a finite cover of it, and over the overlaps of two members. Suppose the
sections over the object are the equalizer of the sections over the members and over the
overlaps, at each level and at the limit, and that the sections over the members and over the
overlaps at the limit are the filtered colimit of those at the levels. Then so are the sections
over the object: filtered colimits of sets commute with finite limits.

This is the combinatorial core of passing from affine pieces to quasi-compact objects in
Stacks 09YQ, stated for bare types and maps.

## Main results

* `Stacks.Germs.exists_upper_bound`: a finite family of levels has a common upper bound.
* `Stacks.Germs.colimit_of_finite_equalizer`: the colimit property for the sections over the
  object.
-/

@[expose] public section

universe w u

namespace Stacks.Germs

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]

/-- A finite family of levels of a directed set has a common upper bound. -/
theorem exists_upper_bound {A : Type*} [Finite A] (f : A → I) : ∃ k : I, ∀ a, f a ≤ k := by
  classical
  obtain ⟨k, hk⟩ := (Set.finite_range f).bddAbove
  exact ⟨k, fun a => hk ⟨a, rfl⟩⟩

/-- **Germs of sections over an object covered by finitely many pieces.** `E i`, `P i a`, `Q i a b`
are the sections at level `i` over the object, over the member `a` and over the overlap of `a`
and `b`; `Ew`, `Pw a`, `Qw a b` the same at the limit; `rE`, `q₁`, `q₂` the restrictions; `tE`,
`tP`, `tQ` the transitions; `τE`, `τP`, `τQ` the maps to the limit. -/
theorem colimit_of_finite_equalizer {A O : Type*} [Finite A] [Finite O] (src tgt : O → A)
    {E : I → Type w} {P : I → A → Type w} {Q : I → O → Type w}
    {Ew : Type w} {Pw : A → Type w} {Qw : O → Type w}
    (rE : ∀ i a, E i → P i a) (q₁ : ∀ i o, P i (src o) → Q i o) (q₂ : ∀ i o, P i (tgt o) → Q i o)
    (rEw : ∀ a, Ew → Pw a) (q₁w : ∀ o, Pw (src o) → Qw o) (q₂w : ∀ o, Pw (tgt o) → Qw o)
    (tE : ∀ {i j : I}, i ≤ j → E i → E j) (tP : ∀ {i j : I}, i ≤ j → ∀ a, P i a → P j a)
    (tQ : ∀ {i j : I}, i ≤ j → ∀ o, Q i o → Q j o)
    (τE : ∀ i, E i → Ew) (τP : ∀ i a, P i a → Pw a) (τQ : ∀ i o, Q i o → Qw o)
    (sep : ∀ i (x y : E i), (∀ a, rE i a x = rE i a y) → x = y)
    (glue : ∀ i (z : ∀ a, P i a), (∀ o, q₁ i o (z (src o)) = q₂ i o (z (tgt o))) →
      ∃ x, ∀ a, rE i a x = z a)
    (sepw : ∀ x y : Ew, (∀ a, rEw a x = rEw a y) → x = y)
    (cocyclew : ∀ (x : Ew) o, q₁w o (rEw (src o) x) = q₂w o (rEw (tgt o) x))
    (htP : ∀ {i j k : I} (d : i ≤ j) (e : j ≤ k) a (y : P i a),
      tP (d.trans e) a y = tP e a (tP d a y))
    (htQ : ∀ {i j k : I} (d : i ≤ j) (e : j ≤ k) o (y : Q i o),
      tQ (d.trans e) o y = tQ e o (tQ d o y))
    (hrE_t : ∀ {i j : I} (d : i ≤ j) a (x : E i), rE j a (tE d x) = tP d a (rE i a x))
    (hq₁_t : ∀ {i j : I} (d : i ≤ j) o (y : P i (src o)),
      q₁ j o (tP d (src o) y) = tQ d o (q₁ i o y))
    (hq₂_t : ∀ {i j : I} (d : i ≤ j) o (y : P i (tgt o)),
      q₂ j o (tP d (tgt o) y) = tQ d o (q₂ i o y))
    (hτP_t : ∀ {i j : I} (d : i ≤ j) a (y : P i a), τP j a (tP d a y) = τP i a y)
    (hτP_r : ∀ i a (x : E i), τP i a (rE i a x) = rEw a (τE i x))
    (hτQ₁ : ∀ i o (y : P i (src o)), τQ i o (q₁ i o y) = q₁w o (τP i (src o) y))
    (hτQ₂ : ∀ i o (y : P i (tgt o)), τQ i o (q₂ i o y) = q₂w o (τP i (tgt o) y))
    (hP_surj : ∀ a (s : Pw a), ∃ (i : I) (y : P i a), τP i a y = s)
    (hP_inj : ∀ i a (y y' : P i a), τP i a y = τP i a y' →
      ∃ (j : I) (d : i ≤ j), tP d a y = tP d a y')
    (hQ_inj : ∀ i o (y y' : Q i o), τQ i o y = τQ i o y' →
      ∃ (j : I) (d : i ≤ j), tQ d o y = tQ d o y') :
    (∀ s : Ew, ∃ (i : I) (x : E i), τE i x = s) ∧
      ∀ i (x x' : E i), τE i x = τE i x' → ∃ (j : I) (d : i ≤ j), tE d x = tE d x' := by
  classical
  refine ⟨fun s => ?_, fun i x x' hxx' => ?_⟩
  · choose i₀ y₀ hy₀ using fun a => hP_surj a (rEw a s)
    obtain ⟨k₀, hk₀⟩ := exists_upper_bound i₀
    let y : ∀ a, P k₀ a := fun a => tP (hk₀ a) a (y₀ a)
    have hy : ∀ a, τP k₀ a (y a) = rEw a s := fun a => (hτP_t _ _ _).trans (hy₀ a)
    have hpair : ∀ o, τQ k₀ o (q₁ k₀ o (y (src o))) = τQ k₀ o (q₂ k₀ o (y (tgt o))) := by
      intro o
      rw [hτQ₁, hτQ₂, hy, hy]
      exact cocyclew s o
    choose k₁ d₁ hd₁ using fun o => hQ_inj k₀ o _ _ (hpair o)
    obtain ⟨k₂, hk₂⟩ := exists_upper_bound k₁
    obtain ⟨k, hk₀k, hk₂k⟩ := directed_of (· ≤ ·) k₀ k₂
    let z : ∀ a, P k a := fun a => tP hk₀k a (y a)
    have hz : ∀ o, q₁ k o (z (src o)) = q₂ k o (z (tgt o)) := by
      intro o
      have e : k₁ o ≤ k := (hk₂ o).trans hk₂k
      calc q₁ k o (z (src o)) = tQ ((d₁ o).trans e) o (q₁ k₀ o (y (src o))) := hq₁_t _ _ _
        _ = tQ e o (tQ (d₁ o) o (q₁ k₀ o (y (src o)))) := htQ _ _ _ _
        _ = tQ e o (tQ (d₁ o) o (q₂ k₀ o (y (tgt o)))) := congrArg (tQ e o) (hd₁ o)
        _ = tQ ((d₁ o).trans e) o (q₂ k₀ o (y (tgt o))) := (htQ _ _ _ _).symm
        _ = q₂ k o (z (tgt o)) := (hq₂_t _ _ _).symm
    obtain ⟨x, hx⟩ := glue k z hz
    refine ⟨k, x, sepw _ _ fun a => ?_⟩
    rw [← hτP_r, hx]
    exact (hτP_t _ _ _).trans (hy a)
  · have h : ∀ a, τP i a (rE i a x) = τP i a (rE i a x') := fun a => by
      rw [hτP_r, hτP_r, hxx']
    choose j d hd using fun a => hP_inj i a _ _ (h a)
    obtain ⟨j₁, hj₁⟩ := exists_upper_bound j
    obtain ⟨k, hik, hj₁k⟩ := directed_of (· ≤ ·) i j₁
    refine ⟨k, hik, sep k _ _ fun a => ?_⟩
    have e : j a ≤ k := (hj₁ a).trans hj₁k
    calc rE k a (tE hik x) = tP ((d a).trans e) a (rE i a x) := hrE_t _ _ _
      _ = tP e a (tP (d a) a (rE i a x)) := htP _ _ _ _
      _ = tP e a (tP (d a) a (rE i a x')) := congrArg (tP e a) (hd a)
      _ = tP ((d a).trans e) a (rE i a x') := (htP _ _ _ _).symm
      _ = rE k a (tE hik x') := (hrE_t _ _ _).symm

end Stacks.Germs

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# A lifting criterion for a map of complexes to be a quasi-isomorphism

Let `p : P ⟶ K` be a map of cochain complexes in an abelian category. Say that `p` *has cycle
boundary lifts* in degree `n` if, for every object `T` with a cycle `a : T ⟶ P.X (n + 1)` and a
map `b : T ⟶ K.X n` whose differential matches the image of `a`, the pair `(a, b)` can be lifted
to a map into `P.X n` after replacing `T` by a quotient-free cover, i.e. after precomposing with
an epimorphism onto `T`. When this holds in degrees `n` and `n - 1`, the map `p` induces an
isomorphism on degree-`n` homology.

This is the homological input to the construction of Stacks 0DIT: the tower built there
satisfies the lifting condition in every degree below its bound by construction, and that is
what makes the resulting map of complexes a quasi-isomorphism.

## Main definitions

* `Stacks.SheafOfModules.ComplexLifting.HasCycleBoundaryLifts`: the lifting condition.

## Main results

* `Stacks.SheafOfModules.ComplexLifting.isIso_homologyMap_of_lifts`: the lifting condition in
  two consecutive degrees makes the degree-`n` homology map an isomorphism.

## Implementation notes

Surjectivity is expressed as an epimorphism onto the test object rather than by elements, so
that the criterion applies in any abelian category. Injectivity of the homology map is proved
with pseudoelements, which is where that generality is paid for: a pseudoelement of the homology
is lifted to a cycle, its image is seen to be a boundary, and the lifting condition in the
previous degree produces a preimage of the corresponding element of the pullback.

## References

* [Stacks Project, Tag 0DIT](https://stacks.math.columbia.edu/tag/0DIT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace Stacks.SheafOfModules.ComplexLifting

variable {A : Type u} [Category.{v} A] [Abelian A] {P K : CochainComplex A ℤ}

/-- `p` has cycle boundary lifts in degree `n` when a cycle of `P` in degree `n + 1` together
with a compatible element of `K` in degree `n` lift, after passing to a cover, to an element of
`P` in degree `n`. -/
def HasCycleBoundaryLifts (p : P ⟶ K) (n : ℤ) : Prop :=
  ∀ (T : A) (a : T ⟶ P.X (n + 1)) (b : T ⟶ K.X n),
    a ≫ P.d (n + 1) (n + 1 + 1) = 0 →
    a ≫ p.f (n + 1) = b ≫ K.d n (n + 1) →
    ∃ (Y : A) (e : Y ⟶ T), Epi e ∧ ∃ c : Y ⟶ P.X n,
      c ≫ P.d n (n + 1) = e ≫ a ∧ c ≫ p.f n = e ≫ b

/-- The lifting condition makes the map on cycles an epimorphism. -/
lemma epi_cyclesMap_of_lifts (p : P ⟶ K) (n : ℤ) (h : HasCycleBoundaryLifts p n) :
    Epi (cyclesMap p n) := by
  obtain ⟨Y, e, he, c, hc, hc'⟩ := h (K.cycles n) 0 (K.iCycles n) (by simp) (by simp)
  have hc0 : c ≫ P.d n (n + 1) = 0 := by simpa using hc
  let c' := P.liftCycles c (n + 1) (by simp) hc0
  have he' : c' ≫ cyclesMap p n = e := by
    simpa [c', ← cancel_mono (K.iCycles n)] using hc'
  exact epi_of_epi_fac he'

/-- The lifting condition makes the comparison into the pullback of the cycles square an
epimorphism. -/
lemma epi_cyclePullback_of_lifts (p : P ⟶ K) (n : ℤ) (h : HasCycleBoundaryLifts p n)
    (w : P.toCycles n (n + 1) ≫ cyclesMap p (n + 1) = p.f n ≫ K.toCycles n (n + 1)) :
    Epi (pullback.lift (P.toCycles n (n + 1)) (p.f n) w) := by
  let T := pullback (cyclesMap p (n + 1)) (K.toCycles n (n + 1))
  let a : T ⟶ P.X (n + 1) := pullback.fst _ _ ≫ P.iCycles (n + 1)
  let b : T ⟶ K.X n := pullback.snd _ _
  have ha : a ≫ P.d (n + 1) (n + 1 + 1) = 0 := by simp [a]
  have hab : a ≫ p.f (n + 1) = b ≫ K.d n (n + 1) := by
    dsimp [a, b]
    rw [Category.assoc, ← cyclesMap_i, ← Category.assoc, pullback.condition, Category.assoc,
      K.toCycles_i]
  obtain ⟨Y, e, he, c, hc, hc'⟩ := h T a b ha hab
  have hce : c ≫ pullback.lift (P.toCycles n (n + 1)) (p.f n) w = e := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← cancel_mono (P.iCycles (n + 1)), Category.assoc,
        P.toCycles_i]
      simpa only [a, Category.assoc] using hc
    · rwa [Category.assoc, pullback.lift_snd]
  exact epi_of_epi_fac hce

/-- The lifting condition in degree `m` makes the degree-`m + 1` homology map a monomorphism. -/
lemma mono_homologyMap_of_lifts (p : P ⟶ K) (m : ℤ) (h : HasCycleBoundaryLifts p m) :
    Mono (homologyMap p (m + 1)) := by
  have w : P.toCycles m (m + 1) ≫ cyclesMap p (m + 1) = p.f m ≫ K.toCycles m (m + 1) := by
    simp [← cancel_mono (K.iCycles (m + 1))]
  let l := pullback.lift (P.toCycles m (m + 1)) (p.f m) w
  have hl : Epi l := epi_cyclePullback_of_lifts p m h w
  apply Abelian.Pseudoelement.mono_of_zero_of_map_zero
  intro η hη
  obtain ⟨c, hc⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi (P.homologyπ (m + 1)) η
  have hk : Abelian.Pseudoelement.pseudoApply (K.homologyπ (m + 1))
      (Abelian.Pseudoelement.pseudoApply (cyclesMap p (m + 1)) c) = 0 := by
    rw [← Abelian.Pseudoelement.comp_apply, ← homologyπ_naturality,
      Abelian.Pseudoelement.comp_apply, hc, hη]
  have hex : (ShortComplex.mk (K.toCycles m (m + 1)) (K.homologyπ (m + 1))
      (K.toCycles_comp_homologyπ m (m + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel m (m + 1) (by simp))
  obtain ⟨b, hb⟩ := Abelian.Pseudoelement.pseudo_exact_of_exact hex _ hk
  obtain ⟨s, hs, _⟩ := Abelian.Pseudoelement.pseudo_pullback hb.symm
  obtain ⟨x, hx⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi l s
  have hd : Abelian.Pseudoelement.pseudoApply (P.toCycles m (m + 1)) x = c := by
    simpa only [← Abelian.Pseudoelement.comp_apply, l, pullback.lift_fst, hs] using
      congrArg (Abelian.Pseudoelement.pseudoApply
        (pullback.fst (cyclesMap p (m + 1)) (K.toCycles m (m + 1)))) hx
  rw [← hc, ← hd, ← Abelian.Pseudoelement.comp_apply, P.toCycles_comp_homologyπ,
    Abelian.Pseudoelement.zero_apply]

/-- The lifting condition in degrees `n` and `n - 1` makes the degree-`n` homology map an
isomorphism. -/
lemma isIso_homologyMap_of_lifts (p : P ⟶ K) (n : ℤ) (h : HasCycleBoundaryLifts p n)
    (hprev : HasCycleBoundaryLifts p (n - 1)) : IsIso (homologyMap p n) := by
  have : Epi (cyclesMap p n) := epi_cyclesMap_of_lifts p n h
  have : Epi (homologyMap p n) := epi_of_epi_fac (homologyπ_naturality p n)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := mono_homologyMap_of_lifts p m (by simpa using hprev)
  exact isIso_of_mono_of_epi _

end Stacks.SheafOfModules.ComplexLifting

end

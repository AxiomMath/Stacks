module

public import StacksFrontier.CategoryTheory.Triangulated.TriangulatedEnvelopeInduction

/-!
# Eventual orthogonality propagates through the triangulated envelope

Let `𝒟` be a triangulated category, `E` an object of `𝒟` and `l` a filter on `ℤ` invariant under
the translations (`atTop` or `atBot`). Say that an object `P` is *eventually orthogonal* to `E`
along `l` if the morphisms `P⟦-i⟧ ⟶ E` vanish for `l`-almost every `i`; for `l = atTop` this is
`Hom(P⟦-i⟧, E) = 0` for `i ≫ 0`, for `l = atBot` it is `Hom(P⟦-i⟧, E) = 0` for `i ≪ 0`.

Eventual orthogonality is inherited by direct sums, direct summands and shifts, and satisfies the
two-out-of-three property for distinguished triangles. So by the induction principle of
[Stacks, Tag 0ATH], if an object `G` is eventually orthogonal to `E`, so is every object of the
triangulated envelope `⟨G⟩`. This is the step "(2) implies (7)(a)" in the proofs of
[Stacks, Tags 0GEN and 0GEQ].

## Main results

* `CategoryTheory.ObjectProperty.EventuallyOrthogonal`
* `CategoryTheory.ObjectProperty.triangEnvelope_singleton_le_eventuallyOrthogonal`

## References

* [Stacks, Tag 0ATH](https://stacks.math.columbia.edu/tag/0ATH)
* [Stacks, Tag 0GEN](https://stacks.math.columbia.edu/tag/0GEN)
-/

@[expose] public section

universe v u v' u'

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive Pretriangulated ZeroObject

/-- If `p : A ⟶ B` is an epimorphism and there is at most one morphism `A ⟶ X`, then there is at
most one morphism `B ⟶ X`. -/
private theorem subsingleton_of_epi {C : Type u} [Category.{v} C] {A B X : C} (p : A ⟶ B) [Epi p]
    [Subsingleton (A ⟶ X)] : Subsingleton (B ⟶ X) :=
  ⟨fun _ _ => (cancel_epi p).1 (Subsingleton.elim _ _)⟩

/-- If every morphism `B ⟶ X` factors through `g : B ⟶ D` and there is at most one morphism
`D ⟶ X`, then there is at most one morphism `B ⟶ X`. -/
private theorem subsingleton_of_factors_left {C : Type u} [Category.{v} C] {B D X : C} (g : B ⟶ D)
    (h : ∀ f : B ⟶ X, ∃ k : D ⟶ X, f = g ≫ k) [Subsingleton (D ⟶ X)] :
    Subsingleton (B ⟶ X) := by
  refine ⟨fun f f' => ?_⟩
  obtain ⟨k, rfl⟩ := h f
  obtain ⟨k', rfl⟩ := h f'
  rw [Subsingleton.elim k k']

/-- If every morphism `A ⟶ B` factors through `g : D ⟶ B` and there is at most one morphism
`A ⟶ D`, then there is at most one morphism `A ⟶ B`. -/
private theorem subsingleton_of_factors_right {C : Type u} [Category.{v} C] {A B D : C}
    (g : D ⟶ B) (h : ∀ f : A ⟶ B, ∃ k : A ⟶ D, f = k ≫ g) [Subsingleton (A ⟶ D)] :
    Subsingleton (A ⟶ B) := by
  refine ⟨fun f f' => ?_⟩
  obtain ⟨k, rfl⟩ := h f
  obtain ⟨k', rfl⟩ := h f'
  rw [Subsingleton.elim k k']

section Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

section Triangles

variable {X : C} (T : Triangle C) (hT : T ∈ distTriang C)
include hT

/-- For a distinguished triangle `T`, if there is at most one morphism `T.obj₂ ⟶ X` and at most
one morphism `T.obj₃⟦-1⟧ ⟶ X`, then there is at most one morphism `T.obj₁ ⟶ X`. -/
theorem subsingleton_obj₁_of_distinguished [Subsingleton (T.obj₂ ⟶ X)]
    [Subsingleton ((T.obj₃)⟦(-1 : ℤ)⟧ ⟶ X)] : Subsingleton (T.obj₁ ⟶ X) := by
  have hT' := inv_rot_of_distTriang T hT
  have : Subsingleton (T.invRotate.obj₁ ⟶ X) :=
    ‹Subsingleton ((T.obj₃)⟦(-1 : ℤ)⟧ ⟶ X)›
  have : Subsingleton (T.invRotate.obj₃ ⟶ X) := ‹Subsingleton (T.obj₂ ⟶ X)›
  exact subsingleton_of_factors_left T.invRotate.mor₂ fun f =>
    Triangle.yoneda_exact₂ _ hT' f (Subsingleton.elim _ _)

/-- For a distinguished triangle `T`, if there is at most one morphism `T.obj₁ ⟶ X` and at most
one morphism `T.obj₃ ⟶ X`, then there is at most one morphism `T.obj₂ ⟶ X`. -/
theorem subsingleton_obj₂_of_distinguished [Subsingleton (T.obj₁ ⟶ X)]
    [Subsingleton (T.obj₃ ⟶ X)] : Subsingleton (T.obj₂ ⟶ X) := by
  exact subsingleton_of_factors_left T.mor₂ fun f =>
    Triangle.yoneda_exact₂ T hT f (Subsingleton.elim _ _)

/-- For a distinguished triangle `T`, if there is at most one morphism `T.obj₂ ⟶ X` and at most
one morphism `T.obj₁⟦1⟧ ⟶ X`, then there is at most one morphism `T.obj₃ ⟶ X`. -/
theorem subsingleton_obj₃_of_distinguished [Subsingleton (T.obj₂ ⟶ X)]
    [Subsingleton ((T.obj₁)⟦(1 : ℤ)⟧ ⟶ X)] : Subsingleton (T.obj₃ ⟶ X) := by
  exact subsingleton_of_factors_left T.mor₃ fun f =>
    Triangle.yoneda_exact₃ T hT f (Subsingleton.elim _ _)

end Triangles

section Shift

/-- `P` is *eventually orthogonal* to `E` along a filter `l` on `ℤ` if the morphisms
`P⟦-i⟧ ⟶ E` vanish for `l`-almost every `i`. For `l = atTop` this is the vanishing of
`Hom(P⟦-i⟧, E)` for `i ≫ 0`, for `l = atBot` its vanishing for `i ≪ 0`. -/
def EventuallyOrthogonal (l : Filter ℤ) (P E : C) : Prop :=
  ∀ᶠ i in l, Subsingleton (P⟦-i⟧ ⟶ E)

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A morphism `X⟦n⟧ ⟶ E` is a morphism `X ⟶ E⟦-n⟧`, the shifts being adjoint. -/
theorem subsingleton_shift_iff (X E : C) (n : ℤ) :
    Subsingleton (X⟦n⟧ ⟶ E) ↔ Subsingleton (X ⟶ E⟦-n⟧) :=
  ((shiftEquiv C n).toAdjunction.homEquiv X E).subsingleton_congr

variable {l : Filter ℤ} (hl : ∀ k : ℤ, Filter.Tendsto (fun i => i + k) l l)

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
include hl in
/-- Eventual orthogonality to `E` is stable under the shifts. -/
theorem eventuallyOrthogonal_shift {P E : C} (hP : EventuallyOrthogonal l P E) (n : ℤ) :
    EventuallyOrthogonal l (P⟦n⟧) E := by
  refine ((hl (-n)).eventually hP).mono fun i hi => ?_
  have e : (P⟦n⟧)⟦-i⟧ ≅ P⟦-(i + -n)⟧ :=
    (shiftFunctorAdd' C n (-i) (-(i + -n)) (by omega)).symm.app P
  exact subsingleton_of_epi e.inv

include hl in
/-- **Eventual orthogonality propagates through the triangulated envelope.** Along a filter `l` on
`ℤ` invariant under the translations, if `G` is eventually orthogonal to `E`, so is every object
of `⟨G⟩`. This is the induction principle of [Stacks, Tag 0ATH]. -/
theorem triangEnvelope_singleton_le_eventuallyOrthogonal [IsTriangulated C] (G E : C)
    (hG : EventuallyOrthogonal l G E) :
    (ObjectProperty.singleton G).triangEnvelope ≤ fun P => EventuallyOrthogonal l P E := by
  have shiftDist : ∀ (T : Triangle C) (_ : T ∈ distTriang C) (i : ℤ),
      (Triangle.shiftFunctor C (-i)).obj T ∈ distTriang C := fun T hT i =>
    Triangle.shift_distinguished T hT (-i)
  refine triangEnvelope_singleton_le_of_sums_of_extensions_of_summands G _ ?_ ?_ ?_ ?_ ?_
    (fun n => eventuallyOrthogonal_shift hl hG n)
  · intro K L h₁ h₂
    refine (h₁.and h₂).mono fun i ⟨hK, hL⟩ => ?_
    rw [subsingleton_shift_iff] at hK hL ⊢
    refine ⟨fun (f g : K ⊞ L ⟶ _) => ?_⟩
    ext
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  · intro T hT h₂ h₃
    have h₃' := eventuallyOrthogonal_shift hl h₃ (-1)
    refine (h₂.and h₃').mono fun i ⟨hb, hc⟩ => ?_
    let T' := (Triangle.shiftFunctor C (-i)).obj T
    have hT' := shiftDist T hT i
    have e : (T.obj₃⟦(-1 : ℤ)⟧)⟦-i⟧ ≅ T'.obj₃⟦(-1 : ℤ)⟧ :=
      (shiftFunctorComm C (-1) (-i)).app T.obj₃
    have : Subsingleton (T'.obj₂ ⟶ E) := hb
    have : Subsingleton (T'.obj₃⟦(-1 : ℤ)⟧ ⟶ E) := subsingleton_of_epi e.hom
    exact subsingleton_obj₁_of_distinguished T' hT'
  · intro T hT h₁ h₃
    refine (h₁.and h₃).mono fun i ⟨ha, hc⟩ => ?_
    have : Subsingleton (((Triangle.shiftFunctor C (-i)).obj T).obj₁ ⟶ E) := ha
    have : Subsingleton (((Triangle.shiftFunctor C (-i)).obj T).obj₃ ⟶ E) := hc
    exact subsingleton_obj₂_of_distinguished _ (shiftDist T hT i)
  · intro T hT h₁ h₂
    have h₁' := eventuallyOrthogonal_shift hl h₁ 1
    refine (h₁'.and h₂).mono fun i ⟨ha, hb⟩ => ?_
    let T' := (Triangle.shiftFunctor C (-i)).obj T
    have e : (T.obj₁⟦(1 : ℤ)⟧)⟦-i⟧ ≅ T'.obj₁⟦(1 : ℤ)⟧ :=
      (shiftFunctorComm C 1 (-i)).app T.obj₁
    have : Subsingleton (T'.obj₂ ⟶ E) := hb
    have : Subsingleton (T'.obj₁⟦(1 : ℤ)⟧ ⟶ E) := subsingleton_of_epi e.hom
    exact subsingleton_obj₃_of_distinguished T' (shiftDist T hT i)
  · intro K L h
    refine ⟨h.mono fun i hi => ?_, h.mono fun i hi => ?_⟩
    · rw [subsingleton_shift_iff] at hi ⊢
      exact subsingleton_of_epi (biprod.fst : K ⊞ L ⟶ K)
    · rw [subsingleton_shift_iff] at hi ⊢
      exact subsingleton_of_epi (biprod.snd : K ⊞ L ⟶ L)

/-! ### Moving the target -/

section Target

omit hl [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Eventual orthogonality only depends on the target up to isomorphism. -/
theorem eventuallyOrthogonal_of_iso_target {P E E' : C} (e : E ≅ E')
    (h : EventuallyOrthogonal l P E) : EventuallyOrthogonal l P E' :=
  h.mono fun _ _ => ⟨fun _ _ => (cancel_mono e.inv).1 (Subsingleton.elim _ _)⟩

omit hl [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Eventual orthogonality only depends on the source up to isomorphism. -/
theorem eventuallyOrthogonal_of_iso_source {P P' E : C} (e : P ≅ P')
    (h : EventuallyOrthogonal l P E) : EventuallyOrthogonal l P' E :=
  h.mono fun i _ => subsingleton_of_epi ((shiftFunctor C (-i)).mapIso e).hom

omit hl [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Everything is eventually orthogonal to a zero object. -/
theorem eventuallyOrthogonal_of_isZero_target {P E : C} (hE : IsZero E) :
    EventuallyOrthogonal l P E :=
  Filter.Eventually.of_forall fun _ => ⟨fun f g => hE.eq_of_tgt f g⟩

omit hl in
/-- A direct summand of an eventually orthogonal object is eventually orthogonal. -/
theorem eventuallyOrthogonal_of_biprod_left {P Q E : C}
    (h : EventuallyOrthogonal l (P ⊞ Q) E) : EventuallyOrthogonal l P E := by
  refine h.mono fun i hi => ?_
  rw [subsingleton_shift_iff] at hi ⊢
  exact subsingleton_of_epi (biprod.fst : P ⊞ Q ⟶ P)

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
include hl in
/-- Eventual orthogonality to `E` passes to the shifts of `E`. -/
theorem eventuallyOrthogonal_shift_target {P E : C} (h : EventuallyOrthogonal l P E) (n : ℤ) :
    EventuallyOrthogonal l P (E⟦n⟧) := by
  refine ((hl n).eventually h).mono fun i hi => ?_
  have e : (P⟦-i⟧)⟦-n⟧ ≅ P⟦-(i + n)⟧ :=
    (shiftFunctorAdd' C (-i) (-n) (-(i + n)) (by omega)).symm.app P
  have h' : Subsingleton ((P⟦-i⟧)⟦-n⟧ ⟶ E) := subsingleton_of_epi e.inv
  exact @Equiv.subsingleton _ _
    ((shiftEquiv' C (-n) n (by omega)).toAdjunction.homEquiv (P⟦-i⟧) E).symm h'

omit hl in
/-- **Two out of three for the target, second vertex.** -/
theorem eventuallyOrthogonal_obj₂_target {P : C} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : EventuallyOrthogonal l P T.obj₁) (h₃ : EventuallyOrthogonal l P T.obj₃) :
    EventuallyOrthogonal l P T.obj₂ := by
  refine (h₁.and h₃).mono fun i ⟨ha, hc⟩ => ?_
  exact subsingleton_of_factors_right T.mor₁ fun f =>
    Triangle.coyoneda_exact₂ T hT f (Subsingleton.elim _ _)

omit hl in
/-- **Two out of three for the target, third vertex.** -/
theorem eventuallyOrthogonal_obj₃_target {P : C} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : EventuallyOrthogonal l P T.obj₂)
    (h₁ : EventuallyOrthogonal l P (T.obj₁⟦(1 : ℤ)⟧)) :
    EventuallyOrthogonal l P T.obj₃ := by
  refine (h₂.and h₁).mono fun i ⟨hb, ha⟩ => ?_
  exact subsingleton_of_factors_right T.mor₂ fun f =>
    Triangle.coyoneda_exact₃ T hT f (Subsingleton.elim _ _)

end Target

end Shift

end Pretriangulated

section Adjunction

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
  {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ]

include adj in
/-- **Eventual orthogonality across an adjunction.** For an adjunction `L ⊣ R` whose left adjoint
commutes with the shifts, `L P` is eventually orthogonal to `N` exactly when `P` is eventually
orthogonal to `R N`. -/
theorem eventuallyOrthogonal_leftAdjoint_iff {l : Filter ℤ} (P : C) (N : D) :
    EventuallyOrthogonal l (L.obj P) N ↔ EventuallyOrthogonal l P (R.obj N) := by
  have key : ∀ i : ℤ, Subsingleton ((L.obj P)⟦-i⟧ ⟶ N) ↔ Subsingleton (P⟦-i⟧ ⟶ R.obj N) := by
    intro i
    refine Iff.trans ?_ (adj.homEquiv (P⟦-i⟧) N).subsingleton_congr
    exact (((L.commShiftIso (-i)).app P).homFromEquiv (Z := N) |>.subsingleton_congr).symm
  exact ⟨fun h => h.mono fun i hi => (key i).1 hi, fun h => h.mono fun i hi => (key i).2 hi⟩

end Adjunction

end CategoryTheory.ObjectProperty

end

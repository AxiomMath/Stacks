module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit

/-!
# Morphisms out of a derived colimit of an eventually stable system

Let `K = hocolim Kₙ` be a derived colimit, with coprojections `cₙ : Kₙ ⟶ K`, of a system
`(Kₙ, fₙ)` in a pre-triangulated category, and let `B` be an object.  Morphisms out of `K` sit in
the Milnor sequence
`0 ⟶ lim¹ Hom(Kₙ[1], B) ⟶ Hom(K, B) ⟶ lim Hom(Kₙ, B) ⟶ 0`.
If the inverse systems `Hom(Kₙ, B)` and `Hom(Kₙ[1], B)` are eventually stable — from an index
`N` on, `fₙ^*` is bijective on the first and surjective on the second — then the `lim¹` term
vanishes and the limit is `Hom(K_N, B)`, so composing with `c_N` is a bijection
`Hom(K, B) ≃ Hom(K_N, B)`.

## Main results

* `CategoryTheory.Pretriangulated.IsHomotopyColimitWith.bijective_comp_of_stable`: composing
  with `c_N` is bijective on morphisms out of `K` into an object against which the system is
  eventually stable.

The three facts about inverse sequences of abelian groups it rests on are proved first:
`exists_compatible_of_surjective` (a compatible family through a given element, when the
transitions are eventually surjective), `eq_zero_of_compatible` (a compatible family vanishing at
one stage vanishes, when the transitions are eventually injective) and
`exists_sub_shift_eq_of_surjective` (the vanishing of `lim¹` for eventually surjective
transitions).
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated.HomotopyColimitHomStable

/-! ### Inverse sequences of abelian groups -/

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)]

/-- If the transitions of an inverse sequence of abelian groups are surjective from the index `N`
on, then every element of the `N`-th term lies on a compatible family. -/
theorem exists_compatible_of_surjective (N : ℕ) (t : ∀ n, A (n + 1) →+ A n)
    (ht : ∀ n, N ≤ n → Function.Surjective (t n)) (β : A N) :
    ∃ b : ∀ n, A n, (∀ n, b n = t n (b (n + 1))) ∧ b N = β := by
  induction N generalizing A with
  | zero =>
    let b : ∀ n, A n := fun n =>
      Nat.rec (motive := A) β (fun m bm => (ht m (Nat.zero_le m) bm).choose) n
    exact ⟨b, fun n => (ht n (Nat.zero_le n) (b n)).choose_spec.symm, rfl⟩
  | succ N ih =>
    obtain ⟨b', hb', hb'N⟩ := ih (A := fun n => A (n + 1)) (fun n => t (n + 1))
      (fun n hn => ht (n + 1) (by omega)) β
    let b : ∀ n, A n := fun n => Nat.casesOn (motive := A) n (t 0 (b' 0)) b'
    refine ⟨b, fun n => ?_, hb'N⟩
    cases n with
    | zero => rfl
    | succ m => exact hb' m

/-- If the transitions of an inverse sequence of abelian groups are injective from the index `N`
on, then a compatible family which vanishes at `N` vanishes. -/
theorem eq_zero_of_compatible (N : ℕ) (t : ∀ n, A (n + 1) →+ A n)
    (ht : ∀ n, N ≤ n → Function.Injective (t n)) (b : ∀ n, A n)
    (hb : ∀ n, b n = t n (b (n + 1))) (hN : b N = 0) (n : ℕ) : b n = 0 := by
  have below : ∀ k m, m + k = N → b m = 0 := by
    intro k
    induction k with
    | zero =>
      intro m hm
      subst hm
      exact hN
    | succ k ih =>
      intro m hm
      rw [hb m, ih (m + 1) (by omega), map_zero]
  rcases le_total n N with h | h
  · exact below (N - n) n (by omega)
  · induction n, h using Nat.le_induction with
    | base => exact hN
    | succ m hm ih => exact ht m hm (by rw [← hb m, ih, map_zero])

/-- **`lim¹` vanishes for eventually surjective transitions.**  If the transitions of an inverse
sequence of abelian groups are surjective from the index `N` on, then the map
`(wₙ) ↦ (wₙ - tₙ wₙ₊₁)` of the product to itself is surjective. -/
theorem exists_sub_shift_eq_of_surjective (N : ℕ) (t : ∀ n, A (n + 1) →+ A n)
    (ht : ∀ n, N ≤ n → Function.Surjective (t n)) (z : ∀ n, A n) :
    ∃ w : ∀ n, A n, ∀ n, w n - t n (w (n + 1)) = z n := by
  induction N generalizing A with
  | zero =>
    let w : ∀ n, A n := fun n =>
      Nat.rec (motive := A) 0 (fun m wm => (ht m (Nat.zero_le m) (wm - z m)).choose) n
    refine ⟨w, fun n => ?_⟩
    have := (ht n (Nat.zero_le n) (w n - z n)).choose_spec
    change w n - t n ((ht n (Nat.zero_le n) (w n - z n)).choose) = z n
    rw [this, sub_sub_cancel]
  | succ N ih =>
    obtain ⟨w', hw'⟩ := ih (A := fun n => A (n + 1)) (fun n => t (n + 1))
      (fun n hn => ht (n + 1) (by omega)) (fun n => z (n + 1))
    let w : ∀ n, A n := fun n => Nat.casesOn (motive := A) n (z 0 + t 0 (w' 0)) w'
    refine ⟨w, fun n => ?_⟩
    cases n with
    | zero => exact add_sub_cancel_right _ _
    | succ m => exact hw' m

end HomotopyColimitHomStable

/-! ### Morphisms out of a derived colimit -/

open Limits HomotopyColimitHomStable

/-- The map `id - shift` on `⊕ Kₙ`. -/
private noncomputable abbrev idSubShift {C : Type*} [Category C] [Preadditive C] (F : ℕ ⥤ C)
    [HasCoproduct F.obj] : ∐ F.obj ⟶ ∐ F.obj :=
  Sigma.desc fun n ↦ Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)

private theorem ι_comp_idSubShift {C : Type*} [Category C] [Preadditive C] (F : ℕ ⥤ C)
    [HasCoproduct F.obj] (n : ℕ) : Sigma.ι F.obj n ≫ idSubShift F =
      Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1) :=
  Sigma.ι_comp_desc _ _

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The coprojections of a derived colimit are compatible with the transition maps. -/
theorem IsHomotopyColimitWith.coprojection_eq {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (n : ℕ) :
    c n = F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) := by
  obtain ⟨p, q, hT, hc⟩ := h
  have h0 := Sigma.ι F.obj n ≫= comp_distTriang_mor_zero₁₂ _ hT
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, comp_zero, Sigma.ι_comp_desc_assoc,
    Preadditive.sub_comp, Category.assoc, hc] at h0
  exact sub_eq_zero.1 h0

omit [HasZeroObject D] [Pretriangulated D] in
/-- **`lim¹ Hom(Kₙ[1], B)` vanishes for an eventually stable system.**  If, from the index `N` on,
composing with `fₙ[1]` is surjective from `Hom(Kₙ₊₁[1], B)` to `Hom(Kₙ[1], B)`, then every
morphism `(⊕ Kₙ)[1] ⟶ B` factors through `d[1]`, where `d = id - shift` on `⊕ Kₙ`. -/
private theorem exists_eq_shift_map_comp_of_surjective {F : ℕ ⥤ D} [HasCoproduct F.obj]
    (B : D) (N : ℕ)
    (h₁ : ∀ n, N ≤ n → Function.Surjective (fun x : (F.obj (n + 1))⟦(1 : ℤ)⟧ ⟶ B =>
      (F.map (homOfLE (Nat.le_succ n)))⟦(1 : ℤ)⟧' ≫ x))
    (z : (∐ F.obj)⟦(1 : ℤ)⟧ ⟶ B) :
    ∃ w, z = (idSubShift F)⟦(1 : ℤ)⟧' ≫ w := by
  let hs := isColimitOfPreserves (shiftFunctor D (1 : ℤ)) (colimit.isColimit
    (Discrete.functor F.obj))
  obtain ⟨w, hw⟩ := exists_sub_shift_eq_of_surjective (A := fun n => (F.obj n)⟦(1 : ℤ)⟧ ⟶ B) N
    (fun n => Preadditive.leftComp B ((F.map (homOfLE (Nat.le_succ n)))⟦(1 : ℤ)⟧'))
    h₁ (fun n => (Sigma.ι F.obj n)⟦(1 : ℤ)⟧' ≫ z)
  let s : Cocone (Discrete.functor F.obj ⋙ shiftFunctor D (1 : ℤ)) :=
    { pt := B
      ι := Discrete.natTrans fun j => w j.as }
  refine ⟨hs.desc s, hs.hom_ext fun ⟨n⟩ => ?_⟩
  have f1 : ∀ m, (Sigma.ι F.obj m)⟦(1 : ℤ)⟧' ≫ hs.desc s = w m := fun m => hs.fac s ⟨m⟩
  change (Sigma.ι F.obj n)⟦(1 : ℤ)⟧' ≫ z =
    (Sigma.ι F.obj n)⟦(1 : ℤ)⟧' ≫ (idSubShift F)⟦(1 : ℤ)⟧' ≫ hs.desc s
  rw [← Functor.map_comp_assoc, ι_comp_idSubShift, Functor.map_sub, Preadditive.sub_comp,
    Functor.map_comp, Category.assoc, f1, f1]
  exact (hw n).symm

/-- If, from the index `N` on, composing with `fₙ` is injective from `Hom(Kₙ₊₁, B)` to
`Hom(Kₙ, B)` and composing with `fₙ[1]` is surjective from `Hom(Kₙ₊₁[1], B)` to `Hom(Kₙ[1], B)`,
then composing with `c_N` is injective on `Hom(K, B)`. -/
private theorem IsHomotopyColimitWith.injective_comp_of_stable {F : ℕ ⥤ D}
    [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (B : D) (N : ℕ)
    (h₀ : ∀ n, N ≤ n →
      Function.Injective (fun x : F.obj (n + 1) ⟶ B => F.map (homOfLE (Nat.le_succ n)) ≫ x))
    (h₁ : ∀ n, N ≤ n → Function.Surjective (fun x : (F.obj (n + 1))⟦(1 : ℤ)⟧ ⟶ B =>
      (F.map (homOfLE (Nat.le_succ n)))⟦(1 : ℤ)⟧' ≫ x)) :
    Function.Injective (fun x : K ⟶ B => c N ≫ x) := by
  have hcomp := h.coprojection_eq
  obtain ⟨p, q, hT, hc⟩ := h
  intro x x' hxx
  rw [← sub_eq_zero]
  have hN : c N ≫ (x - x') = 0 := by
    simpa only [Preadditive.comp_sub] using sub_eq_zero.2 hxx
  have hall := eq_zero_of_compatible (A := fun n => F.obj n ⟶ B) N
    (fun n => Preadditive.leftComp B (F.map (homOfLE (Nat.le_succ n))))
    (fun n hn => h₀ n hn) (fun n => c n ≫ (x - x'))
    (fun n => by
      change c n ≫ (x - x') = F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) ≫ (x - x')
      rw [hcomp n, Category.assoc]) hN
  have hp : p ≫ (x - x') = 0 :=
    Sigma.hom_ext _ _ fun n => by
      rw [← Category.assoc, hc, comp_zero]
      exact hall n
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hT (x - x') hp
  obtain ⟨w, hw⟩ := exists_eq_shift_map_comp_of_surjective B N h₁ g
  rw [hg, hw]
  change q ≫ (idSubShift F)⟦(1 : ℤ)⟧' ≫ w = 0
  rw [← Category.assoc, show q ≫ (idSubShift F)⟦(1 : ℤ)⟧' = 0 from
    comp_distTriang_mor_zero₃₁ _ hT, zero_comp]

/-- If, from the index `N` on, composing with `fₙ` is surjective from `Hom(Kₙ₊₁, B)` to
`Hom(Kₙ, B)`, then composing with `c_N` is surjective from `Hom(K, B)` to `Hom(K_N, B)`. -/
private theorem IsHomotopyColimitWith.surjective_comp_of_stable {F : ℕ ⥤ D}
    [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (B : D) (N : ℕ)
    (h₀ : ∀ n, N ≤ n →
      Function.Surjective (fun x : F.obj (n + 1) ⟶ B => F.map (homOfLE (Nat.le_succ n)) ≫ x)) :
    Function.Surjective (fun x : K ⟶ B => c N ≫ x) := by
  obtain ⟨p, q, hT, hc⟩ := h
  intro β
  obtain ⟨b, hb, hbN⟩ := exists_compatible_of_surjective (A := fun n => F.obj n ⟶ B) N
    (fun n => Preadditive.leftComp B (F.map (homOfLE (Nat.le_succ n)))) (fun n hn => h₀ n hn) β
  have hdb : idSubShift F ≫ Sigma.desc b = 0 :=
    Sigma.hom_ext _ _ fun n => by
      rw [← Category.assoc, ι_comp_idSubShift, Preadditive.sub_comp, Category.assoc,
        Sigma.ι_comp_desc, Sigma.ι_comp_desc, comp_zero, sub_eq_zero]
      exact hb n
  obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ _ hT (Sigma.desc b) hdb
  refine ⟨x, ?_⟩
  change c N ≫ x = β
  rw [← hc, Category.assoc]
  change Sigma.ι F.obj N ≫ (Triangle.mk (idSubShift F) p q).mor₂ ≫ x = β
  rw [← hx, Sigma.ι_comp_desc, hbN]

/-- **Morphisms out of a derived colimit of an eventually stable system.**  Let
`K = hocolim Kₙ` with coprojections `cₙ`, and let `B` be an object such that, from the index `N`
on, composing with the transition map `fₙ : Kₙ ⟶ Kₙ₊₁` is bijective from `Hom(Kₙ₊₁, B)` to
`Hom(Kₙ, B)` and surjective from `Hom(Kₙ₊₁[1], B)` to `Hom(Kₙ[1], B)`.  Then composing with `c_N`
is a bijection `Hom(K, B) ⟶ Hom(K_N, B)`. -/
theorem IsHomotopyColimitWith.bijective_comp_of_stable {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (B : D) (N : ℕ)
    (h₀ : ∀ n, N ≤ n →
      Function.Bijective (fun x : F.obj (n + 1) ⟶ B => F.map (homOfLE (Nat.le_succ n)) ≫ x))
    (h₁ : ∀ n, N ≤ n → Function.Surjective (fun x : (F.obj (n + 1))⟦(1 : ℤ)⟧ ⟶ B =>
      (F.map (homOfLE (Nat.le_succ n)))⟦(1 : ℤ)⟧' ≫ x)) :
    Function.Bijective (fun x : K ⟶ B => c N ≫ x) :=
  ⟨IsHomotopyColimitWith.injective_comp_of_stable h B N (fun n hn => (h₀ n hn).1) h₁,
    IsHomotopyColimitWith.surjective_comp_of_stable h B N fun n hn => (h₀ n hn).2⟩

end CategoryTheory.Pretriangulated

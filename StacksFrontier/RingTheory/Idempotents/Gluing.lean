module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.Order.Ring.Idempotent
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Gluing over the idempotents of a ring

The idempotents of a commutative ring `C` form a Boolean algebra, the Boolean algebra of clopen
subsets of `Spec C`. A presheaf of abelian groups `M` on it is *additive* if for disjoint `e, f`
restriction identifies `M (e ⊔ f)` with `M e × M f`; this is the sheaf condition for the finite
disjoint covers which generate the topology of the profinite space of components.

This file proves that for a morphism `φ : M ⟶ N` of additive presheaves, bijectivity of `φ` at
the top element is a local condition: it holds if and only if, at every prime `𝔭` of `C`, `φ`
is bijective on germs at `𝔭`, the germs being taken along the idempotents not in `𝔭`. The
argument is the compactness of `Spec C`: a family of idempotents reaching outside every prime
generates the unit ideal, so finitely many of them already have supremum `⊤`, and those can be
disjointified.

When the germs at `𝔭` are computed by colimit cocones, bijectivity on germs is bijectivity of the
induced map of colimits; `bijective_desc_iff_isBijectiveAt` records that translation.

## Main definitions

* `StacksDraft.IdempotentGluing.IsAdditive`: additivity of a presheaf on idempotents.
* `StacksDraft.IdempotentGluing.IsBijectiveAt`: bijectivity on germs at a prime.

## Main results

* `StacksDraft.IdempotentGluing.bijective_app_top_iff`: bijectivity at the top is equivalent to
  bijectivity on germs at every prime.
* `StacksDraft.IdempotentGluing.bijective_desc_iff_isBijectiveAt`: bijectivity on germs is
  bijectivity on colimits along the idempotents not in the prime.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV): the passage from the
  cofiltered limit of finite disjoint unions to the cohomology of the limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite OrderDual

universe w u

namespace StacksDraft.IdempotentGluing

variable {C : Type u} [CommRing C]

/-- The Boolean algebra of idempotents of `C`. -/
abbrev Idem (C : Type u) [CommRing C] := {e : C // IsIdempotentElem e}

/-- Restriction from `f` to a smaller idempotent `e` in a presheaf on idempotents. -/
abbrev res (M : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}) {e f : Idem C} (h : e ≤ f) :
    M.obj (toDual f) → M.obj (toDual e) :=
  fun m => M.map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) m

/-- Restricting from `g` to `f` and then from `f` to `e` is restricting from `g` to `e`. -/
theorem res_res (M : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}) {e f g : Idem C} (hef : e ≤ f)
    (hfg : f ≤ g) (m : M.obj (toDual g)) : res M hef (res M hfg m) = res M (hef.trans hfg) m := by
  simp only [res, ← ConcreteCategory.comp_apply, ← M.map_comp]
  rfl

/-- Restriction from `e` to itself is the identity. -/
theorem res_refl (M : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}) {e : Idem C} (m : M.obj (toDual e)) :
    res M (le_refl e) m = m := by
  show (M.map (𝟙 (toDual e))) m = m
  rw [M.map_id]
  rfl

/-- Restriction sends `0` to `0`. -/
theorem res_zero (M : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}) {e f : Idem C} (h : e ≤ f) :
    res M h 0 = 0 := map_zero _

/-- Restriction commutes with subtraction. -/
theorem res_sub (M : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}) {e f : Idem C} (h : e ≤ f)
    (m m' : M.obj (toDual f)) : res M h (m - m') = res M h m - res M h m' := map_sub _ _ _

/-- A morphism of presheaves on idempotents commutes with restriction. -/
theorem naturality_apply {M N : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}} (φ : M ⟶ N) {e f : Idem C}
    (h : e ≤ f) (m : M.obj (toDual f)) :
    φ.app (toDual e) (res M h m) = res N h (φ.app (toDual f) m) := by
  simp only [res, ← ConcreteCategory.comp_apply, φ.naturality]

/-- A presheaf on idempotents is *additive* if, for disjoint `e` and `f`, restriction identifies
`M (e ⊔ f)` with `M e × M f`. -/
def IsAdditive (M : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}) : Prop :=
  ∀ e f : Idem C, Disjoint e f →
    Function.Bijective (fun m : M.obj (toDual (e ⊔ f)) =>
      (res M (le_sup_left : e ≤ e ⊔ f) m, res M (le_sup_right : f ≤ e ⊔ f) m))

/-- `φ` is *bijective on germs at the prime `𝔭`*: an element killed by `φ` dies on some smaller
idempotent not in `𝔭`, and every element of the target is, on some smaller idempotent not in
`𝔭`, in the image of `φ`. -/
def IsBijectiveAt {M N : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}} (φ : M ⟶ N) (P : Ideal C) : Prop :=
  (∀ (e : Idem C), (e : C) ∉ P → ∀ m : M.obj (toDual e), φ.app (toDual e) m = 0 →
      ∃ (e' : Idem C) (h : e' ≤ e), (e' : C) ∉ P ∧ res M h m = 0) ∧
    (∀ (e : Idem C), (e : C) ∉ P → ∀ n : N.obj (toDual e),
      ∃ (e' : Idem C) (h : e' ≤ e), (e' : C) ∉ P ∧
        ∃ m : M.obj (toDual e'), φ.app (toDual e') m = res N h n)

section Cover

/-- **Compactness of `Spec C` in the language of idempotents.** If every prime not containing
`g` misses some idempotent `e ≤ g` with property `Q`, then `g` is the supremum of finitely many
idempotents below `g` with property `Q`. -/
theorem exists_finset_sup_eq (g : Idem C) (Q : Idem C → Prop)
    (hQ : ∀ P : Ideal C, P.IsPrime → (g : C) ∉ P → ∃ e : Idem C, e ≤ g ∧ (e : C) ∉ P ∧ Q e) :
    ∃ s : Finset (Idem C), (∀ e ∈ s, e ≤ g ∧ Q e) ∧ s.sup id = g := by
  classical
  let S : Set (Idem C) := {e | e ≤ g ∧ Q e}
  have hspan : Ideal.span (((↑) : Idem C → C) '' S ∪ {1 - (g : C)}) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hg : (g : C) ∉ P := by
      intro hg
      have h1 : 1 - (g : C) ∈ P := hle (Ideal.subset_span (Or.inr rfl))
      exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using P.add_mem h1 hg))
    obtain ⟨e, heg, heP, hQe⟩ := hQ P hP.isPrime hg
    exact heP (hle (Ideal.subset_span (Or.inl ⟨e, ⟨heg, hQe⟩, rfl⟩)))
  obtain ⟨t, htS, h1⟩ := Submodule.mem_span_finite_of_mem_span
    ((Ideal.eq_top_iff_one _).mp hspan)
  have ht' : ↑(t.erase (1 - (g : C))) ⊆ ((↑) : Idem C → C) '' S := by
    intro z hz
    rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff] at hz
    exact (htS hz.1).resolve_right hz.2
  obtain ⟨s, hsS, hs⟩ := Finset.subset_set_image_iff.mp ht'
  refine ⟨s, fun e he => hsS he, ?_⟩
  have hle : s.sup id ≤ g := Finset.sup_le fun e he => (hsS he).1
  refine le_antisymm hle ?_
  -- every element of the span of `t` kills `g (1 - sup s)`
  set h := s.sup id
  have hkill : ∀ z ∈ Submodule.span C (t : Set C), z * ((g : C) * (1 - h)) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      by_cases hz' : z = 1 - (g : C)
      · rw [hz', ← mul_assoc, sub_mul, one_mul, g.2.eq, sub_self, zero_mul]
      · have : z ∈ ((↑) : Idem C → C) '' (s : Set (Idem C)) := by
          rw [← Finset.coe_image, hs]
          exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hz', hz⟩)
        obtain ⟨e, he, rfl⟩ := this
        have heg : (e : C) * g = e := (hsS he).1
        have heh : (e : C) * h = e := (Finset.le_sup (f := id) he : e ≤ h)
        rw [← mul_assoc, heg, mul_sub, mul_one, heh, sub_self]
    | zero => rw [zero_mul]
    | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_eq_mul, mul_assoc, ha, mul_zero]
  have := hkill 1 h1
  rw [one_mul, mul_sub, mul_one, sub_eq_zero] at this
  exact this.symm

end Cover


section Additive

variable {M N : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}}

/-- Additivity, for an idempotent which is the supremum of two disjoint ones only up to
equality. -/
theorem IsAdditive.bijective_of_eq (hM : IsAdditive M) {e f k : Idem C} (hd : Disjoint e f)
    (hk : e ⊔ f = k) (he : e ≤ k) (hf : f ≤ k) :
    Function.Bijective (fun m : M.obj (toDual k) => (res M he m, res M hf m)) := by
  subst hk
  exact hM e f hd

/-- An additive presheaf vanishes at `⊥`. -/
theorem IsAdditive.eq_zero_of_eq_bot (hM : IsAdditive M) {k : Idem C} (hk : k = ⊥)
    (x : M.obj (toDual k)) : x = 0 := by
  subst hk
  obtain ⟨y, hy⟩ := (hM.bijective_of_eq (disjoint_bot_left (a := (⊥ : Idem C))) (by simp)
    le_rfl le_rfl).2 (0, x)
  simp only [res_refl, Prod.mk.injEq] at hy
  rw [← hy.2, hy.1]

/-- Additivity for the disjoint decomposition `e ⊔ f = e ⊔ (f \ e)`. -/
private theorem IsAdditive.bijective_sdiff (hM : IsAdditive M) (e f : Idem C) :
    Function.Bijective (fun m : M.obj (toDual (e ⊔ f)) =>
      (res M (le_sup_left : e ≤ e ⊔ f) m,
        res M (sdiff_le.trans le_sup_right : f \ e ≤ e ⊔ f) m)) :=
  hM.bijective_of_eq (disjoint_sdiff_self_right : Disjoint e (f \ e))
    (sup_sdiff_self_right e f) le_sup_left (sdiff_le.trans le_sup_right)

/-- Two elements of an additive presheaf agreeing on `e` and on `f` agree on `e ⊔ f`. -/
theorem IsAdditive.res_eq_of_res_eq (hM : IsAdditive M) {g e f : Idem C} (he : e ≤ g)
    (hf : f ≤ g) (m m' : M.obj (toDual g)) (h1 : res M he m = res M he m')
    (h2 : res M hf m = res M hf m') :
    res M (sup_le he hf) m = res M (sup_le he hf) m' := by
  have hfe : f \ e ≤ f := sdiff_le
  apply (hM.bijective_sdiff e f).1
  simp only [res_res, Prod.mk.injEq]
  refine ⟨h1, ?_⟩
  rw [← res_res M hfe hf, ← res_res M hfe hf, h2]

/-- An element of an additive presheaf vanishing on each member of a finite family vanishes on
their supremum. -/
theorem IsAdditive.res_sup_eq_zero (hM : IsAdditive M) {g : Idem C} (m : M.obj (toDual g))
    (s : Finset (Idem C)) (hs : ∀ e ∈ s, ∃ h : e ≤ g, res M h m = 0)
    (hsg : s.sup id ≤ g) : res M hsg m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hM.eq_zero_of_eq_bot rfl _
  | insert a s ha ih =>
    obtain ⟨hag, ham⟩ := hs a (Finset.mem_insert_self a s)
    have hsg' : s.sup id ≤ g := (Finset.sup_mono (Finset.subset_insert a s)).trans hsg
    have := hM.res_eq_of_res_eq hag hsg' m 0 (by rw [ham, res_zero])
      (by rw [ih (fun e he => hs e (Finset.mem_insert_of_mem he)) hsg', res_zero])
    rw [res_zero] at this
    have hsup : a ⊔ s.sup id = (insert a s).sup id := by rw [Finset.sup_insert]; rfl
    revert hsg
    rw [← hsup]
    intro hsg
    exact this

/-- In an additive presheaf, an element over `e` and an element over `f` which agree on `e ⊓ f`
glue to an element over `e ⊔ f`. -/
theorem IsAdditive.exists_glue (hM : IsAdditive M) {e f : Idem C} (m : M.obj (toDual e))
    (m' : M.obj (toDual f)) :
    ∃ n : M.obj (toDual (e ⊔ f)), res M le_sup_left n = m ∧
      res M (sdiff_le.trans le_sup_right : f \ e ≤ e ⊔ f) n = res M sdiff_le m' := by
  obtain ⟨n, hn⟩ := (hM.bijective_sdiff e f).2 (m, res M sdiff_le m')
  exact ⟨n, (Prod.mk.injEq _ _ _ _).mp hn⟩

end Additive

section Main

variable {M N : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}}

/-- If `φ` is bijective at `⊤` between additive presheaves, it is bijective at every
idempotent: restriction to `g` and to its complement identifies `φ` at `⊤` with the product of
`φ` at `g` and at `gᶜ`. -/
theorem bijective_app_of_bijective_app_top (hM : IsAdditive M) (hN : IsAdditive N) (φ : M ⟶ N)
    (hφ : Function.Bijective (φ.app (toDual ⊤))) (g : Idem C) :
    Function.Bijective (φ.app (toDual g)) := by
  have hd : Disjoint g gᶜ := disjoint_compl_right
  have hk : g ⊔ gᶜ = ⊤ := sup_compl_eq_top
  have hMb := hM.bijective_of_eq hd hk le_top le_top
  have hNb := hN.bijective_of_eq hd hk le_top le_top
  refine ⟨(injective_iff_map_eq_zero (φ.app (toDual g)).hom).mpr fun m hm => ?_, fun n => ?_⟩
  · obtain ⟨x, hx⟩ := hMb.2 (m, 0)
    simp only [Prod.mk.injEq] at hx
    have hφx : φ.app (toDual ⊤) x = 0 := by
      apply hNb.1
      simp only [← naturality_apply, hx.1, hx.2, hm, map_zero]
    have := hφ.1 (hφx.trans (map_zero _).symm)
    rw [← hx.1, this, res_zero]
  · obtain ⟨y, hy⟩ := hNb.2 (n, 0)
    simp only [Prod.mk.injEq] at hy
    obtain ⟨x, rfl⟩ := hφ.2 y
    exact ⟨res M le_top x, by rw [naturality_apply, hy.1]⟩

/-- **Gluing along idempotents.** For a morphism `φ` of additive presheaves on the idempotents of
`C`, `φ` is bijective at `⊤` if and only if it is bijective on germs at every prime of `C`. -/
theorem bijective_app_top_iff (hM : IsAdditive M) (hN : IsAdditive N) (φ : M ⟶ N) :
    Function.Bijective (φ.app (toDual ⊤)) ↔ ∀ P : Ideal C, P.IsPrime → IsBijectiveAt φ P := by
  classical
  constructor
  · intro hφ P _
    refine ⟨fun e _ m hm => ⟨e, le_rfl, ‹_›, ?_⟩, fun e _ n => ⟨e, le_rfl, ‹_›, ?_⟩⟩
    · rw [res_refl]
      exact (bijective_app_of_bijective_app_top hM hN φ hφ e).1 (hm.trans (map_zero _).symm)
    · obtain ⟨m, hm⟩ := (bijective_app_of_bijective_app_top hM hN φ hφ e).2 n
      exact ⟨m, by rw [hm, res_refl]⟩
  · intro H
    have h1P : ∀ P : Ideal C, P.IsPrime → ((⊤ : Idem C) : C) ∉ P := fun P hP h =>
      hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
    refine ⟨(injective_iff_map_eq_zero (φ.app (toDual ⊤)).hom).mpr fun m hm => ?_, fun n => ?_⟩
    · obtain ⟨s, hs, hsup⟩ := exists_finset_sup_eq (⊤ : Idem C)
        (fun e => ∃ h : e ≤ ⊤, res M h m = 0) (fun P hP _ => by
          obtain ⟨e', h, he', hm'⟩ := (H P hP).1 ⊤ (h1P P hP) m hm
          exact ⟨e', h, he', h, hm'⟩)
      have := hM.res_sup_eq_zero m s (fun e he => (hs e he).2) (hsup ▸ le_rfl)
      have hcast : ∀ (k : Idem C) (hk : k = ⊤) (x : M.obj (toDual ⊤)),
          res M (hk ▸ le_rfl : k ≤ ⊤) x = 0 → x = 0 := by
        rintro k rfl x hx
        rwa [res_refl] at hx
      exact hcast _ hsup m this
    · obtain ⟨s, hs, hsup⟩ := exists_finset_sup_eq (⊤ : Idem C)
        (fun e => ∃ (h : e ≤ ⊤) (m : M.obj (toDual e)), φ.app (toDual e) m = res N h n)
        (fun P hP _ => by
          obtain ⟨e', h, he', hm'⟩ := (H P hP).2 ⊤ (h1P P hP) n
          exact ⟨e', h, he', h, hm'⟩)
      have key : ∀ t : Finset (Idem C), t ⊆ s → ∀ k : Idem C, t.sup id = k →
          ∃ m : M.obj (toDual k), φ.app (toDual k) m = res N le_top n := by
        intro t
        induction t using Finset.induction_on with
        | empty =>
          rintro - k rfl
          exact ⟨0, (hN.eq_zero_of_eq_bot rfl _).trans (hN.eq_zero_of_eq_bot rfl _).symm⟩
        | insert a t ha ih =>
          rintro hts k rfl
          obtain ⟨mt, hmt⟩ := ih ((Finset.subset_insert a t).trans hts) _ rfl
          obtain ⟨_, ma, hma⟩ := (hs a (hts (Finset.mem_insert_self a t))).2
          obtain ⟨g, hg1, hg2⟩ := hM.exists_glue ma mt
          have hsup' : a ⊔ t.sup id = (insert a t).sup id := by rw [Finset.sup_insert]; rfl
          have hφg : φ.app (toDual (a ⊔ t.sup id)) g = res N le_top n := by
            apply (hN.bijective_sdiff a (t.sup id)).1
            simp only [Prod.mk.injEq, ← naturality_apply, hg1, hg2, res_res]
            refine ⟨hma, ?_⟩
            rw [naturality_apply, hmt, res_res]
          rw [← hsup']
          exact ⟨g, hφg⟩
      obtain ⟨m, hm⟩ := key s subset_rfl ⊤ hsup
      exact ⟨m, by rw [hm, res_refl]⟩

end Main

section Germs

variable (P : Ideal C) [P.IsPrime]

/-- The idempotents not in the prime `𝔭`, ordered by reverse inclusion of the corresponding
clopen subsets: the clopen neighbourhoods of the point `𝔭` of `Spec C`, directed towards `𝔭`. -/
abbrev GermIdx := {e : (Idem C)ᵒᵈ // ((ofDual e : Idem C) : C) ∉ P}

/-- The inclusion of the idempotents not in `𝔭` among all idempotents, in reverse order. -/
abbrev germIncl : GermIdx P ⥤ (Idem C)ᵒᵈ := Monotone.functor (f := Subtype.val) fun _ _ h => h

/-- Two idempotents not in `𝔭` are both refined by their product, which is again not in `𝔭`
since `𝔭` is prime. -/
instance : IsDirected (GermIdx P) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨toDual (ofDual a.1 ⊓ ofDual b.1), fun h => by
    rcases Ideal.IsPrime.mem_or_mem ‹_› h with h | h
    exacts [a.2 h, b.2 h]⟩, show ofDual a.1 ⊓ ofDual b.1 ≤ ofDual a.1 from inf_le_left,
    show ofDual a.1 ⊓ ofDual b.1 ≤ ofDual b.1 from inf_le_right⟩⟩

/-- The idempotent `1` is not in the prime `𝔭`. -/
instance : Nonempty (GermIdx P) :=
  ⟨⟨toDual ⊤, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one P).mpr h)⟩⟩

/-- The idempotents not in `𝔭`, in reverse order, form a filtered category. -/
instance : IsFiltered (GermIdx P) := inferInstance

/-- A colimit cocone over the germs sends an element to the same value as its restriction. -/
private theorem germ_ι_app_res {P : Ideal C} {F : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}}
    {c : Cocone (germIncl P ⋙ F)} {e e' : GermIdx P} (h : e ≤ e') (x : F.obj e.1) :
    c.ι.app e' (res F h x) = c.ι.app e x :=
  ConcreteCategory.congr_hom (c.w (homOfLE h)) x

variable [UnivLE.{u, w}] {M N : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}}

/-- Two elements have the same image in a colimit of germs iff they agree on a smaller
idempotent not in `𝔭`. -/
private theorem germ_ι_eq_iff {F : (Idem C)ᵒᵈ ⥤ AddCommGrpCat.{w}}
    {c : Cocone (germIncl P ⋙ F)} (hc : IsColimit c) (e : GermIdx P) (x y : F.obj e.1) :
    c.ι.app e x = c.ι.app e y ↔ ∃ (e' : GermIdx P) (h : e ≤ e'), res F h x = res F h y := by
  have := preservesFilteredColimitsOfSize_of_univLE.{w, w, u, u} (forget AddCommGrpCat.{w})
  rw [Concrete.isColimit_rep_eq_iff_exists _ hc]
  constructor
  · rintro ⟨k, f, g, hfg⟩
    have : f = g := Subsingleton.elim _ _
    subst this
    exact ⟨k, leOfHom f, hfg⟩
  · rintro ⟨e', h, hx⟩
    exact ⟨e', homOfLE h, homOfLE h, hx⟩

/-- **Germs as colimits.** If the germs of `M` and `N` at `𝔭` are computed by colimit cocones
along the idempotents not in `𝔭`, then the map induced by `φ` on those colimits is bijective if
and only if `φ` is bijective on germs at `𝔭`. -/
theorem bijective_desc_iff_isBijectiveAt (φ : M ⟶ N)
    {cM : Cocone (germIncl P ⋙ M)} (hcM : IsColimit cM)
    {cN : Cocone (germIncl P ⋙ N)} (hcN : IsColimit cN) (ψ : cM.pt ⟶ cN.pt)
    (hψ : ∀ j, cM.ι.app j ≫ ψ = φ.app j.1 ≫ cN.ι.app j) :
    Function.Bijective ψ ↔ IsBijectiveAt φ P := by
  have := preservesFilteredColimitsOfSize_of_univLE.{w, w, u, u}
    (forget AddCommGrpCat.{w})
  have hψa : ∀ j x, ψ (cM.ι.app j x) = cN.ι.app j (φ.app j.1 x) := fun j x => by
    rw [← ConcreteCategory.comp_apply, hψ, ConcreteCategory.comp_apply]
  have hzeroM : ∀ (e : GermIdx P) (x : M.obj e.1), cM.ι.app e x = 0 ↔
      ∃ (e' : GermIdx P) (h : e ≤ e'), res M h x = 0 := fun e x => by
    have := germ_ι_eq_iff P hcM e x 0
    rw [map_zero] at this
    rw [this]
    exact exists_congr fun _ => exists_congr fun _ => Eq.congr_right (map_zero _)
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun e he m hm => ?_, fun e he n => ?_⟩
    · have : cM.ι.app ⟨toDual e, he⟩ m = 0 := hinj (by
        rw [hψa, map_zero]
        exact (show φ.app (toDual e) m = 0 from hm) ▸ map_zero _)
      obtain ⟨e', h, h0⟩ := (hzeroM ⟨toDual e, he⟩ m).mp this
      exact ⟨ofDual e'.1, h, e'.2, h0⟩
    · obtain ⟨z, hz⟩ := hsurj (cN.ι.app ⟨toDual e, he⟩ n)
      obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep _ hcM z
      obtain ⟨k, hke, hkj⟩ := (inferInstance : IsDirected (GermIdx P) (· ≤ ·)).directed
        (⟨toDual e, he⟩ : GermIdx P) j
      have h1 : cN.ι.app k (φ.app k.1 (res M hkj y)) = cN.ι.app k (res N hke n) := by
        calc cN.ι.app k (φ.app k.1 (res M hkj y))
            = ψ (cM.ι.app k (res M hkj y)) := (hψa _ _).symm
          _ = ψ (cM.ι.app j y) := congrArg ψ (germ_ι_app_res hkj y)
          _ = cN.ι.app ⟨toDual e, he⟩ n := hz
          _ = cN.ι.app k (res N hke n) := (germ_ι_app_res hke n).symm
      obtain ⟨k', hk', hk'eq⟩ := (germ_ι_eq_iff P hcN k _ _).mp h1
      refine ⟨ofDual k'.1, hke.trans hk', k'.2, res M (hkj.trans hk') y, ?_⟩
      have h2 : res M (hkj.trans hk') y = res M hk' (res M hkj y) := (res_res M _ _ y).symm
      have h3 : res N (hke.trans hk') n = res N hk' (res N hke n) := (res_res N _ _ n).symm
      have h4 := naturality_apply φ (e := ofDual k'.1) (f := ofDual k.1) hk' (res M hkj y)
      refine (congrArg _ h2).trans (h4.trans ?_)
      exact hk'eq.trans h3.symm
  · rintro ⟨hinj, hsurj⟩
    refine ⟨(injective_iff_map_eq_zero ψ.hom).mpr fun z hz => ?_, fun z => ?_⟩
    · obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep _ hcM z
      rw [hψa] at hz
      obtain ⟨e', h, h0⟩ := (germ_ι_eq_iff P hcN j _ 0).mp (hz.trans (map_zero _).symm)
      rw [show res N h (0 : N.obj j.1) = 0 from map_zero _] at h0
      have h0'' : φ.app (toDual (ofDual e'.1)) (res M h y) = 0 :=
        (naturality_apply φ (e := ofDual e'.1) (f := ofDual j.1) h y).trans h0
      obtain ⟨e'', h', he'', h0'⟩ := hinj (ofDual e'.1) e'.2 _ h0''
      exact (hzeroM j y).mpr ⟨⟨toDual e'', he''⟩, h'.trans h,
        (res_res M h' h y).symm.trans h0'⟩
    · obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep _ hcN z
      obtain ⟨e', h, he', m, hm⟩ := hsurj (ofDual j.1) j.2 y
      refine ⟨cM.ι.app ⟨toDual e', he'⟩ m, ?_⟩
      rw [hψa]
      show cN.ι.app ⟨toDual e', he'⟩ _ = _
      rw [hm]
      exact germ_ι_app_res (e := j) (e' := ⟨toDual e', he'⟩) h y

end Germs

/-! ### Gluing for a family of kernels -/

section Kernels

variable {H : Type*} [AddCommGroup H]

/-- A family of subgroups of an abelian group `H` indexed by the idempotents of `C`, thought of as
the kernels of the restrictions of `H` to the clopen subsets of `Spec C`, is *additive* if it is
antitone, everything at `⊥`, and if for disjoint `e` and `f` the kernel at `e ⊔ f` contains the
intersection of the kernels at `e` and `f` and any two classes at `e` and at `f` are matched by one
element. -/
structure IsAdditiveKernels (K : Idem C → AddSubgroup H) : Prop where
  antitone : Antitone K
  bot : K ⊥ = ⊤
  inf_le : ∀ e f : Idem C, Disjoint e f → K e ⊓ K f ≤ K (e ⊔ f)
  exists_sub_mem : ∀ e f : Idem C, Disjoint e f → ∀ x y : H, ∃ z, z - x ∈ K e ∧ z - y ∈ K f

variable {K : Idem C → AddSubgroup H}

/-- For additive kernels, `K e ⊓ K f ≤ K (e ⊔ f)` holds for all `e` and `f`, not only for
disjoint ones. -/
theorem IsAdditiveKernels.inf_le_sup (hK : IsAdditiveKernels K) (e f : Idem C) :
    K e ⊓ K f ≤ K (e ⊔ f) := by
  intro x ⟨hxe, hxf⟩
  have := hK.inf_le e (f \ e) disjoint_sdiff_self_right ⟨hxe, hK.antitone sdiff_le hxf⟩
  rwa [sup_sdiff_self_right] at this

/-- For additive kernels, an element lying in the kernel at every idempotent of a finite set lies
in the kernel at their join. -/
theorem IsAdditiveKernels.mem_finset_sup (hK : IsAdditiveKernels K) (s : Finset (Idem C))
    {x : H} (hx : ∀ e ∈ s, x ∈ K e) : x ∈ K (s.sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, hK.bot]
    exact AddSubgroup.mem_top x
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    exact hK.inf_le_sup a _ ⟨hx a (Finset.mem_insert_self a s),
      ih fun e he => hx e (Finset.mem_insert_of_mem he)⟩

variable {H' : Type*} [AddCommGroup H'] {K' : Idem C → AddSubgroup H'}

/-- **Gluing for kernels.** Let `ρ : H → H'` be a homomorphism and `K`, `K'` additive families
of subgroups indexed by the idempotents of `C`, preserved by `ρ`, with `K ⊤ = K' ⊤ = 0`. Suppose
that at every prime `𝔭` of `C` there are surjections `π : H → H_𝔭`, `π' : H' → H'_𝔭` whose
kernels are the unions of the `K e`, respectively `K' e`, over the idempotents `e ∉ 𝔭`, and a
homomorphism `ρ_𝔭 : H_𝔭 → H'_𝔭` with `ρ_𝔭 ∘ π = π' ∘ ρ`. Then `ρ` is bijective if and only if
every `ρ_𝔭` is. -/
theorem bijective_iff_forall_bijective_germ (hK : IsAdditiveKernels K)
    (hK' : IsAdditiveKernels K') (ρ : H →+ H') (hρ : ∀ e x, x ∈ K e → ρ x ∈ K' e)
    (htop : K ⊤ = ⊥) (htop' : K' ⊤ = ⊥)
    (Hp : ∀ P : Ideal C, P.IsPrime → Type*) [∀ P hP, AddCommGroup (Hp P hP)]
    (Hp' : ∀ P : Ideal C, P.IsPrime → Type*) [∀ P hP, AddCommGroup (Hp' P hP)]
    (π : ∀ P hP, H →+ Hp P hP) (π' : ∀ P hP, H' →+ Hp' P hP)
    (hπ : ∀ P hP, Function.Surjective (π P hP)) (hπ' : ∀ P hP, Function.Surjective (π' P hP))
    (hker : ∀ P hP x, π P hP x = 0 ↔ ∃ e : Idem C, (e : C) ∉ P ∧ x ∈ K e)
    (hker' : ∀ P hP x, π' P hP x = 0 ↔ ∃ e : Idem C, (e : C) ∉ P ∧ x ∈ K' e)
    (ρp : ∀ P hP, Hp P hP →+ Hp' P hP) (hρp : ∀ P hP x, ρp P hP (π P hP x) = π' P hP (ρ x)) :
    Function.Bijective ρ ↔ ∀ P hP, Function.Bijective (ρp P hP) := by
  classical
  have hzero : ∀ x : H, x ∈ K ⊤ → x = 0 := fun x hx => by rwa [htop] at hx
  have hzero' : ∀ x : H', x ∈ K' ⊤ → x = 0 := fun x hx => by rwa [htop'] at hx
  constructor
  · intro hρbij P hP
    refine ⟨(injective_iff_map_eq_zero (ρp P hP)).mpr fun z hz => ?_, fun z => ?_⟩
    · obtain ⟨x, rfl⟩ := hπ P hP z
      rw [hρp, hker'] at hz
      obtain ⟨e, he, hx⟩ := hz
      obtain ⟨z, hz1, hz2⟩ := hK.exists_sub_mem e eᶜ disjoint_compl_right x 0
      have hρz : ρ z = 0 := by
        apply hzero'
        rw [← (sup_compl_eq_top : e ⊔ eᶜ = ⊤)]
        refine hK'.inf_le e eᶜ disjoint_compl_right ⟨?_, ?_⟩
        · simpa [map_sub] using (K' e).add_mem (hρ e _ hz1) hx
        · simpa using hρ eᶜ _ hz2
      have hz0 : z = 0 := hρbij.1 (hρz.trans (map_zero ρ).symm)
      rw [hker]
      exact ⟨e, he, by simpa [hz0] using (K e).neg_mem hz1⟩
    · obtain ⟨y, rfl⟩ := hπ' P hP z
      obtain ⟨x, rfl⟩ := hρbij.2 y
      exact ⟨π P hP x, hρp P hP x⟩
  · intro hH
    refine ⟨(injective_iff_map_eq_zero ρ).mpr fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨s, hs, hsup⟩ := exists_finset_sup_eq (⊤ : Idem C) (fun e => x ∈ K e)
        fun P hP _ => by
          have h0 : ρp P hP (π P hP x) = 0 := by rw [hρp, hx, map_zero]
          obtain ⟨e, he, hxe⟩ := (hker P hP x).mp ((hH P hP).1 (h0.trans (map_zero _).symm))
          exact ⟨e, le_top, he, hxe⟩
      exact hzero x (hsup ▸ hK.mem_finset_sup s fun e he => (hs e he).2)
    · -- local preimages
      obtain ⟨s, hs, hsup⟩ := exists_finset_sup_eq (⊤ : Idem C)
        (fun e => ∃ x : H, y - ρ x ∈ K' e) fun P hP _ => by
          obtain ⟨z, hz⟩ := (hH P hP).2 (π' P hP y)
          obtain ⟨x, rfl⟩ := hπ P hP z
          rw [hρp, ← sub_eq_zero, ← map_sub, hker'] at hz
          obtain ⟨e, he, hxy⟩ := hz
          exact ⟨e, le_top, he, x, by simpa using (K' e).neg_mem hxy⟩
      -- glue the local preimages along the finite family
      have key : ∀ t : Finset (Idem C), t ⊆ s → ∃ x : H, y - ρ x ∈ K' (t.sup id) := by
        intro t
        induction t using Finset.induction_on with
        | empty => intro _; exact ⟨0, by rw [Finset.sup_empty, hK'.bot]; trivial⟩
        | insert a t ha ih =>
          intro hts
          obtain ⟨x, hx⟩ := ih ((Finset.subset_insert a t).trans hts)
          obtain ⟨xa, hxa⟩ := (hs a (hts (Finset.mem_insert_self a t))).2
          set g := t.sup id
          obtain ⟨z, hz1, hz2⟩ := hK.exists_sub_mem g (a \ g) disjoint_sdiff_self_right x xa
          refine ⟨z, ?_⟩
          rw [Finset.sup_insert]
          have glue : ∀ (i : Idem C) (u : H), y - ρ u ∈ K' i → z - u ∈ K i → y - ρ z ∈ K' i :=
            fun i u hu hzu => by
              simpa [map_sub, sub_sub, add_sub_cancel] using (K' i).sub_mem hu (hρ i _ hzu)
          have := hK'.inf_le g (a \ g) disjoint_sdiff_self_right
            ⟨glue g x hx hz1, glue _ xa (hK'.antitone sdiff_le hxa) hz2⟩
          rwa [sup_sdiff_self_right, sup_comm] at this
      obtain ⟨x, hx⟩ := key s subset_rfl
      rw [hsup] at hx
      exact ⟨x, (sub_eq_zero.mp (hzero' _ hx)).symm⟩

end Kernels

end StacksDraft.IdempotentGluing

module

public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplexH1

/-!
# Čech differentials of families of groups indexed by finite sets

For a family of additive groups `X s` indexed by the subsets `s` of `Fin r`, together with maps
`ι : X s → X t` for `s ⊆ t`, this file defines the alternating Čech differential on the products
`∏_{#s = p} X s` by the formula of `FormalGlueing.glueingDifferential`, and proves its basic
properties: naturality, the explicit formulas in degrees one and two, and `δ ∘ δ = 0` in degree
one.

## Main definitions

* `Rig.SquareZeroLift.cechDiff`: the Čech differential of a family.

## Main results

* `Rig.SquareZeroLift.glueingDifferential_eq_cechDiff`: the glueing differential is the Čech
  differential of the family of localizations.
* `Rig.SquareZeroLift.cechDiff_natural`: naturality.
* `Rig.SquareZeroLift.cechDiff_cechDiff`: `δ ∘ δ = 0` in degree one.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open Cech FormalGlueing

universe v v'

variable {r : ℕ} (X : Finset (Fin r) → Type v) [∀ s, AddCommGroup (X s)]
  (ι : ∀ {s t : Finset (Fin r)}, s ⊆ t → X s →+ X t)

/-- The product of the members of a family indexed by the subsets of a fixed size. -/
abbrev FamTerm (p : ℕ) := (s : {s : Finset (Fin r) // s.card = p}) → X s.1

/-- The alternating Čech differential of a family. -/
def cechDiff (p : ℕ) (x : FamTerm X p) : FamTerm X (p + 1) := fun T ↦
  ∑ k ∈ T.1.attach, cechSign T.1 k •
    ι (show (eraseIndex p T k).1 ⊆ T.1 from Finset.erase_subset _ _) (x (eraseIndex p T k))

/-- The component of the Čech differential at `T` is the signed sum over `k ∈ T` of the images of
the components at `T \ {k}`. -/
theorem cechDiff_apply (p : ℕ) (x : FamTerm X p) (T : {s : Finset (Fin r) // s.card = p + 1}) :
    cechDiff X ι p x T = ∑ k ∈ T.1.attach, cechSign T.1 k •
      ι (show (eraseIndex p T k).1 ⊆ T.1 from Finset.erase_subset _ _)
        (x (eraseIndex p T k)) := rfl

/-- The Čech differential commutes with subtraction. -/
theorem cechDiff_sub (p : ℕ) (x y : FamTerm X p) :
    cechDiff X ι p (x - y) = cechDiff X ι p x - cechDiff X ι p y := by
  funext T
  simp only [cechDiff, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

/-- The Čech differential is additive. -/
theorem cechDiff_add (p : ℕ) (x y : FamTerm X p) :
    cechDiff X ι p (x + y) = cechDiff X ι p x + cechDiff X ι p y := by
  funext T
  simp only [cechDiff, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

/-- The Čech differential commutes with negation. -/
theorem cechDiff_neg (p : ℕ) (x : FamTerm X p) :
    cechDiff X ι p (-x) = -cechDiff X ι p x := by
  funext T
  simp only [cechDiff, Pi.neg_apply, map_neg, smul_neg, Finset.sum_neg_distrib]

/-- The Čech differential of zero is zero. -/
theorem cechDiff_zero (p : ℕ) : cechDiff X ι p 0 = 0 := by
  funext T
  simp [cechDiff]

/-- The glueing differential is the Čech differential of the family of localizations. -/
theorem glueingDifferential_eq_cechDiff {R : Type*} [CommRing R] (f : Fin r → R)
    (M : Type*) [AddCommGroup M] [Module R M] (p : ℕ) (x : GlueingTerm f M p) :
    glueingDifferential f M p x =
      cechDiff (cechMod f M) (fun h ↦ (cechι f M h).toAddMonoidHom) p x := by
  funext T
  rw [glueingDifferential_apply_component]
  rfl

/-- Naturality of the Čech differential. -/
theorem cechDiff_natural {Y : Finset (Fin r) → Type v'} [∀ s, AddCommGroup (Y s)]
    (ιY : ∀ {s t : Finset (Fin r)}, s ⊆ t → Y s →+ Y t) (F : ∀ s, X s →+ Y s) {p : ℕ}
    (hp : 0 < p)
    (hF : ∀ (s t : Finset (Fin r)) (h : s ⊆ t), s.Nonempty → ∀ x, F t (ι h x) = ιY h (F s x))
    (x : FamTerm X p) (T : {s : Finset (Fin r) // s.card = p + 1}) :
    F T.1 (cechDiff X ι p x T) = cechDiff Y ιY p (fun s ↦ F s.1 (x s)) T := by
  simp only [cechDiff, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hF _ _ _ (Finset.card_pos.mp (by rw [(eraseIndex p T k).2]; exact hp))]

/-- Equal indices `s = t` give equal images `ι (x s) = ι (x t)` in a common superset `U`. -/
theorem component_congr {p : ℕ} (x : FamTerm X p) {s t : {s : Finset (Fin r) // s.card = p}}
    (hst : s = t) {U : Finset (Fin r)} (hs : s.1 ⊆ U) (ht : t.1 ⊆ U) :
    ι hs (x s) = ι ht (x t) := by
  subst hst
  rfl

/-- The Čech sign only depends on the set of elements of `s` below `k`. -/
private theorem cechSign_eq_of_filter_eq {s t : Finset (Fin r)} {k : Fin r}
    (h : s.filter (· < k) = t) : cechSign s k = (-1) ^ t.card := by
  simp [cechSign, h]

/-- The Čech differential in degree one, on a pair `{i, j}` with `i < j`. -/
theorem cechDiff_one_apply (x : FamTerm X 1) (T : {s : Finset (Fin r) // s.card = 2})
    {i j : Fin r} (hij : i < j) (hT : T.1 = {i, j})
    (u v : {s : Finset (Fin r) // s.card = 1}) (hu : u.1 = {i}) (hv : v.1 = {j})
    (hsu : u.1 ⊆ T.1) (hsv : v.1 ⊆ T.1) :
    cechDiff X ι 1 x T = ι hsv (x v) - ι hsu (x u) := by
  obtain ⟨T, hT2⟩ := T
  simp only at hT
  subst hT
  let a : ({i, j} : Finset (Fin r)) := ⟨i, by simp⟩
  let b : ({i, j} : Finset (Fin r)) := ⟨j, by simp⟩
  have hab : a ≠ b := fun h ↦ (ne_of_lt hij) (congrArg Subtype.val h)
  have hTa : ({i, j} : Finset (Fin r)).attach = {a, b} := by
    ext k
    simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases k with ⟨k, hk⟩
    rcases (show k = i ∨ k = j by simpa using hk) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hsi : cechSign ({i, j} : Finset (Fin r)) i = 1 :=
    (cechSign_eq_of_filter_eq (t := ∅) (by ext k; simp; omega)).trans (by simp)
  have hsj : cechSign ({i, j} : Finset (Fin r)) j = -1 :=
    (cechSign_eq_of_filter_eq (t := {i}) (by ext k; simp; omega)).trans (by simp)
  rw [cechDiff_apply, hTa, Finset.sum_pair hab]
  have ea : (eraseIndex 1 ⟨{i, j}, hT2⟩ a).1 = v.1 := by
    rw [hv]; ext k; simp [eraseIndex, a]; omega
  have eb : (eraseIndex 1 ⟨{i, j}, hT2⟩ b).1 = u.1 := by
    rw [hu]; ext k; simp [eraseIndex, b]; omega
  rw [component_congr X ι x (Subtype.ext ea) _ hsv, component_congr X ι x (Subtype.ext eb) _ hsu]
  simp only [a, b, hsi, hsj, one_smul, neg_smul]
  abel

/-- The Čech differential in degree two, on a triple `{i, j, l}` with `i < j < l`. -/
theorem cechDiff_two_apply (x : FamTerm X 2)
    (T : {s : Finset (Fin r) // s.card = 3}) {i j l : Fin r} (hij : i < j) (hjl : j < l)
    (hT : T.1 = {i, j, l}) (u₁ u₂ u₃ : {s : Finset (Fin r) // s.card = 2})
    (h₁ : u₁.1 = {j, l}) (h₂ : u₂.1 = {i, l}) (h₃ : u₃.1 = {i, j})
    (hs₁ : u₁.1 ⊆ T.1) (hs₂ : u₂.1 ⊆ T.1) (hs₃ : u₃.1 ⊆ T.1) :
    cechDiff X ι 2 x T = ι hs₁ (x u₁) - ι hs₂ (x u₂) + ι hs₃ (x u₃) := by
  obtain ⟨T, hT3⟩ := T
  simp only at hT
  subst hT
  have hil : i < l := hij.trans hjl
  let a : ({i, j, l} : Finset (Fin r)) := ⟨i, by simp⟩
  let b : ({i, j, l} : Finset (Fin r)) := ⟨j, by simp⟩
  let c : ({i, j, l} : Finset (Fin r)) := ⟨l, by simp⟩
  have hab : a ≠ b := fun h ↦ (ne_of_lt hij) (congrArg Subtype.val h)
  have hac : a ≠ c := fun h ↦ (ne_of_lt hil) (congrArg Subtype.val h)
  have hbc : b ≠ c := fun h ↦ (ne_of_lt hjl) (congrArg Subtype.val h)
  have hTa : ({i, j, l} : Finset (Fin r)).attach = {a, b, c} := by
    ext k
    simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases k with ⟨k, hk⟩
    rcases (show k = i ∨ k = j ∨ k = l by simpa using hk) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have hsi : cechSign ({i, j, l} : Finset (Fin r)) i = 1 :=
    (cechSign_eq_of_filter_eq (t := ∅) (by ext k; simp; omega)).trans (by simp)
  have hsj : cechSign ({i, j, l} : Finset (Fin r)) j = -1 :=
    (cechSign_eq_of_filter_eq (t := {i}) (by ext k; simp; omega)).trans (by simp)
  have hsl : cechSign ({i, j, l} : Finset (Fin r)) l = 1 :=
    (cechSign_eq_of_filter_eq (t := {i, j}) (by ext k; simp; omega)).trans
      (by simp [Finset.card_pair (ne_of_lt hij)])
  rw [cechDiff_apply, hTa, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
  have ea : (eraseIndex 2 ⟨{i, j, l}, hT3⟩ a).1 = u₁.1 := by
    rw [h₁]; ext k; simp [eraseIndex, a]; omega
  have eb : (eraseIndex 2 ⟨{i, j, l}, hT3⟩ b).1 = u₂.1 := by
    rw [h₂]; ext k; simp [eraseIndex, b]; omega
  have ec : (eraseIndex 2 ⟨{i, j, l}, hT3⟩ c).1 = u₃.1 := by
    rw [h₃]; ext k; simp [eraseIndex, c]; omega
  rw [component_congr X ι x (Subtype.ext ea) _ hs₁, component_congr X ι x (Subtype.ext eb) _ hs₂,
    component_congr X ι x (Subtype.ext ec) _ hs₃]
  simp only [a, b, c, hsi, hsj, hsl, one_smul, neg_smul]
  abel

/-- Every three-element subset of `Fin r` is `{i, j, l}` for some `i < j < l`. -/
theorem exists_sorted_triple (T : {s : Finset (Fin r) // s.card = 3}) :
    ∃ i j l : Fin r, i < j ∧ j < l ∧ T.1 = {i, j, l} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ := Finset.card_eq_three.mp T.2
  rw [hT]
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨x, y, z, h1, h3, rfl⟩
  · exact ⟨x, z, y, h2, h3, by ext; simp; tauto⟩
  · exact absurd (h1.trans h3) (lt_asymm h2)
  · exact ⟨z, x, y, h2, h1, by ext; simp; tauto⟩
  · exact ⟨y, x, z, h1, h2, by ext; simp; tauto⟩
  · exact absurd (h1.trans h2) (lt_asymm h3)
  · exact ⟨y, z, x, h3, h2, by ext; simp; tauto⟩
  · exact ⟨z, y, x, h3, h1, by ext; simp; tauto⟩

/-- `δ ∘ δ = 0` in degree one, for a functorial family. -/
theorem cechDiff_cechDiff
    (hfun : ∀ (s t w : Finset (Fin r)) (h : s ⊆ t) (h' : t ⊆ w), s.Nonempty →
      ∀ x, ι h' (ι h x) = ι (h.trans h') x)
    (x : FamTerm X 1) : cechDiff X ι 2 (cechDiff X ι 1 x) = 0 := by
  funext T
  obtain ⟨i, j, l, hij, hjl, hT⟩ := exists_sorted_triple T
  have hil := hij.trans hjl
  have s1 : ({j, l} : Finset (Fin r)) ⊆ T.1 := by rw [hT]; intro x; simp; tauto
  have s2 : ({i, l} : Finset (Fin r)) ⊆ T.1 := by rw [hT]; intro x; simp; tauto
  have s3 : ({i, j} : Finset (Fin r)) ⊆ T.1 := by rw [hT]; intro x; simp; tauto
  rw [cechDiff_two_apply X ι _ T hij hjl hT ⟨{j, l}, Finset.card_pair (ne_of_lt hjl)⟩
    ⟨{i, l}, Finset.card_pair (ne_of_lt hil)⟩ ⟨{i, j}, Finset.card_pair (ne_of_lt hij)⟩
    rfl rfl rfl s1 s2 s3]
  rw [cechDiff_one_apply X ι x _ hjl rfl (singletonIndex j) (singletonIndex l) rfl rfl
      (by simp) (by simp),
    cechDiff_one_apply X ι x _ hil rfl (singletonIndex i) (singletonIndex l) rfl rfl
      (by simp) (by simp),
    cechDiff_one_apply X ι x _ hij rfl (singletonIndex i) (singletonIndex j) rfl rfl
      (by simp) (by simp)]
  simp only [map_sub, hfun _ _ _ _ _ (Finset.singleton_nonempty _), Pi.zero_apply]
  abel

/-- The components of a degree-one cocycle agree on the overlap `{i, j}` with `i < j`. -/
theorem component_eq_of_cechDiff_one_eq_zero {x : FamTerm X 1} (h : cechDiff X ι 1 x = 0)
    (T : {s : Finset (Fin r) // s.card = 2}) {i j : Fin r} (hij : i < j) (hT : T.1 = {i, j})
    (u v : {s : Finset (Fin r) // s.card = 1}) (hu : u.1 ⊆ T.1) (hv : v.1 ⊆ T.1)
    (hu' : u.1 = {i}) (hv' : v.1 = {j}) : ι hu (x u) = ι hv (x v) := by
  have := congrFun h T
  rw [cechDiff_one_apply X ι x T hij hT u v hu' hv' hu hv] at this
  exact (sub_eq_zero.mp this).symm

/-- A degree-one term is a cocycle exactly when its components agree on all overlaps. -/
theorem cechDiff_one_eq_zero_iff (x : FamTerm X 1) :
    cechDiff X ι 1 x = 0 ↔ ∀ (T : {s : Finset (Fin r) // s.card = 2})
      (u v : {s : Finset (Fin r) // s.card = 1}) (hu : u.1 ⊆ T.1) (hv : v.1 ⊆ T.1),
      ι hu (x u) = ι hv (x v) := by
  refine ⟨fun h T u v hu hv ↦ ?_, fun h ↦ funext fun T ↦ ?_⟩
  · obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp T.2
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp u.2
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp v.2
    have hai : a = i ∨ a = j := by simpa [hT] using hu (by simp [ha] : a ∈ u.1)
    have hbi : b = i ∨ b = j := by simpa [hT] using hv (by simp [hb] : b ∈ v.1)
    by_cases hab : a = b
    · subst hab
      exact component_congr X ι x (Subtype.ext (ha.trans hb.symm)) hu hv
    rcases hai with rfl | rfl <;> rcases hbi with rfl | rfl
    · exact absurd rfl hab
    · rcases lt_or_gt_of_ne hij with h1 | h1
      · exact component_eq_of_cechDiff_one_eq_zero X ι h T h1 hT u v hu hv ha hb
      · exact (component_eq_of_cechDiff_one_eq_zero X ι h T h1
          (hT.trans (Finset.pair_comm _ _)) v u hv hu hb ha).symm
    · rcases lt_or_gt_of_ne hij with h1 | h1
      · exact (component_eq_of_cechDiff_one_eq_zero X ι h T h1 hT v u hv hu hb ha).symm
      · exact component_eq_of_cechDiff_one_eq_zero X ι h T h1
          (hT.trans (Finset.pair_comm _ _)) u v hu hv ha hb
    · exact absurd rfl hab
  · obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp T.2
    rcases lt_or_gt_of_ne hij with h1 | h1
    · rw [cechDiff_one_apply X ι x T h1 hT (singletonIndex i) (singletonIndex j) rfl rfl
        (by rw [hT]; simp) (by rw [hT]; simp), h _ (singletonIndex j) (singletonIndex i)
        (by rw [hT]; simp) (by rw [hT]; simp)]
      simp
    · rw [cechDiff_one_apply X ι x T h1 (hT.trans (Finset.pair_comm _ _)) (singletonIndex j)
        (singletonIndex i) rfl rfl (by rw [hT]; simp) (by rw [hT]; simp),
        h _ (singletonIndex i) (singletonIndex j) (by rw [hT]; simp) (by rw [hT]; simp)]
      simp

end Rig.SquareZeroLift

end

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Where the Gysin map of an `Ext` class is bijective

Let `P : C ⥤ D` be an exact functor of abelian categories, `M : C`, `A : D` and
`γ ∈ Ext^c(P M, A)`. For `X : C` the **Gysin map** of `γ` at `X` is
`Ext^q(X, M) → Ext^{q+c}(P X, A)`, `w ↦ P(w) ∘ γ` (`Stacks.EtaleCohomology.Purity.Gysin.gysin`).
We say `γ` is **good at `X`** (`Stacks.EtaleCohomology.Purity.Gysin.IsGoodAt`) if its Gysin maps
at `X` are bijective in every degree and `Ext^q(P X, A) = 0` for `q < c`. For `P = i_*` along a
closed immersion, `M = Λ` and `A = Λ`, `γ` is a purity class exactly when it is good everywhere.

This file proves the formal properties of goodness that make purity classes glue.

* Goodness is invariant under isomorphism of `X` (`IsGoodAt.of_iso`).
* **Two out of three**: in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, goodness at `X₁`
  and `X₂` gives goodness at `X₃` (`IsGoodAt.of_shortExact`); this is the five lemma on the two
  long exact sequences of `Ext`, which the Gysin maps intertwine.
* Goodness at `X` and `X'` gives goodness at `X ⊞ X'` (`IsGoodAt.biprod`).
* **Transfer**: if `a = P(φ) ∘ γ` for `φ : M' ⟶ M`, and composition with `φ` is bijective on
  `Ext(X, -)`, then `a` is good at `X` exactly when `γ` is (`isGoodAt_comp_mk₀_iff`).
* Composition with a unit scalar is bijective on `Ext` (`bijective_comp_mk₀_smul_id`), so the
  transfer applies to it.
* **Gluing**: in a short exact sequence `0 → X₁ → X ⊞ X' → X₃ → 0` with maps `(κ, -κ')` and
  `(ε, ε')`, classes `a`, `a'` on `X` and `X'` that agree on `X₁` come from a class on `X₃`
  (`exists_comp_eq_of_shortExact`).
* **Rigidity**: two classes good at `X` itself, when `X` has only scalar endomorphisms, differ
  by a unit scalar (`exists_isUnit_eq_mk₀_smul_comp`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' w'' v₁ v₂ u₁ u₂

namespace Stacks.EtaleCohomology.Purity.Gysin

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w'} D]
  (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

section Gysin

variable {M : C} {A : D} {c : ℕ} (γ : Ext (P.obj M) A c)

/-- **The Gysin map** `Ext^q(X, M) → Ext^{q'}(P X, A)`, `w ↦ P(w) ∘ γ`, for `q + c = q'`. -/
def gysin (X : C) (q q' : ℕ) (h : q + c = q') : Ext X M q →+ Ext (P.obj X) A q' where
  toFun w := (w.mapExactFunctor P).comp γ h
  map_zero' := by simp [Ext.zero_comp]
  map_add' w w' := by simp [Ext.add_comp]

/-- The Gysin map sends `w` to `P(w) ∘ γ`. -/
theorem gysin_apply (X : C) (q q' : ℕ) (h : q + c = q') (w : Ext X M q) :
    gysin P γ X q q' h w = (w.mapExactFunctor P).comp γ h := rfl

/-- **`γ` is good at `X`**: its Gysin maps at `X` are bijective in every degree and
`Ext^q(P X, A) = 0` for `q < c`. -/
def IsGoodAt (X : C) : Prop :=
  (∀ (q q' : ℕ) (h : q + c = q'), Function.Bijective (gysin P γ X q q' h)) ∧
    ∀ q, q < c → Subsingleton (Ext (P.obj X) A q)

/-- The Gysin map is natural for precomposition with a morphism in degree zero. -/
theorem gysin_mk₀_comp {X Y : C} (f : X ⟶ Y) (q q' : ℕ) (h : q + c = q') (w : Ext Y M q) :
    gysin P γ X q q' h ((Ext.mk₀ f).comp w (zero_add q)) =
      (Ext.mk₀ (P.map f)).comp (gysin P γ Y q q' h w) (zero_add q') := by
  simp only [gysin_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.comp_assoc _ _ _ _ _ (by omega)

/-- The Gysin map is natural for precomposition with an extension class. -/
theorem gysin_extClass_comp {S : ShortComplex C} (hS : S.ShortExact) {q q' q₁ q₁' : ℕ}
    (h : q + c = q') (h₁ : 1 + q = q₁) (h₁' : 1 + q' = q₁') (w : Ext S.X₁ M q) :
    gysin P γ S.X₃ q₁ q₁' (by omega) (hS.extClass.comp w h₁) =
      (hS.map_of_exact P).extClass.comp (gysin P γ S.X₁ q q' h w) h₁' := by
  simp only [gysin_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact Ext.comp_assoc _ _ _ _ _ (by omega)

/-- Composition with an isomorphism in degree zero, on the left, is bijective. -/
theorem bijective_mk₀_comp_of_iso {E : Type*} [Category E] [Abelian E] [HasExt.{w''} E]
    {X X' Y : E} (e : X ≅ X') (n : ℕ) :
    Function.Bijective (fun z : Ext X' Y n => (Ext.mk₀ e.hom).comp z (zero_add n)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun z => (Ext.mk₀ e.inv).comp z (zero_add n),
    fun z => ?_, fun z => ?_⟩
  · change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp z (zero_add n)) (zero_add n) = z
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  · change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp z (zero_add n)) (zero_add n) = z
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]

/-- A degree zero class killed by composition with an epimorphism is zero. -/
private theorem eq_zero_of_mk₀_comp_eq_zero_of_epi {E : Type*} [Category E] [Abelian E]
    [HasExt.{w''} E] {M N : E} (L : E) (g : M ⟶ N) [Epi g] {z : Ext N L 0}
    (hz : (Ext.mk₀ g).comp z (zero_add 0) = 0) : z = 0 :=
  Ext.precomp_mk₀_injective_of_epi L g (by rw [map_zero]; exact hz)

/-- **Goodness is invariant under isomorphism.** -/
theorem IsGoodAt.of_iso {X X' : C} (e : X ≅ X') (hX : IsGoodAt P γ X) : IsGoodAt P γ X' := by
  refine ⟨fun q q' h => ?_, fun q hq => ?_⟩
  · have hc : (fun z => (Ext.mk₀ (P.map e.hom)).comp z (zero_add q')) ∘ gysin P γ X' q q' h =
        gysin P γ X q q' h ∘ (fun w => (Ext.mk₀ e.hom).comp w (zero_add q)) :=
      funext fun w => (gysin_mk₀_comp P γ e.hom q q' h w).symm
    have h2 := (hX.1 q q' h).comp (bijective_mk₀_comp_of_iso e q)
    rw [← hc] at h2
    exact (Function.Bijective.of_comp_iff' (bijective_mk₀_comp_of_iso (P.mapIso e) q') _).1 h2
  · have := hX.2 q hq
    exact (bijective_mk₀_comp_of_iso (P.mapIso e) q).1.subsingleton

/-- **Two out of three**: goodness at `X₁` and `X₂` of a short exact sequence gives goodness at
`X₃`, by the five lemma on the long exact sequences of `Ext(-, M)` and `Ext(P(-), A)`. -/
theorem IsGoodAt.of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : IsGoodAt P γ S.X₁) (h₂ : IsGoodAt P γ S.X₂) : IsGoodAt P γ S.X₃ := by
  have hS' : (S.map P).ShortExact := hS.map_of_exact P
  have : Epi S.g := hS.epi_g
  have : Epi (P.map S.g) := hS'.epi_g
  have hfg : ∀ (n : ℕ) (t : Ext (P.obj S.X₃) A n),
      (Ext.mk₀ (P.map S.f)).comp ((Ext.mk₀ (P.map S.g)).comp t (zero_add n)) (zero_add n) = 0 := by
    intro n t
    rw [Ext.mk₀_comp_mk₀_assoc, ← P.map_comp, S.zero, P.map_zero, Ext.mk₀_zero, Ext.zero_comp]
  refine ⟨fun q q' h => ⟨fun y y' hyy => ?_, fun t => ?_⟩, fun n hn => ?_⟩
  · rw [← sub_eq_zero] at hyy ⊢
    rw [← map_sub] at hyy
    generalize y - y' = y₀ at hyy ⊢
    have hg : (Ext.mk₀ S.g).comp y₀ (zero_add q) = 0 := by
      apply (h₂.1 q q' h).1
      rw [gysin_mk₀_comp, hyy, Ext.comp_zero, map_zero]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      exact eq_zero_of_mk₀_comp_eq_zero_of_epi M S.g hg
    · obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS M y₀ hg (n₀ := q - 1) (by omega)
      subst hx
      rw [gysin_extClass_comp P γ hS (show q - 1 + c = q' - 1 by omega) _ (by omega)] at hyy
      obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ hS' A
        (gysin P γ S.X₁ (q - 1) (q' - 1) (by omega) x) (by omega) hyy
      obtain ⟨z', rfl⟩ := (h₂.1 (q - 1) (q' - 1) (by omega)).2 z
      have hx : x = (Ext.mk₀ S.f).comp z' (zero_add (q - 1)) := by
        apply (h₁.1 (q - 1) (q' - 1) (by omega)).1
        rw [gysin_mk₀_comp]
        exact hz.symm
      rw [hx, ← Ext.comp_assoc_of_second_deg_zero, hS.extClass_comp, Ext.zero_comp]
  · obtain ⟨y₂, hy₂⟩ := (h₂.1 q q' h).2 ((Ext.mk₀ (P.map S.g)).comp t (zero_add q'))
    have hf : (Ext.mk₀ S.f).comp y₂ (zero_add q) = 0 := by
      apply (h₁.1 q q' h).1
      rw [gysin_mk₀_comp, hy₂, map_zero]
      exact hfg q' t
    obtain ⟨y₃, hy₃⟩ := Ext.contravariant_sequence_exact₂ hS M y₂ hf
    have hd : (Ext.mk₀ (P.map S.g)).comp (t - gysin P γ S.X₃ q q' h y₃) (zero_add q') = 0 := by
      rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, ← sub_eq_add_neg, ← gysin_mk₀_comp, hy₃,
        hy₂, sub_self]
    rcases Nat.eq_zero_or_pos q' with hq' | hq'
    · subst hq'
      refine ⟨y₃, ?_⟩
      exact (sub_eq_zero.1 (eq_zero_of_mk₀_comp_eq_zero_of_epi A (P.map S.g) hd)).symm
    · obtain ⟨s, hs⟩ := Ext.contravariant_sequence_exact₃ hS' A _ hd (n₀ := q' - 1) (by omega)
      rcases Nat.eq_zero_or_pos q with hq | hq
      · subst hq
        have hsub := h₁.2 (q' - 1) (by omega)
        refine ⟨y₃, ?_⟩
        rw [@Subsingleton.elim _ hsub s 0, Ext.comp_zero] at hs
        exact (sub_eq_zero.1 hs.symm).symm
      · obtain ⟨x, hx⟩ := (h₁.1 (q - 1) (q' - 1) (by omega)).2 s
        refine ⟨y₃ + hS.extClass.comp x (show 1 + (q - 1) = q by omega), ?_⟩
        rw [map_add, gysin_extClass_comp P γ hS (show q - 1 + c = q' - 1 by omega) _
          (show 1 + (q' - 1) = q' by omega), hx, hs, add_sub_cancel]
  · refine ⟨fun t t' => ?_⟩
    suffices hz : ∀ t : Ext (P.obj S.X₃) A n, t = 0 by rw [hz t, hz t']
    intro t
    have hsub₂ := h₂.2 n hn
    have hg : (Ext.mk₀ (P.map S.g)).comp t (zero_add n) = 0 := @Subsingleton.elim _ hsub₂ _ _
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact eq_zero_of_mk₀_comp_eq_zero_of_epi A (P.map S.g) hg
    · obtain ⟨s, rfl⟩ := Ext.contravariant_sequence_exact₃ hS' A t hg (n₀ := n - 1) (by omega)
      have hsub₁ := h₁.2 (n - 1) (by omega)
      rw [@Subsingleton.elim _ hsub₁ s 0, Ext.comp_zero]

/-- A class decomposes along a splitting `f₁ ≫ g₁ + f₂ ≫ g₂ = 𝟙` of its source. -/
theorem ext_eq_add_of_splitting {E : Type*} [Category E] [Abelian E] [HasExt.{w''} E]
    {Z Z₁ Z₂ Y : E} (f₁ : Z ⟶ Z₁) (g₁ : Z₁ ⟶ Z) (f₂ : Z ⟶ Z₂) (g₂ : Z₂ ⟶ Z)
    (hfg : f₁ ≫ g₁ + f₂ ≫ g₂ = 𝟙 Z) {n : ℕ} (t : Ext Z Y n) :
    t = (Ext.mk₀ f₁).comp ((Ext.mk₀ g₁).comp t (zero_add n)) (zero_add n) +
      (Ext.mk₀ f₂).comp ((Ext.mk₀ g₂).comp t (zero_add n)) (zero_add n) := by
  rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, ← Ext.add_comp, ← Ext.mk₀_add, hfg,
    Ext.mk₀_id_comp]

/-- **Goodness at a biproduct** follows from goodness at the two summands. -/
theorem IsGoodAt.biprod {X X' : C} (h : IsGoodAt P γ X) (h' : IsGoodAt P γ X') :
    IsGoodAt P γ (X ⊞ X') := by
  have hP : P.map biprod.fst ≫ P.map biprod.inl + P.map biprod.snd ≫ P.map biprod.inr =
      𝟙 (P.obj (X ⊞ X')) := by
    rw [← P.map_comp, ← P.map_comp, ← P.map_add, biprod.total, P.map_id]
  refine ⟨fun q q' hq => ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, fun t => ?_⟩,
    fun n hn => ⟨fun t t' => ?_⟩⟩
  · have key : ∀ {Y : C}, IsGoodAt P γ Y → ∀ j : Y ⟶ X ⊞ X',
        (Ext.mk₀ j).comp w (zero_add q) = 0 := fun hY j =>
      (injective_iff_map_eq_zero _).1 (hY.1 q q' hq).1 _ (by rw [gysin_mk₀_comp, hw, Ext.comp_zero])
    rw [ext_eq_add_of_splitting biprod.fst biprod.inl biprod.snd biprod.inr biprod.total w,
      key h, key h', Ext.comp_zero, Ext.comp_zero, add_zero]
  · obtain ⟨y₁, hy₁⟩ := (h.1 q q' hq).2 ((Ext.mk₀ (P.map biprod.inl)).comp t (zero_add q'))
    obtain ⟨y₂, hy₂⟩ := (h'.1 q q' hq).2 ((Ext.mk₀ (P.map biprod.inr)).comp t (zero_add q'))
    refine ⟨(Ext.mk₀ biprod.fst).comp y₁ (zero_add q) + (Ext.mk₀ biprod.snd).comp y₂ (zero_add q),
      ?_⟩
    rw [map_add, gysin_mk₀_comp, gysin_mk₀_comp, hy₁, hy₂]
    exact (ext_eq_add_of_splitting _ _ _ _ hP t).symm
  · have := h.2 n hn
    have := h'.2 n hn
    rw [ext_eq_add_of_splitting _ _ _ _ hP t, ext_eq_add_of_splitting _ _ _ _ hP t',
      Subsingleton.elim ((Ext.mk₀ (P.map biprod.inl)).comp t (zero_add n))
        ((Ext.mk₀ (P.map biprod.inl)).comp t' (zero_add n)),
      Subsingleton.elim ((Ext.mk₀ (P.map biprod.inr)).comp t (zero_add n))
        ((Ext.mk₀ (P.map biprod.inr)).comp t' (zero_add n))]

/-- The Gysin map of `P(φ) ∘ γ` is that of `γ` after composition with `φ`. -/
theorem gysin_mk₀_map_comp {M' : C} (φ : M' ⟶ M) (X : C) (q q' : ℕ) (h : q + c = q')
    (w : Ext X M' q) :
    gysin P ((Ext.mk₀ (P.map φ)).comp γ (zero_add c)) X q q' h w =
      gysin P γ X q q' h (w.comp (Ext.mk₀ φ) (add_zero q)) := by
  simp only [gysin_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm

/-- **Transfer**: if composition with `φ : M' ⟶ M` is bijective on `Ext(X, -)`, then
`P(φ) ∘ γ` is good at `X` exactly when `γ` is. -/
theorem isGoodAt_comp_mk₀_iff {M' : C} (φ : M' ⟶ M) (X : C)
    (hφ : ∀ q, Function.Bijective (fun w : Ext X M' q => w.comp (Ext.mk₀ φ) (add_zero q))) :
    IsGoodAt P ((Ext.mk₀ (P.map φ)).comp γ (zero_add c)) X ↔ IsGoodAt P γ X := by
  have e : ∀ q q' (h : q + c = q'),
      ⇑(gysin P ((Ext.mk₀ (P.map φ)).comp γ (zero_add c)) X q q' h) =
        gysin P γ X q q' h ∘ (fun w : Ext X M' q => w.comp (Ext.mk₀ φ) (add_zero q)) :=
    fun q q' h => funext (gysin_mk₀_map_comp P γ φ X q q' h)
  refine ⟨fun H => ⟨fun q q' h => ?_, H.2⟩, fun H => ⟨fun q q' h => ?_, H.2⟩⟩
  · have := H.1 q q' h
    rw [e] at this
    exact (Function.Bijective.of_comp_iff _ (hφ q)).1 this
  · rw [e]
    exact (H.1 q q' h).comp (hφ q)

omit [HasExt C] in
/-- **Gluing**: in a short exact sequence `0 → X₁ → X ⊞ X' → X₃ → 0` with maps `(κ, -κ')` and
`(ε, ε')`, classes on `P X` and `P X'` that agree on `P X₁` come from a class on `P X₃`. -/
theorem exists_comp_eq_of_shortExact {X₁ X X' X₃ : C} (κ : X₁ ⟶ X) (κ' : X₁ ⟶ X')
    (ε : X ⟶ X₃) (ε' : X' ⟶ X₃) (w : biprod.lift κ (-κ') ≫ biprod.desc ε ε' = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) {A : D} {c : ℕ} (a : Ext (P.obj X) A c)
    (a' : Ext (P.obj X') A c)
    (h : (Ext.mk₀ (P.map κ)).comp a (zero_add c) = (Ext.mk₀ (P.map κ')).comp a' (zero_add c)) :
    ∃ γ : Ext (P.obj X₃) A c, (Ext.mk₀ (P.map ε)).comp γ (zero_add c) = a ∧
      (Ext.mk₀ (P.map ε')).comp γ (zero_add c) = a' := by
  let x : Ext (P.obj (X ⊞ X')) A c :=
    (Ext.mk₀ (P.map biprod.fst)).comp a (zero_add c) +
      (Ext.mk₀ (P.map biprod.snd)).comp a' (zero_add c)
  have hx : (Ext.mk₀ (P.map (biprod.lift κ (-κ')))).comp x (zero_add c) = 0 := by
    simp only [x, Ext.comp_add, Ext.mk₀_comp_mk₀_assoc, ← P.map_comp, biprod.lift_fst,
      biprod.lift_snd, P.map_neg, Ext.mk₀_neg, Ext.neg_comp, h, add_neg_cancel]
  obtain ⟨γ, hγ'⟩ := Ext.contravariant_sequence_exact₂ (hS.map_of_exact P) A x hx
  have hγ : (Ext.mk₀ (P.map (biprod.desc ε ε'))).comp γ (zero_add c) = x := hγ'
  have key : ∀ {Y : C} (j : Y ⟶ X ⊞ X') (e : Y ⟶ X₃) (b : Ext (P.obj Y) A c),
      j ≫ biprod.desc ε ε' = e → (Ext.mk₀ (P.map j)).comp x (zero_add c) = b →
      (Ext.mk₀ (P.map e)).comp γ (zero_add c) = b := by
    intro Y j e b he hb
    rw [← he, P.map_comp, ← Ext.mk₀_comp_mk₀_assoc]
    rw [hγ, hb]
  exact ⟨γ, key biprod.inl ε a (by simp) (by
    simp only [x, Ext.comp_add, Ext.mk₀_comp_mk₀_assoc, ← P.map_comp, biprod.inl_fst,
      biprod.inl_snd, P.map_id, P.map_zero, Ext.mk₀_id_comp, Ext.mk₀_zero, Ext.zero_comp,
      add_zero]), key biprod.inr ε' a' (by simp) (by
    simp only [x, Ext.comp_add, Ext.mk₀_comp_mk₀_assoc, ← P.map_comp, biprod.inr_fst,
      biprod.inr_snd, P.map_id, P.map_zero, Ext.mk₀_id_comp, Ext.mk₀_zero, Ext.zero_comp,
      zero_add])⟩

/-- **Rigidity**: two classes on `P X` that are good at `X` differ by a unit scalar, when the
endomorphisms of `X` are the scalars of a commutative ring acting faithfully. -/
theorem exists_isUnit_eq_mk₀_smul_comp {R : Type*} [CommRing R] [Linear R C] {X : C}
    {A : D} {c : ℕ} {b b' : Ext (P.obj X) A c} (hb : IsGoodAt P b X) (hb' : IsGoodAt P b' X)
    (hend : ∀ v : X ⟶ X, ∃ r : R, v = r • 𝟙 X) (hfaith : ∀ r : R, r • 𝟙 X = 0 → r = 0) :
    ∃ r : R, IsUnit r ∧ b = (Ext.mk₀ (P.map (r • 𝟙 X))).comp b' (zero_add c) := by
  have key : ∀ {b₁ b₂ : Ext (P.obj X) A c}, IsGoodAt P b₂ X →
      ∃ r : R, b₁ = (Ext.mk₀ (P.map (r • 𝟙 X))).comp b₂ (zero_add c) := by
    intro b₁ b₂ h₂
    obtain ⟨u, hu⟩ := (h₂.1 0 c (zero_add c)).2 b₁
    obtain ⟨v, rfl⟩ := (Ext.mk₀_bijective X X).2 u
    obtain ⟨r, rfl⟩ := hend v
    refine ⟨r, ?_⟩
    rw [← hu, gysin_apply, Ext.mapExactFunctor_mk₀]
  obtain ⟨r, hr⟩ := key hb'
  obtain ⟨r', hr'⟩ := key (b₁ := b') hb
  refine ⟨r, ?_, hr⟩
  have hcomp : b = (Ext.mk₀ (P.map ((r' * r) • 𝟙 X))).comp b (zero_add c) := by
    conv_lhs => rw [hr, hr']
    rw [Ext.mk₀_comp_mk₀_assoc, ← P.map_comp, Linear.smul_comp, Category.id_comp, smul_smul,
      mul_comm]
  have hinj := (hb.1 0 c (zero_add c)).1
  have h1 : gysin P b X 0 c (zero_add c) (Ext.mk₀ ((r' * r) • 𝟙 X)) =
      gysin P b X 0 c (zero_add c) (Ext.mk₀ (𝟙 X)) := by
    rw [gysin_apply, gysin_apply, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, ← hcomp,
      P.map_id, Ext.mk₀_id_comp]
  have h2 := (Ext.mk₀_bijective X X).1 (hinj h1)
  have h3 : (r' * r - 1) • 𝟙 X = 0 := by rw [sub_smul, h2, one_smul, sub_self]
  exact IsUnit.of_mul_eq_one_right r' (sub_eq_zero.1 (hfaith _ h3))

/-- Composition with a unit scalar is bijective on `Ext`. -/
theorem bijective_comp_mk₀_smul_id {E : Type*} [Category E] [Abelian E] [HasExt.{w''} E]
    {R : Type*} [Ring R] [Linear R E] {X Y : E} (r : R) (hr : IsUnit r) (n : ℕ) :
    Function.Bijective (fun z : Ext X Y n => z.comp (Ext.mk₀ (r • 𝟙 Y)) (add_zero n)) := by
  have e : (fun z : Ext X Y n => z.comp (Ext.mk₀ (r • 𝟙 Y)) (add_zero n)) = fun z => r • z :=
    funext fun z => (Ext.smul_eq_comp_mk₀ z r).symm
  rw [e]
  refine Function.bijective_iff_has_inverse.mpr ⟨fun z => (↑hr.unit⁻¹ : R) • z,
    fun z => ?_, fun z => ?_⟩
  · simp only [smul_smul, hr.val_inv_mul, one_smul]
  · simp only [smul_smul, hr.mul_val_inv, one_smul]

end Gysin

end Stacks.EtaleCohomology.Purity.Gysin

end

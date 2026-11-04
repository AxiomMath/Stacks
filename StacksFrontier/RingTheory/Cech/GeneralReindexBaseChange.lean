module

public import StacksFrontier.RingTheory.Cech.GeneralReindex
public import StacksFrontier.RingTheory.Cech.RingBaseChange

/-!
# Changing the ring and the index set at once

For a ring map `φ : A →+* B`, a family `f` in `A`, a family `g` in `B` and an index map
`α : Fin s → Fin r` such that `φ (f (α j))` divides a power of `g j`, the comparison map of
extended alternating Čech complexes along `φ` and `α`, and its functoriality.

## Main definitions

* `Cech.genRingTerm`: the comparison map of degree-`p` terms along a ring map and a reindexing.
* `Cech.cechGenRingMap`: the comparison map of Čech complexes along a ring map and a reindexing.

## Main results

* `Stacks.CechRingBaseChange.termMap_comp_genTerm`: change of rings commutes with the general
  reindexing of the terms of the Čech complex.
* `Cech.genRingTerm_id_ring`: along the identity ring map the comparison is the same-ring one.
* `Cech.genRingTerm_comp`: the comparisons compose.
-/

@[expose] public noncomputable section

open CategoryTheory
open ExtendedAlternatingCech (Idx)

universe u

namespace Stacks.CechRingBaseChange

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] {r s t : ℕ}

/-! ### Change of rings against a general reindexing -/

/-- The divisibility condition of `Cech.cechGenMap`, transported along a ring map. -/
theorem mapFamily_dvd (φ : A →+* B) (f : Fin r → A) (g : Fin s → A) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n) :
    ∀ j : Fin s, ∃ n : ℕ, mapFamily φ f (α j) ∣ mapFamily φ g j ^ n := by
  intro j
  obtain ⟨n, c, hc⟩ := hα j
  exact ⟨n, φ c, by rw [← map_pow, hc, map_mul]⟩

/-- Every element of `Cech.cechSub f U` acts invertibly on the localization of `B` at the image
family of `g` over `V`, as soon as `U ⊆ α(V)`. -/
theorem isUnit_algebraMap_restrictedLoc (φ : A →+* B) (f : Fin r → A) (g : Fin s → A)
    (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n) {U : Finset (Fin r)}
    {V : Finset (Fin s)} (hU : U ⊆ V.image α) (y : Cech.cechSub f U) :
    IsUnit (algebraMap A (Module.End A ↑((ModuleCat.restrictScalars φ).obj
      (ModuleCat.of B (Cech.cechMod (mapFamily φ g) B V)))) (y : A)) := by
  have hB := Cech.isUnit_locTarget_cechSub (mapFamily φ f) (mapFamily φ g) α
    (mapFamily_dvd φ f g α hα) B hU
    (⟨φ (y : A), mem_cechSub_mapFamily φ f y.2⟩ : Cech.cechSub (mapFamily φ f) U)
  rwa [Module.End.isUnit_iff] at hB ⊢

/-- Two linear maps out of a localization of `A` agree if they agree on the image of `A`, provided
every element of `Cech.cechSub f U` acts invertibly on the target. -/
private theorem ext_of_mkLinearMap {M : Type*} [AddCommGroup M] [Module A M] (f : Fin r → A)
    (U : Finset (Fin r)) (hM : ∀ y : Cech.cechSub f U, IsUnit (algebraMap A (Module.End A M) y))
    {F G : Cech.cechMod f A U →ₗ[A] M}
    (h : ∀ a, F (LocalizedModule.mkLinearMap (Cech.cechSub f U) A a) =
      G (LocalizedModule.mkLinearMap (Cech.cechSub f U) A a)) : F = G :=
  IsLocalizedModule.ext (Cech.cechSub f U) (LocalizedModule.mkLinearMap (Cech.cechSub f U) A) hM
    (LinearMap.ext h)

/-- **Change of rings commutes with the general reindexing on one localization**: `Cech.locLift`
of the image families after `modMap φ f U` is `modMap φ g V` after `Cech.locLift`. -/
theorem modMap_locLift (φ : A →+* B) (f : Fin r → A) (g : Fin s → A) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n) {U : Finset (Fin r)} {V : Finset (Fin s)}
    (hU : U ⊆ V.image α) (y : Cech.cechMod f A U) :
    Cech.locLift (mapFamily φ f) (mapFamily φ g) α (mapFamily_dvd φ f g α hα) B U V hU
        (modMap φ f U y) =
      modMap φ g V (Cech.locLift f g α hα A U V hU y) := by
  have key : (restrictHom φ (ModuleCat.ofHom (Cech.locLift (mapFamily φ f) (mapFamily φ g) α
        (mapFamily_dvd φ f g α hα) B U V hU))).comp (modMap φ f U) =
      (modMap φ g V).comp (Cech.locLift f g α hα A U V hU) := by
    refine ext_of_mkLinearMap f U (isUnit_algebraMap_restrictedLoc φ f g α hα hU) fun a => ?_
    show Cech.locLift (mapFamily φ f) (mapFamily φ g) α (mapFamily_dvd φ f g α hα) B U V hU
        (modMap φ f U (LocalizedModule.mkLinearMap (Cech.cechSub f U) A a)) =
      modMap φ g V (Cech.locLift f g α hα A U V hU
        (LocalizedModule.mkLinearMap (Cech.cechSub f U) A a))
    rw [modMap_mkLinearMap, Cech.locLift_mkLinearMap, Cech.locLift_mkLinearMap,
      modMap_mkLinearMap]
  exact LinearMap.congr_fun key y

/-- The components of the change-of-rings map on the terms of the complex. -/
theorem termMap_component (φ : A →+* B) (f : Fin r → A) (p : ℕ) (x : Cech.cechTerm f A p)
    (U : Idx r p) :
    DirectSum.component B (Idx r p) (fun U => Cech.cechMod (mapFamily φ f) B U.1) U
      (termMap φ f p x) = modMap φ f U.1 (x U) := by
  induction x using DirectSum.induction_on with
  | zero =>
      have h0 : termMap φ f p 0 = 0 := map_zero _
      simp only [h0, map_zero, DirectSum.zero_apply]
      exact map_zero _
  | of U' y =>
      have hlof := termMap_lof φ f p U' y
      by_cases h : U' = U
      · subst h
        have h1 : DirectSum.component B (Idx r p)
              (fun t : Idx r p => Cech.cechMod (mapFamily φ f) B t.1) U'
              (DirectSum.lof B (Idx r p)
                (fun t : Idx r p => Cech.cechMod (mapFamily φ f) B t.1) U'
                (modMap φ f U'.1 y)) = modMap φ f U'.1 y :=
          DirectSum.component.lof_self B U' _
        have h2 : (DirectSum.lof A (Idx r p) (fun t : Idx r p => Cech.cechMod f A t.1) U' y) U'
            = y := by
          rw [DirectSum.apply_eq_component (R := A)]
          exact DirectSum.component.lof_self (R := A) (ι := Idx r p)
            (M := fun t : Idx r p => Cech.cechMod f A t.1) U' y
        simp only [← DirectSum.lof_eq_of A, hlof, h1, h2]
        rfl
      · have h1 := DirectSum.component.of (R := B) (ι := Idx r p)
          (M := fun t : Idx r p => Cech.cechMod (mapFamily φ f) B t.1) U U' (modMap φ f U'.1 y)
        have h2 : (DirectSum.lof A (Idx r p) (fun t : Idx r p => Cech.cechMod f A t.1) U' y) U
            = 0 := by
          rw [DirectSum.apply_eq_component (R := A), DirectSum.component.of, dite_eq_right h]
        simp only [← DirectSum.lof_eq_of A, hlof, h1, h2, dite_eq_right h, map_zero]
        rfl
  | add u v hu hv =>
      have hadd : termMap φ f p (u + v) = termMap φ f p u + termMap φ f p v := map_add _ _ _
      have hca : DirectSum.component B (Idx r p)
            (fun U => Cech.cechMod (mapFamily φ f) B U.1) U
            (termMap φ f p u + termMap φ f p v)
          = DirectSum.component B (Idx r p) (fun U => Cech.cechMod (mapFamily φ f) B U.1) U
              (termMap φ f p u)
            + DirectSum.component B (Idx r p) (fun U => Cech.cechMod (mapFamily φ f) B U.1) U
              (termMap φ f p v) := map_add _ _ _
      simp only [hadd, hca, hu, hv, DirectSum.add_apply, map_add]
      rfl

/-- **Change of rings commutes with the general reindexing** of the terms of the Čech complex:
the square formed by the two change-of-rings maps and the two comparison maps commutes. -/
theorem termMap_comp_genTerm (φ : A →+* B) (f : Fin r → A) (g : Fin s → A) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n) (p : ℕ) :
    (restrictHom φ (ModuleCat.ofHom (Cech.genTerm (mapFamily φ f) (mapFamily φ g) α
        (mapFamily_dvd φ f g α hα) B p))).comp (termMap φ f p) =
      (termMap φ g p).comp (Cech.genTerm f g α hα A p) := by
  refine LinearMap.ext fun x => DirectSum.ext_component B fun V => ?_
  have hL : DirectSum.component B (Idx s p) (fun V => Cech.cechMod (mapFamily φ g) B V.1) V
        ((restrictHom φ (ModuleCat.ofHom (Cech.genTerm (mapFamily φ f) (mapFamily φ g) α
          (mapFamily_dvd φ f g α hα) B p))).comp (termMap φ f p) x)
      = if h : (V.1.image α).card = p then
          Cech.invSign α V.1 • Cech.locLift (mapFamily φ f) (mapFamily φ g) α
            (mapFamily_dvd φ f g α hα) B (V.1.image α) V.1 Finset.Subset.rfl
            (DirectSum.component B (Idx r p) (fun U => Cech.cechMod (mapFamily φ f) B U.1)
              ⟨V.1.image α, h⟩ (termMap φ f p x))
        else 0 :=
    Cech.genTerm_apply (mapFamily φ f) (mapFamily φ g) α (mapFamily_dvd φ f g α hα) B p
      (termMap φ f p x) V
  have hR : DirectSum.component B (Idx s p) (fun V => Cech.cechMod (mapFamily φ g) B V.1) V
        ((termMap φ g p).comp (Cech.genTerm f g α hα A p) x)
      = modMap φ g V.1 (Cech.genTerm f g α hα A p x V) :=
    termMap_component φ g p (Cech.genTerm f g α hα A p x) V
  rw [hL, hR, Cech.genTerm_apply]
  by_cases hV : (V.1.image α).card = p
  · have hc := termMap_component φ f p x ⟨V.1.image α, hV⟩
    have hml := modMap_locLift φ f g α hα (U := V.1.image α) (V := V.1) Finset.Subset.rfl
      (x ⟨V.1.image α, hV⟩)
    simp only [dite_eq_left hV, hc, hml, map_zsmul]
    rfl
  · simp only [dite_eq_right hV, map_zero]
    rfl

/-! ### Change of rings along the identity -/

/-- Along the identity ring map the change-of-rings map on one localization is the identity. -/
theorem modMap_id (f : Fin r → A) (U : Finset (Fin r)) :
    modMap (RingHom.id A) f U = LinearMap.id := by
  refine ext_of_mkLinearMap f U (isUnit_algebraMap_restrictedMod (RingHom.id A) f (le_refl U))
    fun a => ?_
  show modMap (RingHom.id A) f U (LocalizedModule.mkLinearMap (Cech.cechSub f U) A a) =
    LocalizedModule.mkLinearMap (Cech.cechSub f U) A a
  rw [modMap_mkLinearMap]
  rfl

/-- **Along the identity ring map the change-of-rings map on the terms is the identity.** -/
theorem termMap_id (f : Fin r → A) (p : ℕ) : termMap (RingHom.id A) f p = LinearMap.id := by
  refine DirectSum.linearMap_ext A fun U => LinearMap.ext fun y => ?_
  show termMap (RingHom.id A) f p
      (DirectSum.lof A (Idx r p) (fun U => Cech.cechMod f A U.1) U y) =
    DirectSum.lof A (Idx r p) (fun U => Cech.cechMod f A U.1) U y
  rw [termMap_lof, modMap_id]
  rfl

end Stacks.CechRingBaseChange

/-! ### The comparison along a ring map together with a reindexing -/

namespace Cech

open Stacks.CechRingBaseChange

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] {r s t : ℕ}

/-- **The comparison map of degree-`p` terms along a ring map together with a reindexing**: for
`φ : A → B`, a family `f` in `A`, a family `g` in `B` and `α : Fin s → Fin r` such that
`φ (f (α j))` divides a power of `g j`, the change of rings followed by the comparison map of the
image family with `g`. -/
def genRingTerm (φ : A →+* B) (f : Fin r → A) (g : Fin s → B) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) (p : ℕ) :
    cechTerm f A p →ₗ[A]
      ↑((ModuleCat.restrictScalars φ).obj (ModuleCat.of B (cechTerm g B p))) :=
  (restrictHom φ (ModuleCat.ofHom (genTerm (mapFamily φ f) g α hα B p))).comp (termMap φ f p)

/-- The comparison map commutes with the Čech differentials. -/
theorem genRingTerm_comp_cechD (φ : A →+* B) (f : Fin r → A) (g : Fin s → B)
    (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) (p : ℕ) :
    (genRingTerm φ f g α hα (p + 1)).comp (cechD f A p) =
      (restrictHom φ (ModuleCat.ofHom (cechD g B p))).comp (genRingTerm φ f g α hα p) := by
  refine LinearMap.ext fun x => ?_
  have h1 := LinearMap.congr_fun (termMap_comp_cechD φ f p) x
  have h2 := genTerm_comm (mapFamily φ f) g α hα B p (termMap φ f p x)
  exact (congrArg (fun z => genTerm (mapFamily φ f) g α hα B (p + 1) z) h1).trans h2

/-- **The comparison map of complexes along a ring map together with a reindexing.** -/
def cechGenRingMap (φ : A →+* B) (f : Fin r → A) (g : Fin s → B) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) :
    cechComplex f A ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (cechComplex g B) where
  f p := ConcreteCategory.ofHom (C := ModuleCat.{u} A) (genRingTerm φ f g α hα p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    rw [cechComplex_d, Functor.mapHomologicalComplex_obj_d, cechComplex_d]
    exact ConcreteCategory.ext (genRingTerm_comp_cechD φ f g α hα p).symm

/-- The degreewise components of the comparison map of complexes. -/
@[simp] theorem cechGenRingMap_f (φ : A →+* B) (f : Fin r → A) (g : Fin s → B)
    (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) (p : ℕ) :
    ((cechGenRingMap φ f g α hα).f p).hom = genRingTerm φ f g α hα p := rfl

/-- Changing the index map changes the comparison map of terms accordingly. -/
theorem genRingTerm_congr (φ : A →+* B) (f : Fin r → A) (g : Fin s → B) {α α' : Fin s → Fin r}
    (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n)
    (hα' : ∀ j : Fin s, ∃ n : ℕ, φ (f (α' j)) ∣ g j ^ n) (hαα : α = α') (p : ℕ) :
    genRingTerm φ f g α hα p = genRingTerm φ f g α' hα' p := by
  subst hαα
  rfl

/-- Changing the index map changes the comparison map of complexes accordingly. -/
theorem cechGenRingMap_congr (φ : A →+* B) (f : Fin r → A) (g : Fin s → B)
    {α α' : Fin s → Fin r} (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n)
    (hα' : ∀ j : Fin s, ∃ n : ℕ, φ (f (α' j)) ∣ g j ^ n) (hαα : α = α') :
    cechGenRingMap φ f g α hα = cechGenRingMap φ f g α' hα' := by
  subst hαα
  rfl

/-- **In degree zero the comparison is `φ` on the ring**: it sends the class of `a` in the
summand indexed by the empty set to the class of `φ a`. -/
theorem genRingTerm_lof_zero (φ : A →+* B) (f : Fin r → A) (g : Fin s → B) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) (a : A) :
    genRingTerm φ f g α hα 0 (DirectSum.lof A (Idx r 0) (fun U => cechMod f A U.1) default
        (LocalizedModule.mkLinearMap (cechSub f (∅ : Finset (Fin r))) A a)) =
      DirectSum.lof B (Idx s 0) (fun V => cechMod g B V.1) default
        (LocalizedModule.mkLinearMap (cechSub g (∅ : Finset (Fin s))) B (φ a)) := by
  have h1 := termMap_lof φ f 0 (default : Idx r 0)
    (LocalizedModule.mkLinearMap (cechSub f (∅ : Finset (Fin r))) A a)
  have h2 := congrArg
    (fun z => DirectSum.lof B (Idx r 0) (fun U => cechMod (mapFamily φ f) B U.1) default z)
    (modMap_mkLinearMap φ f (∅ : Finset (Fin r)) a)
  have h3 := genTerm_lof_zero (mapFamily φ f) g α hα B (φ a)
  exact (congrArg (fun z => genTerm (mapFamily φ f) g α hα B 0 z) (h1.trans h2)).trans h3

/-! ### Functoriality -/

/-- **Along the identity ring map the comparison is the same-ring comparison.** -/
theorem genRingTerm_id_ring (f : Fin r → A) (g : Fin s → A) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, (RingHom.id A) (f (α j)) ∣ g j ^ n) (p : ℕ) :
    genRingTerm (RingHom.id A) f g α hα p = genTerm f g α hα A p := by
  refine LinearMap.ext fun x => ?_
  exact congrArg (fun z => genTerm (mapFamily (RingHom.id A) f) g α hα A p z)
    (LinearMap.congr_fun (termMap_id f p) x)

/-- **The comparisons compose**, degreewise: for `A → B → C` the composite of the comparison for
`φ` and `α` with the comparison for `ψ` and `β` is the comparison for `ψ ∘ φ` and `α ∘ β`. -/
theorem genRingTerm_comp (φ : A →+* B) (ψ : B →+* C) (f : Fin r → A) (g : Fin s → B)
    (h : Fin t → C) (α : Fin s → Fin r) (β : Fin t → Fin s)
    (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n)
    (hβ : ∀ k : Fin t, ∃ n : ℕ, ψ (g (β k)) ∣ h k ^ n)
    (hαβ : ∀ k : Fin t, ∃ n : ℕ, (ψ.comp φ) (f (α (β k))) ∣ h k ^ n) (p : ℕ) :
    (restrictHom φ (ModuleCat.ofHom (genRingTerm ψ g h β hβ p))).comp
        (genRingTerm φ f g α hα p) = genRingTerm (ψ.comp φ) f h (α ∘ β) hαβ p := by
  refine LinearMap.ext fun x => ?_
  have e1 := LinearMap.congr_fun (termMap_comp_genTerm ψ (mapFamily φ f) g α hα p)
    (termMap φ f p x)
  have e2 := LinearMap.congr_fun
    (genTerm_comp (mapFamily ψ (mapFamily φ f)) (mapFamily ψ g) α
      (mapFamily_dvd ψ (mapFamily φ f) g α hα) C h β hβ hαβ p)
    (termMap ψ (mapFamily φ f) p (termMap φ f p x))
  have e3 := LinearMap.congr_fun (termMap_comp_termMap φ ψ f p) x
  refine ((congrArg (fun z => genTerm (mapFamily ψ g) h β hβ C p z) e1.symm).trans e2).trans ?_
  exact congrArg
    (fun z => genTerm (mapFamily ψ (mapFamily φ f)) h (α ∘ β) hαβ C p z) e3

/-- **A same-ring comparison on the source is absorbed** into the comparison along a ring map. -/
theorem genRingTerm_comp_genTerm (φ : A →+* B) (f : Fin r → A) (f' : Fin s → A) (g : Fin t → B)
    (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ f' j ^ n) (β : Fin t → Fin s)
    (hβ : ∀ k : Fin t, ∃ n : ℕ, φ (f' (β k)) ∣ g k ^ n) (γ : Fin t → Fin r)
    (hγ : ∀ k : Fin t, ∃ n : ℕ, φ (f (γ k)) ∣ g k ^ n) (hγαβ : γ = α ∘ β) (p : ℕ) :
    (genRingTerm φ f' g β hβ p).comp (genTerm f f' α hα A p) = genRingTerm φ f g γ hγ p := by
  subst hγαβ
  refine LinearMap.ext fun x => ?_
  have e1 := LinearMap.congr_fun (termMap_comp_genTerm φ f f' α hα p) x
  have e2 := LinearMap.congr_fun
    (genTerm_comp (mapFamily φ f) (mapFamily φ f') α (mapFamily_dvd φ f f' α hα) B g β hβ
      (fun k => hγ k) p) (termMap φ f p x)
  exact (congrArg (fun z => genTerm (mapFamily φ f') g β hβ B p z) e1.symm).trans e2

/-- **A same-ring comparison on the target is absorbed** into the comparison along a ring map. -/
theorem genTerm_comp_genRingTerm (φ : A →+* B) (f : Fin r → A) (g : Fin s → B) (g' : Fin t → B)
    (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) (δ : Fin t → Fin s)
    (hδ : ∀ k : Fin t, ∃ n : ℕ, g (δ k) ∣ g' k ^ n) (γ : Fin t → Fin r)
    (hγ : ∀ k : Fin t, ∃ n : ℕ, φ (f (γ k)) ∣ g' k ^ n) (hγαδ : γ = α ∘ δ) (p : ℕ) :
    (restrictHom φ (ModuleCat.ofHom (genTerm g g' δ hδ B p))).comp (genRingTerm φ f g α hα p)
      = genRingTerm φ f g' γ hγ p := by
  subst hγαδ
  exact LinearMap.ext fun x => LinearMap.congr_fun
    (genTerm_comp (mapFamily φ f) g α hα B g' δ hδ (fun k => hγ k) p) (termMap φ f p x)

end Cech


end

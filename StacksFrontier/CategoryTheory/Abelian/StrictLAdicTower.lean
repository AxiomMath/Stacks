module

public import StacksFrontier.CategoryTheory.Abelian.TowerMittagLeffler
public import StacksFrontier.CategoryTheory.Abelian.PowExact

/-!
# Strict ℓ-adic towers in an abelian category

A tower `P : ℕᵒᵖ ⥤ C` in an abelian category is *strict ℓ-adic* when its level `n` is killed by
`ℓⁿ⁺¹` and each transition `Pₙ₊₁ ⟶ Pₙ` is the quotient by `ℓⁿ⁺¹`
(`CategoryTheory.LAdicTower.IsStrict`): the levels of an ℓ-adic sheaf
([Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)), read in any abelian category of sheaves
of modules, form such a tower. Multiplication by `ℓ` on `Pₙ₊₁` factors through the transition,
which gives the Verschiebung `Pₙ ⟶ Pₙ₊₁` (`CategoryTheory.LAdicTower.IsStrict.verschiebung`), and
when the levels are flat (`CategoryTheory.Abelian.PowExact`) the sequences

`0 → P_a → P_{a+b+1} → P_b → 0`

(the iterated Verschiebung, then the transition) are short exact
(`CategoryTheory.LAdicTower.IsStrict.shortExact`).

## Main definitions

* `CategoryTheory.LAdicTower.IsStrict`: the predicate that a tower is strict ℓ-adic.
* `CategoryTheory.LAdicTower.IsStrict.verschiebung`: the Verschiebung `Pₙ ⟶ Pₙ₊₁` of a strict
  tower.

## Main results

* `CategoryTheory.LAdicTower.IsStrict.of_isCokernel`: a tower whose levels are killed by `ℓⁿ⁺¹`
  and whose transitions are cokernels of `ℓⁿ⁺¹` is strict.
* `CategoryTheory.LAdicTower.IsStrict.isVerschiebung`: the Verschiebung of a strict tower is a
  Verschiebung for `ℓ`.
* `CategoryTheory.LAdicTower.IsStrict.shortExact`: with flat levels, the sequences
  `0 → P_a → P_{a+b+1} → P_b → 0` are short exact.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Preadditive Opposite CategoryTheory.Abelian

namespace CategoryTheory.LAdicTower

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {P : ℕᵒᵖ ⥤ C} {ℓ : ℕ}

/-! ### Functors applied to towers with a Verschiebung -/

section Map

variable {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) (T : ℕᵒᵖ ⥤ C)
  (v : ∀ n, towerObj T n ⟶ towerObj T (n + 1))

/-- A functor carries the iterated Verschiebung to the iterated Verschiebung of the image tower. -/
theorem map_verschiebungMap {a b : ℕ} (h : a ≤ b) :
    G.map (verschiebungMap T v h) = verschiebungMap (T ⋙ G) (fun n => G.map (v n)) h := by
  induction b, h using Nat.le_induction with
  | base => rw [verschiebungMap_self, verschiebungMap_self, G.map_id]; rfl
  | succ b hab ih =>
    rw [verschiebungMap_le_succ T v hab, verschiebungMap_le_succ (T ⋙ G) _ hab, G.map_comp, ih]

/-- An additive functor carries a Verschiebung to a Verschiebung. -/
theorem IsVerschiebung.map [G.Additive] {ℓ : ℕ} (hv : IsVerschiebung T v ℓ) :
    IsVerschiebung (T ⋙ G) (fun n => G.map (v n)) ℓ where
  v_t n := by
    show G.map (v n) ≫ G.map (towerMap T (Nat.le_succ n)) = _
    rw [← G.map_comp, hv.v_t n, G.map_nsmul, G.map_id]; rfl
  t_v n := by
    show G.map (towerMap T (Nat.le_succ n)) ≫ G.map (v n) = _
    rw [← G.map_comp, hv.t_v n, G.map_nsmul, G.map_id]; rfl

end Map

/-! ### Flatness along isomorphisms and exact functors -/

section PowExact

variable {p m : ℕ}

/-- Flatness (`CategoryTheory.Abelian.PowExact`) is invariant under isomorphism. -/
theorem powExact_of_iso {X Y : C} (e : X ≅ Y) (h : PowExact p m X) : PowExact p m Y := by
  intro a ha T x hx
  obtain ⟨T', π, hπ, y, hy⟩ := h a ha (x ≫ e.inv) (by
    rw [Category.assoc, ← nsmul_id_comp, ← Category.assoc, hx, zero_comp])
  refine ⟨T', π, hπ, y ≫ e.hom, ?_⟩
  rw [Category.assoc, ← nsmul_id_comp e.hom, ← Category.assoc, ← hy, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end PowExact

/-- A tower is *strict ℓ-adic* when its level `n` is killed by `ℓⁿ⁺¹` and each transition
`Pₙ₊₁ ⟶ Pₙ` is an epimorphism with kernel `ℓⁿ⁺¹ Pₙ₊₁` (up to refinements). -/
structure IsStrict (P : ℕᵒᵖ ⥤ C) (ℓ : ℕ) : Prop where
  /-- The level `n` is killed by `ℓⁿ⁺¹`. -/
  annihilated : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj P n) = 0
  /-- The kernel of the transition `Pₙ₊₁ ⟶ Pₙ` is `ℓⁿ⁺¹ Pₙ₊₁`, up to refinements. -/
  exact : ∀ (n : ℕ) ⦃X : C⦄ (x : X ⟶ towerObj P (n + 1)), x ≫ towerMap P (Nat.le_succ n) = 0 →
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (y : X' ⟶ towerObj P (n + 1)),
      π ≫ x = y ≫ (ℓ ^ (n + 1) • 𝟙 _)
  /-- The transition `Pₙ₊₁ ⟶ Pₙ` is an epimorphism. -/
  epi : ∀ n, Epi (towerMap P (Nat.le_succ n))

/-- If the level `b` is killed by `ℓᵇ⁺¹`, then multiplication by `ℓᵇ⁺¹` on `P_m` followed by the
transition `P_m ⟶ P_b` is zero. -/
private theorem nsmul_id_comp_towerMap_eq_zero {b m : ℕ} (hb : ℓ ^ (b + 1) • 𝟙 (towerObj P b) = 0)
    (h : b ≤ m) : (ℓ ^ (b + 1) • 𝟙 (towerObj P m)) ≫ towerMap P h = 0 := by
  rw [nsmul_id_comp, hb, comp_zero]

/-- If the level `n` is killed by `ℓⁿ⁺¹` for every `n`, then multiplication by `ℓⁿ⁺¹` on `Pₙ₊₁`
followed by the transition `Pₙ₊₁ ⟶ Pₙ` is zero. -/
theorem nsmul_id_comp_eq_zero (hann : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj P n) = 0) (n : ℕ) :
    (ℓ ^ (n + 1) • 𝟙 (towerObj P (n + 1))) ≫ towerMap P (Nat.le_succ n) = 0 :=
  nsmul_id_comp_towerMap_eq_zero (hann n) _

/-- A tower whose levels are killed by the powers of `ℓ` and whose transitions are cokernels of
multiplication by `ℓⁿ⁺¹` is strict. -/
theorem IsStrict.of_isCokernel (hann : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj P n) = 0)
    (hc : ∀ n, IsColimit (CokernelCofork.ofπ _ (nsmul_id_comp_eq_zero hann n))) :
    IsStrict P ℓ where
  annihilated := hann
  exact n X x hx := by
    have h : (ShortComplex.mk _ _ (nsmul_id_comp_eq_zero hann n)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (hc n)
    exact h.exact_up_to_refinements x hx
  epi n := Cofork.IsColimit.epi (hc n)

namespace IsStrict

variable (hP : IsStrict P ℓ)
include hP

/-- The sequence `Pₙ₊₁ ⟶ Pₙ₊₁ ⟶ Pₙ` given by multiplication by `ℓⁿ⁺¹` and the transition is
exact. -/
theorem shortComplex_exact (n : ℕ) :
    (ShortComplex.mk _ _ (nsmul_id_comp_eq_zero hP.annihilated n)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro X x hx
  exact hP.exact n x hx

/-- The transition `Pₙ₊₁ ⟶ Pₙ` is the cokernel of `ℓⁿ⁺¹`. -/
def isCokernel (n : ℕ) :
    IsColimit (CokernelCofork.ofπ _ (nsmul_id_comp_eq_zero hP.annihilated n)) :=
  haveI := hP.epi n
  (hP.shortComplex_exact n).gIsCokernel

/-- **The Verschiebung** `Pₙ ⟶ Pₙ₊₁`: multiplication by `ℓ` on `Pₙ₊₁` kills `ℓⁿ⁺¹`, hence factors
through the transition. -/
def verschiebung (n : ℕ) : towerObj P n ⟶ towerObj P (n + 1) :=
  (hP.isCokernel n).desc (CokernelCofork.ofπ (ℓ • 𝟙 (towerObj P (n + 1))) (by
    rw [nsmul_comp, Category.id_comp, smul_smul, ← pow_succ, hP.annihilated (n + 1)]))

/-- The transition `Pₙ₊₁ ⟶ Pₙ` followed by the Verschiebung is multiplication by `ℓ`. -/
theorem towerMap_verschiebung (n : ℕ) :
    towerMap P (Nat.le_succ n) ≫ hP.verschiebung n = ℓ • 𝟙 _ :=
  (hP.isCokernel n).fac _ WalkingParallelPair.one

/-- The Verschiebung of a strict tower is a Verschiebung for `ℓ`. -/
theorem isVerschiebung : IsVerschiebung P hP.verschiebung ℓ where
  t_v := hP.towerMap_verschiebung
  v_t n := by
    have := hP.epi n
    rw [← cancel_epi (towerMap P (Nat.le_succ n)), reassoc_of% hP.towerMap_verschiebung n,
      nsmul_comp, Category.id_comp, comp_nsmul, Category.comp_id]

/-- Every transition map `P_m ⟶ P_b` of a strict tower is an epimorphism. -/
theorem towerMap_epi {b m : ℕ} (h : b ≤ m) : Epi (towerMap P h) := by
  induction m, h using Nat.le_induction with
  | base => rw [towerMap_self]; infer_instance
  | succ m hbm ih =>
    rw [← towerMap_comp P hbm (Nat.le_succ m)]
    have := hP.epi m
    exact epi_comp _ _

/-- The kernel of `P_m ⟶ P_b` is `ℓ^{b+1} P_m`, up to refinements. -/
theorem towerMap_exact {b m : ℕ} (h : b ≤ m) ⦃X : C⦄ (x : X ⟶ towerObj P m)
    (hx : x ≫ towerMap P h = 0) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (y : X' ⟶ towerObj P m),
      π ≫ x = y ≫ (ℓ ^ (b + 1) • 𝟙 _) := by
  induction m, h using Nat.le_induction generalizing X with
  | base =>
    have : x = 0 := by simpa [towerMap_self] using hx
    exact ⟨X, 𝟙 X, inferInstance, 0, by rw [this, comp_zero, zero_comp]⟩
  | succ m hbm ih =>
    have hx' : (x ≫ towerMap P (Nat.le_succ m)) ≫ towerMap P hbm = 0 := by
      rw [Category.assoc, towerMap_comp]; exact hx
    obtain ⟨X₁, π₁, hπ₁, y, hy⟩ := ih (x ≫ towerMap P (Nat.le_succ m)) hx'
    have := hP.epi m
    obtain ⟨X₂, π₂, hπ₂, y', hy'⟩ := surjective_up_to_refinements_of_epi
      (towerMap P (Nat.le_succ m)) y
    have h1 : π₂ ≫ π₁ ≫ x ≫ towerMap P (Nat.le_succ m) =
        (y' ≫ (ℓ ^ (b + 1) • 𝟙 _)) ≫ towerMap P (Nat.le_succ m) := by
      rw [hy, ← Category.assoc, hy']
      simp only [nsmul_comp, comp_nsmul, Category.comp_id]
    have hz : (π₂ ≫ π₁ ≫ x - y' ≫ (ℓ ^ (b + 1) • 𝟙 _)) ≫ towerMap P (Nat.le_succ m) = 0 := by
      rw [sub_comp, sub_eq_zero]
      simpa only [Category.assoc] using h1
    obtain ⟨X₃, π₃, hπ₃, z, hz'⟩ := hP.exact m _ hz
    refine ⟨X₃, π₃ ≫ π₂ ≫ π₁, inferInstance,
      π₃ ≫ y' + z ≫ (ℓ ^ (m - b) • 𝟙 _), ?_⟩
    have e : (ℓ ^ (m - b) • 𝟙 (towerObj P (m + 1))) ≫ (ℓ ^ (b + 1) • 𝟙 _) =
        ℓ ^ (m + 1) • 𝟙 _ := by
      rw [nsmul_comp, Category.id_comp, smul_smul, ← pow_add]
      congr 2
      omega
    rw [comp_sub, sub_eq_iff_eq_add] at hz'
    rw [add_comp, Category.assoc z, e, Category.assoc, Category.assoc, hz', Category.assoc]
    exact add_comm _ _

/-- The iterated Verschiebung followed by the transition `P_m ⟶ P_b`, `m = a + b + 1`, is zero. -/
theorem verschiebungMap_towerMap_eq_zero (a b m : ℕ) (hm : a + b + 1 = m) :
    verschiebungMap P hP.verschiebung (show a ≤ m by omega) ≫
      towerMap P (show b ≤ m by omega) = 0 := by
  have := hP.towerMap_epi (show a ≤ m by omega)
  rw [← cancel_epi (towerMap P (show a ≤ m by omega)), comp_zero,
    ← Category.assoc, hP.isVerschiebung.towerMap_verschiebungMap_self,
    show m - a = b + 1 by omega]
  exact nsmul_id_comp_towerMap_eq_zero (hP.annihilated b) _

/-- **The sequences `0 → P_a → P_m → P_b → 0`, `m = a + b + 1`, of a strict tower with flat
levels are short exact**: the first map is the iterated Verschiebung, the second the
transition. -/
theorem shortExact (hflat : ∀ n, PowExact ℓ (n + 1) (towerObj P n)) (a b m : ℕ)
    (hm : a + b + 1 = m) :
    (ShortComplex.mk (verschiebungMap P hP.verschiebung (show a ≤ m by omega))
      (towerMap P (show b ≤ m by omega))
      (hP.verschiebungMap_towerMap_eq_zero a b m hm)).ShortExact := by
  have := hP.towerMap_epi (show b ≤ m by omega)
  have := hP.towerMap_epi (show a ≤ m by omega)
  refine ShortComplex.ShortExact.mk' ?_ ?_ inferInstance
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro X x hx
    obtain ⟨X', π, hπ, y, hy⟩ := hP.towerMap_exact (show b ≤ m by omega) x hx
    refine ⟨X', π, hπ, y ≫ towerMap P (show a ≤ m by omega), ?_⟩
    dsimp
    rw [hy, Category.assoc, hP.isVerschiebung.towerMap_verschiebungMap_self,
      show m - a = b + 1 by omega]
  · apply Preadditive.mono_of_cancel_zero
    intro X x hx
    obtain ⟨X₁, π₁, hπ₁, w, hw⟩ := surjective_up_to_refinements_of_epi
      (towerMap P (show a ≤ m by omega)) x
    have hw0 : w ≫ (ℓ ^ (b + 1) • 𝟙 (towerObj P m)) = 0 := by
      rw [← show m - a = b + 1 by omega,
        ← hP.isVerschiebung.towerMap_verschiebungMap_self (show a ≤ m by omega),
        ← Category.assoc, ← hw, Category.assoc, hx, comp_zero]
    obtain ⟨X₂, π₂, hπ₂, y, hy⟩ := hflat m (b + 1) (by omega) w hw0
    have h0 : π₂ ≫ π₁ ≫ x = 0 := by
      rw [hw, ← Category.assoc, hy, Category.assoc, show m + 1 - (b + 1) = a + 1 by omega,
        nsmul_id_comp_towerMap_eq_zero (hP.annihilated a), comp_zero]
    rw [← cancel_epi π₁, ← cancel_epi π₂, comp_zero, comp_zero]
    exact h0

end IsStrict

end CategoryTheory.LAdicTower

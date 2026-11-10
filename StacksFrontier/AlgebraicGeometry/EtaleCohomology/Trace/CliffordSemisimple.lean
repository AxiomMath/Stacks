module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Restriction of a semisimple representation to a normal subgroup (Clifford)

Let `ρ : Γ → End(V)` be a finite-dimensional representation of a group in which every stable
subspace has a stable complement (a semisimple representation).  Then the same holds for the
restriction of `ρ` to any normal subgroup `N` of `Γ`.

## Main definitions

* `Stacks.EtaleCohomology.IsStableUnder`: a subspace stable under every element of a set of
  endomorphisms.
* `Stacks.EtaleCohomology.IsIrreducibleUnder`: a nonzero stable subspace with no stable
  subspaces other than `0` and itself.

## Main results

* `Stacks.EtaleCohomology.exists_isCompl_of_normal`: the restriction of a semisimple representation
  to a normal subgroup is semisimple.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `W` is stable under every element of `S`. -/
def IsStableUnder (S : Set (Module.End K V)) (W : Submodule K V) : Prop :=
  ∀ s ∈ S, W ≤ W.comap s

omit [FiniteDimensional K V] in
/-- The sum of two `S`-stable subspaces is `S`-stable. -/
theorem isStableUnder_sup {S : Set (Module.End K V)} {W₁ W₂ : Submodule K V}
    (h₁ : IsStableUnder S W₁) (h₂ : IsStableUnder S W₂) : IsStableUnder S (W₁ ⊔ W₂) :=
  fun s hs => sup_le ((h₁ s hs).trans (Submodule.comap_mono le_sup_left))
    ((h₂ s hs).trans (Submodule.comap_mono le_sup_right))

omit [FiniteDimensional K V] in
/-- The intersection of two `S`-stable subspaces is `S`-stable. -/
theorem isStableUnder_inf {S : Set (Module.End K V)} {W₁ W₂ : Submodule K V}
    (h₁ : IsStableUnder S W₁) (h₂ : IsStableUnder S W₂) : IsStableUnder S (W₁ ⊓ W₂) :=
  fun s hs _ hx => ⟨h₁ s hs hx.1, h₂ s hs hx.2⟩

omit [FiniteDimensional K V] in
/-- The supremum of a family of `S`-stable subspaces is `S`-stable. -/
theorem isStableUnder_sSup {S : Set (Module.End K V)} {T : Set (Submodule K V)}
    (h : ∀ W ∈ T, IsStableUnder S W) : IsStableUnder S (sSup T) :=
  fun s hs => sSup_le fun W hW => (h W hW s hs).trans (Submodule.comap_mono (le_sSup hW))

/-- `W` is `S`-irreducible: nonzero, `S`-stable, with no `S`-stable subspaces but `0` and `W`. -/
def IsIrreducibleUnder (S : Set (Module.End K V)) (W : Submodule K V) : Prop :=
  W ≠ ⊥ ∧ IsStableUnder S W ∧ ∀ W' ≤ W, IsStableUnder S W' → W' = ⊥ ∨ W' = W

/-- Every nonzero `S`-stable subspace contains an `S`-irreducible one. -/
theorem exists_isIrreducibleUnder_le {S : Set (Module.End K V)} {W : Submodule K V}
    (hW : W ≠ ⊥) (hS : IsStableUnder S W) : ∃ X ≤ W, IsIrreducibleUnder S X := by
  classical
  let P : ℕ → Prop := fun d => ∃ X ≤ W, X ≠ ⊥ ∧ IsStableUnder S X ∧ Module.finrank K X = d
  have hP : ∃ d, P d := ⟨_, W, le_rfl, hW, hS, rfl⟩
  obtain ⟨X, hXW, hX0, hXS, hXd⟩ := Nat.find_spec hP
  refine ⟨X, hXW, hX0, hXS, fun X' hX' hX'S => ?_⟩
  by_contra h
  simp only [not_or] at h
  have hlt : X' < X := lt_of_le_of_ne hX' h.2
  have := Nat.find_min' hP ⟨X', hX'.trans hXW, h.1, hX'S, rfl⟩
  rw [← hXd] at this
  exact absurd (Submodule.finrank_lt_finrank_of_lt hlt) (not_lt.mpr this)

/-- **A sum of irreducible subspaces is semisimple.**  If `V` is the sum of its `S`-irreducible
subspaces, every `S`-stable subspace has an `S`-stable complement. -/
theorem exists_isCompl_of_sSup_eq_top {S : Set (Module.End K V)}
    (htop : sSup {X | IsIrreducibleUnder S X} = ⊤) {W : Submodule K V} (hW : IsStableUnder S W) :
    ∃ W', IsCompl W W' ∧ IsStableUnder S W' := by
  classical
  let P : ℕ → Prop := fun d => ∃ W', Disjoint W W' ∧ IsStableUnder S W' ∧
    Module.finrank K V - Module.finrank K W' = d
  have hP : ∃ d, P d := ⟨_, ⊥, disjoint_bot_right, fun s _ => bot_le, rfl⟩
  obtain ⟨W', hdis, hW'S, hd⟩ := Nat.find_spec hP
  refine ⟨W', ⟨hdis, ?_⟩, hW'S⟩
  rw [codisjoint_iff, eq_top_iff, ← htop]
  refine sSup_le fun X hX => ?_
  by_contra hXle
  have hXi : X ⊓ (W ⊔ W') = ⊥ :=
    (hX.2.2 _ inf_le_left (isStableUnder_inf hX.2.1 (isStableUnder_sup hW hW'S))).resolve_right
      fun h => hXle (h ▸ inf_le_right)
  have hdis' : Disjoint W (W' ⊔ X) := by
    rw [disjoint_iff]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxW, hx'⟩ := hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    have hzX : z ∈ X ⊓ (W ⊔ W') := ⟨hz, by
      simpa using Submodule.sub_mem _ (Submodule.mem_sup_left hxW) (Submodule.mem_sup_right hy)⟩
    rw [hXi, Submodule.mem_bot] at hzX
    subst hzX
    rw [add_zero] at hxW ⊢
    exact (Submodule.mem_bot K).mpr (Submodule.disjoint_def.mp hdis y hxW hy)
  have hlt : W' < W' ⊔ X := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hXW' : X ≤ W' := h ▸ le_sup_right
    have : X ≤ X ⊓ (W ⊔ W') := le_inf le_rfl (hXW'.trans le_sup_right)
    rw [hXi] at this
    exact hX.1 (eq_bot_iff.mpr this)
  have hmin := Nat.find_min' hP ⟨W' ⊔ X, hdis', isStableUnder_sup hW'S hX.2.1, rfl⟩
  rw [← hd] at hmin
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : Module.finrank K (W' ⊔ X : Submodule K V) ≤ Module.finrank K V :=
    Submodule.finrank_le _
  omega

/-- A semisimple representation is the sum of its irreducible subspaces. -/
theorem sSup_isIrreducibleUnder_eq_top {S : Set (Module.End K V)}
    (hss : ∀ W, IsStableUnder S W → ∃ W', IsCompl W W' ∧ IsStableUnder S W') :
    sSup {X | IsIrreducibleUnder S X} = ⊤ := by
  set T := sSup {X | IsIrreducibleUnder S X}
  obtain ⟨T', hc, hT'⟩ := hss T (isStableUnder_sSup fun X hX => hX.2.1)
  by_contra hne
  have hT'0 : T' ≠ ⊥ := by
    rintro rfl
    exact hne (by simpa using hc.sup_eq_top)
  obtain ⟨X, hXT', hX⟩ := exists_isIrreducibleUnder_le hT'0 hT'
  have hXT : X ≤ T := le_sSup hX
  exact hX.1 (eq_bot_iff.mpr ((le_inf hXT hXT').trans hc.inf_eq_bot.le))

omit [FiniteDimensional K V] in
/-- If `W` is stable under `b` and `u⁻¹ a u = b`, then `u W` is stable under `a`. -/
theorem map_unit_le_comap {W : Submodule K V} {a b : Module.End K V} {u : (Module.End K V)ˣ}
    (h : W ≤ W.comap b) (hab : ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) * a * u = b) :
    W.map (u : Module.End K V) ≤ (W.map (u : Module.End K V)).comap a := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨b w, h hw, ?_⟩
  rw [← hab, ← Module.End.mul_apply, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul,
    Module.End.mul_apply]

/-- **Clifford.**  The restriction of a semisimple representation of a group `Γ` to a normal
subgroup `N` is semisimple. -/
theorem exists_isCompl_of_normal (Γ N : Subgroup (Module.End K V)ˣ) (hNΓ : N ≤ Γ)
    (hnormal : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hss : ∀ W, IsStableUnder (Units.val '' (Γ : Set (Module.End K V)ˣ)) W →
      ∃ W', IsCompl W W' ∧ IsStableUnder (Units.val '' (Γ : Set (Module.End K V)ˣ)) W')
    {W : Submodule K V} (hW : IsStableUnder (Units.val '' (N : Set (Module.End K V)ˣ)) W) :
    ∃ W', IsCompl W W' ∧ IsStableUnder (Units.val '' (N : Set (Module.End K V)ˣ)) W' := by
  set SΓ : Set (Module.End K V) := Units.val '' (Γ : Set (Module.End K V)ˣ)
  set SN : Set (Module.End K V) := Units.val '' (N : Set (Module.End K V)ˣ)
  refine exists_isCompl_of_sSup_eq_top (eq_top_iff.mpr ?_) hW
  rw [← sSup_isIrreducibleUnder_eq_top hss]
  refine sSup_le fun X hX => ?_
  have htrans : ∀ γ ∈ Γ, ∀ X₀ : Submodule K V, IsStableUnder SN X₀ →
      IsStableUnder SN (X₀.map (γ : Module.End K V)) := by
    rintro γ hγ X₀ hX₀ _ ⟨n, hn, rfl⟩
    refine map_unit_le_comap (hX₀ _ ⟨γ⁻¹ * n * γ, ?_, rfl⟩) ?_
    · simpa using hnormal γ⁻¹ (inv_mem hγ) n hn
    · simp [Units.val_mul, mul_assoc]
  have hXN : IsStableUnder SN X := fun s ⟨n, hn, hs⟩ => hX.2.1 s ⟨n, hNΓ hn, hs⟩
  obtain ⟨X₀, hX₀X, hX₀⟩ := exists_isIrreducibleUnder_le hX.1 hXN
  have hirr : ∀ γ ∈ Γ, IsIrreducibleUnder SN (X₀.map (γ : Module.End K V)) := by
    intro γ hγ
    refine ⟨fun h => hX₀.1 ?_, htrans γ hγ X₀ hX₀.2.1, fun Y hY hYS => ?_⟩
    · rw [eq_bot_iff] at h ⊢
      intro x hx
      have := h ⟨x, hx, rfl⟩
      rw [Submodule.mem_bot] at this ⊢
      have h2 := congrArg ((γ⁻¹ : (Module.End K V)ˣ) : Module.End K V) this
      simpa [← Module.End.mul_apply] using h2
    · have hY' : Y.map ((γ⁻¹ : (Module.End K V)ˣ) : Module.End K V) ≤ X₀ := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hY hy
        simpa [← Module.End.mul_apply] using hx
      rcases hX₀.2.2 _ hY' (htrans γ⁻¹ (inv_mem hγ) Y hYS) with h | h
      · left
        rw [eq_bot_iff] at h ⊢
        intro y hy
        have := h ⟨y, hy, rfl⟩
        rw [Submodule.mem_bot] at this ⊢
        have h2 := congrArg (γ : Module.End K V) this
        simpa [← Module.End.mul_apply] using h2
      · right
        refine le_antisymm hY ?_
        rintro _ ⟨x, hx, rfl⟩
        rw [← h] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa [← Module.End.mul_apply] using hy
  set Y := sSup {Z | ∃ γ ∈ Γ, Z = X₀.map (γ : Module.End K V)}
  have hYX : Y ≤ X := sSup_le fun Z ⟨γ, hγ, hZ⟩ => by
    subst hZ
    rintro _ ⟨x, hx, rfl⟩
    exact hX.2.1 _ ⟨γ, hγ, rfl⟩ (hX₀X hx)
  have hYS : IsStableUnder SΓ Y := by
    rintro _ ⟨γ', hγ', rfl⟩
    refine sSup_le fun Z ⟨γ, hγ, hZ⟩ => ?_
    subst hZ
    rintro _ ⟨x, hx, rfl⟩
    change (γ' : Module.End K V) ((γ : Module.End K V) x) ∈ Y
    have hmem : X₀.map ((γ' * γ : (Module.End K V)ˣ) : Module.End K V) ≤ Y :=
      le_sSup ⟨γ' * γ, mul_mem hγ' hγ, rfl⟩
    exact hmem ⟨x, hx, by rw [Units.val_mul, Module.End.mul_apply]⟩
  have hY0 : Y ≠ ⊥ := by
    intro h
    have : X₀.map ((1 : (Module.End K V)ˣ) : Module.End K V) ≤ Y := le_sSup ⟨1, one_mem _, rfl⟩
    rw [h, Units.val_one, Module.End.one_eq_id, Submodule.map_id] at this
    exact hX₀.1 (eq_bot_iff.mpr this)
  rw [← (hX.2.2 Y hYX hYS).resolve_left hY0]
  exact sSup_le fun Z ⟨γ, hγ, hZ⟩ => le_sSup (hZ ▸ hirr γ hγ)

end Stacks.EtaleCohomology

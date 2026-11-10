module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology.ProIso

@[expose] public section

/-!
# Homology of an adic complex modulo ideal powers (tag 0EGU)

For a complex `K → L → M` of finite modules over a Noetherian ring, the homology of the complex
reduced modulo `I ^ n` is pro-isomorphic to `H ⧸ I ^ n H` with a uniform Artin--Rees shift:
`Stacks.AdicSystem.ArtinReesHomology.exists_uniform_adic_homology_comparison`.
-/

/-! ## Tag 0EGU -/

section

open CategoryTheory CategoryTheory.Limits Opposite InverseSequence

namespace Stacks.AdicSystem.ArtinReesHomology

private lemma artinRees_preimage_bound
    {A L M : Type*} [CommRing A]
    [AddCommGroup L] [Module A L] [Module.Finite A L]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [IsNoetherianRing A]
    (I : Ideal A) (β : L →ₗ[A] M) :
    ∃ c : ℕ, ∀ n ≥ c,
      (I ^ n • (⊤ : Submodule A M)).comap β ≤
        LinearMap.ker β ⊔ I ^ (n - c) • (⊤ : Submodule A L) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (I := I) (LinearMap.range β)
  refine ⟨c, fun n hn x hx => ?_⟩
  have hβ : β x ∈ I ^ n • (⊤ : Submodule A M) ⊓ LinearMap.range β :=
    ⟨hx, ⟨x, rfl⟩⟩
  rw [hc n hn] at hβ
  have hβrange : β x ∈ I ^ (n - c) • LinearMap.range β := by
    have hle : I ^ (n - c) •
        ((I ^ c • (⊤ : Submodule A M)) ⊓ LinearMap.range β) ≤
        I ^ (n - c) • LinearMap.range β :=
      smul_mono_right (I ^ (n - c)) inf_le_right
    exact hle hβ
  have hβ' : β x ∈ Submodule.map β (I ^ (n - c) • (⊤ : Submodule A L)) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact hβrange
  rcases hβ' with ⟨y, hy, hxy⟩
  have hker : x - y ∈ LinearMap.ker β := by
    rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
  have hx_eq : x = (x - y) + y := by abel
  rw [hx_eq]
  exact Submodule.add_mem_sup hker hy

private lemma artinRees_kernel_intersection_bound
    {A L : Type*} [CommRing A]
    [AddCommGroup L] [Module A L] [Module.Finite A L]
    [IsNoetherianRing A]
    (I : Ideal A) (N : Submodule A L) :
    ∃ c : ℕ, ∀ n ≥ c,
      (I ^ n • (⊤ : Submodule A L)) ⊓ N ≤ I ^ (n - c) • N := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (I := I) N
  refine ⟨c, fun n hn => ?_⟩
  rw [hc n hn]
  exact smul_mono_right (I ^ (n - c)) inf_le_right

/-- A pro-isomorphism of inverse sequences induces an isomorphism of their limits. -/
private noncomputable def limitIsoOfProIso
    {C : Type*} [CategoryTheory.Category C]
    (X Y : ℕᵒᵖ ⥤ C) [HasLimit X] [HasLimit Y]
    (e : ProIso X Y) : limit X ≅ limit Y := by
  let cXY : Cone Y := Cone.mk (limit X) {
    app := fun j => limit.π X (op (e.α (unop j))) ≫ e.φ (unop j)
    naturality := by
      intro j k f
      have h : unop k ≤ unop j := leOfHom f.unop
      have hf : f = (homOfLE h).op := Subsingleton.elim _ _
      subst f
      simp only [Functor.const_obj_map]
      calc
        𝟙 (limit X) ≫ limit.π X (op (e.α (unop k))) ≫ e.φ (unop k) =
            limit.π X (op (e.α (unop k))) ≫ e.φ (unop k) := by simp
        _ = (limit.π X (op (e.α (unop j))) ≫ tr X (e.αmono h)) ≫
              e.φ (unop k) := by rw [tr, limit.w X ((homOfLE (e.αmono h)).op)]
        _ = limit.π X (op (e.α (unop j))) ≫
              (e.φ (unop j) ≫ tr Y h) := by
              rw [CategoryTheory.Category.assoc, e.φnat h]
        _ = (limit.π X (op (e.α (unop j))) ≫ e.φ (unop j)) ≫
              Y.map (homOfLE h).op := by simp [tr, CategoryTheory.Category.assoc] }
  let cYX : Cone X := Cone.mk (limit Y) {
    app := fun j => limit.π Y (op (e.β (unop j))) ≫ e.ψ (unop j)
    naturality := by
      intro j k f
      have h : unop k ≤ unop j := leOfHom f.unop
      have hf : f = (homOfLE h).op := Subsingleton.elim _ _
      subst f
      simp only [Functor.const_obj_map]
      calc
        𝟙 (limit Y) ≫ limit.π Y (op (e.β (unop k))) ≫ e.ψ (unop k) =
            limit.π Y (op (e.β (unop k))) ≫ e.ψ (unop k) := by simp
        _ = (limit.π Y (op (e.β (unop j))) ≫ tr Y (e.βmono h)) ≫
              e.ψ (unop k) := by rw [tr, limit.w Y ((homOfLE (e.βmono h)).op)]
        _ = limit.π Y (op (e.β (unop j))) ≫
              (e.ψ (unop j) ≫ tr X h) := by
              rw [CategoryTheory.Category.assoc, e.ψnat h]
        _ = (limit.π Y (op (e.β (unop j))) ≫ e.ψ (unop j)) ≫
              X.map (homOfLE h).op := by simp [tr, CategoryTheory.Category.assoc] }
  let f : limit X ⟶ limit Y := limit.lift Y cXY
  let g : limit Y ⟶ limit X := limit.lift X cYX
  refine ⟨f, g, ?_, ?_⟩
  · apply limit.hom_ext
    intro j
    let m : ℕ := unop j
    have hg : g ≫ limit.π X j =
        limit.π Y (op (e.β m)) ≫ e.ψ m := by
      simp [g, cYX, m]
    have hf : f ≫ limit.π Y (op (e.β m)) =
        limit.π X (op (e.α (e.β m))) ≫ e.φ (e.β m) := by
      simp [f, cXY]
    rw [CategoryTheory.Category.assoc, hg, ← CategoryTheory.Category.assoc, hf,
      CategoryTheory.Category.assoc, e.ψφ m]
    simpa only [tr, CategoryTheory.Category.id_comp] using
      limit.w X ((homOfLE (le_trans (e.βle m) (e.αle (e.β m)))).op)
  · apply limit.hom_ext
    intro j
    let m : ℕ := unop j
    have hf : f ≫ limit.π Y j =
        limit.π X (op (e.α m)) ≫ e.φ m := by
      simp [f, cXY, m]
    have hg : g ≫ limit.π X (op (e.α m)) =
        limit.π Y (op (e.β (e.α m))) ≫ e.ψ (e.α m) := by
      simp [g, cYX]
    rw [CategoryTheory.Category.assoc, hf, ← CategoryTheory.Category.assoc, hg,
      CategoryTheory.Category.assoc, e.φψ m]
    simpa only [tr, CategoryTheory.Category.id_comp] using
      limit.w Y ((homOfLE (le_trans (e.αle m) (e.βle (e.α m)))).op)

set_option maxHeartbeats 500000 in
-- The proof elaborates a family of quotient maps and both inverse-system limits.
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0EGU.** For a complex of finite modules over a Noetherian ring, homology after
reduction modulo `I ^ n` and the quotients by `I ^ n` of the original homology are canonically
pro-isomorphic.  A single positive shift controls the inverse-system images, the comparison on
ideal multiples, and the kernels and cokernels of all comparison maps. -/
@[stacks 0EGU]
theorem exists_uniform_adic_homology_comparison
    {A K L M : Type*} [CommRing A]
    [AddCommGroup K] [Module A K] [Module.Finite A K]
    [AddCommGroup L] [Module A L] [Module.Finite A L]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [IsNoetherianRing A]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (hcomplex : β.comp α = 0) :
    let H := (LinearMap.ker β) ⧸
      (LinearMap.range α).comap (LinearMap.ker β).subtype
    let cycles : ℕ → Submodule A L := fun n =>
      (I ^ n • (⊤ : Submodule A M)).comap β
    let boundaries : ℕ → Submodule A L := fun n =>
      LinearMap.range α ⊔ I ^ n • (⊤ : Submodule A L)
    let Hn : ℕ → Type _ := fun n =>
      cycles n ⧸ (boundaries n).comap (cycles n).subtype
    ∃ (toLevel : ∀ n, H →ₗ[A] Hn n)
      (transition : ∀ n, Hn (n + 1) →ₗ[A] Hn n)
      (quotTransition : ∀ n,
        (H ⧸ I ^ (n + 1) • (⊤ : Submodule A H)) →ₗ[A]
          (H ⧸ I ^ n • (⊤ : Submodule A H)))
      (fromQuotient : ∀ n,
        (H ⧸ I ^ n • (⊤ : Submodule A H)) →ₗ[A] Hn n),
      (∀ n (x : LinearMap.ker β) (y : cycles n), (y : L) = x →
        toLevel n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) ∧
      (∀ n (x : cycles (n + 1)) (y : cycles n), (y : L) = x →
        transition n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) ∧
      (∀ n (x : H),
        quotTransition n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) ∧
      (∀ n, transition n ∘ₗ toLevel (n + 1) = toLevel n) ∧
      (∀ n, fromQuotient n ∘ₗ (I ^ n • (⊤ : Submodule A H)).mkQ = toLevel n) ∧
      let Hsys : ℕᵒᵖ ⥤ ModuleCat A :=
        Functor.ofOpSequence (X := fun n => ModuleCat.of A (Hn n))
          (fun n => ModuleCat.ofHom (transition n))
      let Qsys : ℕᵒᵖ ⥤ ModuleCat A :=
        Functor.ofOpSequence
          (X := fun n => ModuleCat.of A (H ⧸ I ^ n • (⊤ : Submodule A H)))
          (fun n => ModuleCat.ofHom (quotTransition n))
      ∃ c : ℕ, 0 < c ∧
        (∃ back : ∀ n, c ≤ n → Hn n →ₗ[A]
            (H ⧸ I ^ (n - c) • (⊤ : Submodule A H)),
          (∀ n (hn : c ≤ n),
            (back n hn).comp (fromQuotient n) =
              (tr Qsys (Nat.sub_le n c)).hom) ∧
          (∀ n (hn : c ≤ n),
            (fromQuotient (n - c)).comp (back n hn) =
              (tr Hsys (Nat.sub_le n c)).hom) ∧
          Nonempty (ProIso Hsys Qsys) ∧
          Nonempty (limit Hsys ≅ limit Qsys) ∧
          (Hsys ⋙ forget (ModuleCat A)).IsMittagLeffler ∧
          (∀ n, LinearMap.range (tr Hsys (Nat.le_add_right n c)).hom =
            LinearMap.range (toLevel n)) ∧
          (∃ toLevelQuotient : ∀ n k,
              (H ⧸ I ^ k • (⊤ : Submodule A H)) →ₗ[A]
                (Hn n ⧸ I ^ k • (⊤ : Submodule A (Hn n))),
            (∀ n k, (toLevelQuotient n k).comp
                (I ^ k • (⊤ : Submodule A H)).mkQ =
              (I ^ k • (⊤ : Submodule A (Hn n))).mkQ.comp (toLevel n)) ∧
            (∀ n (hn : c ≤ n) (x : Hn n),
              x ∈ I ^ c • (⊤ : Submodule A (Hn n)) →
              toLevelQuotient n (n - c) (back n hn x) =
                (I ^ (n - c) • (⊤ : Submodule A (Hn n))).mkQ x)) ∧
          (∀ n,
            I ^ c ≤ Module.annihilator A (LinearMap.ker (fromQuotient n)) ∧
            I ^ c ≤ Module.annihilator A
              (Hn n ⧸ LinearMap.range (fromQuotient n)))) := by
  classical
  dsimp only
  let H := (LinearMap.ker β) ⧸
    (LinearMap.range α).comap (LinearMap.ker β).subtype
  let cycles : ℕ → Submodule A L := fun n =>
    (I ^ n • (⊤ : Submodule A M)).comap β
  let boundaries : ℕ → Submodule A L := fun n =>
    LinearMap.range α ⊔ I ^ n • (⊤ : Submodule A L)
  let Hn (n : ℕ) := cycles n ⧸ (boundaries n).comap (cycles n).subtype
  let rel (n : ℕ) := (boundaries n).comap (cycles n).subtype
  let S : Submodule A (LinearMap.ker β) :=
    (LinearMap.range α).comap (LinearMap.ker β).subtype
  obtain ⟨c₁, hc₁⟩ := artinRees_preimage_bound I β
  obtain ⟨c₂, hc₂⟩ := artinRees_kernel_intersection_bound I (LinearMap.ker β)
  let c := c₁ + c₂ + 1
  have hcpos : 0 < c := by dsimp [c]; omega
  have kerCycles (n : ℕ) : LinearMap.ker β ≤ cycles n := by
    intro x hx
    change β x ∈ I ^ n • (⊤ : Submodule A M)
    rw [LinearMap.mem_ker.mp hx]
    exact zero_mem _
  have cyclesMono {a b : ℕ} (hab : a ≤ b) : cycles b ≤ cycles a :=
    Submodule.comap_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hab))
  have decomp (n : ℕ) (hn : c₁ ≤ n) (y : cycles n) :
      ∃ z : LinearMap.ker β, (y : L) - z ∈ I ^ (n - c₁) • (⊤ : Submodule A L) := by
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp (hc₁ n hn y.property)
    exact ⟨⟨z, hz⟩, by rw [show (y : L) - z = w by rw [← hzw]; abel]; exact hw⟩
  have hmapS (t : ℕ) : Submodule.map S.mkQ (I ^ t • (⊤ : Submodule A (LinearMap.ker β))) =
      I ^ t • (⊤ : Submodule A H) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  let toLevel : ∀ n, H →ₗ[A] Hn n := fun n =>
    S.liftQ
      ((rel n).mkQ.comp ((LinearMap.ker β).inclusion (kerCycles n)))
      (by
        intro x hx
        change (x : L) ∈ LinearMap.range α at hx
        rcases hx with ⟨v, hv⟩
        apply (Submodule.Quotient.mk_eq_zero (rel n)).2
        change (x : L) ∈ boundaries n
        exact Submodule.mem_sup_left ⟨v, hv⟩)
  let transition : ∀ n, Hn (n + 1) →ₗ[A] Hn n := fun n =>
    (rel (n + 1)).mapQ (rel n)
      ((cycles (n + 1)).inclusion (cyclesMono n.le_succ))
      (by
        intro x hx
        change (x : L) ∈ boundaries n
        have hp : I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (by omega)
        exact (Submodule.comap_mono
          (sup_le_sup le_rfl (Submodule.smul_mono_left hp))) hx)
  let quotTransition : ∀ n,
      (H ⧸ I ^ (n + 1) • (⊤ : Submodule A H)) →ₗ[A]
        (H ⧸ I ^ n • (⊤ : Submodule A H)) := fun n =>
    (I ^ (n + 1) • (⊤ : Submodule A H)).mapQ
      (I ^ n • (⊤ : Submodule A H)) LinearMap.id (by
        intro x hx
        exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) hx)
  let fromQuotient : ∀ n,
      (H ⧸ I ^ n • (⊤ : Submodule A H)) →ₗ[A] Hn n := fun n =>
    (I ^ n • (⊤ : Submodule A H)).liftQ (toLevel n) (by
      intro x hx
      rw [← hmapS n] at hx
      rcases hx with ⟨y, hy, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero (rel n)).2
      change ((LinearMap.ker β).subtype y) ∈ boundaries n
      exact Submodule.mem_sup_right
        (Submodule.smul_top_le_comap_smul_top (I ^ n) (LinearMap.ker β).subtype hy))
  have hαker : LinearMap.range α ≤ LinearMap.ker β := by
    intro x hx
    rcases hx with ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    simpa [LinearMap.comp_apply] using congrArg (fun f : K →ₗ[A] M => f v) hcomplex
  let backWitness : ∀ (n t : ℕ) (ht : t + c ≤ n),
      {g : Hn n →ₗ[A] (H ⧸ I ^ t • (⊤ : Submodule A H)) //
        ∀ (y : cycles n) (z : LinearMap.ker β),
          (y : L) - (z : L) ∈ I ^ (n - c₁) • (⊤ : Submodule A L) →
          g (Submodule.Quotient.mk y) =
            (I ^ t • (⊤ : Submodule A H)).mkQ (S.mkQ z)} := fun n t ht => by
    let m := n - c₁
    let P := LinearMap.ker β
    let J := I ^ m • (⊤ : Submodule A L)
    let U := P ⊔ J
    let V := J.comap U.subtype
    let T := P.comap P.subtype ⊓ J.comap P.subtype
    let quotientEquiv := LinearMap.quotientInfEquivSupQuotient P J
    let f : P →ₗ[A] H ⧸ I ^ t • (⊤ : Submodule A H) :=
      (I ^ t • (⊤ : Submodule A H)).mkQ.comp S.mkQ
    have hn1 : c₁ ≤ n := by dsimp [c] at ht; omega
    have hU : cycles n ≤ U := by
      dsimp [U, J, m, P, cycles]
      exact hc₁ n hn1
    have hT : T ≤ f.ker := by
      intro x hx
      have hxJ : (x : L) ∈ J := hx.2
      have hix : (x : L) ∈ (I ^ m • (⊤ : Submodule A L)) ⊓ P :=
        ⟨hxJ, x.property⟩
      have hbound := hc₂ m (by dsimp [c] at ht; omega) hix
      have hexp : t ≤ m - c₂ := by dsimp [m, c] at ht ⊢; omega
      have hxP : (x : L) ∈ I ^ (m - c₂) • P := hbound
      have hxPt : x ∈ I ^ t • (⊤ : Submodule A P) :=
        (Submodule.mem_smul_top_iff (I ^ t) P x).2
          (Submodule.smul_mono_left (Ideal.pow_le_pow_right hexp) hxP)
      have hxH : S.mkQ x ∈ I ^ t • (⊤ : Submodule A H) := by
        rw [← hmapS t]
        exact ⟨x, hxPt, rfl⟩
      change (I ^ t • (⊤ : Submodule A H)).mkQ (S.mkQ x) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 hxH
    let lift := T.liftQ f hT
    let bridge : cycles n →ₗ[A] H ⧸ I ^ t • (⊤ : Submodule A H) :=
      lift.comp (quotientEquiv.symm.toLinearMap.comp
        (V.mkQ.comp ((cycles n).inclusion hU)))
    have hkill : rel n ≤ bridge.ker := by
      intro x hx
      have hxB : (x : L) ∈ boundaries n := hx
      obtain ⟨a, ha, b, hb, hab⟩ := (Submodule.mem_sup.mp hxB)
      have haP : a ∈ LinearMap.ker β := hαker ha
      have haC : a ∈ cycles n := by
        change β a ∈ I ^ n • (⊤ : Submodule A M)
        rw [LinearMap.mem_ker.mp haP]
        exact zero_mem _
      have hbC : b ∈ cycles n :=
        (Submodule.smul_top_le_comap_smul_top (I ^ n) β) hb
      have hxEq : x = ⟨a, haC⟩ + ⟨b, hbC⟩ := Subtype.ext hab.symm
      have haU : a ∈ U := Submodule.mem_sup_left haP
      have hbJ : b ∈ J := by
        dsimp [J, m]
        exact Submodule.smul_mono_left
          (Ideal.pow_le_pow_right (by dsimp [c] at ht; omega)) hb
      have hbU : b ∈ U := Submodule.mem_sup_right hbJ
      have haEq := LinearMap.quotientInfEquivSupQuotient_symm_apply_left P J
        ⟨a, haU⟩ haP
      have haS : (⟨a, haP⟩ : P) ∈ S := by
        change a ∈ LinearMap.range α
        exact ha
      have haZero : f ⟨a, haP⟩ = 0 := by
        change (I ^ t • (⊤ : Submodule A H)).mkQ (S.mkQ ⟨a, haP⟩) = 0
        have hmk : S.mkQ ⟨a, haP⟩ = 0 := (Submodule.Quotient.mk_eq_zero S).2 haS
        rw [hmk, map_zero]
      have hbV : (⟨b, hbU⟩ : U) ∈ V := by
        change b ∈ J
        exact hbJ
      have hbZero : V.mkQ ⟨b, hbU⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero V).2 hbV
      have hbBridge : bridge ⟨b, hbC⟩ = 0 := by
        change lift (quotientEquiv.symm (V.mkQ ⟨b, hbU⟩)) = 0
        rw [hbZero]
        simp
      have haBridge : bridge ⟨a, haC⟩ = 0 := by
        change lift ((LinearMap.quotientInfEquivSupQuotient P J).symm
          (Submodule.Quotient.mk ⟨a, haU⟩)) = 0
        rw [haEq]
        simp [lift, Submodule.liftQ_apply, haZero]
      rw [hxEq]
      change bridge (⟨a, haC⟩ + ⟨b, hbC⟩) = 0
      rw [map_add, haBridge, hbBridge, zero_add]
    refine ⟨(rel n).liftQ bridge hkill, ?_⟩
    intro y z hyz
    have hyU : (y : L) ∈ U := hU y.property
    have hzU : (z : L) ∈ U := Submodule.mem_sup_left z.property
    have hEq : V.mkQ (⟨y, hyU⟩ : U) = V.mkQ (⟨z, hzU⟩ : U) := by
      change (Submodule.Quotient.mk (⟨y, hyU⟩ : U) : U ⧸ V) =
        Submodule.Quotient.mk (⟨z, hzU⟩ : U)
      rw [Submodule.Quotient.eq]
      change (y : L) - (z : L) ∈ J
      exact hyz
    have hzEq := LinearMap.quotientInfEquivSupQuotient_symm_apply_left P J
      ⟨z, hzU⟩ z.property
    change lift (quotientEquiv.symm (V.mkQ ⟨y, hyU⟩)) =
      (I ^ t • (⊤ : Submodule A H)).mkQ (S.mkQ z)
    rw [hEq]
    change lift ((LinearMap.quotientInfEquivSupQuotient P J).symm
      (Submodule.Quotient.mk ⟨z, hzU⟩)) =
        (I ^ t • (⊤ : Submodule A H)).mkQ (S.mkQ z)
    rw [hzEq]
    rfl
  let back : ∀ n, c ≤ n → Hn n →ₗ[A]
      (H ⧸ I ^ (n - c) • (⊤ : Submodule A H)) := fun n hn =>
    (backWitness n (n - c) (by omega)).val
  have hBackRep (n : ℕ) (hn : c ≤ n) (y : cycles n) (z : LinearMap.ker β)
      (hyz : (y : L) - (z : L) ∈ I ^ (n - c₁) • (⊤ : Submodule A L)) :
      back n hn (Submodule.Quotient.mk y) =
        (I ^ (n - c) • (⊤ : Submodule A H)).mkQ (S.mkQ z) :=
    (backWitness n (n - c) (by omega)).property y z hyz
  have hTo (n : ℕ) (x : LinearMap.ker β) (y : cycles n) (hxy : (y : L) = x) :
      toLevel n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
    change (rel n).mkQ ((LinearMap.ker β).inclusion (kerCycles n) x) =
      (rel n).mkQ y
    congr 1
    exact Subtype.ext hxy.symm
  have hTransition (n : ℕ) (x : cycles (n + 1)) (y : cycles n)
      (hxy : (y : L) = x) :
      transition n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
    change (rel n).mkQ (⟨x, cyclesMono n.le_succ x.property⟩ : cycles n) = (rel n).mkQ y
    congr 1
    exact Subtype.ext hxy.symm
  have hQuotTransition (n : ℕ) (x : H) :
      quotTransition n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
    simp [quotTransition, Submodule.mapQ_apply]
  have hCompat (n : ℕ) : transition n ∘ₗ toLevel (n + 1) = toLevel n := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      let y₁ : cycles (n + 1) := ⟨x, kerCycles (n + 1) x.property⟩
      let y₀ : cycles n := ⟨x, kerCycles n x.property⟩
      change transition n (toLevel (n + 1) (Submodule.Quotient.mk x)) =
        toLevel n (Submodule.Quotient.mk x)
      rw [hTo (n + 1) x y₁ rfl, hTransition n y₁ y₀ rfl, hTo n x y₀ rfl]
  have hFromApply (n : ℕ) (x : H) :
      fromQuotient n ((I ^ n • (⊤ : Submodule A H)).mkQ x) = toLevel n x := rfl
  have hFrom (n : ℕ) :
      fromQuotient n ∘ₗ (I ^ n • (⊤ : Submodule A H)).mkQ = toLevel n :=
    LinearMap.ext (hFromApply n)
  let Hsys : ℕᵒᵖ ⥤ ModuleCat A :=
    Functor.ofOpSequence (X := fun n => ModuleCat.of A (Hn n))
      (fun n => ModuleCat.ofHom (transition n))
  let Qsys : ℕᵒᵖ ⥤ ModuleCat A :=
    Functor.ofOpSequence
      (X := fun n => ModuleCat.of A (H ⧸ I ^ n • (⊤ : Submodule A H)))
      (fun n => ModuleCat.ofHom (quotTransition n))
  have tr_trans (X : ℕᵒᵖ ⥤ ModuleCat A) {a b d : ℕ}
      (hab : a ≤ b) (hbd : b ≤ d) :
      tr X (hab.trans hbd) = tr X hbd ≫ tr X hab := by
    simp only [tr, ← Functor.map_comp, ← op_comp]
    rfl
  have trHRep : ∀ {a b : ℕ} (hab : a ≤ b) (x : cycles b) (y : cycles a),
      (y : L) = x →
      (tr Hsys hab).hom (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base =>
        intro x y hxy
        have heq : x = y := Subtype.ext hxy.symm
        subst y
        have hid : tr Hsys (le_refl a) = 𝟙 _ := by simp [tr]
        rw [hid]
        simp
    | succ b hb ih =>
        intro x y hxy
        let z : cycles b := ⟨x, cyclesMono b.le_succ x.property⟩
        have hs : (tr Hsys (Nat.le_succ b)).hom (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk z := by
          have hstep : tr Hsys (Nat.le_succ b) =
              ModuleCat.ofHom (transition b) := by
            simp [Hsys, tr]
          rw [hstep]
          exact hTransition b x z rfl
        rw [tr_trans Hsys hb (Nat.le_succ b)]
        change (tr Hsys hb).hom ((tr Hsys (Nat.le_succ b)).hom
          (Submodule.Quotient.mk x)) = Submodule.Quotient.mk y
        rw [hs]
        exact ih z y hxy
  have trQRep : ∀ {a b : ℕ} (hab : a ≤ b) (x : H),
      (tr Qsys hab).hom ((I ^ b • (⊤ : Submodule A H)).mkQ x) =
        (I ^ a • (⊤ : Submodule A H)).mkQ x := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base =>
        intro x
        have hid : tr Qsys (le_refl a) = 𝟙 _ := by simp [tr]
        rw [hid]
        simp
    | succ b hb ih =>
        intro x
        have hs : (tr Qsys (Nat.le_succ b)).hom
            ((I ^ (b + 1) • (⊤ : Submodule A H)).mkQ x) =
            (I ^ b • (⊤ : Submodule A H)).mkQ x := by
          have hstep : tr Qsys (Nat.le_succ b) =
              ModuleCat.ofHom (quotTransition b) := by
            simp [Qsys, tr]
          rw [hstep]
          exact hQuotTransition b x
        rw [tr_trans Qsys hb (Nat.le_succ b)]
        change (tr Qsys hb).hom ((tr Qsys (Nat.le_succ b)).hom
          ((I ^ (b + 1) • (⊤ : Submodule A H)).mkQ x)) = _
        rw [hs]
        exact ih x
  have hBackWitnessFrom (n t : ℕ) (ht : t + c ≤ n) :
      ((backWitness n t ht).val).comp (fromQuotient n) =
        (tr Qsys (by omega : t ≤ n)).hom := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction x using Submodule.Quotient.induction_on with
      | _ z =>
        let y : cycles n := ⟨z, kerCycles n z.property⟩
        change (backWitness n t ht).val (fromQuotient n
          ((I ^ n • (⊤ : Submodule A H)).mkQ (S.mkQ z))) =
          (tr Qsys (by omega : t ≤ n)).hom
            ((I ^ n • (⊤ : Submodule A H)).mkQ (S.mkQ z))
        rw [hFromApply]
        change (backWitness n t ht).val (toLevel n (Submodule.Quotient.mk z)) =
          (tr Qsys (by omega : t ≤ n)).hom
            ((I ^ n • (⊤ : Submodule A H)).mkQ (S.mkQ z))
        rw [hTo n z y rfl, (backWitness n t ht).property y z (by
          change (z : L) - (z : L) ∈ I ^ (n - c₁) • (⊤ : Submodule A L)
          simp),
          trQRep (by omega : t ≤ n) (S.mkQ z)]
  have hBackFrom (n : ℕ) (hn : c ≤ n) :
      (back n hn).comp (fromQuotient n) =
        (tr Qsys (Nat.sub_le n c)).hom :=
    hBackWitnessFrom n (n - c) (by omega)
  have hFromBackWitness (n t : ℕ) (ht : t + c ≤ n) :
      (fromQuotient t).comp (backWitness n t ht).val =
        (tr Hsys (by omega : t ≤ n)).hom := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      have hn1 : c₁ ≤ n := by dsimp [c] at ht; omega
      obtain ⟨zz, hyz⟩ := decomp n hn1 y
      have hexp : t ≤ n - c₁ := by dsimp [c] at ht; omega
      have hyz' : (y : L) - (zz : L) ∈ I ^ t • (⊤ : Submodule A L) :=
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hexp)) hyz
      let yy : cycles t := ⟨y, cyclesMono (by omega : t ≤ n) y.property⟩
      let zc : cycles t := ⟨zz, kerCycles t zz.property⟩
      have hEq : (Submodule.Quotient.mk zc : Hn t) =
          Submodule.Quotient.mk yy := by
        rw [Submodule.Quotient.eq]
        change (zz : L) - (y : L) ∈ boundaries t
        apply Submodule.mem_sup_right
        rw [show (zz : L) - (y : L) = -((y : L) - zz) by abel]
        exact (I ^ t • (⊤ : Submodule A L)).neg_mem hyz'
      change fromQuotient t ((backWitness n t ht).val (Submodule.Quotient.mk y)) =
        (tr Hsys (by omega : t ≤ n)).hom (Submodule.Quotient.mk y)
      rw [(backWitness n t ht).property y zz hyz]
      rw [hFromApply]
      change toLevel t (Submodule.Quotient.mk zz) =
        (tr Hsys (by omega : t ≤ n)).hom (Submodule.Quotient.mk y)
      rw [hTo t zz zc rfl, trHRep (by omega : t ≤ n) y yy rfl]
      exact hEq
  have hFromBack (n : ℕ) (hn : c ≤ n) :
      (fromQuotient (n - c)).comp (back n hn) =
        (tr Hsys (Nat.sub_le n c)).hom :=
    hFromBackWitness n (n - c) (by omega)
  have hToNat : ∀ {a b : ℕ} (hab : a ≤ b),
      (tr Hsys hab).hom.comp (toLevel b) = toLevel a := by
    intro a b hab
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
      let zb : cycles b := ⟨z, kerCycles b z.property⟩
      let za : cycles a := ⟨z, kerCycles a z.property⟩
      change (tr Hsys hab).hom (toLevel b (Submodule.Quotient.mk z)) =
        toLevel a (Submodule.Quotient.mk z)
      rw [hTo b z zb rfl, trHRep hab zb za rfl, hTo a z za rfl]
  have hFromNat : ∀ {a b : ℕ} (hab : a ≤ b),
      (tr Hsys hab).hom.comp (fromQuotient b) =
        (fromQuotient a).comp (tr Qsys hab).hom := by
    intro a b hab
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (tr Hsys hab).hom
        (fromQuotient b ((I ^ b • (⊤ : Submodule A H)).mkQ x)) =
        fromQuotient a ((tr Qsys hab).hom
          ((I ^ b • (⊤ : Submodule A H)).mkQ x))
      rw [hFromApply, trQRep hab x, hFromApply]
      exact LinearMap.congr_fun (hToNat hab) x
  have hBackWitnessNat : ∀ {a b s t : ℕ} (hab : a ≤ b) (hst : s ≤ t)
      (ha : s + c ≤ a) (hb : t + c ≤ b),
      ((backWitness a s ha).val).comp (tr Hsys hab).hom =
        (tr Qsys hst).hom.comp (backWitness b t hb).val := by
    intro a b s t hab hst ha hb
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      have hb1 : c₁ ≤ b := by dsimp [c] at hb; omega
      obtain ⟨zz, hyz⟩ := decomp b hb1 y
      have hpow : a - c₁ ≤ b - c₁ := Nat.sub_le_sub_right hab c₁
      have hyzA : (y : L) - (zz : L) ∈ I ^ (a - c₁) • (⊤ : Submodule A L) :=
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hpow)) hyz
      let ya : cycles a := ⟨y, cyclesMono hab y.property⟩
      change (backWitness a s ha).val ((tr Hsys hab).hom (Submodule.Quotient.mk y)) =
        (tr Qsys hst).hom ((backWitness b t hb).val (Submodule.Quotient.mk y))
      rw [trHRep hab y ya rfl, (backWitness a s ha).property ya zz hyzA,
        (backWitness b t hb).property y zz hyz, trQRep hst (S.mkQ zz)]
  let backShift (n : ℕ) : Hn (n + c) →ₗ[A]
      (H ⧸ I ^ n • (⊤ : Submodule A H)) :=
    (backWitness (n + c) n (by omega)).val
  have hPro : Nonempty (ProIso Hsys Qsys) := by
    refine ⟨{
      α := fun n => n + c
      β := id
      αmono := fun a b hab => Nat.add_le_add_right hab c
      βmono := monotone_id
      αle := fun n => Nat.le_add_right n c
      βle := fun n => le_refl n
      φ := fun n => ModuleCat.ofHom (backShift n)
      ψ := fun n => ModuleCat.ofHom (fromQuotient n)
      φnat := ?_
      ψnat := ?_
      ψφ := ?_
      φψ := ?_ }⟩
    · intro m m' h
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, backShift] using
        hBackWitnessNat (Nat.add_le_add_right h c) h (by omega) (by omega)
    · intro m m' h
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using (hFromNat h).symm
    · intro m
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, backShift, id_eq] using
        hFromBackWitness (m + c) m (by omega)
    · intro m
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, backShift] using
        hBackWitnessFrom (m + c) m (by omega)
  have hFromRange (n : ℕ) : LinearMap.range (fromQuotient n) =
      LinearMap.range (toLevel n) := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨y, rfl⟩
      rcases Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule A H)) y with
        ⟨z, rfl⟩
      exact ⟨z, (LinearMap.congr_fun (hFrom n) z).symm⟩
    · intro x hx
      rcases hx with ⟨y, rfl⟩
      exact ⟨(I ^ n • (⊤ : Submodule A H)).mkQ y,
        LinearMap.congr_fun (hFrom n) y⟩
  have hRange (n : ℕ) :
      LinearMap.range (tr Hsys (Nat.le_add_right n c)).hom =
        LinearMap.range (toLevel n) := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨y, rfl⟩
      have he := LinearMap.congr_fun (hFromBackWitness (n + c) n (by omega)) y
      rw [LinearMap.comp_apply] at he
      rw [← hFromRange n]
      exact ⟨backShift n y, he⟩
    · intro x hx
      rcases hx with ⟨y, rfl⟩
      have he := LinearMap.congr_fun (hToNat (Nat.le_add_right n c)) y
      rw [LinearMap.comp_apply] at he
      exact ⟨toLevel (n + c) y, he⟩
  have hML : (Hsys ⋙ forget (ModuleCat A)).IsMittagLeffler := by
    intro j
    let n : ℕ := unop j
    refine ⟨op (n + c), (homOfLE (Nat.le_add_right n c)).op, ?_⟩
    intro k g x hx
    have hx' : x ∈ LinearMap.range (tr Hsys (Nat.le_add_right n c)).hom := by
      rcases hx with ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    rw [hRange n] at hx'
    rcases hx' with ⟨z, hz⟩
    have hnk : n ≤ unop k := leOfHom g.unop
    obtain rfl : g = (homOfLE hnk).op := Subsingleton.elim _ _
    refine ⟨toLevel (unop k) z, ?_⟩
    change (tr Hsys hnk).hom (toLevel (unop k) z) = x
    exact (LinearMap.congr_fun (hToNat hnk) z).trans hz
  have hMulRange (n : ℕ) (a : A) (ha : a ∈ I ^ c) (x : Hn n) :
      a • x ∈ LinearMap.range (fromQuotient n) := by
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      have hay : (a • y : L) ∈ cycles (n + c) := by
        change β (a • (y : L)) ∈ I ^ (n + c) • (⊤ : Submodule A M)
        rw [map_smul]
        have hh : a • β (y : L) ∈ I ^ c • (I ^ n • (⊤ : Submodule A M)) :=
          Submodule.smul_mem_smul ha y.property
        simpa [← mul_smul, ← pow_add, add_comm] using hh
      let ay : cycles (n + c) := ⟨a • y, hay⟩
      let ay0 : cycles n := a • y
      have heq : (tr Hsys (Nat.le_add_right n c)).hom (Submodule.Quotient.mk ay) =
          a • (Submodule.Quotient.mk y : Hn n) := by
        rw [trHRep (Nat.le_add_right n c) ay ay0 rfl]
        change (rel n).mkQ (a • y) = a • (rel n).mkQ y
        exact map_smul (rel n).mkQ a y
      rw [hFromRange n, ← hRange n]
      exact ⟨Submodule.Quotient.mk ay, heq⟩
  have hAnnKernel (n : ℕ) :
      I ^ c ≤ Module.annihilator A (LinearMap.ker (fromQuotient n)) := by
    intro a ha
    apply Module.mem_annihilator.mpr
    intro x
    have hxzero : fromQuotient n (x : H ⧸ I ^ n • (⊤ : Submodule A H)) = 0 :=
      LinearMap.mem_ker.mp x.property
    rcases Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule A H)) x.val with
      ⟨z, hz⟩
    have hmul : a • z ∈ I ^ n • (⊤ : Submodule A H) := by
      by_cases hn : c ≤ n
      · have hzero : (tr Qsys (Nat.sub_le n c)).hom
            ((I ^ n • (⊤ : Submodule A H)).mkQ z) = 0 := by
          change (tr Qsys (Nat.sub_le n c)).hom
            (Submodule.Quotient.mk z) = 0
          rw [hz]
          have hh := LinearMap.congr_fun (hBackFrom n hn) x.val
          rw [LinearMap.comp_apply, hxzero, map_zero] at hh
          exact hh.symm
        rw [trQRep (Nat.sub_le n c) z] at hzero
        have hz' : z ∈ I ^ (n - c) • (⊤ : Submodule A H) :=
          (Submodule.Quotient.mk_eq_zero _).mp hzero
        have hh : a • z ∈ I ^ c • (I ^ (n - c) • (⊤ : Submodule A H)) :=
          Submodule.smul_mem_smul ha hz'
        have he : c + (n - c) = n := by omega
        simpa [← mul_smul, ← pow_add, he] using hh
      · have hsmall : I ^ c • (⊤ : Submodule A H) ≤
            I ^ n • (⊤ : Submodule A H) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        exact hsmall (Submodule.smul_mem_smul ha Submodule.mem_top)
    apply Subtype.ext
    change a • (x : H ⧸ I ^ n • (⊤ : Submodule A H)) = 0
    rw [← hz]
    change (I ^ n • (⊤ : Submodule A H)).mkQ (a • z) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hmul
  have hAnnCoker (n : ℕ) :
      I ^ c ≤ Module.annihilator A
        (Hn n ⧸ LinearMap.range (fromQuotient n)) := by
    intro a ha
    apply Module.mem_annihilator.mpr
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (LinearMap.range (fromQuotient n)).mkQ (a • x) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hMulRange n a ha x)
  let toLevelQuotient : ∀ n k,
      (H ⧸ I ^ k • (⊤ : Submodule A H)) →ₗ[A]
        (Hn n ⧸ I ^ k • (⊤ : Submodule A (Hn n))) := fun n k =>
    (I ^ k • (⊤ : Submodule A H)).liftQ
      ((I ^ k • (⊤ : Submodule A (Hn n))).mkQ.comp (toLevel n)) (by
        intro x hx
        apply (Submodule.Quotient.mk_eq_zero _).2
        exact (Submodule.smul_top_le_comap_smul_top (I ^ k) (toLevel n)) hx)
  have hToLevelQuotient (n k : ℕ) :
      (toLevelQuotient n k).comp (I ^ k • (⊤ : Submodule A H)).mkQ =
        (I ^ k • (⊤ : Submodule A (Hn n))).mkQ.comp (toLevel n) := by
    apply LinearMap.ext
    intro x
    rfl
  have hIcRange (n : ℕ) : I ^ c • (⊤ : Submodule A (Hn n)) ≤
      LinearMap.range (fromQuotient n) := by
    apply Submodule.smul_le.mpr
    intro a ha x _
    exact hMulRange n a ha x
  have hQuotientOnMultiples (n : ℕ) (hn : c ≤ n) (x : Hn n)
      (hx : x ∈ I ^ c • (⊤ : Submodule A (Hn n))) :
      toLevelQuotient n (n - c) (back n hn x) =
        (I ^ (n - c) • (⊤ : Submodule A (Hn n))).mkQ x := by
    rcases hIcRange n hx with ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | _ z =>
      have he : back n hn
          (fromQuotient n ((I ^ n • (⊤ : Submodule A H)).mkQ z)) =
          (I ^ (n - c) • (⊤ : Submodule A H)).mkQ z :=
        (LinearMap.congr_fun (hBackFrom n hn)
          ((I ^ n • (⊤ : Submodule A H)).mkQ z)).trans
          (trQRep (Nat.sub_le n c) z)
      change toLevelQuotient n (n - c)
          (back n hn (fromQuotient n ((I ^ n • (⊤ : Submodule A H)).mkQ z))) =
        (I ^ (n - c) • (⊤ : Submodule A (Hn n))).mkQ
          (fromQuotient n ((I ^ n • (⊤ : Submodule A H)).mkQ z))
      rw [he]
      change toLevelQuotient n (n - c)
          ((I ^ (n - c) • (⊤ : Submodule A H)).mkQ z) =
        (I ^ (n - c) • (⊤ : Submodule A (Hn n))).mkQ (toLevel n z)
      rfl
  have hLimit : Nonempty (limit Hsys ≅ limit Qsys) :=
    ⟨limitIsoOfProIso Hsys Qsys hPro.some⟩
  refine ⟨toLevel, transition, quotTransition, fromQuotient,
    hTo, hTransition, hQuotTransition, hCompat, hFrom, c, hcpos, back,
    hBackFrom, hFromBack, hPro, hLimit, hML, hRange,
    ⟨toLevelQuotient, hToLevelQuotient, hQuotientOnMultiples⟩,
    fun n => ⟨hAnnKernel n, hAnnCoker n⟩⟩

end Stacks.AdicSystem.ArtinReesHomology

end

end

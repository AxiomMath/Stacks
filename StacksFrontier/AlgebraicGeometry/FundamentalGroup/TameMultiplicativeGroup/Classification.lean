module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.ClassificationLevel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.TowerIntegralClosure

/-!
# Points of tame covers of `𝐆_m` factor through the Kummer tower

Let `C` be a finite formally unramified `k[x]_x`-algebra, tame at `0` and `∞`, and `ψ : C → Ω`
a point over the geometric generic point. Then `ψ(C)` lies in the image of the base point
`k₀^{(m)} : 𝔽_{m!}[X]_X → Ω`, `X ↦ t_m`, for some `m`.

At a layer `m` where the cover is unramified over `𝐏¹` (`exists_level_forall_isUnramifiedAt`),
`N = F(t_m)(ψ(C))` is spanned over `F(t_m)` by its constants, which are finitely many elements of
`Ω` algebraic over `k`, hence lie in `𝔽_{m'!}` for some `m' ≥ m`. So `ψ(C) ⊆ 𝔽_{m'!}(t_{m'})`
(`t_m` is a power of `t_{m'}`). Every `ψ(c)` is integral over the image of `k[x]_x`, which lies in
that of `k₀^{(m')}`, and this image is integrally closed in `𝔽_{m'!}(t_{m'})`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.exists_forall_mem_range_towerPoint`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial IntermediateField

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

attribute [local instance 20000] integralClosureAlgebraOfBase

variable (k : Type u) [Field k] [Fintype k]

/-- **An element of `Ω` algebraic over `k` lies in some `𝔽_d`.** -/
theorem exists_mem_frobField_of_isIntegral {a : Omega k} (ha : _root_.IsIntegral k a) :
    ∃ d, d ≠ 0 ∧ a ∈ frobField k d := by
  classical
  have : FiniteDimensional k k⟮a⟯ := IntermediateField.adjoin.finiteDimensional ha
  have : Finite k⟮a⟯ := Module.finite_of_finite k
  let : Fintype k⟮a⟯ := Fintype.ofFinite _
  refine ⟨Module.finrank k k⟮a⟯, Module.finrank_pos.ne', ?_⟩
  rw [mem_frobField, ← Module.card_eq_pow_finrank (K := k) (V := k⟮a⟯)]
  have h := congrArg (fun z : k⟮a⟯ ↦ (z : Omega k)) (FiniteField.pow_card (AdjoinSimple.gen k a))
  simpa only [SubmonoidClass.coe_pow, AdjoinSimple.coe_gen] using h

/-- **Finitely many algebraic elements lie in a layer of the tower.** -/
theorem exists_le_forall_mem_towerField (S : Finset (Omega k)) (hS : ∀ a ∈ S, _root_.IsIntegral k a)
    (m : ℕ) : ∃ m', m ≤ m' ∧ ∀ a ∈ S, a ∈ towerField k m' := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨m, le_rfl, fun a ha ↦ absurd ha (Finset.notMem_empty a)⟩
  | @insert a S _ ih =>
    obtain ⟨m₁, hm₁, h₁⟩ := ih fun b hb ↦ hS b (Finset.mem_insert_of_mem hb)
    obtain ⟨d, hd, had⟩ := exists_mem_frobField_of_isIntegral k (hS a (Finset.mem_insert_self a S))
    refine ⟨max m₁ d, hm₁.trans (le_max_left _ _), fun b hb ↦ ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact frobField_mono k ((Nat.dvd_factorial (Nat.pos_of_ne_zero hd) le_rfl).trans
        (Nat.factorial_dvd_factorial (le_max_right _ _))) had
    · exact frobField_mono k (Nat.factorial_dvd_factorial (le_max_left _ _)) (h₁ b hb)

/-- For `m ≤ m'`, the generator `t_m` is a power of `t_{m'}`. -/
theorem exists_towerRoot_pow_eq {m m' : ℕ} (h : m ≤ m') :
    ∃ r, towerRoot k m' ^ r = towerRoot k m := by
  induction h with
  | refl => exact ⟨1, pow_one _⟩
  | step _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨towerRatio k _ * r, by rw [pow_mul, towerRoot_succ_pow, hr]⟩

/-- `𝔽_{m!}(t_m) ⊆ 𝔽_{m'!}(t_{m'})` for `m ≤ m'`. -/
theorem mem_levelField_of_le {m m' : ℕ} (h : m ≤ m') {z : Omega k} (hz : z ∈ levelField k m) :
    z ∈ levelField k m' := by
  have hle : (levelField k m).restrictScalars k ≤ (levelField k m').restrictScalars k := by
    rw [IntermediateField.restrictScalars_adjoin]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x (hx | hx)
    · exact (levelField k m').algebraMap_mem
        ⟨x, frobField_mono k (Nat.factorial_dvd_factorial h) hx⟩
    · rw [Set.mem_singleton_iff.mp hx]
      obtain ⟨r, hr⟩ := exists_towerRoot_pow_eq k h
      rw [← hr]
      change towerRoot k m' ^ r ∈ levelField k m'
      exact pow_mem (IntermediateField.mem_adjoin_simple_self (towerField k m') (towerRoot k m')) r
  exact hle hz

section Cover

variable {k} {C : Type u} [CommRing C] (φ : Ring k →+* C) (hfin : φ.Finite)
  (hfu : φ.FormallyUnramified) (ψ : C →+* Omega k) (hψ : ψ.comp φ = baseHom k)

include hfin hψ in
/-- **A point of a cover in `𝔽_{m!}(t_m)` comes from the `m`-th base point.** If `ψ c` lies in
`levelField k m`, then it lies in the range of `towerPoint k m`. -/
theorem mem_range_towerPoint_of_mem_levelField (m : ℕ) (c : C) (hc : ψ c ∈ levelField k m) :
    ψ c ∈ (towerPoint k m).range := by
  refine mem_range_towerPoint_of_isIntegralElem k m hc ?_
  obtain ⟨p, hp, hpc⟩ := hfin.to_isIntegral c
  refine ⟨p.map (kummerMap k (towerField k m) (towerN k m)), hp.map _, ?_⟩
  rw [eval₂_map, towerPoint_comp_kummerMap, ← hψ, ← Polynomial.hom_eval₂, hpc, map_zero]

/-- The structure map `k[x]_x → F(t_m)` of the `m`-th layer. -/
def levelHom (m : ℕ) : Ring k →+* levelField k m :=
  (towerPointAdjoin k m).comp (kummerMap k (towerField k m) (towerN k m))

include hψ in
/-- The image of `z ∈ k[x]_x` under `levelHom m`, viewed in `Ω`, is `ψ (φ z)`. -/
theorem algebraMap_levelHom (m : ℕ) (z : Ring k) :
    algebraMap (levelField k m) (Omega k) (levelHom m z) = ψ (φ z) :=
  (towerPoint_kummerMap k m z).trans (RingHom.congr_fun hψ z).symm

/-- The constants of the field of a point are algebraic over `k`. -/
theorem isIntegral_of_mem_constants (m : ℕ)
    (x : integralClosure (towerField k m) (coverField k m ψ)) :
    _root_.IsIntegral k ((x : coverField k m ψ) : Omega k) := by
  have h1 : _root_.IsIntegral (towerField k m) (x : coverField k m ψ) := x.2
  have : IsScalarTower (towerField k m) (coverField k m ψ) (Omega k) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h2 : _root_.IsIntegral (towerField k m) ((x : coverField k m ψ) : Omega k) :=
    h1.map (IsScalarTower.toAlgHom (towerField k m) (coverField k m ψ) (Omega k))
  exact isIntegral_trans (R := k) _ h2

include hfin hfu hψ in
/-- **At an unramified layer, a point lies in a layer of the function fields.** -/
theorem exists_forall_mem_levelField (m : ℕ)
    (H₀ : ∀ (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {levelGen k m})
        (coverField k m ψ))) [P.IsPrime],
        Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {levelGen k m}) P)
    (H₁ : ∀ (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
        (coverField k m ψ))) [P.IsPrime],
        Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹}) P) :
    ∃ m', m ≤ m' ∧ ∀ c, ψ c ∈ levelField k m' := by
  classical
  obtain ⟨hfd, hsep, -⟩ :=
    cover_adjoin_facts φ ψ hfin hfu (levelHom m) (algebraMap_levelHom φ ψ hψ m)
  have : FiniteDimensional (levelField k m) (coverField k m ψ) := hfd
  have : Algebra.IsSeparable (levelField k m) (coverField k m ψ) := hsep
  have hspan := span_integralClosure_eq_top_of_forall_isUnramifiedAt (F := towerField k m)
    (K := levelField k m) (N := coverField k m ψ) (transcendental_levelGen k m) H₀ H₁
  have : FiniteDimensional (towerField k m) (integralClosure (towerField k m) (coverField k m ψ)) :=
    (finite_integralClosure (transcendental_levelGen k m) (N := coverField k m ψ)).1
  have : Finite (integralClosure (towerField k m) (coverField k m ψ)) :=
    Module.finite_of_finite (towerField k m)
  let := Fintype.ofFinite (integralClosure (towerField k m) (coverField k m ψ))
  obtain ⟨m', hm', hE⟩ := exists_le_forall_mem_towerField k
    (Finset.univ.image fun x : integralClosure (towerField k m) (coverField k m ψ) ↦
      ((x : coverField k m ψ) : Omega k)) (by
        intro a ha
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
        exact isIntegral_of_mem_constants ψ m x) m
  refine ⟨m', hm', fun c ↦ ?_⟩
  have hc : (⟨ψ c, IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩⟩ : coverField k m ψ) ∈
      Submodule.span (levelField k m)
        (integralClosure (towerField k m) (coverField k m ψ) : Set (coverField k m ψ)) :=
    hspan ▸ Submodule.mem_top
  refine Submodule.span_induction
    (p := fun (x : coverField k m ψ) _ ↦ ((x : coverField k m ψ) : Omega k) ∈ levelField k m')
    (fun x hx ↦ ?_) ?_ (fun _ _ _ _ ha hb ↦ ?_) (fun a x _ hx ↦ ?_) hc
  · exact (levelField k m').algebraMap_mem ⟨_, hE _ (Finset.mem_image.mpr
      ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩)⟩
  · exact zero_mem _
  · exact add_mem ha hb
  · rw [IntermediateField.coe_smul, Algebra.smul_def]
    exact mul_mem (mem_levelField_of_le k hm' a.2) hx

include hfin hfu hψ in
/-- **Classification of tame covers of `𝐆_m` (ring form).** For a finite formally unramified
`k[x]_x`-algebra `C`, tamely ramified at `0` and at `∞`, every point `ψ : C → Ω` over the geometric
generic point factors through the base point `k₀^{(m)}` of a layer of the Kummer tower. -/
theorem exists_forall_mem_range_towerPoint
    (h₀ : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartZero k)
      (Spec.map (CommRingCat.ofHom φ)))
    (h₁ : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartInfty k)
      (Spec.map (CommRingCat.ofHom φ))) :
    ∃ m, ∀ c, ψ c ∈ (towerPoint k m).range := by
  obtain ⟨m, H₀, H₁⟩ := exists_level_forall_isUnramifiedAt φ hfin hfu ψ hψ h₀ h₁
  obtain ⟨m', -, H⟩ := exists_forall_mem_levelField φ hfin hfu ψ hψ m H₀ H₁
  exact ⟨m', fun c ↦ mem_range_towerPoint_of_mem_levelField φ hfin ψ hψ m' c (H c)⟩

end Cover

end AlgebraicGeometry.TameMultiplicativeGroup

end

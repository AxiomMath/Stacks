module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitAlgebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# The liftable elements form a closed subring

This continues `AlgebraicGeometry.Artin.StageLift` (the ring skeleton of the "algebra" paragraphs
of the proof of Stacks 0GI5). The elements of `B` liftable at a stage `k` are those `b` for which
`(φ b, ψ_k b)` lies in the image of `Â_k ⟶ Â × Ĉ_k`. The source argues with topological generators
`b_1, …, b_n` of `B` over the base ring `R` (Stacks 0GC6): once the generators lift, so does all of
`B`. The reason is that the image of `Â_k ⟶ Â × Ĉ_k` is closed. This uses three facts: the
Artin–Rees lemma for `Â_k ⟶ Ĉ_k`, the kernel of `Â ⟶ Ĉ` meeting a level of the filtration of `Â`
in zero, and the completeness of `Â_k`.

Here the filtrations of `Â` and `Ĉ_k` are arbitrary decreasing sequences of ideals. In the source
they are the `I`-adic filtration of `Â` and the kernels of `Ĉ_k ⟶ H⁰(V'_k ×_{V_k} Z_{k,n}, 𝒪)`.

## Main results

* `AlgebraicGeometry.Artin.StageLift.isGoodAt_of_approx`: an element approximated to every
  order by liftable data is liftable.
* `AlgebraicGeometry.Artin.StageLift.isGoodAt_of_dense`: if a dense subring is liftable at a
  stage, so is everything.
* `AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom`: the lift `B ⟶ Â_k` at a
  stage, continuous, and equal to the image of every liftable witness of the stage before.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory Opposite Topology

universe v w

namespace AlgebraicGeometry.Artin.StageLift

variable {K : Type*} [Category K]
  {Ah Ch : Kᵒᵖ ⥤ CommRingCat.{v}} (α : Ah ⟶ Ch)
  {Al Cl : CommRingCat.{v}} (αl : Al ⟶ Cl)
  (ρA : ∀ k : K, Ah.obj (op k) ⟶ Al) (ρC : ∀ k : K, Ch.obj (op k) ⟶ Cl)
  (hρA : ∀ {k k' : K} (g : k' ⟶ k), Ah.map g.op ≫ ρA k' = ρA k)
  (hρC : ∀ {k k' : K} (g : k' ⟶ k), Ch.map g.op ≫ ρC k' = ρC k)
  {B : Type w} [CommRing B] (φ : B →+* Al) {k₀ : K} (ψ : B →+* Ch.obj (op k₀))
  (IA : ∀ k : K, Ideal (Ah.obj (op k))) (FA : ℕ → Ideal Al)
  (FC : ∀ k : K, ℕ → Ideal (Ch.obj (op k)))

/-- Congruence modulo the submodule `I ^ n • ⊤` of `R` is equivalent to `x - y ∈ I ^ n`. -/
theorem smodEq_pow_iff {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/-- If `g x_n - t ∈ F (n + c)` for a decreasing filtration `F`, then so is `g (x_{n+1} - x_n)`. -/
private theorem map_sub_succ_mem {R X : Type*} [CommRing R] [CommRing X] (g : R →+* X)
    (F : ℕ → Ideal X) (hF : Antitone F) (t : X) (c : ℕ) (x : ℕ → R)
    (hx : ∀ n, g (x n) - t ∈ F (n + c)) (n : ℕ) : g (x (n + 1) - x n) ∈ F (n + c) := by
  have := (F (n + c)).sub_mem (hF (by omega : n + c ≤ n + 1 + c) (hx (n + 1))) (hx n)
  rwa [sub_sub_sub_cancel_right, ← map_sub] at this

/-- If `L` is the limit of `z_n` and `z_n - x_n` is killed by `g`, `g x_n - t` lies in `F (n + c)`
and `g` sends `I ^ n` into `F n`, then `g L = t` for a separated filtration `F`. -/
private theorem map_limit_eq {R X : Type*} [CommRing R] [CommRing X] (g : R →+* X)
    (F : ℕ → Ideal X) (hsep : ∀ y : X, (∀ n, y ∈ F n) → y = 0) (hF : Antitone F) (I : Ideal R)
    (hgI : ∀ n, ∀ x ∈ I ^ n, g x ∈ F n) (c : ℕ) (L : R) (z x : ℕ → R) (t : X)
    (hLz : ∀ n, L - z n ∈ I ^ n) (hz : ∀ n, g (z n - x n) = 0)
    (hx : ∀ n, g (x n) - t ∈ F (n + c)) : g L = t := by
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  have e : g L - t = g (L - z n) + g (z n - x n) + (g (x n) - t) := by
    simp only [map_sub]
    ring
  rw [e, hz n, add_zero]
  exact (F n).add_mem (hgI n _ (hLz n)) (hF (by omega : n ≤ n + c) (hx n))

/-- **The liftable elements form a closed set.** Suppose `Â_k` is `I_k`-precomplete, the
filtrations of `Â` and `Ĉ_k` are separated and decreasing and receive the powers of `I_k`, and the
Artin–Rees condition `hAR` holds. If `b` is approximated to every order by liftable data, then
`b` is liftable at `f`. -/
theorem isGoodAt_of_approx {k : K} (f : k ⟶ k₀) (b : B)
    (hpre : IsPrecomplete (IA k) (Ah.obj (op k)))
    (hsepA : ∀ y : Al, (∀ n, y ∈ FA n) → y = 0)
    (hsepC : ∀ y : Ch.obj (op k), (∀ n, y ∈ FC k n) → y = 0)
    (hFA : Antitone FA) (hFC : Antitone (FC k))
    (hρI : ∀ n, ∀ x ∈ IA k ^ n, (ρA k).hom x ∈ FA n)
    (hαI : ∀ n, ∀ x ∈ IA k ^ n, (α.app (op k)).hom x ∈ FC k n)
    (hAR : ∃ c : ℕ, ∀ (n : ℕ) (x : Ah.obj (op k)), (α.app (op k)).hom x ∈ FC k (n + c) →
      (ρA k).hom x ∈ FA (n + c) →
        ∃ y ∈ IA k ^ n, (α.app (op k)).hom (x - y) = 0 ∧ (ρA k).hom (x - y) = 0)
    (happrox : ∀ n : ℕ, ∃ x : Ah.obj (op k), (ρA k).hom x - φ b ∈ FA n ∧
      (α.app (op k)).hom x - (Ch.map f.op).hom (ψ b) ∈ FC k n) :
    IsGoodAt α ρA φ ψ f b := by
  obtain ⟨c, hc⟩ := hAR
  choose x hxA hxC using fun n => happrox (n + c)
  have step : ∀ n, ∃ y ∈ IA k ^ n,
      (α.app (op k)).hom (x (n + 1) - x n - y) = 0 ∧ (ρA k).hom (x (n + 1) - x n - y) = 0 := by
    intro n
    exact hc n _ (map_sub_succ_mem _ _ hFC _ c x hxC n) (map_sub_succ_mem _ _ hFA _ c x hxA n)
  choose y hy hyα hyρ using step
  let z : ℕ → Ah.obj (op k) := fun n => x 0 + ∑ i ∈ Finset.range n, y i
  have hz : ∀ n, (α.app (op k)).hom (z n - x n) = 0 ∧ (ρA k).hom (z n - x n) = 0 := by
    intro n
    induction n with
    | zero => simp [z]
    | succ n ih =>
      have e : z (n + 1) - x (n + 1) = (z n - x n) - (x (n + 1) - x n - y n) := by
        simp only [z, Finset.sum_range_succ]
        ring
      rw [e, map_sub (α.app (op k)).hom, map_sub (ρA k).hom, ih.1, ih.2, hyα, hyρ, sub_zero]
      simp
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      z m ≡ z n [SMOD (IA k ^ m • ⊤ : Submodule (Ah.obj (op k)) (Ah.obj (op k)))] := by
    intro m n hmn
    rw [smodEq_pow_iff]
    have e : z m - z n = -∑ i ∈ Finset.Ico m n, y i := by
      simp only [z]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      ring
    rw [e]
    exact (Ideal.neg_mem_iff _).2 (Submodule.sum_mem _ fun i hi =>
      Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hy i))
  obtain ⟨L, hL⟩ := hpre.prec' z hcauchy
  have hLz : ∀ n, L - z n ∈ IA k ^ n := fun n => (smodEq_pow_iff _ _ _ _).1 (hL n).symm
  exact ⟨L, map_limit_eq _ FA hsepA hFA (IA k) hρI c L z x _ hLz (fun n => (hz n).2) hxA,
    map_limit_eq _ (FC k) hsepC hFC (IA k) hαI c L z x _ hLz (fun n => (hz n).1) hxC⟩

/-- **If a dense subring is liftable at a stage, so is all of `B`.** Here `φ` and `ψ` are
continuous for the filtrations, and the filtration of `Ĉ_{k₀}` maps into that of `Ĉ_k`. -/
theorem isGoodAt_of_dense [TopologicalSpace B] [IsTopologicalRing B] {k : K} (f : k ⟶ k₀)
    (hpre : IsPrecomplete (IA k) (Ah.obj (op k)))
    (hsepA : ∀ y : Al, (∀ n, y ∈ FA n) → y = 0)
    (hsepC : ∀ y : Ch.obj (op k), (∀ n, y ∈ FC k n) → y = 0)
    (hFA : Antitone FA) (hFC : Antitone (FC k))
    (hρI : ∀ n, ∀ x ∈ IA k ^ n, (ρA k).hom x ∈ FA n)
    (hαI : ∀ n, ∀ x ∈ IA k ^ n, (α.app (op k)).hom x ∈ FC k n)
    (hAR : ∃ c : ℕ, ∀ (n : ℕ) (x : Ah.obj (op k)), (α.app (op k)).hom x ∈ FC k (n + c) →
      (ρA k).hom x ∈ FA (n + c) →
        ∃ y ∈ IA k ^ n, (α.app (op k)).hom (x - y) = 0 ∧ (ρA k).hom (x - y) = 0)
    (hφc : ∀ n, (φ ⁻¹' (FA n : Set Al)) ∈ 𝓝 (0 : B))
    (hψc : ∀ n, (ψ ⁻¹' (FC k₀ n : Set (Ch.obj (op k₀)))) ∈ 𝓝 (0 : B))
    (hmapC : ∀ n, ∀ y ∈ FC k₀ n, (Ch.map f.op).hom y ∈ FC k n)
    (R₀ : Subring B) (hdense : Dense (R₀ : Set B)) (hgood : ∀ b ∈ R₀, IsGoodAt α ρA φ ψ f b)
    (b : B) : IsGoodAt α ρA φ ψ f b := by
  refine isGoodAt_of_approx α ρA φ ψ IA FA FC f b hpre hsepA hsepC hFA hFC hρI hαI hAR
    fun n => ?_
  have hU : (fun y : B => y - b) ⁻¹' (φ ⁻¹' (FA n : Set Al) ∩ ψ ⁻¹' (FC k₀ n : Set _)) ∈ 𝓝 b := by
    have h0 : (φ ⁻¹' (FA n : Set Al) ∩ ψ ⁻¹' (FC k₀ n : Set _)) ∈ 𝓝 ((fun y : B => y - b) b) := by
      simp only [sub_self]
      exact Filter.inter_mem (hφc n) (hψc n)
    exact (continuous_id.sub continuous_const).continuousAt h0
  obtain ⟨b', hb', hb'R⟩ := hdense.inter_open_nonempty _ isOpen_interior
    ⟨b, mem_interior_iff_mem_nhds.2 hU⟩
  obtain ⟨hb'₁, hb'₂⟩ := interior_subset hb'
  obtain ⟨x, hx₁, hx₂⟩ := hgood b' hb'R
  refine ⟨x, ?_, ?_⟩
  · rw [hx₁, ← map_sub]
    exact hb'₁
  · rw [hx₂, ← map_sub, ← map_sub]
    exact hmapC n _ hb'₂

variable [IsCofiltered K]

include hρA hρC in
/-- **The continuous lift at a stage** (the "final algebra arguments" of the proof of Stacks 0GI5,
in the form of `AlgebraicGeometry.Artin.StageLift.exists_stage_ringHom` with its finiteness input
replaced by topological generators). Suppose, besides the inputs `hcoker`, `hker`, `hL` of
`exists_stage_ringHom`, that the closedness hypotheses of `isGoodAt_of_approx` hold at every
stage, that `φ` and `ψ` are continuous for the filtrations, and that `B` is topologically generated
by a finite set `s` over a subring `R₀` liftable at every stage. Then there are stages
`g : k ⟶ k₂ ⟶ k₀` and a ring map `φ_k : B ⟶ Â_k` lifting `φ` and `ψ`, continuous for the
`I_k`-adic filtration, and equal to the image of every liftable witness at `k₂`. -/
theorem exists_stage_continuous_ringHom [TopologicalSpace B] [IsTopologicalRing B]
    (hρ : ∀ {k : K} (x : Ah.obj (op k)),
      αl.hom ((ρA k).hom x) = (ρC k).hom ((α.app (op k)).hom x))
    (hφψ : ∀ b, αl.hom (φ b) = (ρC k₀).hom (ψ b))
    (hcoker : ∃ (k₁ : K) (f₁ : k₁ ⟶ k₀), ∀ c : Ch.obj (op k₀),
      (ρC k₀).hom c ∈ αl.hom.range →
        (Ch.map f₁.op).hom c ∈ (α.app (op k₁)).hom.range)
    (hker : ∀ y : Al, αl.hom y = 0 →
      ∃ (k : K) (z : Ah.obj (op k)), (α.app (op k)).hom z = 0 ∧ (ρA k).hom z = y)
    (hL : ∀ {k : K}, ∃ (k' : K) (g : k' ⟶ k), ∀ x : Ah.obj (op k),
      (α.app (op k)).hom x = 0 → (ρA k).hom x = 0 → (Ah.map g.op).hom x = 0)
    (hpre : ∀ k, IsPrecomplete (IA k) (Ah.obj (op k)))
    (hsepA : ∀ y : Al, (∀ n, y ∈ FA n) → y = 0)
    (hsepC : ∀ k, ∀ y : Ch.obj (op k), (∀ n, y ∈ FC k n) → y = 0)
    (hFA : Antitone FA) (hFC : ∀ k, Antitone (FC k))
    (hρI : ∀ k n, ∀ x ∈ IA k ^ n, (ρA k).hom x ∈ FA n)
    (hαI : ∀ k n, ∀ x ∈ IA k ^ n, (α.app (op k)).hom x ∈ FC k n)
    (hAR : ∀ k, ∃ c : ℕ, ∀ (n : ℕ) (x : Ah.obj (op k)), (α.app (op k)).hom x ∈ FC k (n + c) →
      (ρA k).hom x ∈ FA (n + c) →
        ∃ y ∈ IA k ^ n, (α.app (op k)).hom (x - y) = 0 ∧ (ρA k).hom (x - y) = 0)
    (hmapA : ∀ {k k' : K} (g : k' ⟶ k) (n : ℕ), ∀ x ∈ IA k ^ n, (Ah.map g.op).hom x ∈ IA k' ^ n)
    (hmapC : ∀ {k : K} (f : k ⟶ k₀) (n : ℕ), ∀ y ∈ FC k₀ n, (Ch.map f.op).hom y ∈ FC k n)
    (hφc : ∀ n, (φ ⁻¹' (FA n : Set Al)) ∈ 𝓝 (0 : B))
    (hψc : ∀ n, (ψ ⁻¹' (FC k₀ n : Set (Ch.obj (op k₀)))) ∈ 𝓝 (0 : B))
    (R₀ : Subring B) (s : Finset B)
    (hdense : Dense (Subring.closure ((R₀ : Set B) ∪ (s : Set B)) : Set B))
    (hR₀ : ∀ {k : K} (f : k ⟶ k₀), ∀ b ∈ R₀, IsGoodAt α ρA φ ψ f b) :
    ∃ (k₂ : K) (f₂ : k₂ ⟶ k₀) (k : K) (g : k ⟶ k₂) (φk : B →+* Ah.obj (op k)),
      (∀ b, (ρA k).hom (φk b) = φ b) ∧
      (∀ b, (α.app (op k)).hom (φk b) = (Ch.map (g ≫ f₂).op).hom (ψ b)) ∧
      (∀ b (x : Ah.obj (op k₂)), (ρA k₂).hom x = φ b →
        (α.app (op k₂)).hom x = (Ch.map f₂.op).hom (ψ b) → (Ah.map g.op).hom x = φk b) ∧
      ∀ n : ℕ,
        (φk ⁻¹' ((IA k ^ n : Ideal (Ah.obj (op k))) : Set (Ah.obj (op k)))) ∈ 𝓝 (0 : B) := by
  classical
  obtain ⟨k₁, f₁, hf₁⟩ := hcoker
  have hrange₁ : ∀ b, (Ch.map f₁.op).hom (ψ b) ∈ (α.app (op k₁)).hom.range :=
    fun b => hf₁ _ ⟨φ b, hφψ b⟩
  obtain ⟨k₂, g₂, h₂⟩ :=
    exists_forall_mem_isGoodAt α αl ρA ρC hρA hρC φ ψ hρ hφψ hker f₁ hrange₁ s
  have hgood : ∀ b, IsGoodAt α ρA φ ψ (g₂ ≫ f₁) b := by
    refine isGoodAt_of_dense α ρA φ ψ IA FA FC (g₂ ≫ f₁) (hpre k₂) hsepA (hsepC k₂) hFA
      (hFC k₂) (hρI k₂) (hαI k₂) (hAR k₂) hφc hψc (hmapC _) _ hdense
      fun b hb => (Subring.closure_le (t := goodSubring α ρA φ ψ (g₂ ≫ f₁))).2 ?_ hb
    rintro b' (hb' | hb')
    · exact hR₀ _ b' hb'
    · exact h₂ b' hb'
  obtain ⟨k₃, g₃, hg₃⟩ := hL (k := k₂)
  choose w hw₁ hw₂ using hgood
  have huniq : ∀ (b : B) (x : Ah.obj (op k₂)), (ρA k₂).hom x = φ b →
      (α.app (op k₂)).hom x = (Ch.map (g₂ ≫ f₁).op).hom (ψ b) →
        (Ah.map g₃.op).hom x = (Ah.map g₃.op).hom (w b) := by
    intro b x hx₁ hx₂
    rw [← sub_eq_zero, ← map_sub]
    exact hg₃ _ (by rw [map_sub, hx₂, hw₂, sub_self]) (by rw [map_sub, hx₁, hw₁, sub_self])
  let φk : B →+* Ah.obj (op k₃) :=
    { toFun := fun b => (Ah.map g₃.op).hom (w b)
      map_one' := (huniq 1 1 (by rw [map_one, map_one])
        (by rw [map_one, map_one, map_one])).symm.trans (map_one _)
      map_mul' := fun a b => (huniq (a * b) (w a * w b) (by rw [map_mul, hw₁, hw₁, map_mul])
        (by rw [map_mul, hw₂, hw₂, map_mul, map_mul])).symm.trans (map_mul _ _ _)
      map_zero' := (huniq 0 0 (by rw [map_zero, map_zero])
        (by rw [map_zero, map_zero, map_zero])).symm.trans (map_zero _)
      map_add' := fun a b => (huniq (a + b) (w a + w b) (by rw [map_add, hw₁, hw₁, map_add])
        (by rw [map_add, hw₂, hw₂, map_add, map_add])).symm.trans (map_add _ _ _) }
  have hφk : ∀ b, φk b = (Ah.map g₃.op).hom (w b) := fun _ => rfl
  refine ⟨k₂, g₂ ≫ f₁, k₃, g₃, φk, fun b => ?_, fun b => ?_, fun b x hx₁ hx₂ => ?_, fun n => ?_⟩
  · rw [hφk, ρA_map_apply ρA hρA, hw₁]
  · rw [hφk, α_map_apply, hw₂, ← Ch_map_comp_apply]
  · rw [hφk]
    exact huniq b x hx₁ hx₂
  · obtain ⟨c, hc⟩ := hAR k₂
    refine Filter.mem_of_superset (Filter.inter_mem (hφc (n + c)) (hψc (n + c))) ?_
    rintro b ⟨hb₁, hb₂⟩
    obtain ⟨y, hy, hy₁, hy₂⟩ := hc n (w b) (by rw [hw₂]; exact hmapC _ _ _ hb₂)
      (by rw [hw₁]; exact hb₁)
    have hy' : (Ah.map g₃.op).hom y = φk b := by
      rw [hφk]
      refine huniq b y ?_ ?_
      · rw [map_sub, sub_eq_zero] at hy₂
        rw [← hy₂, hw₁]
      · rw [map_sub, sub_eq_zero] at hy₁
        rw [← hy₁, hw₂]
    rw [Set.mem_preimage, ← hy']
    exact hmapA g₃ n y hy

end AlgebraicGeometry.Artin.StageLift

end

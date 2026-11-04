module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.LiftStep

/-!
# The thickening induction

Over a Noetherian base `R` with a maximal ideal `𝔪`, the lifting step
`Stacks.CubeOpenAtUnit.surjective_quoDrop_app_top` applies at every exponent: `𝔪ⁿ⁺¹ / 𝔪ⁿ⁺²` has a
basis over `R / 𝔪` lifted to elements of `𝔪ⁿ⁺¹` (`Stacks.CubeOpenAtUnit.exists_basis_pow`). Hence
every global section of `ℱ / 𝔪ℱ` lifts to every `ℱ / 𝔪ⁿ⁺¹ℱ`, as soon as the face conditions hold.
This is step 1(a) of the cube proof in abstract form.

## Main results

* `Stacks.CubeOpenAtUnit.exists_basis_pow`: lifts of a basis of `𝔪ⁿ⁺¹ / 𝔪ⁿ⁺²`.
* `Stacks.CubeOpenAtUnit.exists_lift_of_faces`: every section of `ℱ / 𝔪ℱ` lifts to `ℱ / 𝔪ⁿ⁺¹ℱ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.Coherent (baseSectionHom)

universe u

namespace Stacks.CubeOpenAtUnit

section Basis

variable {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal] (n : ℕ)

/-- A spanning family of `𝔪ⁿ⁺¹` modulo `𝔪ⁿ⁺²` with a relation having a unit coefficient can be
shortened. -/
theorem exists_shorter {d : ℕ} (r : Fin (d + 1) → R) (j : Fin (d + 1))
    (hspan : m ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ m ^ (n + 2))
    (hr : ∀ k, r k ∈ m ^ (n + 1)) (a : Fin (d + 1) → R)
    (ha : ∑ k, a k * r k ∈ m ^ (n + 2)) (hj : a j ∉ m) :
    m ^ (n + 1) ≤ Ideal.span (Set.range (fun i : Fin d => r (j.succAbove i))) ⊔ m ^ (n + 2) := by
  set r' := fun i : Fin d => r (j.succAbove i)
  refine hspan.trans (sup_le ?_ le_sup_right)
  rw [Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨i, rfl⟩
  · obtain ⟨b, c, hc, hbc⟩ := Ideal.IsMaximal.exists_inv ‹m.IsMaximal› hj
    set T := ∑ i : Fin d, a (k.succAbove i) * r (k.succAbove i)
    have hsum : ∑ l, a l * r l = a k * r k + T := Fin.sum_univ_succAbove _ k
    have hT : b * T ∈ Ideal.span (Set.range r') :=
      Ideal.mul_mem_left _ _ (Submodule.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
    have hrest : b * (a k * r k + T) + c * r k ∈ m ^ (n + 2) := by
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hsum ▸ ha)) ?_
      rw [show n + 2 = 1 + (n + 1) by omega, pow_add, pow_one]
      exact Ideal.mul_mem_mul hc (hr k)
    have hid : r k = -(b * T) + (b * (a k * r k + T) + c * r k) := by
      linear_combination (-(r k)) * hbc
    rw [hid]
    exact Submodule.add_mem_sup ((Ideal.neg_mem_iff _).2 hT) hrest
  · exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)

/-- **A basis of `𝔪ⁿ⁺¹ / 𝔪ⁿ⁺²`, lifted to `𝔪ⁿ⁺¹`.** For `R` Noetherian there are
`r₁, …, r_d ∈ 𝔪ⁿ⁺¹` spanning `𝔪ⁿ⁺¹` modulo `𝔪ⁿ⁺²` such that `∑ aₖ rₖ ∈ 𝔪ⁿ⁺²` forces every
`aₖ ∈ 𝔪`: take a spanning family of minimal length. -/
theorem exists_basis_pow [IsNoetherianRing R] :
    ∃ (d : ℕ) (r : Fin d → R), (∀ k, r k ∈ m ^ (n + 1)) ∧
      m ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ m ^ (n + 2) ∧
      ∀ a : Fin d → R, ∑ k, a k * r k ∈ m ^ (n + 2) → ∀ k, a k ∈ m := by
  classical
  let P : ℕ → Prop := fun d => ∃ r : Fin d → R, (∀ k, r k ∈ m ^ (n + 1)) ∧
    m ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ m ^ (n + 2)
  have hP : ∃ d, P d := by
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (m ^ (n + 1)) : (m ^ (n + 1)).FG)
    refine ⟨s.card, fun k => (s.equivFin.symm k : R), fun k => ?_, ?_⟩
    · rw [← hs]
      exact Ideal.subset_span (s.equivFin.symm k).2
    · have hrange : Set.range (fun k => (s.equivFin.symm k : R)) = (s : Set R) := by
        ext x
        exact ⟨fun ⟨k, hk⟩ => hk ▸ (s.equivFin.symm k).2, fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp⟩⟩
      rw [hrange, Ideal.span, hs]
      exact le_sup_left
  obtain ⟨r, hr, hspan⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, r, hr, hspan, ?_⟩
  have hmin : ∀ d' < Nat.find hP, ¬ P d' := fun d' h => Nat.find_min hP h
  generalize Nat.find hP = d at r hr hspan hmin
  intro a ha j
  by_contra hj
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos j).ne'
  exact hmin d' (Nat.lt_succ_self d') ⟨_, fun i => hr _, exists_shorter m n r j hspan hr a ha hj⟩

end Basis

/-- The category of sheaves of modules on a scheme has finite biproducts. -/
local instance hasFiniteBiproducts_modules'' (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
  (m : Ideal R) [m.IsMaximal] (G : X.Modules) [G.IsQuasicoherent]

/-- Lowering the exponent from `n + 1` to `1`. -/
abbrev quoDropOne (n : ℕ) : quo g m G (n + 1) ⟶ quo g m G 1 :=
  idealPowerQuotientDrop (baseIdealSheaf R m g) (Nat.le_add_left 1 n) G

omit [IsNoetherianRing R] [m.IsMaximal] [SheafOfModules.IsQuasicoherent G] in
/-- At `n = 0` the map `ℱ / 𝔪ℱ ⟶ ℱ / 𝔪ℱ` lowering the exponent to `1` is the identity. -/
theorem quoDropOne_zero : quoDropOne g m G 0 = 𝟙 _ := by
  refine (cancel_epi (quoπ g m G 1)).1 ?_
  rw [idealPowerQuotientDrop_π, Category.comp_id]

omit [IsNoetherianRing R] [m.IsMaximal] [SheafOfModules.IsQuasicoherent G] in
/-- Lowering the exponent from `n + 2` to `n + 1` and then to `1` is lowering it from `n + 2` to
`1`. -/
theorem quoDrop_quoDropOne (n : ℕ) :
    quoDrop g m G (n + 1) ≫ quoDropOne g m G n = quoDropOne g m G (n + 1) := by
  refine (cancel_epi (quoπ g m G (n + 2))).1 ?_
  rw [quoπ_quoDrop_assoc, idealPowerQuotientDrop_π, idealPowerQuotientDrop_π]

/-- **Every section of `ℱ / 𝔪ℱ` lifts to every `ℱ / 𝔪ⁿ⁺¹ℱ`**, under the hypotheses of
`Stacks.CubeOpenAtUnit.surjective_quoDrop_app_top` at every exponent. -/
theorem exists_lift_of_faces
    (hflat : ∀ U : X.affineOpens, (baseSectionHom R g U.1).Flat ∧
      Module.Flat Γ(X, U.1) Γ(G, U.1))
    {ι : Type*} (φ : ι → Face G)
    (hflatF : ∀ i, ∀ U : (φ i).F.affineOpens, (baseSectionHom R ((φ i).j ≫ g) U.1).Flat ∧
      Module.Flat Γ((φ i).F, U.1) Γ((φ i).G', U.1))
    (hsurj : ∀ n i, Function.Surjective ((quoDrop ((φ i).j ≫ g) m (φ i).G' (n + 1)).app ⊤))
    (hinj : ∀ c : (H X 1).obj (quo g m G 1),
      (∀ i, ((H X 1).map ((φ i).quoMap 1)).hom c = 0) → c = 0)
    (t₀ : Γ(quo g m G 1, ⊤)) (n : ℕ) :
    ∃ t : Γ(quo g m G (n + 1), ⊤), (quoDropOne g m G n).app ⊤ t = t₀ := by
  induction n with
  | zero => exact ⟨t₀, by rw [quoDropOne_zero]; rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨d, r, hr, hspan, hind⟩ := exists_basis_pow m n
    obtain ⟨t', ht'⟩ := surjective_quoDrop_app_top (g := g) (I := m) (G := G) r hr hflat hspan hind
      φ hflatF (hsurj n) hinj t
    refine ⟨t', ?_⟩
    rw [← quoDrop_quoDropOne, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, ht', ht]

end Stacks.CubeOpenAtUnit

end

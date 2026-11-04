module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Maps out of a finitely presented module into a filtered colimit

Let `D : J ⥤ ModuleCat R` be a diagram over a filtered category, and `c` a colimit cocone of `D`
preserved by the forgetful functor. Every map from a finitely presented `R`-module into `c.pt`
factors through one of the stages of the diagram.

## Main results

* `Module.FinitePresentation.exists_comp_eq_of_isColimit` — a map from a finitely presented
  module into a filtered colimit of modules factors through a stage.
-/

@[expose] public section

universe w uJ vJ u

open CategoryTheory CategoryTheory.Limits

namespace Module

variable {R : Type u} [Ring R] {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
  {D : J ⥤ ModuleCat.{w} R} [PreservesColimit D (forget (ModuleCat.{w} R))] {c : Cocone D}

/-- Finitely many elements of a filtered colimit of modules are images of elements of a single
stage of the diagram. -/
private theorem exists_rep_fin (hc : IsColimit c) (n : ℕ) (x : Fin n → c.pt) :
    ∃ (j : J) (y : Fin n → D.obj j), ∀ a, c.ι.app j (y a) = x a := by
  induction n with
  | zero =>
    exact ⟨Classical.choice (IsFiltered.nonempty (C := J)), Fin.elim0, fun a => Fin.elim0 a⟩
  | succ n ih =>
    obtain ⟨j, y, hy⟩ := ih fun a => x a.succ
    obtain ⟨k, z, hz⟩ := Concrete.isColimit_exists_rep D hc (x 0)
    refine ⟨IsFiltered.max j k,
      Fin.cases (D.map (IsFiltered.rightToMax j k) z)
        fun a => D.map (IsFiltered.leftToMax j k) (y a), fun a => ?_⟩
    refine Fin.cases ?_ (fun a => ?_) a
    · exact (c.w_apply (IsFiltered.rightToMax j k) z).trans hz
    · exact (c.w_apply (IsFiltered.leftToMax j k) (y a)).trans (hy a)

/-- Finitely many elements of one stage of a filtered diagram whose images in the colimit vanish
are killed by a single transition map. -/
private theorem exists_map_eq_zero_fin (hc : IsColimit c) (n : ℕ) (j : J) (x : Fin n → D.obj j)
    (hx : ∀ a, c.ι.app j (x a) = 0) :
    ∃ (k : J) (v : j ⟶ k), ∀ a, D.map v (x a) = 0 := by
  induction n generalizing j with
  | zero => exact ⟨j, 𝟙 j, fun a => Fin.elim0 a⟩
  | succ n ih =>
    obtain ⟨k, v, v', hvv⟩ := Concrete.isColimit_exists_of_rep_eq D hc (x 0) (0 : D.obj j)
      ((hx 0).trans (map_zero (c.ι.app j).hom).symm)
    have hzero : D.map v (x 0) = 0 := hvv.trans (map_zero (D.map v').hom)
    obtain ⟨l, t, ht⟩ := ih k (fun a => D.map v (x a.succ)) fun a =>
      (c.w_apply v (x a.succ)).trans (hx a.succ)
    refine ⟨l, v ≫ t, fun a => ?_⟩
    rw [D.map_comp]
    refine Fin.cases ?_ (fun a => ht a) a
    show D.map t (D.map v (x 0)) = 0
    rw [hzero, map_zero]

/-- A map from a finitely presented module into a filtered colimit of modules factors through one
of the stages of the diagram. -/
theorem FinitePresentation.exists_comp_eq_of_isColimit (hc : IsColimit c) {M : ModuleCat.{w} R}
    [Module.FinitePresentation R M] (φ : M ⟶ c.pt) :
    ∃ (j : J) (ψ : M ⟶ D.obj j), ψ ≫ c.ι.app j = φ := by
  classical
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  set bn := Pi.basisFun R (Fin n)
  set bm := Pi.basisFun R (Fin m)
  obtain ⟨j, y, hy⟩ := exists_rep_fin hc n fun a => φ (f (bn a))
  set ψ₀ : (Fin n → R) →ₗ[R] D.obj j := bn.constr ℕ y with hψ₀
  have key : (c.ι.app j).hom ∘ₗ ψ₀ = φ.hom ∘ₗ f := by
    refine bn.ext fun a => ?_
    simpa [hψ₀] using hy a
  obtain ⟨k, v, hv⟩ := exists_map_eq_zero_fin hc m j (fun l => ψ₀ (g (bm l))) fun l => by
    have h := LinearMap.congr_fun key (g (bm l))
    simp only [LinearMap.comp_apply] at h
    rw [hfg.apply_apply_eq_zero] at h
    simpa using h
  have hzero : ((D.map v).hom ∘ₗ ψ₀) ∘ₗ g = 0 := bm.ext fun l => hv l
  have hker : LinearMap.ker f ≤ LinearMap.ker ((D.map v).hom ∘ₗ ψ₀) := by
    intro p hp
    obtain ⟨q, rfl⟩ := (hfg p).mp (LinearMap.mem_ker.mp hp)
    exact LinearMap.congr_fun hzero q
  refine ⟨k, ModuleCat.ofHom ((Submodule.liftQ _ ((D.map v).hom ∘ₗ ψ₀) hker).comp
    (LinearMap.quotKerEquivOfSurjective f hf).symm.toLinearMap), ?_⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
  obtain ⟨q, rfl⟩ := hf p
  have hsymm : (LinearMap.quotKerEquivOfSurjective f hf).symm (f q) = Submodule.Quotient.mk q := by
    rw [LinearEquiv.symm_apply_eq]
    simp [LinearMap.quotKerEquivOfSurjective]
  simpa [hsymm, c.w_apply v (ψ₀ q)] using LinearMap.congr_fun key q

end Module

end

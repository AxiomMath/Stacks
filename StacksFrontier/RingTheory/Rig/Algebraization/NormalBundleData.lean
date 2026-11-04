module

public import StacksFrontier.RingTheory.Rig.Algebraization.NormalBundleOfRel
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria

/-!
# Existence of the normal bundle data of a rig-smooth algebra

Let `A` be a Noetherian ring, `a ∈ A`, and `B = A⟨x₁, …, x_N⟩ / J` a rig-smooth object of the
category of Stacks 0AL4 over `(A, (a))`. This file produces the data `Rig.NormalBundle.Data`
consumed by the construction of the completed normal bundle.

Rig-smoothness gives `c₀` and a `B`-linear map `h : Bᴺ → J / J²` with `h ∘ d = a^{c₀}`, where
`d` is the differential of the completed naive cotangent complex. Choosing generators `fₗ` of
`J` and writing `h(eᵢ) = ∑ₗ Sₗᵢ [fₗ]` gives the relation `∑ₗ (S · Jac − a^{c₀})ₗⱼ fₗ ∈ J²`.
`Rig.NormalBundle.Data.ofRel` turns that relation into the data, through the improved lift of
`E₀ = (Jac · S)ᵀ`.

## Main results

* `Rig.NormalBundle.nonempty_data`: a rig-smooth object admits normal bundle data for any
  completed polynomial presentation.
-/

@[expose] public noncomputable section

universe u v

namespace Rig

namespace NormalBundle

section Data

open Algebra.Extension

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {a : A}

omit [IsNoetherianRing A] in
/-- The class in `J / J²` of `g = ∑ₗ vₗ fₗ` is `∑ₗ vₗ • [fₗ]`. -/
private theorem cotangent_mk_eq_sum_smul {B : AdicFiniteTypeAlgebra.{u, v} A (Ideal.span {a})}
    {Pres : CompletedPolynomialPresentation (Ideal.span {a}) B} {m : ℕ}
    (fk : Fin m → Pres.extension.ker) (v : Fin m → Pres.completedPolynomialRing)
    (g : Pres.extension.ker)
    (hg : g.1 = ∑ l, v l * show Pres.completedPolynomialRing from (fk l).1) :
    Cotangent.mk g = ∑ l, Pres.toAlgHom (v l) • Cotangent.mk (fk l) := by
  let w : Fin m → Pres.extension.Ring := v
  have : g = ∑ l, w l • fk l := Subtype.ext <| by
    rw [hg, Submodule.coe_sum]
    rfl
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_smul]
  exact (algebraMap_smul B.carrier (w l) _).symm

/-- **Normal bundle data exist for rig-smooth algebras.** If `B` is rig-smooth over `(A, (a))`,
then every completed polynomial presentation of `B` admits the data `Rig.NormalBundle.Data` of a
completed normal bundle. -/
theorem nonempty_data (B : AdicFiniteTypeAlgebra.{u, v} A (Ideal.span {a}))
    (Pres : CompletedPolynomialPresentation (Ideal.span {a}) B) (hB : IsRigSmooth B) :
    Nonempty (Data B Pres) := by
  classical
  let K := completedNaiveCotangentComplex B Pres
  obtain ⟨c, hc⟩ := (isRigSmooth_iff_cotangentFactorization B Pres).1 hB
  obtain ⟨h, hh⟩ := hc (a ^ c) (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) c)
  let u : Pres.completedPolynomialRing := algebraMap A Pres.completedPolynomialRing (a ^ c)
  have hu : algebraMap A B.carrier (a ^ c) = Pres.toAlgHom u := (Pres.toAlgHom.commutes _).symm
  have hhd : ∀ x, h (K.differential x) = Pres.toAlgHom u • x := fun x ↦ by
    simpa [hu] using LinearMap.congr_fun hh x
  have : IsNoetherianRing Pres.completedPolynomialRing := AdicCompletion.isNoetherianRing _
  obtain ⟨m, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (Ideal.fg_of_isNoetherianRing Pres.ideal)
  have hker : Pres.extension.ker = Pres.ideal := Pres.ker_eq_ideal
  have hfJ (l : Fin m) : f l ∈ Pres.ideal := hf ▸ Submodule.subset_span (Set.mem_range_self l)
  let fk : Fin m → Pres.extension.ker := fun l ↦ ⟨f l, hker.ge (hfJ l)⟩
  have hS (i : Fin Pres.variableCount) : ∃ s : Fin m → Pres.completedPolynomialRing,
      h (fun j ↦ if i = j then 1 else 0) = ∑ l, Pres.toAlgHom (s l) • Cotangent.mk (fk l) := by
    obtain ⟨g, hg⟩ := Cotangent.mk_surjective (h fun j ↦ if i = j then 1 else 0)
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hf.ge (hker.le g.2))
    exact ⟨s, hg ▸ cotangent_mk_eq_sum_smul fk s g (by rw [← hs]; rfl)⟩
  choose S0 hS0 using hS
  let S : Matrix (Fin m) (Fin Pres.variableCount) Pres.completedPolynomialRing :=
    fun l i ↦ S0 i l
  let Jac := jacobian B Pres f
  have hdf (l : Fin m) : K.differential (Cotangent.mk (fk l)) =
      fun k ↦ Pres.toAlgHom (Jac k l) := K.differential_mk (fk l)
  have hrel (j : Fin m) : ∑ l, ((S * Jac) l j -
      (1 : Matrix (Fin m) (Fin m) Pres.completedPolynomialRing) l j * u) * f l ∈
        Pres.ideal ^ 2 := by
    let g : Pres.extension.ker := ⟨∑ l, ((S * Jac) l j -
      (1 : Matrix (Fin m) (Fin m) Pres.completedPolynomialRing) l j * u) * f l,
      hker.ge (Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_left _ _ (hfJ l))⟩
    have hhdf : h (K.differential (Cotangent.mk (fk j))) =
        ∑ l, Pres.toAlgHom ((S * Jac) l j) • Cotangent.mk (fk l) := by
      rw [hdf, LinearMap.pi_apply_eq_sum_univ]
      simp_rw [hS0, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [← Finset.sum_smul, Matrix.mul_apply, map_sum]
      simp only [map_mul, S]
      exact congrArg (· • _) (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)
    rw [hhd] at hhdf
    have hg : Cotangent.mk g = 0 := by
      rw [cotangent_mk_eq_sum_smul fk _ g rfl]
      simp only [map_sub, sub_smul, Finset.sum_sub_distrib, ← hhdf, Matrix.one_apply,
        apply_ite Pres.toAlgHom, map_zero, ite_mul, one_mul, zero_mul, ite_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    rw [← hker]
    exact (Cotangent.mk_eq_zero_iff g).1 hg
  exact ⟨Data.ofRel B Pres f hf c S hrel⟩

end Data

end NormalBundle

end Rig

end

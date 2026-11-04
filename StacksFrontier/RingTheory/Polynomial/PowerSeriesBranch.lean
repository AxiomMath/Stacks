module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Power series branches of a plane curve and the multiplicity zero count

Let `Ψ ∈ K[X][Y]` be monic in `Y`. At a point `(a, b)` of the curve `Ψ = 0` where `∂Ψ/∂Y` does not
vanish, Hensel's lemma in `K⟦s⟧` gives a branch: a power series `β(s)` with `β(0) = b` and
`Ψ(a + s, β(s)) = 0`. The order of vanishing of a second polynomial `g` along such branches is
controlled by the resultant: summed over finitely many branches through distinct points, the
orders of `g(a + s, β(s))` are at most the `X`-degree of `Res_Y(Ψ, g)`.

## Main results

* `Polynomial.exists_powerSeries_root_of_simple_root`: the branch through a simple point.
* `Polynomial.order_aeval_C_add_X`: the order of `r(a + s)` is the multiplicity of the root `a`.
* `Polynomial.sum_order_le_rootMultiplicity_resultant`: the branches over one value of `X`.
* `Polynomial.sum_order_le_natDegree_resultant`: the multiplicity zero count.
-/

@[expose] public section

open Polynomial


namespace Polynomial

variable {K : Type*} [Field K]

/-- The constant coefficient of `r(a + s)` is `r(a)`, as an equality of ring homomorphisms. -/
private theorem constantCoeff_comp_aeval_C_add_X (a : K) :
    PowerSeries.constantCoeff.comp
      (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom =
      evalRingHom a := by
  ext <;> simp

/-- The constant coefficient of `Ψ(a + s, β(s))` is `Ψ(a, β(0))`. -/
theorem constantCoeff_eval_map_aeval_C_add_X (Ψ : K[X][X]) (a : K) (β : PowerSeries K) :
    PowerSeries.constantCoeff
        ((Ψ.map (aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval β) =
      Ψ.evalEval a (PowerSeries.constantCoeff β) := by
  rw [eval_map, hom_eval₂, constantCoeff_comp_aeval_C_add_X, eval₂_evalRingHom]

/-- **Hensel's lemma along a branch.** If `b` is a simple root of `Ψ(a, Y)` for `Ψ ∈ K[X][Y]`
monic in `Y`, then there is a power series `β(s)` with `β(0) = b` and `Ψ(a + s, β(s)) = 0`. -/
theorem exists_powerSeries_root_of_simple_root {Ψ : K[X][X]} (hΨ : Ψ.Monic) {a b : K}
    (h0 : Ψ.evalEval a b = 0) (h1 : (derivative Ψ).evalEval a b ≠ 0) :
    ∃ β : PowerSeries K, PowerSeries.constantCoeff β = b ∧
      (Ψ.map (aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval β = 0 := by
  set φ := (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom
  have hmon : (Ψ.map φ).Monic := hΨ.map φ
  have hc : ∀ f : K[X][X], PowerSeries.constantCoeff ((f.map φ).eval (PowerSeries.C b)) =
      f.evalEval a b := fun f => by
    rw [constantCoeff_eval_map_aeval_C_add_X]; simp
  have hmem : (Ψ.map φ).eval (PowerSeries.C b) ∈ Ideal.span {PowerSeries.X} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, hc, h0]
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {PowerSeries.X})
      ((Ψ.map φ).derivative.eval (PowerSeries.C b))) := by
    refine IsUnit.map _ ?_
    rw [PowerSeries.isUnit_iff_constantCoeff, derivative_map, hc]
    exact h1.isUnit
  obtain ⟨β, hβ, hβb⟩ := HenselianRing.is_henselian (I := Ideal.span {PowerSeries.X})
    (Ψ.map φ) hmon (PowerSeries.C b) hmem hunit
  refine ⟨β, ?_, hβ⟩
  rwa [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C,
    sub_eq_zero] at hβb

end Polynomial

namespace Polynomial

variable {K : Type*} [Field K]

/-- The order at `s = 0` of `r(a + s)` is the multiplicity of `a` as a root of `r`. -/
theorem order_aeval_C_add_X {r : K[X]} (hr : r ≠ 0) (a : K) :
    (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K) r).order =
      r.rootMultiplicity a := by
  obtain ⟨q, hq, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr a
  have hq0 : q.eval a ≠ 0 := fun h => hdvd (dvd_iff_isRoot.mpr h)
  conv_lhs => rw [hq]
  rw [map_mul, map_pow, PowerSeries.order_mul, map_sub, aeval_X, aeval_C,
    show (PowerSeries.C a + PowerSeries.X : PowerSeries K) -
      algebraMap K (PowerSeries K) a = PowerSeries.X by simp,
    PowerSeries.order_X_pow, PowerSeries.order_zero_of_isUnit, add_zero]
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h : PowerSeries.constantCoeff (aeval (R := K)
      (PowerSeries.C a + PowerSeries.X : PowerSeries K) q) = q.eval a :=
    RingHom.congr_fun (constantCoeff_comp_aeval_C_add_X a) q
  rw [h]; exact hq0.isUnit

/-- The multiplicities of finitely many roots of a nonzero polynomial add up to at most its
degree. -/
theorem sum_rootMultiplicity_le_natDegree {p : K[X]} (hp : p ≠ 0) (A : Finset K) :
    ∑ a ∈ A, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  calc ∑ a ∈ A, p.rootMultiplicity a = ∑ a ∈ A, p.roots.count a := by simp [count_roots]
    _ ≤ ∑ a ∈ A ∪ p.roots.toFinset, p.roots.count a :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ a ∈ p.roots.toFinset, p.roots.count a := by
        refine (Finset.sum_subset Finset.subset_union_right fun a _ ha => ?_).symm
        exact Multiset.count_eq_zero.mpr (by simpa using ha)
    _ = Multiset.card p.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ p.natDegree := card_roots' p

end Polynomial

namespace Polynomial

variable {K : Type*} [Field K]

/-- **The branches over one point.** Fix `a`. If the power series `β t` for `t ∈ T` are pairwise
distinct roots of `Ψ(a + s, Y)`, then the orders of `g(a + s, β t)` add up to at most the
multiplicity of `a` as a root of `Res_Y(Ψ, g)`. -/
theorem sum_order_le_rootMultiplicity_resultant {Ψ g : K[X][X]} (hΨ : Ψ.Monic)
    (hres : resultant Ψ g ≠ 0) (a : K) (T : Finset (PowerSeries K))
    (hT : ∀ t ∈ T,
      (Ψ.map (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval t
        = 0) :
    ∑ t ∈ T, ((g.map (aeval (R := K)
      (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval t).order ≤
        ((resultant Ψ g).rootMultiplicity a : ℕ∞) := by
  classical
  set φ := (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom
  set Ψa := Ψ.map φ
  set ga := g.map φ
  have hΨa : Ψa.Monic := hΨ.map φ
  have hΨa0 : Ψa ≠ 0 := hΨa.ne_zero
  have hle : T.val ≤ Ψa.roots :=
    (Multiset.le_iff_subset T.nodup).mpr fun t ht =>
      (mem_roots hΨa0).mpr (hT t (Finset.mem_def.mpr ht))
  obtain ⟨H, hH⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hΨa0 T.val).mpr hle
  set Pr : (PowerSeries K)[X] := ∏ t ∈ T, (X - C t)
  have hPr : (T.val.map fun t => X - C t).prod = Pr := rfl
  rw [hPr] at hH
  have hPrm : Pr.Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hHm : H.Monic := hPrm.of_mul_monic_left (hH ▸ hΨa)
  have hdeg : Ψ.natDegree = Pr.natDegree + H.natDegree := by
    rw [← hΨ.natDegree_map φ, ← hPrm.natDegree_mul hHm, ← hH]
  have hga : ga.natDegree ≤ g.natDegree := natDegree_map_le
  have hφres : φ (resultant Ψ g) =
      (∏ t ∈ T, ga.eval t) * resultant H ga H.natDegree g.natDegree := by
    rw [resultant, ← resultant, ← resultant_map_map, hdeg]
    show Ψa.resultant ga _ _ = _
    rw [hH, resultant_mul_left _ _ _ _ hga,
      resultant_prod_left _ _ _ _ (by simp [leadingCoeff_X_sub_C]) hga]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [natDegree_X_sub_C, ← pow_one (X - C t), resultant_X_sub_C_pow_left _ _ _ _ hga, pow_one]
  have hord := order_aeval_C_add_X hres a
  rw [← hord]
  show _ ≤ (φ (resultant Ψ g)).order
  rw [hφres, PowerSeries.order_mul, PowerSeries.order_prod]
  exact le_self_add

/-- **The multiplicity zero count.** Let `Ψ ∈ K[X][Y]` be monic in `Y`, and let `S` be a finite set
of points `P = (P.1, P.2)` together with power series branches `β P` through them, i.e. roots of
`Ψ(P.1 + s, Y)` with `β P (0) = P.2`. Then the orders of vanishing of `g(P.1 + s, β P(s))` add up
to at most the `X`-degree of the resultant `Res_Y(Ψ, g)`, provided it is nonzero. -/
theorem sum_order_le_natDegree_resultant {Ψ g : K[X][X]} (hΨ : Ψ.Monic)
    (S : Finset (K × K)) (β : K × K → PowerSeries K)
    (hβ : ∀ P ∈ S, PowerSeries.constantCoeff (β P) = P.2 ∧
      (Ψ.map (aeval (PowerSeries.C P.1 + PowerSeries.X : PowerSeries K)).toRingHom).eval (β P) = 0)
    (hres : resultant Ψ g ≠ 0) :
    ∑ P ∈ S, ((g.map (aeval (PowerSeries.C P.1 + PowerSeries.X : PowerSeries K)).toRingHom).eval
      (β P)).order ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
  classical
  set A := S.image Prod.fst
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := A)
    (fun P hP => Finset.mem_image_of_mem _ hP)]
  calc ∑ a ∈ A, ∑ P ∈ S with P.1 = a,
        ((g.map (aeval (PowerSeries.C P.1 + PowerSeries.X : PowerSeries K)).toRingHom).eval
          (β P)).order
      ≤ ∑ a ∈ A, ((resultant Ψ g).rootMultiplicity a : ℕ∞) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hinj : Set.InjOn β (S.filter fun P => P.1 = a) := by
          intro P hP P' hP' h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hP hP'
          have h2 : P.2 = P'.2 := by rw [← (hβ P hP.1).1, ← (hβ P' hP'.1).1, h]
          exact Prod.ext (hP.2.trans hP'.2.symm) h2
        rw [Finset.sum_congr rfl (g := fun P => ((g.map (aeval (R := K)
          (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval (β P)).order)
          (fun P hP => by rw [(Finset.mem_filter.mp hP).2]),
          ← Finset.sum_image (f := fun t => ((g.map (aeval (R := K)
            (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval t).order) hinj]
        refine sum_order_le_rootMultiplicity_resultant hΨ hres a _ fun t ht => ?_
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨hPS, rfl⟩ := Finset.mem_filter.mp hP
        exact (hβ P hPS).2
    _ = ((∑ a ∈ A, (resultant Ψ g).rootMultiplicity a : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
        exact_mod_cast sum_rootMultiplicity_le_natDegree hres A

end Polynomial

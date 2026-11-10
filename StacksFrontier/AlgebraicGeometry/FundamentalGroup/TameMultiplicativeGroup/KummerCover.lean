module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kummer covers of `𝐆_m`

Let `k` be a field, `F / k` a finite separable field extension and `n ≥ 1` an integer invertible
in `k`. The *Kummer cover* `K_{n,F} = Spec F[X]_X ⟶ 𝐆_{m,k} = Spec k[x]_x` is given by `x ↦ X^n`
(and the inclusion `k ⊆ F` on constants): it is the composite of the constant field extension
`𝐆_{m,F} ⟶ 𝐆_{m,k}` and of the `n`-th power map of `𝐆_{m,F}`. It is finite étale.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.kummerMap k F n`: the ring map `k[x]_x → F[X]_X`.
* `AlgebraicGeometry.TameMultiplicativeGroup.kummerCover F n`: the finite étale cover.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.kummerMap_finite`,
  `AlgebraicGeometry.TameMultiplicativeGroup.kummerMap_etale`: the Kummer map is finite étale.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable (k : Type u) [Field k] (F : Type u) [Field F] [Algebra k F] (n : ℕ)

/-- The coordinate `X` of `F[X]_X`. -/
abbrev coord : Ring F := algebraMap F[X] (Ring F) X

/-- The coordinate `X` is a unit of `F[X]_X`. -/
theorem isUnit_coord : IsUnit (coord F) := IsLocalization.Away.algebraMap_isUnit X

/-- The polynomial part `k[x] → F[X]`, `x ↦ X^n`, of the Kummer map. -/
def kummerPolyMap : k[X] →+* F[X] := eval₂RingHom (C.comp (algebraMap k F)) (X ^ n)

/-- **The Kummer map** `k[x]_x → F[X]_X`, `x ↦ X^n`. -/
def kummerMap : Ring k →+* Ring F :=
  IsLocalization.Away.lift (X : k[X]) (g := (algebraMap F[X] (Ring F)).comp (kummerPolyMap k F n))
    (by
      change IsUnit (algebraMap F[X] (Ring F) (eval₂ (C.comp (algebraMap k F)) (X ^ n) X))
      rw [eval₂_X, map_pow]
      exact (isUnit_coord F).pow n)

/-- On the image of a polynomial `p ∈ k[x]`, the Kummer map is `kummerPolyMap k F n p`. -/
theorem kummerMap_algebraMap (p : k[X]) :
    kummerMap k F n (algebraMap k[X] (Ring k) p) =
      algebraMap F[X] (Ring F) (kummerPolyMap k F n p) :=
  IsLocalization.Away.lift_eq _ _ p

/-- The Kummer map sends the coordinate `x` to `X^n`. -/
theorem kummerMap_coord : kummerMap k F n (coord k) = coord F ^ n := by
  rw [kummerMap_algebraMap, kummerPolyMap, coe_eval₂RingHom, eval₂_X, map_pow]

/-- The Kummer map sends a constant `a ∈ k` to the constant `a ∈ F`. -/
theorem kummerMap_C (a : k) :
    kummerMap k F n (algebraMap k[X] (Ring k) (C a)) =
      algebraMap F[X] (Ring F) (C (algebraMap k F a)) := by
  rw [kummerMap_algebraMap, kummerPolyMap, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]

/-- For `n > 0`, the map `k[x] → F[X]`, `x ↦ X^n`, is injective. -/
theorem kummerPolyMap_injective {n} (hn : 0 < n) : Function.Injective (kummerPolyMap k F n) := by
  have : (kummerPolyMap k F n : k[X] → F[X]) = fun p ↦ expand F n (p.map (algebraMap k F)) := by
    funext p
    simp only [kummerPolyMap, coe_eval₂RingHom, expand_eq_comp_X_pow]
    rw [eval₂_eq_eval_map, ← map_map, comp, eval_map]
  rw [this]
  exact (expand_injective hn).comp (map_injective _ (algebraMap k F).injective)

/-- `1 / X^m = (X⁻¹)^m` in `F[X]_X`. -/
theorem mk'_one_X_pow (m : ℕ) (s : Submonoid.powers (X : F[X])) (hs : (s : F[X]) = X ^ m) :
    IsLocalization.mk' (Ring F) (1 : F[X]) s = ((isUnit_coord F).unit⁻¹ : (Ring F)ˣ).1 ^ m := by
  rw [IsLocalization.mk'_eq_iff_eq_mul, map_one, hs, map_pow, ← mul_pow,
    Units.inv_mul_of_eq (IsUnit.unit_spec _), one_pow]

/-- For `n > 0`, the Kummer map `k[x]_x → F[X]_X` is injective. -/
theorem kummerMap_injective {n} (hn : 0 < n) : Function.Injective (kummerMap k F n) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (X : k[X])) z
  rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, kummerMap_algebraMap] at hz
  have hu : IsUnit (kummerMap k F n (IsLocalization.mk' (Ring k) (1 : k[X]) s)) :=
    (IsUnit.of_mul_eq_one _ (by rw [IsLocalization.mk'_spec, map_one] :
      IsLocalization.mk' (Ring k) (1 : k[X]) s * algebraMap k[X] (Ring k) s = 1)).map
      (kummerMap k F n)
  have hp : kummerPolyMap k F n p = 0 := IsLocalization.injective (Ring F)
    (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)
    (by rw [hu.mul_left_eq_zero.mp hz, map_zero])
  rw [(kummerPolyMap_injective k F hn) (hp.trans (map_zero _).symm), IsLocalization.mk'_zero]

section Algebra

variable [FiniteDimensional k F]

/-- For `n > 0`, `F[X]_X` is generated as a `k[x]_x`-algebra, via the Kummer map, by the
coordinate `X` and the image of a `k`-basis of `F`. -/
theorem adjoin_coord_basis_eq_top (hn : 0 < n) :
    letI := (kummerMap k F n).toAlgebra
    Algebra.adjoin (Ring k) ({coord F} ∪ Set.range
      (fun i ↦ algebraMap F (Ring F) (Module.finBasis k F i))) = ⊤ := by
  let := (kummerMap k F n).toAlgebra
  set S := Algebra.adjoin (Ring k) ({coord F} ∪ Set.range
      (fun i ↦ algebraMap F (Ring F) (Module.finBasis k F i)))
  have hcoord : coord F ∈ S := Algebra.subset_adjoin (Or.inl rfl)
  have hconst : ∀ a : F, algebraMap F (Ring F) a ∈ S := by
    intro a
    rw [← (Module.finBasis k F).sum_repr a, map_sum]
    refine Subalgebra.sum_mem _ fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul]
    refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    have : algebraMap F (Ring F) (algebraMap k F ((Module.finBasis k F).repr a i)) =
        algebraMap (Ring k) (Ring F) (algebraMap k[X] (Ring k) (C ((Module.finBasis k F).repr a i)))
        := by
      change _ = kummerMap k F n _
      rw [kummerMap_C k F n, IsScalarTower.algebraMap_apply F F[X] (Ring F),
        Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  have hpoly : ∀ p : F[X], algebraMap F[X] (Ring F) p ∈ S := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
    | monomial i a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hcoord _)
      have h := hconst a
      rwa [IsScalarTower.algebraMap_apply F F[X] (Ring F), ← Polynomial.C_eq_algebraMap] at h
  have hinv : ((isUnit_coord F).unit⁻¹ : (Ring F)ˣ).1 ∈ S := by
    have hx : coord F * (coord F ^ (n - 1) *
        kummerMap k F n (IsLocalization.Away.invSelf (X : k[X]))) = 1 := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, ← kummerMap_coord k F n, ← map_mul,
        coord, IsLocalization.Away.mul_invSelf, map_one]
    have h : ((isUnit_coord F).unit⁻¹ : (Ring F)ˣ).1 = coord F ^ (n - 1) *
        algebraMap (Ring k) (Ring F) (IsLocalization.Away.invSelf (X : k[X])) :=
      Units.inv_eq_of_mul_eq_one_right (by rwa [IsUnit.unit_spec])
    rw [h]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hcoord _) (Subalgebra.algebraMap_mem _ _)
  refine eq_top_iff.mpr fun z _ ↦ ?_
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (X : F[X])) z
  obtain ⟨m, hm⟩ := s.2
  rw [IsLocalization.mk'_eq_mul_mk'_one, mk'_one_X_pow F m s hm.symm]
  exact Subalgebra.mul_mem _ (hpoly p) (Subalgebra.pow_mem _ hinv _)

end Algebra

/-- On constants, the Kummer map restricts to the inclusion `k ⊆ F`. -/
theorem kummerMap_comp_algebraMap :
    (kummerMap k F n).comp (algebraMap k (Ring k)) =
      (algebraMap F (Ring F)).comp (algebraMap k F) := by
  ext a
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k k[X] (Ring k), ← C_eq_algebraMap,
    kummerMap_C, RingHom.comp_apply, IsScalarTower.algebraMap_apply F F[X] (Ring F),
    ← C_eq_algebraMap]

/-- Evaluating `p ∈ k[X]` at a constant `a ∈ F` of `F[X]_X` through the Kummer map gives the
constant `p(a)`. -/
theorem eval₂_const_map (p : k[X]) (a : F) :
    p.eval₂ ((kummerMap k F n).comp (algebraMap k (Ring k))) (algebraMap F (Ring F) a) =
      algebraMap F (Ring F) (p.eval₂ (algebraMap k F) a) := by
  rw [kummerMap_comp_algebraMap, ← hom_eval₂]

/-- Evaluating the base change of `q ∈ k[X]` at a constant of `F[X]_X` gives a constant. -/
private theorem aeval_map_const (q : k[X]) (a : F) :
    letI := (kummerMap k F n).toAlgebra
    aeval (algebraMap F (Ring F) a) (q.map (algebraMap k (Ring k))) =
      algebraMap F (Ring F) (aeval a q) := by
  let := (kummerMap k F n).toAlgebra
  rw [aeval_def, eval₂_map]
  exact eval₂_const_map k F n q a

section Etale

variable [FiniteDimensional k F]

/-- Every constant `a ∈ F` of `F[X]_X` is integral over `k[x]_x` via the Kummer map. -/
theorem isIntegral_const (a : F) :
    letI := (kummerMap k F n).toAlgebra
    _root_.IsIntegral (Ring k) (algebraMap F (Ring F) a) := by
  let := (kummerMap k F n).toAlgebra
  obtain ⟨g, hg, hga⟩ := Algebra.IsIntegral.isIntegral (R := k) a
  refine ⟨g.map (algebraMap k (Ring k)), hg.map _, ?_⟩
  rw [← aeval_def, aeval_map_const, aeval_def, hga, map_zero]

omit [FiniteDimensional k F] in
/-- For `n > 0`, the coordinate `X` of `F[X]_X` is integral over `k[x]_x` via the Kummer map. -/
theorem isIntegral_coord (hn : 0 < n) :
    letI := (kummerMap k F n).toAlgebra
    _root_.IsIntegral (Ring k) (coord F) := by
  let := (kummerMap k F n).toAlgebra
  refine ⟨X ^ n - C (coord k), monic_X_pow_sub_C _ hn.ne', ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C]
  change coord F ^ n - kummerMap k F n (coord k) = 0
  rw [kummerMap_coord, sub_self]

/-- **The Kummer map is finite.** -/
theorem kummerMap_finite (hn : 0 < n) : (kummerMap k F n).Finite := by
  let := (kummerMap k F n).toAlgebra
  have hint : ∀ x ∈ ({coord F} ∪ Set.range
      (fun i ↦ algebraMap F (Ring F) (Module.finBasis k F i))), _root_.IsIntegral (Ring k) x := by
    rintro x (hx | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx]
      exact isIntegral_coord k F n hn
    · exact isIntegral_const k F n _
  have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_singleton _).union (Set.finite_range _)) hint
  rw [adjoin_coord_basis_eq_top k F n hn] at hfin
  exact RingHom.finite_algebraMap.mpr (Module.Finite.equiv Subalgebra.topEquiv.toLinearEquiv)

/-- **The Kummer map is formally unramified** when `n ≥ 1` is invertible in `k` and `F / k` is
finite separable. -/
theorem kummerMap_formallyUnramified [Algebra.IsSeparable k F] (hn : IsUnit (n : k)) (hn0 : 0 < n) :
    letI := (kummerMap k F n).toAlgebra
    Algebra.FormallyUnramified (Ring k) (Ring F) := by
  let := (kummerMap k F n).toAlgebra
  refine ⟨?_⟩
  set D := KaehlerDifferential.D (Ring k) (Ring F)
  have hD : D = 0 := by
    apply Derivation.ext_of_adjoin_eq_top _ (adjoin_coord_basis_eq_top k F n hn0)
    rintro x (hx | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx, Derivation.zero_apply]
      have h1 : D (coord F ^ n) = 0 := by
        rw [← kummerMap_coord k F n]
        exact D.map_algebraMap _
      rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Ring F), smul_smul] at h1
      have hu : IsUnit ((n : Ring F) * coord F ^ (n - 1)) := by
        refine IsUnit.mul ?_ ((isUnit_coord F).pow _)
        have := hn.map (algebraMap k (Ring F))
        rwa [map_natCast] at this
      exact (hu.smul_eq_zero).mp h1
    · rw [Derivation.zero_apply]
      set a := Module.finBasis k F i
      have h1 : D (aeval (algebraMap F (Ring F) a)
          ((minpoly k a).map (algebraMap k (Ring k)))) = 0 := by
        rw [aeval_map_const, minpoly.aeval, map_zero, map_zero]
      rw [Derivation.map_aeval, derivative_map, aeval_map_const] at h1
      have hu : IsUnit (algebraMap F (Ring F) (aeval a (derivative (minpoly k a)))) :=
        (isUnit_iff_ne_zero.mpr ((Algebra.IsSeparable.isSeparable k a).aeval_derivative_ne_zero
          (minpoly.aeval k a))).map _
      exact (hu.smul_eq_zero).mp h1
  have htop : (⊤ : Submodule (Ring F) Ω[Ring F⁄Ring k]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation (Ring k) (Ring F), Submodule.span_eq_bot]
    rintro _ ⟨y, rfl⟩
    change D y = 0
    rw [hD, Derivation.zero_apply]
  exact (Submodule.subsingleton_iff (Ring F)).mp (subsingleton_of_bot_eq_top htop.symm)

/-- The ring `k[x]_x` is a Dedekind domain. -/
theorem isDedekindDomain_ring : IsDedekindDomain (Ring k) :=
  IsLocalization.isDedekindDomain k[X] (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)
    (Ring k)

omit [FiniteDimensional k F] in
/-- The Kummer map makes `F[X]_X` a flat `k[x]_x`-module. -/
theorem kummerMap_flat (hn0 : 0 < n) :
    letI := (kummerMap k F n).toAlgebra
    Module.Flat (Ring k) (Ring F) := by
  let := (kummerMap k F n).toAlgebra
  have := isDedekindDomain_ring k
  have : Module.IsTorsionFree (Ring k) (Ring F) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (kummerMap_injective k F hn0)
  infer_instance

/-- **The Kummer map is étale** when `n ≥ 1` is invertible in `k` and `F / k` is finite
separable. -/
theorem kummerMap_etale [Algebra.IsSeparable k F] (hn : IsUnit (n : k)) (hn0 : 0 < n) :
    (kummerMap k F n).Etale := by
  let := (kummerMap k F n).toAlgebra
  have := isDedekindDomain_ring k
  have : Module.Finite (Ring k) (Ring F) :=
    RingHom.finite_algebraMap.mp (kummerMap_finite k F n hn0)
  have : Algebra.FinitePresentation (Ring k) (Ring F) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have := kummerMap_flat k F n hn0
  have := kummerMap_formallyUnramified k F n hn hn0
  exact RingHom.etale_algebraMap.mpr Algebra.Etale.of_formallyUnramified_of_flat

/-- **The Kummer cover** `K_{n,F} = Spec F[X]_X ⟶ 𝐆_{m,k}`, `x ↦ X^n`, as a finite étale cover. -/
@[sga "1 XIII 5.4" "special case"]
def kummerCover [Algebra.IsSeparable k F] (hn : IsUnit (n : k)) (hn0 : 0 < n) :
    FiniteEtaleOver (Gm k) :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (kummerMap k F n)))
    ⟨by rw [IsFinite.SpecMap_iff]; exact kummerMap_finite k F n hn0,
      by rw [HasRingHomProperty.Spec_iff (P := @Etale)]; exact kummerMap_etale k F n hn hn0⟩

end Etale

end AlgebraicGeometry.TameMultiplicativeGroup

end

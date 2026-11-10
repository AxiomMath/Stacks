module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreConjugationReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConclusionsPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyBlockRoots

/-!
# Purity of the fibres of the Fourier family at the closed points

The twisted representation `τ = σ' ⊗ χ` of a fibre of the Fourier family over `k'` is `ι'`-pure
of weight `β` at the closed points of `𝔸¹_{k'}` when `σ` is
(`Stacks.EtaleCohomology.laumonFibreTwistPurityInput`;
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the geometric Frobenius at a closed point
`y'` of `𝔸¹_{k'}` maps to a conjugate of the `e`-th power of the geometric Frobenius at its image
`y` in `U`
(`AlgebraicGeometry.exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow`,
`e = [κ(y') : κ(y)]`), so the roots of `σ'(F_{y'})` are `e`-th powers of roots of `σ(F_y)`, of
absolute value `(#κ(y) ^ e) ^ (β / 2) = #κ(y') ^ (β / 2)`; and `χ` takes values in the `p`-th roots
of unity `ψ(k')`, of absolute value `1`
(`Stacks.EtaleCohomology.exists_isRoot_of_isRoot_charpoly_smul`).

## Main results

* `Stacks.EtaleCohomology.exists_isRoot_of_isRoot_charpoly_smul`.
* `Stacks.EtaleCohomology.norm_map_addChar_eq_one`.
* `Stacks.EtaleCohomology.laumonFibreTwistPurityInput`.
* `Stacks.EtaleCohomology.laumonFibreReciprocityInput_of_duality_topVanishing`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Polynomial

universe u

namespace Stacks.EtaleCohomology

/-- **Roots of a scalar multiple of unit absolute value**: if `|ι c| = 1`, every complex root `z`
of the characteristic polynomial of `c • M` along `ι` has the absolute value of a root of that of
`M`, namely `z / ι c`. -/
public theorem exists_isRoot_of_isRoot_charpoly_smul {E : Type*} [Field E] (ι : E →+* ℂ) {m : ℕ}
    (c : E) (M : Matrix (Fin m) (Fin m) E) (hc : ‖ι c‖ = 1) {z : ℂ}
    (hz : ((c • M).charpoly.map ι).IsRoot z) :
    ∃ w : ℂ, (M.charpoly.map ι).IsRoot w ∧ ‖z‖ = ‖w‖ := by
  have hc0 : ι c ≠ 0 := fun h => by
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  refine ⟨z / ι c, ?_, by rw [norm_div, hc, div_one]⟩
  rw [Polynomial.IsRoot, ← Matrix.charpoly_map, Matrix.eval_charpoly] at hz ⊢
  have hmap : (c • M).map ι = ι c • M.map ι := by
    ext i j
    simp
  have hs : Matrix.scalar (Fin m) z - ι c • M.map ι =
      ι c • (Matrix.scalar (Fin m) (z / ι c) - M.map ι) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp only [Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · field_simp
    · simp
  rw [hmap, hs, Matrix.det_smul] at hz
  exact (mul_eq_zero.1 hz).resolve_left (pow_ne_zero _ hc0)

/-- **The values of an additive character of a field of characteristic `p` have absolute value
`1`** along any `ι`: they are `p`-th roots of unity. -/
public theorem norm_map_addChar_eq_one {k' E : Type*} [Field k'] [Field E] (p : ℕ) [Fact p.Prime]
    [CharP k' p] (ι : E →+* ℂ) (ψ : AddChar k' E) (t : k') : ‖ι (ψ t)‖ = 1 := by
  have h : ψ t ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
      AddChar.map_zero_eq_one]
  have h' : ‖ι (ψ t)‖ ^ p = 1 := by
    rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Fact.out : p.Prime).ne_zero).1 h'

/-- `𝔸¹_{k'} → 𝔸¹_k` is locally of finite type, for `k'` finite over `k`. -/
theorem locallyOfFiniteType_specMap_mapRingHom (k k' : Type u) [Field k] [Field k'] [Finite k']
    [Algebra k k'] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k')))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  refine RingHom.FiniteType.of_comp_finiteType (f := (Polynomial.C : k →+* Polynomial k)) ?_
  have h : (Polynomial.mapRingHom (algebraMap k k')).comp Polynomial.C =
      algebraMap k (Polynomial k') := by
    refine RingHom.ext fun a => ?_
    simp [Polynomial.algebraMap_apply]
  rw [CommRingCat.hom_ofHom, h]
  have : Module.Finite k k' := Module.Finite.of_finite
  exact RingHom.finiteType_algebraMap.2 (Algebra.FiniteType.trans (S := k') inferInstance
    inferInstance)

/-- **Purity of the fibres of the Fourier family at the closed points**:
`Stacks.EtaleCohomology.LaumonFibreTwistPurityInput` holds. -/
public theorem laumonFibreTwistPurityInput : LaumonFibreTwistPurityInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β _ hpure ψ hψ n₀ k' _ _ _ hX' _ _ x' hx' a c p₀ hτ _ _ _ j' kbar' _
    _ _ p' n' _ _ hcard' y z hz
  subst hx'
  have := locallyOfFiniteType_specMap_mapRingHom k k'
  let g : Spec (.of (Polynomial k')) ⟶ U.1 := Spec.map (CommRingCat.ofHom
    (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e
  let f' : Spec (.of (Polynomial k')) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))
  have hy : g.base y.1 ∈ closedPoints U.1 := by
    have : JacobsonSpace U.1 := LocallyOfFiniteType.jacobsonSpace f
    exact g.closedPoints_subset_preimage_closedPoints y.2
  rw [characterTwist_val] at hz
  obtain ⟨w, hw, hzw⟩ := exists_isRoot_of_isRoot_charpoly_smul ι' _ _ (by
    rw [Stacks.ArtinSchreier.artinSchreierCharacter_apply]
    exact norm_map_addChar_eq_one p' ι' _ _) hz
  obtain ⟨h, hh⟩ := exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow g x' y hy
    f f'
  change ((((σ (etaleFundamentalGroupMap g x' (geometricFrobeniusFamily f' x' y)) :
    GL (Fin m) E) : Matrix (Fin m) (Fin m) E).charpoly.map ι').IsRoot w) at hw
  rw [hh, map_mul, map_mul, map_inv, charpoly_conj_val, map_pow, Units.val_pow_eq_pow_val,
    ← Matrix.charpoly_toLin', Matrix.toLin'_pow] at hw
  have := finite_residueField f' y.1 y.2
  have := finite_residueField f (g.base y.1) hy
  obtain ⟨v, hv, rfl⟩ := exists_isRoot_charpoly_map_pow_eq ι' _
    (residueFieldMapDegree_ne_zero g y) hw
  rw [Matrix.charpoly_toLin'] at hv
  have hvn := hpure ⟨g.base y.1, hy⟩ v hv
  have key : ∀ Q D r : ℕ, (((Q : ℕ) : ℝ) ^ (((D : ℤ) * β : ℝ) / 2)) ^ r =
      (((Q ^ (D * r) : ℕ)) : ℝ) ^ ((β : ℝ) / 2) := by
    intro Q D r
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Nat.cast_pow,
      ← Real.rpow_natCast (Q : ℝ) (D * r), ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  have hnat : (p ^ n) ^ (residueDegree f (g.base y.1) * residueFieldMapDegree g y) =
      (p' ^ n') ^ (residueDegree f' y.1 * 1) := by
    have h₁ := natCard_residueField_eq (p := p) (n := n) (f := f) (y := ⟨g.base y.1, hy⟩) hcard
    have h₂ := natCard_residueField_eq (p := p') (n := n') (f := f') (y := y) hcard'
    let := (g.residueFieldMap y.1).hom.toAlgebra
    have : Module.Finite (U.1.residueField (g.base y.1))
        ((Spec (.of (Polynomial k'))).residueField y.1) := Module.Finite.of_finite
    have h₃ := Module.natCard_eq_pow_finrank (K := U.1.residueField (g.base y.1))
      (V := (Spec (.of (Polynomial k'))).residueField y.1)
    rw [mul_one, ← pow_mul, ← pow_mul, ← h₂]
    rw [show n * (residueDegree f (g.base y.1) * residueFieldMapDegree g y) =
      n * residueDegree f (g.base y.1) * residueFieldMapDegree g y by ring, pow_mul, ← h₁, h₃]
    rfl
  have hR : ((p' ^ n' : ℕ) : ℝ) ^ (((residueDegree f' y.1 : ℤ) * β : ℝ) / 2) =
      (((p' ^ n') ^ (residueDegree f' y.1 * 1) : ℕ) : ℝ) ^ ((β : ℝ) / 2) := by
    rw [← key, pow_one]
  rw [hzw, norm_pow, hvn, key, hR, hnat]

/-- **The duality with complex conjugation `Stacks.EtaleCohomology.LaumonFibreReciprocityInput`
from Poincaré duality on the fibres and the vanishing of `H²_c`**: the purity of the fibres is
`Stacks.EtaleCohomology.laumonFibreTwistPurityInput`. -/
public theorem laumonFibreReciprocityInput_of_duality_topVanishing
    (hPD : LaumonFibreDualityInput.{u}) (hvan : LaumonFibreTopVanishingInput.{u}) :
    LaumonFibreReciprocityInput.{u} :=
  laumonFibreReciprocityInput_of_duality_conjugation hPD
    (laumonFibreConjugationInput_of_purity_vanishing laumonFibreTwistPurityInput hvan)

end Stacks.EtaleCohomology

end

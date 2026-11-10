module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.LinearAlgebra.Matrix.Minor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.ZeroScheme
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.Defs

/-!
# Jacobian minors and the vanishing of differentials

Let `g₁, …, g_m` be polynomials in `n` variables over `R` whose Jacobian has rank `n` at a prime
`q` containing them, and let `B = R[x₁, …, x_n]/(g₁, …, g_m)`. Choosing `n` of the equations gives
a maximal minor of the Jacobian, and the full-rank hypothesis says that one such minor does not
lie in `q`. After inverting the image of that minor in `B`, the module of relative Kähler
differentials over `R` vanishes.

## Main definitions

* `AlgebraicGeometry.FullRankJacobianSystem.jacobianMinor` is the determinant of the submatrix
  of the Jacobian selecting `n` of the equations.

## Main results

* `AlgebraicGeometry.FullRankJacobianSystem.exists_jacobianMinor_differentials_subsingleton`
  produces a maximal minor outside the prime whose inversion kills all relative differentials.

## Implementation notes

The vanishing `Ω = 0` is recorded as a `Subsingleton` instance on the module of differentials.
The selected element is a determinant in the polynomial ring, while the localization is taken at
its canonical image in the quotient. The key input is that the ideal of maximal minors of a
matrix annihilates the cokernel of that matrix, in the form
`Matrix.exists_mul_eq_smul_one_of_mem_minorIdeal`, applied to the conormal sequence of the
presentation of `B`.

## References

* [Stacks Project, Tag 024Y](https://stacks.math.columbia.edu/tag/024Y)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

noncomputable section

namespace FullRankJacobianSystem

variable {R : Type u} [CommRing R] {n m : ℕ}

/-- The maximal Jacobian minor of a polynomial system formed by the chosen `n` equations and all
`n` variables. -/
public def jacobianMinor (S : FullRankJacobianSystem R n m) (rows : Fin n ↪ Fin m) :
    MvPolynomial (Fin n) R :=
  (Matrix.of fun i j : Fin n =>
    MvPolynomial.pderiv j (S.equations (rows i))).det

/-- A ring map sends a maximal Jacobian minor to the determinant of the mapped submatrix. -/
private theorem det_submatrix_eq_map_jacobianMinor (S : FullRankJacobianSystem R n m)
    (rows : Fin n ↪ Fin m) {A : Type*} [CommRing A] (φ : MvPolynomial (Fin n) R →+* A)
    (M : Matrix (Fin m) (Fin n) A) (hM : ∀ i j, M i j = φ (MvPolynomial.pderiv j (S.equations i))) :
    (M.submatrix rows id).det = φ (jacobianMinor S rows) := by
  rw [jacobianMinor, RingHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun i j => hM (rows i) j)

/-- A Jacobian of rank `n` at a prime has a maximal minor that does not lie in that prime. -/
private theorem exists_jacobianMinor_notMem_prime (S : FullRankJacobianSystem R n m) :
    ∃ rows : Fin n ↪ Fin m, jacobianMinor S rows ∉ S.prime := by
  classical
  let K := S.prime.ResidueField
  let M : Matrix (Fin m) (Fin n) K := fun i j =>
    algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.pderiv j (S.equations i))
  have hrank : Module.finrank K (Submodule.span K (Set.range M.row)) = n := by
    rw [← Matrix.rank_eq_finrank_span_row M]
    exact S.jacobian_rank
  obtain ⟨f₀, hfmem₀, hfspan, hli₀⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := K) (s := Set.range M.row)
  let e : Fin n ≃ Fin (Module.finrank K (Submodule.span K (Set.range M.row))) :=
    finCongr hrank.symm
  let f : Fin n → (Fin n → K) := fun i => f₀ (e i)
  have hfmem : ∀ i, f i ∈ Set.range M.row := fun i => hfmem₀ (e i)
  have hli : LinearIndependent K f := hli₀.comp e e.injective
  let r : Fin n → Fin m := fun i => Classical.choose (hfmem i)
  have hfr : ∀ i, f i = M.row (r i) := fun i => (Classical.choose_spec (hfmem i)).symm
  have hrinj : Function.Injective r := fun i j hij => hli.injective (by simp [hfr, hij])
  let rows : Fin n ↪ Fin m := ⟨r, hrinj⟩
  have hli' : LinearIndependent K (fun i : Fin n => M.row (rows i)) := by
    convert hli using 1
    funext i
    exact (hfr i).symm
  have hdet : (M.submatrix rows id).det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hli')
  have heq := det_submatrix_eq_map_jacobianMinor S rows
    (algebraMap (MvPolynomial (Fin n) R) K) M fun _ _ => rfl
  refine ⟨rows, fun hmem => hdet ?_⟩
  rw [heq]
  exact (Ideal.algebraMap_residueField_eq_zero (I := S.prime)
    (x := jacobianMinor S rows)).2 hmem

/-- The image in `B = R[x]/(g)` of a maximal Jacobian minor annihilates `Ω[B⁄R]`. -/
private theorem jacobianMinor_smul_eq_zero (S : FullRankJacobianSystem R n m)
    (rows : Fin n ↪ Fin m)
    (x : Ω[(MvPolynomial (Fin n) R ⧸ S.equationIdeal)⁄R]) :
    Ideal.Quotient.mk S.equationIdeal (jacobianMinor S rows) • x = 0 := by
  classical
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := S.equationIdeal
  let B := P ⧸ I
  let d : B := Ideal.Quotient.mk I (jacobianMinor S rows)
  let J := RingHom.ker (algebraMap P B)
  have hsurj : Function.Surjective (algebraMap P B) := Ideal.Quotient.mk_surjective
  have hJI : J = I := Ideal.mk_ker (I := I)
  let := ConormalSeq.cotangentModule hsurj
  let basis := (KaehlerDifferential.mvPolynomialBasis R (Fin n)).baseChange B
  let coords := basis.equivFun
  let map := KaehlerDifferential.mapBaseChange R P B
  let ψ : (Fin n → B) →ₗ[B] Ω[B⁄R] := map.comp coords.symm.toLinearMap
  let cmap := ConormalSeq.conormalMap R hsurj
  let q : J.Cotangent →ₗ[B] (Fin n → B) := coords.toLinearMap.comp cmap
  have hmemJ (i : Fin m) : S.equations i ∈ J := by
    rw [hJI]; exact S.equations_mem_equationIdeal i
  let cgen (i : Fin m) : J.Cotangent := J.toCotangent ⟨S.equations i, hmemJ i⟩
  let jac : Matrix (Fin m) (Fin n) B := fun i j =>
    algebraMap P B (MvPolynomial.pderiv j (S.equations i))
  have hqgen (i : Fin m) : q (cgen i) = jac.row i := by
    funext j
    change (basis.repr (cmap (cgen i))) j = jac i j
    rw [show cmap (cgen i) = (1 : B) ⊗ₜ[P] KaehlerDifferential.D R P (S.equations i) from
      ConormalSeq.conormalMap_toCotangent R hsurj ⟨S.equations i, hmemJ i⟩]
    rw [Module.Basis.baseChange_repr_tmul,
      KaehlerDifferential.mvPolynomialBasis_repr_apply,
      Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
    rfl
  have hψq (z : J.Cotangent) : ψ (q z) = 0 := by
    change map (coords.symm (coords (cmap z))) = 0
    rw [coords.symm_apply_apply]
    have hrange := (ConormalSeq.conormal_exact_sequence R P B hsurj).1
    change cmap z ∈ (LinearMap.ker map).restrictScalars B
    rw [← hrange]
    exact ⟨z, rfl⟩
  have hmem : algebraMap P B (jacobianMinor S rows) ∈ jac.minorIdeal := by
    rw [← det_submatrix_eq_map_jacobianMinor S rows (algebraMap P B) jac fun _ _ => rfl]
    exact Matrix.det_submatrix_mem_minorIdeal jac rows
  obtain ⟨L, hL⟩ := Matrix.exists_mul_eq_smul_one_of_mem_minorIdeal hmem
  have hrowkill (i : Fin m) : ψ (jac.row i) = 0 := by
    rw [← hqgen i]; exact hψq (cgen i)
  have hkillBasis (j : Fin n) : ψ (d • Pi.single j (1 : B)) = 0 := by
    have hcomb : (∑ i : Fin m, L j i • jac.row i) = d • Pi.single j (1 : B) := by
      refine funext fun k => ?_
      have hk := congrArg (fun A : Matrix (Fin n) (Fin n) B => A j k) hL
      change (∑ x : Fin m, L j x * jac x k) = _ at hk
      rw [Ideal.Quotient.algebraMap_eq] at hk
      simpa [Matrix.row, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply, d,
        jac, eq_comm] using hk
    rw [← hcomb]
    simp only [map_sum, map_smul, hrowkill, smul_zero, Finset.sum_const_zero]
  have hsurjψ : Function.Surjective ψ := fun y => by
    obtain ⟨z, hz⟩ := KaehlerDifferential.mapBaseChange_surjective R P B hsurj y
    refine ⟨coords z, ?_⟩
    change map (coords.symm (coords z)) = y
    simpa [map, ψ] using hz
  obtain ⟨v, rfl⟩ := hsurjψ x
  have hv : d • v = ∑ j : Fin n, v j • (d • Pi.single j (1 : B)) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [show d • ψ v = ψ (d • v) from (map_smul ψ d v).symm, hv, map_sum]
  simp [map_smul, hkillBasis]

/-- A Jacobian of rank `n` at a prime has a maximal minor outside that prime such that the
relative differentials of the quotient vanish once that minor is inverted. -/
public theorem exists_jacobianMinor_differentials_subsingleton
    (S : FullRankJacobianSystem R n m) :
    ∃ rows : Fin n ↪ Fin m, jacobianMinor S rows ∉ S.prime ∧
      Subsingleton (Ω[(Localization.Away
        (Ideal.Quotient.mk S.equationIdeal (jacobianMinor S rows)))⁄R]) := by
  classical
  obtain ⟨rows, hnot⟩ := exists_jacobianMinor_notMem_prime S
  refine ⟨rows, hnot, ?_⟩
  let B := MvPolynomial (Fin n) R ⧸ S.equationIdeal
  let d : B := Ideal.Quotient.mk S.equationIdeal (jacobianMinor S rows)
  let Bₛ := Localization.Away d
  let f : Ω[B⁄R] →ₗ[B] Ω[Bₛ⁄R] := KaehlerDifferential.map R R B Bₛ
  have hf : IsLocalizedModule (.powers d) f := omega_localization_total R B (.powers d) Bₛ
  have hkill (s : Submonoid.powers d) (w : Ω[Bₛ⁄R]) (hw : s • w = 0) : w = 0 :=
    ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
      (by simpa [Module.algebraMap_end_apply, Submonoid.smul_def] using hw)
  have hmapzero (y : Ω[B⁄R]) : f y = 0 :=
    hkill ⟨d, Submonoid.mem_powers d⟩ _
      (by simpa [f, map_smul] using congrArg f (jacobianMinor_smul_eq_zero S rows y))
  have hz (y : Ω[Bₛ⁄R]) : y = 0 := by
    obtain ⟨⟨z, s⟩, hs⟩ := hf.surj y
    exact hkill s y (by rw [hs, hmapzero])
  exact ⟨fun y z => by rw [hz y, hz z]⟩

end FullRankJacobianSystem

end

end AlgebraicGeometry

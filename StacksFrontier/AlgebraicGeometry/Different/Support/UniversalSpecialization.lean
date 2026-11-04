module

public import StacksFrontier.AlgebraicGeometry.Different.Support.UniversalPolynomialPresentation
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamily
public import StacksFrontier.AlgebraicGeometry.Different.Support.EtaleDiscreteFibres

/-!
# A nonempty étale fibre of the universal quasi-finite family

Specializing each universal polynomial of the family `Y_{n,d} → X_{n,d}` to `xᵢ ^ d - 1` gives a
fibre over a `ℚ`-point of the coefficient scheme which is nonzero and étale over `ℚ`. Every point
of that fibre lies in the universal quasi-finite open, so the open is nonempty — which is what
makes `Y_{n,d}` irreducible.

## Main definitions

* `AlgebraicGeometry.specialization` is the coefficient specialization to `ℚ`.
* `AlgebraicGeometry.specializedFiberRing` is the base-changed universal quotient ring.

## Main results

* `AlgebraicGeometry.specialization_universalPolynomial` identifies the specialized equations.
* `AlgebraicGeometry.specializedFiberRing_nontrivial` says the fibre is nonzero.
* `AlgebraicGeometry.specializedFiberRing_etale` says it is étale over `ℚ`.
* `AlgebraicGeometry.specializedFiberRing_mem_universalQuasiFiniteOpen` places all of its points
  in the universal quasi-finite open.

## Implementation notes

The coefficient of `xᵢ ^ d` is specialized to `1`, the constant coefficient to `-1`, and all
others to zero, so that the `i`th equation becomes `xᵢ ^ d - 1`. The fibre is represented by the
tensor product of the universal quotient algebra with `ℚ` over the coefficient ring, and its
points map to the ambient universal scheme through the inclusion of the left tensor factor.

Étaleness is obtained from a submersive presentation whose Jacobian is the diagonal matrix with
entries `d * xᵢ ^ (d - 1)`; that matrix is invertible because each `xᵢ` is a unit in the fibre,
being a `d`-th root of one, and `d` is invertible in `ℚ`.

## References

* [Stacks Project, Tag 0FK8](https://stacks.math.columbia.edu/tag/0FK8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

private def pureMultiIndex (n d : ℕ) (i : Fin n) : MultiIndex n d :=
  ⟨fun j ↦ if j = i then ⟨d, by omega⟩ else 0, by
    classical
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp⟩

private lemma multiIndexExponent_zero (n d : ℕ) :
    multiIndexExponent n d (zeroMultiIndex n d) = 0 := by
  ext i
  simp [multiIndexExponent, zeroMultiIndex]

private lemma multiIndexExponent_pure (n d : ℕ) (i : Fin n) :
    multiIndexExponent n d (pureMultiIndex n d i) = Finsupp.single i d := by
  classical
  ext j
  by_cases h : j = i <;> simp [multiIndexExponent, pureMultiIndex, h]

/-- Coefficient specialization sending the `i`th universal polynomial to `xᵢ ^ d - 1`. -/
def specialization (n d : ℕ) [NeZero n] [NeZero d] :
    universalCoefficientRing n d →+* ℚ :=
  (MvPolynomial.aeval fun (iE : Fin n × MultiIndex n d) ↦
    if multiIndexExponent n d iE.2 = Finsupp.single iE.1 d then
      (1 : ℚ)
    else if multiIndexExponent n d iE.2 = 0 then
      (-1 : ℚ)
    else 0).toRingHom

/-- `ℚ` as an algebra over the universal coefficient ring through `specialization`. -/
instance specializationAlgebra (n d : ℕ) [NeZero n] [NeZero d] :
    Algebra (universalCoefficientRing n d) ℚ :=
  (specialization n d).toAlgebra

/-- The fibre of the universal quotient algebra over the `ℚ`-point `specialization`: the tensor
product of the universal quotient ring with `ℚ` over the universal coefficient ring. -/
abbrev specializedFiberRing (n d : ℕ) [NeZero n] [NeZero d] :=
  TensorProduct (universalCoefficientRing n d)
    (universalQuotientRing n d) ℚ

/-- The specialized fibre is a commutative ring, as a tensor product of commutative algebras. -/
instance specializedFiberCommRing (n d : ℕ) [NeZero n] [NeZero d] :
    CommRing (specializedFiberRing n d) := by
  unfold specializedFiberRing
  exact Algebra.TensorProduct.instCommRing
    (R := universalCoefficientRing n d)
    (A := universalQuotientRing n d) (B := ℚ)

/-- The specialized fibre is a `ℚ`-algebra through its right tensor factor. -/
instance specializedFiberAlgebra (n d : ℕ) [NeZero n] [NeZero d] :
    Algebra ℚ (specializedFiberRing n d) :=
  Algebra.TensorProduct.rightAlgebra

private noncomputable def universalPresentation (n d : ℕ) [NeZero n] [NeZero d] :
    Algebra.Presentation (universalCoefficientRing n d)
      (universalQuotientRing n d) (Fin n) (Fin n) :=
  Algebra.Presentation.naive

private instance baseChangedTensorCommRing (n d : ℕ) [NeZero n] [NeZero d] :
    CommRing (TensorProduct (universalCoefficientRing n d) ℚ
      (universalQuotientRing n d)) :=
  Algebra.TensorProduct.instCommRing
    (R := universalCoefficientRing n d)
    (A := ℚ) (B := universalQuotientRing n d)

private noncomputable def baseChangedPresentation (n d : ℕ) [NeZero n] [NeZero d] :
    Algebra.Presentation ℚ
      (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) (Fin n) (Fin n) :=
  (universalPresentation n d).baseChange ℚ

private def evalAtOnes (n : ℕ) : MvPolynomial (Fin n) ℚ →+* ℚ :=
  MvPolynomial.eval fun _ ↦ 1

/-- Under the coefficient specialization, the `i`th equation becomes `xᵢ ^ d - 1`. -/
theorem specialization_universalPolynomial
    (n d : ℕ) [NeZero n] [NeZero d] (i : Fin n) :
    MvPolynomial.map (specialization n d) (universalPolynomial n d i) =
      MvPolynomial.X i ^ d - 1 := by
  classical
  simp only [universalPolynomial, map_sum, MvPolynomial.map_monomial]
  -- The coefficient specialization keeps precisely the constant and `xᵢ^d` terms.
  simp only [specialization, universalCoefficient, MvPolynomial.aeval_X,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have hsingle : ∀ E : MultiIndex n d,
      (multiIndexExponent n d E = Finsupp.single i d) ↔ E = pureMultiIndex n d i :=
    fun _ ↦ (multiIndexExponent_injective n d).eq_iff' (multiIndexExponent_pure n d i)
  have hzero : ∀ E : MultiIndex n d,
      (multiIndexExponent n d E = 0) ↔ E = zeroMultiIndex n d :=
    fun _ ↦ (multiIndexExponent_injective n d).eq_iff' (multiIndexExponent_zero n d)
  have hpz : pureMultiIndex n d i ≠ zeroMultiIndex n d := by
    intro h
    have he := congrArg (fun m : Fin n →₀ ℕ => m i)
      (congrArg (multiIndexExponent n d) h)
    rw [multiIndexExponent_pure, multiIndexExponent_zero, Finsupp.single_apply] at he
    simp only [Finsupp.coe_zero, Pi.zero_apply] at he
    exact (NeZero.ne d) he
  simp_rw [hsingle, hzero]
  have hsplit (E : MultiIndex n d) :
      MvPolynomial.monomial (multiIndexExponent n d E)
          (if E = pureMultiIndex n d i then (1 : ℚ) else
            if E = zeroMultiIndex n d then -1 else 0) =
        (if E = pureMultiIndex n d i then
            MvPolynomial.monomial (multiIndexExponent n d E) (1 : ℚ) else 0) +
        (if E = zeroMultiIndex n d then
            MvPolynomial.monomial (multiIndexExponent n d E) (-1 : ℚ) else 0) := by
    by_cases hp : E = pureMultiIndex n d i <;>
      by_cases hz : E = zeroMultiIndex n d <;>
        simp [hp, hz, hpz, Ne.symm hpz]
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [multiIndexExponent_pure, multiIndexExponent_zero, ← MvPolynomial.X_pow_eq_monomial]
  simp only [MvPolynomial.monomial_zero']
  simp only [sub_eq_add_neg, MvPolynomial.C_neg, MvPolynomial.C_1]

private lemma baseChangedPresentation_relation (n d : ℕ) [NeZero n] [NeZero d]
    (i : Fin n) :
    (baseChangedPresentation n d).relation i = MvPolynomial.X i ^ d - 1 := by
  change MvPolynomial.map (algebraMap (universalCoefficientRing n d) ℚ)
      (universalPolynomial n d i) = _
  rw [show algebraMap (universalCoefficientRing n d) ℚ = specialization n d by rfl]
  exact specialization_universalPolynomial n d i

private noncomputable def baseChangedSubmersivePresentation (n d : ℕ)
    [NeZero n] [NeZero d] :
    Algebra.SubmersivePresentation ℚ
      (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) (Fin n) (Fin n) := by
  let P : Algebra.PreSubmersivePresentation ℚ
      (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) (Fin n) (Fin n) :=
    { __ := baseChangedPresentation n d
      map := id
      map_inj := Function.injective_id }
  refine { __ := P, jacobian_isUnit := ?_ }
  have hmat : P.jacobiMatrix = Matrix.diagonal
      (fun i : Fin n => (d : MvPolynomial (Fin n) ℚ) * MvPolynomial.X i ^ (d - 1)) := by
    ext i j
    rw [P.jacobiMatrix_apply, baseChangedPresentation_relation n d j]
    by_cases hij : i = j
    · subst j
      simp [P]
    · simp [P, hij]
  rw [P.jacobian_eq_jacobiMatrix_det, hmat, Matrix.det_diagonal, map_prod]
  refine IsUnit.prod_univ_iff.mpr fun i ↦ ?_
  have hrel : P.relation i = MvPolynomial.X i ^ d - 1 := baseChangedPresentation_relation n d i
  have hxrel : MvPolynomial.aeval P.val
      (MvPolynomial.X i ^ d - (1 : MvPolynomial (Fin n) ℚ)) = 0 := by
    rw [← hrel]
    exact P.aeval_val_relation i
  have hxpow : (P.val i) ^ d = 1 := by
    have hsub : (P.val i) ^ d -
        (1 : TensorProduct (universalCoefficientRing n d) ℚ
          (universalQuotientRing n d)) = 0 := by
      simpa using hxrel
    exact sub_eq_zero.mp hsub
  have hmul : P.val i * (P.val i) ^ (d - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos d), hxpow]
  have hxunit : IsUnit (P.val i) := isUnit_iff_exists_inv.mpr ⟨_, hmul⟩
  have hdunit : IsUnit (d : ℚ) := isUnit_iff_ne_zero.mpr (mod_cast NeZero.ne d)
  have hconst : algebraMap P.Ring
      (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) (d : P.Ring) =
      algebraMap ℚ (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) (d : ℚ) := by
    simp
  have hX : algebraMap P.Ring
      (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) (MvPolynomial.X i) = P.val i := by
    simp
  rw [map_mul, hconst, map_pow, hX]
  exact IsUnit.mul (hdunit.map (algebraMap ℚ _)) (hxunit.pow (d - 1))

/-- The specialized fibre is nonzero. -/
theorem specializedFiberRing_nontrivial (n d : ℕ) [NeZero n] [NeZero d] :
    Nontrivial (specializedFiberRing n d) := by
  let P := baseChangedPresentation n d
  have hker : P.ker ≤ RingHom.ker (evalAtOnes n) := by
    rw [← P.span_range_relation_eq_ker, Ideal.span_le]
    intro f hf
    rcases hf with ⟨i, rfl⟩
    rw [baseChangedPresentation_relation]
    simp [evalAtOnes]
  let f : P.Quotient →+* ℚ := Ideal.Quotient.lift P.ker (evalAtOnes n) hker
  let e : P.Quotient ≃+* specializedFiberRing n d :=
    P.quotientEquiv.toRingEquiv.trans
      (Algebra.TensorProduct.commRight (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)).toRingEquiv
  refine nontrivial_iff.mpr ⟨1, 0, fun h ↦ ?_⟩
  have h' : (1 : P.Quotient) = 0 := by
    simpa using congrArg e.symm h
  have hm := congrArg f h'
  simp only [f, evalAtOnes, map_one, map_zero] at hm
  exact one_ne_zero hm

/-- The specialized fibre is étale over `ℚ`. -/
theorem specializedFiberRing_etale (n d : ℕ) [NeZero n] [NeZero d] :
    Algebra.Etale ℚ (specializedFiberRing n d) := by
  let P := baseChangedSubmersivePresentation n d
  have hdim : P.dimension = 0 := by
    simp [Algebra.Presentation.dimension]
  have hsmooth : Algebra.IsStandardSmoothOfRelativeDimension 0 ℚ
      (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) :=
    P.isStandardSmoothOfRelativeDimension hdim
  have hEt : Algebra.Etale ℚ
      (TensorProduct (universalCoefficientRing n d) ℚ
        (universalQuotientRing n d)) :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr hsmooth
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.commRight (universalCoefficientRing n d) ℚ
      (universalQuotientRing n d))

/-- Every point of the specialized fibre lies in the universal quasi-finite open. -/
theorem specializedFiberRing_mem_universalQuasiFiniteOpen
    (n d : ℕ) [NeZero n] [NeZero d]
    (x : Spec (.of (specializedFiberRing n d))) :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom
        (R := universalCoefficientRing n d)
        (A := universalQuotientRing n d) (B := ℚ))) x ∈
      universalQuasiFiniteOpen n d := by
  classical
  let A := universalCoefficientRing n d
  let B := universalQuotientRing n d
  let F := specializedFiberRing n d
  let χ := specialization n d
  let φ : B →+* F := Algebra.TensorProduct.includeLeftRingHom
    (R := A) (A := B) (B := ℚ)
  let b : Spec (.of B) := Spec.map (CommRingCat.ofHom φ) x
  let f : Spec (.of B) ⟶ Spec (.of A) := universalAmbientMorphism n d
  apply (mem_universalQuasiFiniteOpen_iff n d b).2
  let p : PrimeSpectrum A := f b
  let _ : x.asIdeal.IsPrime := x.2
  let _ : p.asIdeal.IsPrime := p.2
  let κ := p.asIdeal.ResidueField
  have hmap : (algebraMap A F : A →+* F) =
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := ℚ)).toRingHom.comp χ := by
    change (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap A B)) = _
    rw [Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
    rfl
  have hkernel : p.asIdeal = RingHom.ker χ := by
    have hp : p.asIdeal = Ideal.comap (φ.comp (algebraMap A B)) x.asIdeal := rfl
    rw [hp]
    ext a
    have hscalar : φ (algebraMap A B a) =
        Algebra.TensorProduct.includeRight (R := A) (A := B) (B := ℚ) (χ a) := by
      change (algebraMap A F) a = _
      exact DFunLike.congr_fun hmap a
    change φ (algebraMap A B a) ∈ x.asIdeal ↔ χ a = 0
    rw [hscalar]
    constructor
    · intro ha
      by_contra hχ
      have hu : IsUnit (Algebra.TensorProduct.includeRight
          (R := A) (A := B) (B := ℚ) (χ a)) :=
        (isUnit_iff_ne_zero.mpr hχ).map
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := ℚ)).toRingHom
      exact x.asIdeal.notMem_of_isUnit hu ha
    · intro ha
      simp [ha]
  have hcomp : p.asIdeal.primeCompl ≤
      (IsUnit.submonoid ℚ).comap χ := by
    intro a ha
    exact isUnit_iff_ne_zero.mpr fun hzero ↦ ha (by rw [hkernel]; exact hzero)
  let ρκ : κ →+* ℚ := Ideal.ResidueField.lift p.asIdeal χ
    (by rw [hkernel]) hcomp
  let _ : Algebra κ ℚ := ρκ.toAlgebra
  let _ : IsScalarTower A κ ℚ :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      change χ a = ρκ (algebraMap A κ a)
      exact (Ideal.ResidueField.lift_algebraMap p.asIdeal χ
        (by rw [hkernel]) hcomp a).symm)
  let S := p.asIdeal.Fiber B
  let _ : CommRing S := by
    change CommRing (TensorProduct A p.asIdeal.ResidueField B)
    exact Algebra.TensorProduct.instCommRing
      (R := A) (A := p.asIdeal.ResidueField) (B := B)
  let _ : Algebra κ S := by
    change Algebra κ (TensorProduct A p.asIdeal.ResidueField B)
    exact Algebra.TensorProduct.leftAlgebra
  let ebase : TensorProduct κ ℚ S ≃ₐ[ℚ] F := by
    let e₁ : TensorProduct A (TensorProduct κ ℚ κ) B ≃ₐ[ℚ]
        TensorProduct A ℚ B :=
      Algebra.TensorProduct.congr (Algebra.TensorProduct.rid κ ℚ ℚ)
        (AlgEquiv.refl : B ≃ₐ[A] B)
    exact (Algebra.TensorProduct.assoc A κ ℚ ℚ κ B).symm.trans <|
      e₁.trans (Algebra.TensorProduct.commRight A ℚ B)
  have hEtBase : Algebra.Etale ℚ (TensorProduct κ ℚ S) := by
    let _ : Algebra.Etale ℚ F := specializedFiberRing_etale n d
    exact Algebra.Etale.of_equiv ebase.symm
  have hFF : Module.FaithfullyFlat κ ℚ := by
    apply Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hEtFiber : Algebra.Etale κ S :=
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (R := κ) (S := S) ℚ
  let g : Spec (.of S) ⟶ Spec (.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ S))
  have _ : Etale g :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).mpr hEtFiber)
  have hdisc : DiscreteTopology (Spec (.of S)) := by
    let z : PrimeSpectrum κ := ⊥
    have hpoint (y : Spec (.of S)) : g y = z := by
      have _ : y.asIdeal.IsPrime := y.isPrime
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap κ S) y.asIdeal = ⊥
      have _ : (Ideal.comap (algebraMap κ S) y.asIdeal).IsPrime :=
        Ideal.comap_isPrime (algebraMap κ S) y.asIdeal
      exact Ideal.eq_bot_of_prime _
    have hpre : g ⁻¹' {z} = Set.univ := Set.eq_univ_of_forall hpoint
    let e := (g.fiberHomeo z).trans
      ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ _))
    exact e.discreteTopology_iff.mp (discreteTopology_fiber g z)
  let eFiber := (Spec.fiberToSpecResidueFieldIso A B p).hom.left.homeomorph
  let _ : LocallyOfFiniteType f := universalAmbientMorphism_locallyOfFiniteType n d
  have hi : IsIsolatedPoint (f.asFiber b) := by
    change IsOpen ({f.asFiber b} : Set (f.fiber p))
    let y := eFiber (f.asFiber b)
    have hy : IsOpen ({y} : Set (Spec (.of S))) :=
      (discreteTopology_iff_isOpen_singleton.mp hdisc) y
    have heq : eFiber ⁻¹' ({y} : Set (Spec (.of S))) =
        ({f.asFiber b} : Set (f.fiber p)) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        exact eFiber.injective (by simpa [y] using hz)
      · rintro rfl
        simp [y]
    rw [← heq]
    exact eFiber.isOpen_preimage.mpr hy
  exact (quasiFiniteAt_tfae f b).out 2 1 |>.mp hi

end AlgebraicGeometry

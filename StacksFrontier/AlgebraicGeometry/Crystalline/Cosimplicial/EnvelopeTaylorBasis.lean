module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorLevelCoefficients
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerEnvelope
public import StacksFrontier.RingTheory.DividedPowers.MultiIndexBinomial

/-!
# The divided power envelopes `D(1)` and `D(2)` as free modules over `D`

Let `P = A[x_i] → C` be a polynomial presentation and `E(n)` the divided power envelope of the
kernel `J(n)` of `P ⊗_A ⋯ ⊗_A P → C` (`n + 1` factors), so that the `p`-adically completed
envelope `D(n)` of [Stacks, Tag 07JF] is the completion of `E(n)`.  [Stacks, Lemma 60.17.5,
Tag 07L2] identifies `E(n)` with the divided power polynomial algebra over `E = E(0)` on the
variables `ξ_i(j) = x_i(0) - x_i(j)` (`Crystalline.tensorEnvelopeDPEquiv`).  This module reads off
what the proof of [Stacks, Lemma 60.17.3, Tag 07JG] uses of that identification:

* `E(1)` is free over `E(0)`, through the first coprojection `p₀`, on the divided power monomials
  `ξ^{[K]}`, `ξ_i = x_i ⊗ 1 - 1 ⊗ x_i` (`Crystalline.bijective_envelopeTaylorMonomial`);
* `E(2)` is free over `E(0)`, through the first coprojection `q₀`, on the monomials
  `v^{[K]} u^{[L]}` in `u_i = x_i ⊗ 1 ⊗ 1 - 1 ⊗ x_i ⊗ 1` and `v_i = 1 ⊗ x_i ⊗ 1 - 1 ⊗ 1 ⊗ x_i`
  (`Crystalline.bijective_envelopeTaylorMonomial₂`);
* the three cofaces `E(1) → E(2)` send `ξ^{[L]}` to `u^{[L]}`, `ξ^{[K]}` to `v^{[K]}` and
  `ξ^{[N]}` to `(u + v)^{[N]} = ∑_{K + L = N} v^{[K]} u^{[L]}`, and the diagonal `E(1) → E(0)`
  kills every `ξ^{[K]}` with `K ≠ 0`;
* the monomials multiply as divided power monomials;
* **Taylor's formula for the differential**: writing `p₁(y) = ∑_K p₀(δ_K y) ξ^{[K]}`, the divided
  power differential of `y ∈ E(0)` is `d y = - ∑_i δ_{e_i}(y) d x_i`
  (`Crystalline.dividedPowerDifferential_eq_neg_sum_envelopeTaylorCoeff`).

These are the ring-theoretic inputs of the Taylor coefficients of a crystal,
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorLevelCoefficients.lean`.

## Implementation notes

Through `Crystalline.tensorEnvelopeDPEquiv`, which is an isomorphism of divided power rings, the
monomials are products of divided powers `γ_k(ξ_i(j))` in `E(n)`, so the cofaces, the diagonal and
the products are computed from the renamings of the `x_i(j)` and the divided power binomial and
product formulas.  The first coprojection `E(0) → E(n)` is the coefficient map `E → E⟨ξ_i(j)⟩`
after `E(0) ≅ E`, by the uniqueness half of the universal property of `E`; freeness is then the
monomial basis of the divided power polynomial algebra, transported in degree two along the
linear change of variables `ξ_i(2) ↦ ξ_i(2) - ξ_i(1)`.  Taylor's formula is read off from the
divided power morphism `ψ : E(1) → E(0) ⊕ Ω_{E(0)}` with `ψ ∘ p₀ = (id, 0)` and
`ψ(ξ_i) = (0, -d x_i)`: it satisfies `ψ ∘ p₁ = (id, d)` and kills every `ξ^{[K]}` with `|K| ≥ 2`.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open CategoryTheory Simplicial DividedPowers

universe u v w

noncomputable section

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The reindexing map `E(m) → E(n)` of the envelopes along a map of `SimplexCategory`, as a ring
homomorphism. -/
abbrev envReindex {m n : SimplexCategory} (φ : m ⟶ n) :
    (tensorPowerEnvelope s f m.len).object →+* (tensorPowerEnvelope s f n.len).object :=
  (envelopeReindex s f φ).1.toRingHom

/-! ### The divided powers of the degree-one elements of a divided power polynomial algebra -/

/-- The degree-one element `dp 1 m` of a divided power polynomial algebra lies in its divided
power ideal. -/
private theorem embed_mem_dividedPowerPolynomialIdeal (B : DividedPowerRing.{u}) (T : Type w)
    (m : T →₀ B) :
    DividedPowerAlgebra.embed B (T →₀ B) m ∈ dividedPowerPolynomialIdeal B.ideal T := by
  apply Ideal.mem_sup_right
  change (dividedPowerPolynomialAugmentation B T).toRingHom
    (DividedPowerAlgebra.embed B (T →₀ B) m) = 0
  simp [dividedPowerPolynomialAugmentation, DividedPowerAlgebra.lift_embed_apply]

/-- The divided powers of the degree-one element `dp 1 m` of a divided power polynomial algebra
are the generators `dp n m`. -/
private theorem setIndexedDividedPowerPolynomial_dpow_embed (B : DividedPowerRing.{u})
    (T : Type w) (n : ℕ) (m : T →₀ B) :
    (setIndexedDividedPowerPolynomialDividedPowers B T).dpow n
      (DividedPowerAlgebra.embed B (T →₀ B) m) = DividedPowerAlgebra.dp B n m := by
  classical
  let δ := setIndexedDividedPowerPolynomialDividedPowers B T
  have hmem (m : T →₀ B) : DividedPowerAlgebra.embed B (T →₀ B) m ∈
      dividedPowerPolynomialIdeal B.ideal T :=
    embed_mem_dividedPowerPolynomialIdeal B T m
  induction m using Finsupp.induction generalizing n with
  | zero =>
      cases n with
      | zero =>
          rw [δ.dpow_zero (hmem 0)]
          simp [DividedPowerAlgebra.dp_null]
      | succ n =>
          have hzero : (0 : DividedPowerAlgebra B (T →₀ B)) ∈
              dividedPowerPolynomialIdeal B.ideal T := Ideal.zero_mem _
          have h := δ.dpow_mul (n := n + 1) (a := 0) (x := 0) hzero
          simpa [δ, DividedPowerAlgebra.embed, DividedPowerAlgebra.dp_null] using h
  | @single_add i a m hi ha ih =>
      let x := dividedPowerPolynomialVariable B i
      have hx : x ∈ dividedPowerPolynomialIdeal B.ideal T := by
        simpa [x, dividedPowerPolynomialVariable,
          DividedPowerAlgebra.embed_def] using hmem (Finsupp.single i 1)
      have hvar (j : ℕ) : δ.dpow j x =
          DividedPowerAlgebra.dp B j (Finsupp.single i 1) := by
        simpa [δ, x, dividedPowerPolynomialVariableMonomial] using
          setIndexedDividedPowerPolynomialDividedPowers_dpow_variable B i j
      have hsingle : (Finsupp.single i a : T →₀ B) = a • Finsupp.single i 1 := by
        ext t
        by_cases ht : t = i <;> simp [ht]
      have hdecomp : DividedPowerAlgebra.embed B (T →₀ B) (Finsupp.single i a + m) =
          algebraMap B (DividedPowerAlgebra B (T →₀ B)) a * x +
            DividedPowerAlgebra.embed B (T →₀ B) m := by
        rw [map_add, hsingle, map_smul, Algebra.smul_def]
        rfl
      calc
        δ.dpow n (DividedPowerAlgebra.embed B (T →₀ B) (Finsupp.single i a + m)) =
            (Finset.HasAntidiagonal.antidiagonal n).sum fun k =>
              δ.dpow k.1 (algebraMap B (DividedPowerAlgebra B (T →₀ B)) a * x) *
                δ.dpow k.2 (DividedPowerAlgebra.embed B (T →₀ B) m) := by
          rw [hdecomp, δ.dpow_add (Ideal.mul_mem_left _ _ hx) (hmem m)]
        _ = (Finset.HasAntidiagonal.antidiagonal n).sum fun k =>
              DividedPowerAlgebra.dp B k.1 (a • Finsupp.single i 1) *
                DividedPowerAlgebra.dp B k.2 m := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [δ.dpow_mul hx, ih k.2, hvar k.1, DividedPowerAlgebra.dp_smul]
          simp [Algebra.smul_def, map_pow]
        _ = DividedPowerAlgebra.dp B n (Finsupp.single i a + m) := by
          rw [← hsingle, DividedPowerAlgebra.dp_add]

/-! ### The identification `E(n) ≅ E⟨ξ_i(j)⟩` on divided powers -/

/-- The identification of `E(n)` with the divided power polynomial algebra over `E` carries the
divided power ideal of the latter into that of `E(n)`. -/
private theorem tensorEnvelopeDPEquiv_symm_mem (n : ℕ)
    {x : setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
      (ι × Fin n)}
    (hx : x ∈ dividedPowerPolynomialIdeal (polynomialDividedPowerEnvelope s f).object.ideal
      (ι × Fin n)) :
    (tensorEnvelopeDPEquiv s f n).symm x ∈ (tensorPowerEnvelope s f n).object.ideal :=
  (tensorEnvelopeDPEquiv_symm_isDPMorphism s f n).ideal_comp (Ideal.mem_map_of_mem _ hx)

/-- The identification of `E(n)` with the divided power polynomial algebra carries `dp k m` to
the `k`-th divided power of the image of `dp 1 m`. -/
private theorem tensorEnvelopeDPEquiv_symm_dp (n k : ℕ)
    (m : ι × Fin n →₀ (polynomialDividedPowerEnvelope s f).object) :
    (tensorEnvelopeDPEquiv s f n).symm
        (DividedPowerAlgebra.dp (polynomialDividedPowerEnvelope s f).object k m) =
      (tensorPowerEnvelope s f n).object.dividedPowers.dpow k
        ((tensorEnvelopeDPEquiv s f n).symm
          (DividedPowerAlgebra.dp (polynomialDividedPowerEnvelope s f).object 1 m)) := by
  rw [← setIndexedDividedPowerPolynomial_dpow_embed, ← DividedPowerAlgebra.embed_def]
  exact (tensorEnvelopeDPEquiv_symm_isDPMorphism s f n).map_dpow
    (embed_mem_dividedPowerPolynomialIdeal _ _ m)

/-- The inverse identification carries the variable `ξ_i(j)` to the image of
`x_i(0) - x_i(j)`. -/
private theorem tensorEnvelopeDPEquiv_symm_variable (n : ℕ) (q : ι × Fin n) :
    (tensorEnvelopeDPEquiv s f n).symm
        (DividedPowerAlgebra.dp (polynomialDividedPowerEnvelope s f).object 1
          (Finsupp.single q 1)) =
      (tensorPowerEnvelope s f n).algebraMap.toRingHom (coprojectionDifference s n q) :=
  (RingEquiv.symm_apply_eq _).2 (tensorEnvelopeDPEquiv_coprojectionDifference s f n q).symm

/-- The images of the differences `x_i(0) - x_i(j)` lie in the divided power ideal of `E(n)`. -/
theorem coprojectionDifference_mem (n : ℕ) (q : ι × Fin n) :
    (tensorPowerEnvelope s f n).algebraMap.toRingHom (coprojectionDifference s n q) ∈
      (tensorPowerEnvelope s f n).object.ideal := by
  rw [← tensorEnvelopeDPEquiv_symm_variable]
  exact tensorEnvelopeDPEquiv_symm_mem s f n
    (variable_mem_polynomialIdeal (polynomialDividedPowerEnvelope s f).object q)

/-- **The divided power monomial `ξ^{[K]}` of `E(1)`**, `ξ_i = x_i(0) - x_i(1)`. -/
def envelopeTaylorMonomial (K : ι →₀ ℕ) : (tensorPowerEnvelope s f 1).object :=
  (tensorEnvelopeDPEquiv s f 1).symm
    (dividedPowerPolynomialMonomial _ (K.mapDomain fun i ↦ (i, (0 : Fin 1))))

/-- **The divided power monomial `v^{[K]} u^{[L]}` of `E(2)`**, `u_i = x_i(0) - x_i(1)` and
`v_i = x_i(1) - x_i(2)`.  In the coordinates `ξ_i(1) = x_i(0) - x_i(1)`,
`ξ_i(2) = x_i(0) - x_i(2)` of `Crystalline.tensorEnvelopeDPEquiv`, `u_i = ξ_i(1)` and
`v_i = ξ_i(2) - ξ_i(1)`. -/
def envelopeTaylorMonomial₂ (KL : (ι →₀ ℕ) × (ι →₀ ℕ)) : (tensorPowerEnvelope s f 2).object :=
  (tensorEnvelopeDPEquiv s f 2).symm
    ((KL.1.prod fun i k ↦ DividedPowerAlgebra.dp _ k
        (Finsupp.single (i, (1 : Fin 2)) 1 - Finsupp.single (i, (0 : Fin 2)) 1)) *
      KL.2.prod fun i l ↦ DividedPowerAlgebra.dp _ l (Finsupp.single (i, (0 : Fin 2)) 1))

/-! ### The monomials as divided powers in the envelopes -/

/-- The image `ξ_i(j)` of `x_i(0) - x_i(j)` in `E(n)`. -/
private abbrev envDiff (n : ℕ) (q : ι × Fin n) : (tensorPowerEnvelope s f n).object :=
  (tensorPowerEnvelope s f n).algebraMap.toRingHom (coprojectionDifference s n q)

/-- `ξ^{[K]} = ∏_i γ_{K_i}(ξ_i)` in `E(1)`. -/
private theorem envelopeTaylorMonomial_eq_prod (K : ι →₀ ℕ) :
    envelopeTaylorMonomial s f K = K.prod fun i m ↦
      (tensorPowerEnvelope s f 1).object.dividedPowers.dpow m (envDiff s f 1 (i, 0)) := by
  rw [envelopeTaylorMonomial, dividedPowerPolynomialMonomial, map_finsuppProd,
    Finsupp.prod_mapDomain_index_inj (fun a b h ↦ congrArg Prod.fst h)]
  refine Finsupp.prod_congr fun i _ ↦ ?_
  rw [tensorEnvelopeDPEquiv_symm_dp, tensorEnvelopeDPEquiv_symm_variable]

/-- `v^{[K]} u^{[L]} = ∏_i γ_{K_i}(ξ_i(2) - ξ_i(1)) ∏_i γ_{L_i}(ξ_i(1))` in `E(2)`. -/
private theorem envelopeTaylorMonomial₂_eq_prod (KL : (ι →₀ ℕ) × (ι →₀ ℕ)) :
    envelopeTaylorMonomial₂ s f KL =
      (KL.1.prod fun i k ↦ (tensorPowerEnvelope s f 2).object.dividedPowers.dpow k
          (envDiff s f 2 (i, 1) - envDiff s f 2 (i, 0))) *
        KL.2.prod fun i l ↦ (tensorPowerEnvelope s f 2).object.dividedPowers.dpow l
          (envDiff s f 2 (i, 0)) := by
  rw [envelopeTaylorMonomial₂, map_mul, map_finsuppProd, map_finsuppProd]
  congr 1
  · refine Finsupp.prod_congr fun i _ ↦ ?_
    rw [tensorEnvelopeDPEquiv_symm_dp, ← DividedPowerAlgebra.embed_def, map_sub,
      DividedPowerAlgebra.embed_def, DividedPowerAlgebra.embed_def, map_sub,
      tensorEnvelopeDPEquiv_symm_variable, tensorEnvelopeDPEquiv_symm_variable]
  · refine Finsupp.prod_congr fun i _ ↦ ?_
    rw [tensorEnvelopeDPEquiv_symm_dp, tensorEnvelopeDPEquiv_symm_variable]

/-- The reindexing maps commute with the divided powers. -/
private theorem envReindex_dpow {m n : SimplexCategory} (φ : m ⟶ n) (k : ℕ)
    {x : (tensorPowerEnvelope s f m.len).object}
    (hx : x ∈ (tensorPowerEnvelope s f m.len).object.ideal) :
    envReindex s f φ ((tensorPowerEnvelope s f m.len).object.dividedPowers.dpow k x) =
      (tensorPowerEnvelope s f n.len).object.dividedPowers.dpow k (envReindex s f φ x) :=
  (envelopeReindex s f φ).1.isDPMorphism.map_dpow hx

/-- A reindexing map `E(1) → E(n)` renames `ξ_i = x_i(0) - x_i(1)`. -/
private theorem envReindex_envDiff_one {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (i : ι) :
    envReindex s f φ (envDiff s f 1 (i, 0)) =
      (tensorPowerEnvelope s f n.len).algebraMap.toRingHom
        (MvPolynomial.X (φ.toOrderHom 0, i) - MvPolynomial.X (φ.toOrderHom 1, i)) := by
  change (envelopeReindex s f φ).1 ((tensorPowerEnvelope s f (⦋1⦌ : SimplexCategory).len
    ).algebraMap.toRingHom (coprojectionDifference s 1 (i, 0))) = _
  rw [envelopeReindex_polynomial]
  congr 1
  simp [coprojectionDifference, simplexVariableMap]

/-- A reindexing map `E(1) → E(n)` on a monomial `ξ^{[K]}`. -/
private theorem envReindex_envelopeTaylorMonomial {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n)
    (K : ι →₀ ℕ) :
    envReindex s f φ (envelopeTaylorMonomial s f K) = K.prod fun i m ↦
      (tensorPowerEnvelope s f n.len).object.dividedPowers.dpow m
        ((tensorPowerEnvelope s f n.len).algebraMap.toRingHom
          (MvPolynomial.X (φ.toOrderHom 0, i) - MvPolynomial.X (φ.toOrderHom 1, i))) := by
  rw [envelopeTaylorMonomial_eq_prod, map_finsuppProd]
  refine Finsupp.prod_congr fun i _ ↦ ?_
  rw [envReindex_dpow s f φ _ (coprojectionDifference_mem s f 1 (i, 0)),
    envReindex_envDiff_one]

/-! ### The coprojection `E(0) → E(n)` in the coordinates of `Crystalline.tensorEnvelopeDPEquiv` -/

/-- The coefficient map `E → E⟨ξ_i(j) : j ∈ ∅⟩` is bijective: there are no variables. -/
private theorem bijective_algebraMap_fin_zero :
    Function.Bijective (algebraMap (polynomialDividedPowerEnvelope s f).object
      (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
        (ι × Fin 0))) := by
  refine ⟨coefficient_injective _ _, fun x ↦ ?_⟩
  have hx : x ∈ Submodule.span (polynomialDividedPowerEnvelope s f).object
      (Set.range (dividedPowerPolynomialMonomial (polynomialDividedPowerEnvelope s f).object
        (ι := ι × Fin 0))) := by
    rw [monomial_span_eq_top]
    trivial
  rw [Set.range_unique, Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def, Subsingleton.elim (default : ι × Fin 0 →₀ ℕ) 0,
    dividedPowerPolynomialMonomial, Finsupp.prod_zero_index, mul_one]

/-- The identification `E(0) ≅ E` of the envelope of `J(0)` with that of `J`, read off from
`Crystalline.tensorEnvelopeDPEquiv` in degree zero. -/
private noncomputable def envelopeBaseEquiv :
    (tensorPowerEnvelope s f 0).object ≃+* (polynomialDividedPowerEnvelope s f).object :=
  (tensorEnvelopeDPEquiv s f 0).trans
    (RingEquiv.ofBijective _ (bijective_algebraMap_fin_zero s f)).symm

/-- The inverse of `E(0) ≅ E`: `E(0) ≅ E⟨∅⟩` composed with the coefficients. -/
private theorem tensorEnvelopeDPEquiv_zero_symm_algebraMap
    (y : (tensorPowerEnvelope s f 0).object) :
    (tensorEnvelopeDPEquiv s f 0).symm
        (algebraMap (polynomialDividedPowerEnvelope s f).object
          (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
            (ι × Fin 0)) (envelopeBaseEquiv s f y)) = y := by
  change (tensorEnvelopeDPEquiv s f 0).symm
    ((RingEquiv.ofBijective _ (bijective_algebraMap_fin_zero s f))
      ((RingEquiv.ofBijective _ (bijective_algebraMap_fin_zero s f)).symm
        (tensorEnvelopeDPEquiv s f 0 y))) = y
  rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]

/-- **A coprojection `E(0) → E(n)` onto the first factor is the coefficient map** in the
coordinates of `Crystalline.tensorEnvelopeDPEquiv`. -/
private theorem tensorEnvelopeDPEquiv_envReindex_base {m : SimplexCategory} (φ : ⦋0⦌ ⟶ m)
    (hφ : φ.toOrderHom 0 = 0) (e : (polynomialDividedPowerEnvelope s f).object) :
    tensorEnvelopeDPEquiv s f m.len (envReindex s f φ ((tensorEnvelopeDPEquiv s f 0).symm
        (algebraMap (polynomialDividedPowerEnvelope s f).object
          (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
            (ι × Fin 0)) e))) =
      algebraMap (polynomialDividedPowerEnvelope s f).object
        (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
          (ι × Fin m.len)) e := by
  let E := (polynomialDividedPowerEnvelope s f).object
  let R := setIndexedDividedPowerPolynomialDividedPowerRing E (ι × Fin m.len)
  let θ₁ : DividedPowers.DPMorphism E.dividedPowers R.dividedPowers :=
    DividedPowers.DPMorphism.mk' (f := (tensorEnvelopeDPEquiv s f m.len).toRingHom.comp
      ((envReindex s f φ).comp ((tensorEnvelopeDPEquiv s f 0).symm.toRingHom.comp
        (algebraMap E (setIndexedDividedPowerPolynomialAlgebra E (ι × Fin 0))))))
      (DividedPowers.IsDPMorphism.comp _ (tensorEnvelopeDPEquiv_isDPMorphism s f m.len)
        (DividedPowers.IsDPMorphism.comp _ (envelopeReindex s f φ).1.isDPMorphism
          (DividedPowers.IsDPMorphism.comp _ (tensorEnvelopeDPEquiv_symm_isDPMorphism s f 0)
            (setIndexedDividedPowerPolynomialCoefficient_isDPMorphism E (ι × Fin 0)))))
  have h := envelopeHom_ext (polynomialDividedPowerEnvelope s f) R θ₁
    (setIndexedDividedPowerPolynomialCoefficientDPMorphism E (ι × Fin m.len)) ?_ ?_
  · exact congrArg (fun θ : DividedPowers.DPMorphism E.dividedPowers R.dividedPowers ↦ θ e) h
  · ext a
    change tensorEnvelopeDPEquiv s f m.len (envReindex s f φ ((tensorEnvelopeDPEquiv s f 0).symm
      (algebraMap E (setIndexedDividedPowerPolynomialAlgebra E (ι × Fin 0))
        ((polynomialDividedPowerEnvelope s f).structureMap.toRingHom a)))) =
      algebraMap E (setIndexedDividedPowerPolynomialAlgebra E (ι × Fin m.len))
        ((polynomialDividedPowerEnvelope s f).structureMap.toRingHom a)
    rw [← tensorEnvelopeDPEquiv_structureMap s f 0 a, RingEquiv.symm_apply_apply,
      ← tensorEnvelopeDPEquiv_structureMap s f m.len a]
    congr 1
    exact congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q.toRingHom a) (envelopeReindex s f φ).2
  · refine RingHom.ext fun x ↦ ?_
    change tensorEnvelopeDPEquiv s f m.len (envReindex s f φ ((tensorEnvelopeDPEquiv s f 0).symm
      (algebraMap E (setIndexedDividedPowerPolynomialAlgebra E (ι × Fin 0))
        ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x)))) =
      algebraMap E (setIndexedDividedPowerPolynomialAlgebra E (ι × Fin m.len))
        ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x)
    rw [← tensorEnvelopeDPEquiv_coprojection s f 0 x, RingEquiv.symm_apply_apply,
      ← tensorEnvelopeDPEquiv_coprojection s f m.len x]
    congr 1
    change (envelopeReindex s f φ).1 ((tensorPowerEnvelope s f (⦋0⦌ : SimplexCategory).len
      ).algebraMap.toRingHom _) = _
    rw [envelopeReindex_polynomial]
    congr 1
    simp only [mvPolynomialCoprojection, MvPolynomial.rename_rename]
    congr 2
    funext i
    simp [simplexVariableMap, hφ]

/-- A coprojection `E(0) → E(n)` onto the first factor, in the coordinates of
`Crystalline.tensorEnvelopeDPEquiv`, is the coefficient map after `E(0) ≅ E`. -/
private theorem tensorEnvelopeDPEquiv_envReindex_base' {m : SimplexCategory} (φ : ⦋0⦌ ⟶ m)
    (hφ : φ.toOrderHom 0 = 0) (y : (tensorPowerEnvelope s f 0).object) :
    tensorEnvelopeDPEquiv s f m.len (envReindex s f φ y) =
      algebraMap (polynomialDividedPowerEnvelope s f).object
        (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
          (ι × Fin m.len)) (envelopeBaseEquiv s f y) := by
  have h := tensorEnvelopeDPEquiv_envReindex_base s f φ hφ (envelopeBaseEquiv s f y)
  rwa [tensorEnvelopeDPEquiv_zero_symm_algebraMap] at h

/-- **A free module from a ring isomorphism and a basis.**  If `Φ : S ≅ B` carries `a : R → S`
to the coefficient map of an `R₀`-algebra `B` along `θ : R ≅ R₀`, and the `ξ_K` to a basis of `B`
over `R₀`, then every element of `S` is uniquely `∑_K ξ_K a(m_K)`. -/
private theorem bijective_taylorSum_of_ringEquiv {S R₀ R B X : Type*} [CommRing S] [CommRing R₀]
    [CommRing R] [CommRing B] [Algebra R₀ B] (a : R →+* S) (xi : X → S) (Φ : S ≃+* B)
    (θ : R ≃+* R₀) (b : Module.Basis X R₀ B) (ha : ∀ y, Φ (a y) = algebraMap R₀ B (θ y))
    (hxi : ∀ K, Φ (xi K) = b K) : Function.Bijective (taylorSum a.toAddMonoidHom xi) := by
  let e : (X →₀ R) ≃+ S := (Finsupp.mapRange.addEquiv θ.toAddEquiv).trans
    (b.repr.symm.toAddEquiv.trans Φ.symm.toAddEquiv)
  have h : taylorSum a.toAddMonoidHom xi = e.toAddMonoidHom := by
    refine Finsupp.addHom_ext fun K m ↦ ?_
    rw [taylorSum_single]
    apply Φ.injective
    simp only [e, AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply,
      Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single, LinearEquiv.coe_toAddEquiv,
      RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, RingEquiv.apply_symm_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [smul_eq_mul, map_mul, ha, hxi]
    change _ = b.repr.symm (Finsupp.single K (θ m))
    rw [Module.Basis.repr_symm_single, Algebra.smul_def, mul_comm]
  exact h ▸ e.bijective

/-! ### The change of variables `ξ_i(2) ↦ ξ_i(2) - ξ_i(1)` -/

section ChangeOfVariables

variable {R : Type*} [CommRing R]

/-- The endomorphism of `R^{(ι × {0, 1})}` sending `e_{(i, 1)}` to `e_{(i, 0)}` and
`e_{(i, 0)}` to zero. -/
private noncomputable def shiftEnd : Module.End R (ι × Fin 2 →₀ R) :=
  Finsupp.linearCombination R fun q ↦ if q.2 = 1 then Finsupp.single (q.1, 0) 1 else 0

/-- `shiftEnd` on a basis vector. -/
private theorem shiftEnd_single (q : ι × Fin 2) :
    shiftEnd (R := R) (Finsupp.single q 1) =
      if q.2 = 1 then Finsupp.single (q.1, 0) 1 else 0 := by
  rw [shiftEnd, Finsupp.linearCombination_single, one_smul]

/-- `shiftEnd` squares to zero. -/
private theorem shiftEnd_mul_self : shiftEnd (R := R) (ι := ι) * shiftEnd = 0 := by
  refine Finsupp.lhom_ext fun q c ↦ ?_
  rw [Module.End.mul_apply, shiftEnd, Finsupp.linearCombination_single]
  split_ifs with h
  · simp
  · simp

/-- The change of variables `e_{(i, 1)} ↦ e_{(i, 1)} - e_{(i, 0)}`, `e_{(i, 0)} ↦ e_{(i, 0)}`,
an automorphism of `R^{(ι × {0, 1})}` with inverse `e_{(i, 1)} ↦ e_{(i, 1)} + e_{(i, 0)}`. -/
private noncomputable def shiftEquiv : (ι × Fin 2 →₀ R) ≃ₗ[R] (ι × Fin 2 →₀ R) :=
  LinearEquiv.ofLinearMap (1 - shiftEnd) (1 + shiftEnd)
    (by
      change (1 - shiftEnd) * (1 + shiftEnd) = (1 : Module.End R (ι × Fin 2 →₀ R))
      rw [mul_add, mul_one, sub_mul, one_mul, shiftEnd_mul_self, sub_zero, sub_add_cancel])
    (by
      change (1 + shiftEnd) * (1 - shiftEnd) = (1 : Module.End R (ι × Fin 2 →₀ R))
      rw [mul_sub, mul_one, add_mul, one_mul, shiftEnd_mul_self, add_zero, add_sub_cancel_right])

/-- `shiftEquiv` on a basis vector. -/
private theorem shiftEquiv_single (q : ι × Fin 2) :
    shiftEquiv (R := R) (Finsupp.single q 1) =
      Finsupp.single q 1 - if q.2 = 1 then Finsupp.single (q.1, 0) 1 else 0 := by
  rw [shiftEquiv, LinearEquiv.coe_ofLinearMap, LinearMap.sub_apply, Module.End.one_apply,
    shiftEnd_single]

/-- `ι ⊕ ι ≃ ι × {0, 1}`, the left summand going to `1` and the right one to `0`. -/
private def sumFinTwoEquiv : ι ⊕ ι ≃ ι × Fin 2 where
  toFun := Sum.elim (fun i ↦ (i, 1)) (fun i ↦ (i, 0))
  invFun q := if q.2 = 0 then Sum.inr q.1 else Sum.inl q.1
  left_inv := by rintro (i | i) <;> simp
  right_inv := by
    rintro ⟨i, j⟩
    fin_cases j <;> simp

/-- The exponents on `ι × {0, 1}` are pairs of exponents on `ι`, the first for `1` and the
second for `0`. -/
private def finTwoExponentEquiv : (ι × Fin 2 →₀ ℕ) ≃ (ι →₀ ℕ) × (ι →₀ ℕ) :=
  (Finsupp.domCongr (sumFinTwoEquiv (ι := ι))).symm.toEquiv.trans
    Finsupp.sumFinsuppEquivProdFinsupp

end ChangeOfVariables

/-- **`E(1)` is free over `E(0)` through `p₀` on the monomials `ξ^{[K]}`.** -/
theorem bijective_envelopeTaylorMonomial :
    Function.Bijective (taylorSum (envReindex s f (SimplexCategory.δ (n := 0) 1)).toAddMonoidHom
      (envelopeTaylorMonomial s f)) := by
  refine bijective_taylorSum_of_ringEquiv _ _ (tensorEnvelopeDPEquiv s f 1)
    (envelopeBaseEquiv s f)
    ((dividedPowerPolynomialMonomialBasis (polynomialDividedPowerEnvelope s f).object
      (ι × Fin 1)).reindex (Finsupp.domCongr (Equiv.prodUnique ι (Fin 1))).toEquiv)
    (fun y ↦ ?_) (fun K ↦ ?_)
  · exact tensorEnvelopeDPEquiv_envReindex_base' s f (SimplexCategory.δ (n := 0) 1) rfl y
  · rw [envelopeTaylorMonomial, RingEquiv.apply_symm_apply, Module.Basis.reindex_apply,
      dividedPowerPolynomialMonomialBasis_apply]
    congr 1
    simp [Finsupp.equivMapDomain_eq_mapDomain]
    rfl

/-- **`E(2)` is free over `E(0)` through `q₀` on the monomials `v^{[K]} u^{[L]}`.** -/
theorem bijective_envelopeTaylorMonomial₂ :
    Function.Bijective (taylorSum
      (envReindex s f (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0)).toAddMonoidHom
      (envelopeTaylorMonomial₂ s f)) := by
  let E := (polynomialDividedPowerEnvelope s f).object
  let τ := DividedPowerAlgebra.mapEquiv (shiftEquiv (R := E) (ι := ι))
  refine bijective_taylorSum_of_ringEquiv _ _ (tensorEnvelopeDPEquiv s f 2)
    (envelopeBaseEquiv s f)
    (((dividedPowerPolynomialMonomialBasis E (ι × Fin 2)).map τ.toLinearEquiv).reindex
      finTwoExponentEquiv)
    (fun y ↦ ?_) (fun KL ↦ ?_)
  · exact tensorEnvelopeDPEquiv_envReindex_base' s f (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) rfl y
  · rw [envelopeTaylorMonomial₂, RingEquiv.apply_symm_apply, Module.Basis.reindex_apply,
      Module.Basis.map_apply, dividedPowerPolynomialMonomialBasis_apply]
    change _ = τ (dividedPowerPolynomialMonomial E
      (Finsupp.equivMapDomain sumFinTwoEquiv (Finsupp.sumElim KL.1 KL.2)))
    rw [dividedPowerPolynomialMonomial, map_finsuppProd, Finsupp.prod_equivMapDomain,
      Finsupp.prod_sumElim]
    simp only [τ, DividedPowerAlgebra.mapEquiv_apply, DividedPowerAlgebra.map_apply_dp]
    simp only [sumFinTwoEquiv, Equiv.coe_fn_mk, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    congr 1 <;> refine Finsupp.prod_congr fun i _ ↦ ?_ <;>
      rw [LinearEquiv.coe_coe, shiftEquiv_single] <;> simp <;> rfl

/-- `ξ^{[0]} = 1`. -/
theorem envelopeTaylorMonomial_zero : envelopeTaylorMonomial s f (0 : ι →₀ ℕ) = 1 := by
  rw [envelopeTaylorMonomial_eq_prod, Finsupp.prod_zero_index]

/-- The monomials multiply as divided power monomials. -/
theorem envelopeTaylorMonomial_mul (K L : ι →₀ ℕ) :
    envelopeTaylorMonomial s f K * envelopeTaylorMonomial s f L =
      (dpMulCoeff K L : (tensorPowerEnvelope s f 1).object) *
        envelopeTaylorMonomial s f (K + L) := by
  classical
  simp only [envelopeTaylorMonomial_eq_prod, Finsupp.prod]
  rw [(tensorPowerEnvelope s f 1).object.dividedPowers.prod_dpow_mul_support
    (fun i ↦ coprojectionDifference_mem s f 1 (i, 0)) K L, dpMulCoeff, Finsupp.prod,
    Nat.cast_prod]
  simp only [Finsupp.coe_add, Pi.add_apply]

/-- `v^{[K]} · u^{[L]} = v^{[K]} u^{[L]}`. -/
theorem envelopeTaylorMonomial₂_mul (K L : ι →₀ ℕ) :
    envelopeTaylorMonomial₂ s f (K, 0) * envelopeTaylorMonomial₂ s f (0, L) =
      envelopeTaylorMonomial₂ s f (K, L) := by
  simp only [envelopeTaylorMonomial₂_eq_prod, Finsupp.prod_zero_index, mul_one, one_mul]

/-- The coface `q₀₁ = δ 2 : ⦋1⦌ → ⦋2⦌` sends `ξ^{[L]}` to `u^{[L]}`. -/
theorem envReindex_delta_two_envelopeTaylorMonomial (L : ι →₀ ℕ) :
    envReindex s f (SimplexCategory.δ (n := 1) 2) (envelopeTaylorMonomial s f L) =
      envelopeTaylorMonomial₂ s f (0, L) := by
  rw [envReindex_envelopeTaylorMonomial, envelopeTaylorMonomial₂_eq_prod,
    Finsupp.prod_zero_index, one_mul]
  rfl

/-- The coface `q₁₂ = δ 0 : ⦋1⦌ → ⦋2⦌` sends `ξ^{[K]}` to `v^{[K]}`. -/
theorem envReindex_delta_zero_envelopeTaylorMonomial (K : ι →₀ ℕ) :
    envReindex s f (SimplexCategory.δ (n := 1) 0) (envelopeTaylorMonomial s f K) =
      envelopeTaylorMonomial₂ s f (K, 0) := by
  rw [envReindex_envelopeTaylorMonomial, envelopeTaylorMonomial₂_eq_prod,
    Finsupp.prod_zero_index, mul_one]
  refine Finsupp.prod_congr fun i _ ↦ ?_
  congr 1
  simp only [envDiff, coprojectionDifference, ← map_sub]
  congr 1
  change MvPolynomial.X ((1 : Fin 3), i) - MvPolynomial.X ((2 : Fin 3), i) = _
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

/-- The coface `q₀₂ = δ 1 : ⦋1⦌ → ⦋2⦌` sends `ξ^{[N]}` to
`(u + v)^{[N]} = ∑_{K + L = N} v^{[K]} u^{[L]}`. -/
theorem envReindex_delta_one_envelopeTaylorMonomial [DecidableEq ι] (N : ι →₀ ℕ) :
    envReindex s f (SimplexCategory.δ (n := 1) 1) (envelopeTaylorMonomial s f N) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, envelopeTaylorMonomial₂ s f x := by
  rw [envReindex_envelopeTaylorMonomial]
  have hsplit : ∀ i : ι, (tensorPowerEnvelope s f 2).algebraMap.toRingHom
      (MvPolynomial.X ((SimplexCategory.δ (n := 1) 1).toOrderHom 0, i) -
        MvPolynomial.X ((SimplexCategory.δ (n := 1) 1).toOrderHom 1, i)) =
      (envDiff s f 2 (i, 1) - envDiff s f 2 (i, 0)) + envDiff s f 2 (i, 0) := by
    intro i
    rw [sub_add_cancel]
    rfl
  simp only [hsplit, Finsupp.prod]
  rw [(tensorPowerEnvelope s f 2).object.dividedPowers.prod_dpow_add_support
    (fun i ↦ sub_mem (coprojectionDifference_mem s f 2 (i, 1))
      (coprojectionDifference_mem s f 2 (i, 0)))
    (fun i ↦ coprojectionDifference_mem s f 2 (i, 0)) N]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [envelopeTaylorMonomial₂_eq_prod]
  rfl

/-- The diagonal `σ 0 : ⦋1⦌ → ⦋0⦌` kills `ξ^{[K]}` for `K ≠ 0`. -/
theorem envReindex_degeneracy_envelopeTaylorMonomial {K : ι →₀ ℕ} (hK : K ≠ 0) :
    envReindex s f (SimplexCategory.σ (n := 0) 0) (envelopeTaylorMonomial s f K) = 0 := by
  rw [envReindex_envelopeTaylorMonomial, Finsupp.prod]
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hK
  refine Finset.prod_eq_zero hi ?_
  have h0 : (SimplexCategory.σ (n := 0) 0).toOrderHom 0 =
      (SimplexCategory.σ (n := 0) 0).toOrderHom 1 :=
    @Subsingleton.elim _ (inferInstanceAs (Subsingleton (Fin 1))) _ _
  rw [h0, sub_self, map_zero]
  exact DividedPowers.dpow_eval_zero _ (Finsupp.mem_support_iff.1 hi)

/-- **The Taylor coefficients `δ_K(y)` of an element of `E(0)`**: the coefficients of
`p₁(y) = ∑_K p₀(δ_K y) ξ^{[K]}`. -/
def envelopeTaylorCoeff (y : (tensorPowerEnvelope s f 0).object) :
    (ι →₀ ℕ) →₀ (tensorPowerEnvelope s f 0).object :=
  (AddEquiv.ofBijective _ (bijective_envelopeTaylorMonomial s f)).symm
    (envReindex s f (SimplexCategory.δ (n := 0) 0) y)

/-! ### Taylor's formula for the differential -/

/-- The second coprojection `p₁ : E(0) → E(1)` on `x_i`: `p₁(x_i) = p₀(x_i) - ξ_i`. -/
private theorem envReindex_delta_zero_X (i : ι) :
    envReindex s f (SimplexCategory.δ (n := 0) 0)
        ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i))) =
      envReindex s f (SimplexCategory.δ (n := 0) 1)
          ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i))) -
        envDiff s f 1 (i, 0) := by
  change (envelopeReindex s f _).1 ((tensorPowerEnvelope s f (⦋0⦌ : SimplexCategory).len
      ).algebraMap.toRingHom _) =
    (envelopeReindex s f _).1 ((tensorPowerEnvelope s f (⦋0⦌ : SimplexCategory).len
      ).algebraMap.toRingHom _) - _
  rw [envelopeReindex_polynomial, envelopeReindex_polynomial, envDiff, ← map_sub]
  congr 1
  simp only [MvPolynomial.rename_X, simplexVariableMap, coprojectionDifference]
  change MvPolynomial.X ((1 : Fin 2), i) = MvPolynomial.X ((0 : Fin 2), i) -
    (MvPolynomial.X ((0 : Fin 2), i) - MvPolynomial.X ((1 : Fin 2), i))
  ring

/-- The two coprojections `E(0) → E(1)` agree on the image of the base. -/
private theorem envReindex_delta_structureMap (a : s.A) :
    envReindex s f (SimplexCategory.δ (n := 0) 0)
        ((tensorPowerEnvelope s f 0).structureMap.toRingHom a) =
      envReindex s f (SimplexCategory.δ (n := 0) 1)
        ((tensorPowerEnvelope s f 0).structureMap.toRingHom a) :=
  (congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q.toRingHom a)
    (envelopeReindex s f (SimplexCategory.δ (n := 0) 0)).2).trans
    (congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q.toRingHom a)
      (envelopeReindex s f (SimplexCategory.δ (n := 0) 1)).2).symm

/-- `Ω` lies in the divided power ideal `J ⊕ Ω` of a first-order thickening `D ⊕ Ω`. -/
private theorem inr_mem_firstOrderExtensionIdeal (D : DividedPowerRing.{u}) (Ω : Type v)
    [AddCommGroup Ω] [Module D Ω] [Module (D : Type u)ᵐᵒᵖ Ω] [IsCentralScalar D Ω] (ω : Ω) :
    (TrivSqZeroExt.inr ω : firstOrderExtension D Ω) ∈ firstOrderExtensionIdeal D Ω := by
  rw [mem_firstOrderExtensionIdeal_iff, firstOrderEquiv_apply, TrivSqZeroExt.fst_inr]
  exact zero_mem _

/-- In a first-order thickening `D ⊕ Ω` the divided powers of degree at least two vanish on `Ω`. -/
private theorem firstOrderDividedPowers_dpow_inr (D : DividedPowerRing.{u}) (Ω : Type v)
    [AddCommGroup Ω] [Module D Ω] [Module (D : Type u)ᵐᵒᵖ Ω] [IsCentralScalar D Ω] (k : ℕ)
    (ω : Ω) :
    (firstOrderDividedPowers D Ω).dpow (k + 2) (TrivSqZeroExt.inr ω) = 0 := by
  rw [firstOrderDividedPowers, squareZeroDividedPowers_dpow,
    squareZeroDpow_succ _ _ _ (k + 1) (inr_mem_firstOrderExtensionIdeal D Ω ω)]
  simp [D.dividedPowers.dpow_eval_zero]

section TaylorFormula

attribute [local instance] tensorPowerEnvelopeAlgebra

/-- The action of the opposite ring on `Ω_{E(0)}`, which is the given one. -/
private noncomputable abbrev envelopeDifferentialsOpModule :
    Module ((tensorPowerEnvelope s f 0).object : Type (max u w))ᵐᵒᵖ
      (envelopeDifferentials s f 0) :=
  Module.compHom _ (RingEquiv.toOpposite (tensorPowerEnvelope s f 0).object).symm.toRingHom

attribute [local instance] envelopeDifferentialsOpModule

/-- The two actions of `E(0)` on `Ω_{E(0)}` agree. -/
private theorem envelopeDifferentials_isCentralScalar :
    IsCentralScalar (tensorPowerEnvelope s f 0).object (envelopeDifferentials s f 0) :=
  ⟨fun _ _ ↦ rfl⟩

attribute [local instance] envelopeDifferentials_isCentralScalar

/-- The first-order thickening `E(0) ⊕ Ω_{E(0)}` as a divided power ring. -/
private noncomputable abbrev firstOrderRing : DividedPowerRing.{max u w} :=
  DividedPowerRing.of (firstOrderExtension (tensorPowerEnvelope s f 0).object
      (envelopeDifferentials s f 0))
    (firstOrderExtensionIdeal (tensorPowerEnvelope s f 0).object (envelopeDifferentials s f 0))
    (firstOrderDividedPowers (tensorPowerEnvelope s f 0).object (envelopeDifferentials s f 0))

/-- The universal divided power derivation `d : E(0) → Ω_{E(0)}`. -/
private noncomputable abbrev envD :=
  universalDividedPowerDerivation (A := (s.A : Type u)) (B := (tensorPowerEnvelope s f 0).object)

/-- The coefficient morphism `E ≅ E(0) → E(0) ⊕ Ω`, `e ↦ (e, 0)`. -/
private noncomputable def firstOrderCoeff :
    DividedPowers.DPMorphism (polynomialDividedPowerEnvelope s f).object.dividedPowers
      (firstOrderRing s f).dividedPowers :=
  DividedPowers.DPMorphism.mk'
    (f := (firstOrderP₀ (tensorPowerEnvelope s f 0).object (envelopeDifferentials s f 0)).comp
      ((tensorEnvelopeDPEquiv s f 0).symm.toRingHom.comp
        (algebraMap (polynomialDividedPowerEnvelope s f).object
          (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
            (ι × Fin 0)))))
    (DividedPowers.IsDPMorphism.comp _ (firstOrderP₀_isDPMorphism _ _)
      (DividedPowers.IsDPMorphism.comp _ (tensorEnvelopeDPEquiv_symm_isDPMorphism s f 0)
        (setIndexedDividedPowerPolynomialCoefficient_isDPMorphism _ (ι × Fin 0))))

/-- The images `-d x_i` of the variables `ξ_i`. -/
private noncomputable def firstOrderVariable (q : ι × Fin 1) : (firstOrderRing s f).ideal :=
  ⟨TrivSqZeroExt.inr (-envD s f
      ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), q.1)))),
    inr_mem_firstOrderExtensionIdeal _ _ _⟩

/-- The divided power morphism `E⟨ξ_i⟩ → E(0) ⊕ Ω`, `ξ_i ↦ -d x_i`, over `e ↦ (e, 0)`. -/
private noncomputable def firstOrderPolyMap :
    DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers (polynomialDividedPowerEnvelope s f).object
        (ι × Fin 1)) (firstOrderRing s f).dividedPowers :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial _ (ι × Fin 1)
    (firstOrderRing s f) (firstOrderCoeff s f) (firstOrderVariable s f)).exists.choose

/-- The defining property of `firstOrderPolyMap`. -/
private theorem firstOrderPolyMap_spec :
    (firstOrderPolyMap s f).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism _ (ι × Fin 1)) =
      firstOrderCoeff s f ∧
    ∀ q : ι × Fin 1, firstOrderPolyMap s f
      (dividedPowerPolynomialVariable (polynomialDividedPowerEnvelope s f).object q) =
        (firstOrderVariable s f q : firstOrderRing s f) :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial _ (ι × Fin 1)
    (firstOrderRing s f) (firstOrderCoeff s f) (firstOrderVariable s f)).exists.choose_spec

/-- **The map `ψ : E(1) → E(0) ⊕ Ω`** with `ψ ∘ p₀ = (id, 0)` and `ψ(ξ_i) = (0, -d x_i)`. -/
private noncomputable def firstOrderPsi :
    DividedPowers.DPMorphism (tensorPowerEnvelope s f 1).object.dividedPowers
      (firstOrderRing s f).dividedPowers :=
  DividedPowers.DPMorphism.mk' (f := (firstOrderPolyMap s f).toRingHom.comp
      (tensorEnvelopeDPEquiv s f 1).toRingHom)
    (DividedPowers.IsDPMorphism.comp _ (firstOrderPolyMap s f).isDPMorphism
      (tensorEnvelopeDPEquiv_isDPMorphism s f 1))

/-- `ψ` is `firstOrderPolyMap` after `Crystalline.tensorEnvelopeDPEquiv`. -/
private theorem firstOrderPsi_apply (z : (tensorPowerEnvelope s f 1).object) :
    firstOrderPsi s f z = firstOrderPolyMap s f (tensorEnvelopeDPEquiv s f 1 z) := rfl

/-- `ψ(p₀(y)) = (y, 0)`. -/
private theorem firstOrderPsi_p₀ (y : (tensorPowerEnvelope s f 0).object) :
    firstOrderPsi s f (envReindex s f (SimplexCategory.δ (n := 0) 1) y) =
      TrivSqZeroExt.inl y := by
  rw [firstOrderPsi_apply, tensorEnvelopeDPEquiv_envReindex_base' s f _ rfl]
  have h := congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q (envelopeBaseEquiv s f y))
    (firstOrderPolyMap_spec s f).1
  refine h.trans ?_
  change TrivSqZeroExt.inl ((tensorEnvelopeDPEquiv s f 0).symm
    (algebraMap (polynomialDividedPowerEnvelope s f).object _ (envelopeBaseEquiv s f y))) = _
  rw [tensorEnvelopeDPEquiv_zero_symm_algebraMap]

/-- `ψ(ξ_i) = (0, -d x_i)`. -/
private theorem firstOrderPsi_envDiff (i : ι) :
    firstOrderPsi s f (envDiff s f 1 (i, 0)) =
      TrivSqZeroExt.inr (-envD s f
        ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i)))) := by
  rw [firstOrderPsi_apply, envDiff, tensorEnvelopeDPEquiv_coprojectionDifference]
  exact (firstOrderPolyMap_spec s f).2 (i, 0)

/-- **`ψ(p₁(y)) = (y, d y)`**, by the uniqueness half of the universal property of `E(0)`. -/
private theorem firstOrderPsi_p₁ (y : (tensorPowerEnvelope s f 0).object) :
    firstOrderPsi s f (envReindex s f (SimplexCategory.δ (n := 0) 0) y) =
      firstOrderP₁ (s.A : Type u) (tensorPowerEnvelope s f 0).object _
        (envelopeDifferentials s f 0) (envD s f) y := by
  let θ₁ : DividedPowers.DPMorphism (tensorPowerEnvelope s f 0).object.dividedPowers
      (firstOrderRing s f).dividedPowers :=
    (firstOrderPsi s f).comp (envelopeReindex s f (SimplexCategory.δ (n := 0) 0)).1
  let θ₂ : DividedPowers.DPMorphism (tensorPowerEnvelope s f 0).object.dividedPowers
      (firstOrderRing s f).dividedPowers :=
    DividedPowers.DPMorphism.mk' (firstOrderP₁_isDPMorphism _ _ _ _ (envD s f))
  have hbase : ∀ a : s.A, θ₁ ((tensorPowerEnvelope s f 0).structureMap.toRingHom a) =
      θ₂ ((tensorPowerEnvelope s f 0).structureMap.toRingHom a) := by
    intro a
    change firstOrderPsi s f (envReindex s f _ _) = firstOrderP₁ _ _ _ _ _ _
    rw [envReindex_delta_structureMap, firstOrderPsi_p₀]
    refine TrivSqZeroExt.ext (by simp) ?_
    rw [TrivSqZeroExt.snd_inl, firstOrderP₁_snd]
    exact ((envD s f).map_ringHom a).symm
  have h : θ₁ = θ₂ := by
    refine envelopeHom_ext (tensorPowerEnvelope s f 0) (firstOrderRing s f) θ₁ θ₂ ?_ ?_
    · exact DividedPowers.DPMorphism.ext (funext hbase)
    · refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun q ↦ ?_)
      · have hC : (tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.C a) =
            (tensorPowerEnvelope s f 0).structureMap.toRingHom a :=
          RingHom.congr_fun (tensorPowerEnvelope s f 0).algebraMap_comp a
        simp only [RingHom.comp_apply, DividedPowers.DPMorphism.toRingHom_apply, hC]
        exact hbase a
      · obtain ⟨j, i⟩ := q
        obtain rfl : j = 0 := @Subsingleton.elim _ (inferInstanceAs (Subsingleton (Fin 1))) _ _
        change firstOrderPsi s f (envReindex s f _ _) = firstOrderP₁ _ _ _ _ _ _
        have hsub : firstOrderPsi s f (envReindex s f (SimplexCategory.δ (n := 0) 1)
              ((tensorPowerEnvelope s f 0).algebraMap.toRingHom
                (MvPolynomial.X ((0 : Fin 1), i))) - envDiff s f 1 (i, 0)) =
            firstOrderPsi s f (envReindex s f (SimplexCategory.δ (n := 0) 1)
              ((tensorPowerEnvelope s f 0).algebraMap.toRingHom
                (MvPolynomial.X ((0 : Fin 1), i)))) - firstOrderPsi s f (envDiff s f 1 (i, 0)) :=
          map_sub (firstOrderPsi s f).toRingHom _ _
        rw [envReindex_delta_zero_X, hsub, firstOrderPsi_p₀, firstOrderPsi_envDiff]
        exact TrivSqZeroExt.ext (by simp) (by simp)
  exact congrArg (fun θ : DividedPowers.DPMorphism _ _ ↦ θ y) h

/-- `ψ(ξ^{[K]}) = ∏_i γ_{K_i}(0, -d x_i)`. -/
private theorem firstOrderPsi_envelopeTaylorMonomial (K : ι →₀ ℕ) :
    firstOrderPsi s f (envelopeTaylorMonomial s f K) = K.prod fun i m ↦
      (firstOrderRing s f).dividedPowers.dpow m (TrivSqZeroExt.inr (-envD s f
        ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i))))) := by
  rw [envelopeTaylorMonomial_eq_prod]
  change (firstOrderPsi s f).toRingHom _ = _
  rw [map_finsuppProd]
  refine Finsupp.prod_congr fun i _ ↦ ?_
  rw [← firstOrderPsi_envDiff]
  exact ((firstOrderPsi s f).dpow_comp _ (coprojectionDifference_mem s f 1 (i, 0))).symm

/-- `ψ(ξ^{[K]}) = 0` unless `K = 0` or `K = e_i`. -/
private theorem firstOrderPsi_envelopeTaylorMonomial_eq_zero {K : ι →₀ ℕ} (h0 : K ≠ 0)
    (h1 : ∀ i, K ≠ Finsupp.single i 1) : firstOrderPsi s f (envelopeTaylorMonomial s f K) = 0 := by
  classical
  rw [firstOrderPsi_envelopeTaylorMonomial, Finsupp.prod]
  set ω : ι → envelopeDifferentials s f 0 := fun i ↦ -envD s f
    ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i)))
  set g : ι → firstOrderRing s f :=
    fun j ↦ (firstOrderRing s f).dividedPowers.dpow (K j) (TrivSqZeroExt.inr (ω j))
  change ∏ j ∈ K.support, g j = 0
  have hg : ∀ j ∈ K.support, g j = 0 ∨ g j = TrivSqZeroExt.inr (ω j) := by
    intro j hj
    by_cases h : K j = 1
    · right
      simp only [g, h]
      exact (firstOrderRing s f).dividedPowers.dpow_one (inr_mem_firstOrderExtensionIdeal _ _ _)
    · left
      obtain ⟨k, hk⟩ : ∃ k, K j = k + 2 :=
        ⟨K j - 2, by have := Finsupp.mem_support_iff.1 hj; omega⟩
      simp only [g, hk]
      exact firstOrderDividedPowers_dpow_inr _ _ k _
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 h0
  by_cases hj : ∃ j ∈ K.support, j ≠ i
  · obtain ⟨j, hj, hji⟩ := hj
    rw [← Finset.mul_prod_erase _ _ hi,
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hji, hj⟩), ← mul_assoc]
    have hij : g i * g j = 0 := by
      rcases hg i hi with h | h <;> rcases hg j hj with h' | h' <;> simp [h, h']
    rw [hij, zero_mul]
  · push Not at hj
    have hKi : K i ≠ 1 := by
      intro h
      refine h1 i (Finsupp.ext fun t ↦ ?_)
      by_cases ht : t = i
      · subst ht
        simp [h]
      · rw [Finsupp.single_eq_of_ne ht]
        exact Finsupp.notMem_support_iff.1 fun h' ↦ ht (hj t h')
    obtain ⟨k, hk⟩ : ∃ k, K i = k + 2 :=
      ⟨K i - 2, by have := Finsupp.mem_support_iff.1 hi; omega⟩
    refine Finset.prod_eq_zero hi ?_
    simp only [g, hk]
    exact firstOrderDividedPowers_dpow_inr _ _ k _

/-- `ψ(ξ_i) = (0, -d x_i)`, read on the monomial `ξ^{[e_i]}`. -/
private theorem firstOrderPsi_envelopeTaylorMonomial_single (i : ι) :
    firstOrderPsi s f (envelopeTaylorMonomial s f (Finsupp.single i 1)) =
      TrivSqZeroExt.inr (-envD s f
        ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i)))) := by
  rw [firstOrderPsi_envelopeTaylorMonomial, Finsupp.prod_single_index]
  · exact (firstOrderRing s f).dividedPowers.dpow_one (inr_mem_firstOrderExtensionIdeal _ _ _)
  · exact (firstOrderRing s f).dividedPowers.dpow_zero (inr_mem_firstOrderExtensionIdeal _ _ _)

/-- Taylor's formula, inside the section where `E(0) ⊕ Ω` is available. -/
private theorem dividedPowerDifferential_eq_neg_sum_aux
    (y : (tensorPowerEnvelope s f 0).object) (S : Finset ι)
    (hS : ∀ i ∉ S, envelopeTaylorCoeff s f y (Finsupp.single i 1) = 0) :
    envD s f y = -∑ i ∈ S, envelopeTaylorCoeff s f y (Finsupp.single i 1) •
      envD s f ((tensorPowerEnvelope s f 0).algebraMap.toRingHom
        (MvPolynomial.X ((0 : Fin 1), i))) := by
  classical
  set c := envelopeTaylorCoeff s f y with hcdef
  set σ : (ι →₀ ℕ) → envelopeDifferentials s f 0 :=
    fun K ↦ (firstOrderPsi s f (envelopeTaylorMonomial s f K)).snd with hσ
  have hc : taylorSum (envReindex s f (SimplexCategory.δ (n := 0) 1)).toAddMonoidHom
      (envelopeTaylorMonomial s f) c = envReindex s f (SimplexCategory.δ (n := 0) 0) y :=
    (AddEquiv.ofBijective _ (bijective_envelopeTaylorMonomial s f)).apply_symm_apply _
  have h1 := congrArg (fun z ↦ (firstOrderPsi s f z).snd) hc
  simp only [taylorSum_apply, Finsupp.sum] at h1
  have hsum : (firstOrderPsi s f (∑ K ∈ c.support, envelopeTaylorMonomial s f K •
        (envReindex s f (SimplexCategory.δ (n := 0) 1)).toAddMonoidHom (c K))).snd =
      ∑ K ∈ c.support, c K • σ K := by
    rw [← DividedPowers.DPMorphism.toRingHom_apply, map_sum, TrivSqZeroExt.snd_sum]
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [smul_eq_mul, map_mul, DividedPowers.DPMorphism.toRingHom_apply,
      DividedPowers.DPMorphism.toRingHom_apply, firstOrderPsi_p₀, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, smul_zero, zero_add, op_smul_eq_smul]
  rw [hsum, firstOrderPsi_p₁, firstOrderP₁_snd] at h1
  rw [← h1]
  have hσ0 : ∀ K, K ∉ Finset.image (fun i ↦ Finsupp.single i 1) S → K ∈ c.support →
      c K • σ K = 0 := by
    intro K hK hKc
    by_cases h0 : K = 0
    · rw [h0, hσ]
      simp only [envelopeTaylorMonomial_zero]
      rw [← DividedPowers.DPMorphism.toRingHom_apply, map_one, TrivSqZeroExt.snd_one,
        smul_zero]
    by_cases h1 : ∃ i, K = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := h1
      have hi : i ∉ S := fun hi ↦ hK (Finset.mem_image_of_mem _ hi)
      exact absurd (hS i hi) (Finsupp.mem_support_iff.1 hKc)
    · push Not at h1
      rw [hσ]
      simp only
      rw [firstOrderPsi_envelopeTaylorMonomial_eq_zero s f h0 h1, TrivSqZeroExt.snd_zero,
        smul_zero]
  calc ∑ K ∈ c.support, c K • σ K
      = ∑ K ∈ c.support ∪ Finset.image (fun i ↦ Finsupp.single i 1) S, c K • σ K := by
        refine Finset.sum_subset Finset.subset_union_left fun K _ hK ↦ ?_
        rw [Finsupp.notMem_support_iff.1 hK, zero_smul]
    _ = ∑ K ∈ Finset.image (fun i ↦ Finsupp.single i 1) S, c K • σ K := by
        refine (Finset.sum_subset Finset.subset_union_right fun K hK hK' ↦ ?_).symm
        rcases Finset.mem_union.1 hK with hK | hK
        · exact hσ0 K hK' hK
        · exact absurd hK hK'
    _ = ∑ i ∈ S, c (Finsupp.single i 1) • σ (Finsupp.single i 1) :=
        Finset.sum_image fun i _ j _ h ↦ Finsupp.single_left_injective one_ne_zero h
    _ = _ := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hσ]
        simp only
        rw [firstOrderPsi_envelopeTaylorMonomial_single, TrivSqZeroExt.snd_inr, smul_neg]

end TaylorFormula

/-- **Taylor's formula for the divided power differential**: `d y = - ∑_i δ_{e_i}(y) d x_i`, the
sum over any finite set of indices outside which the first-order coefficients vanish. -/
theorem dividedPowerDifferential_eq_neg_sum_envelopeTaylorCoeff
    (y : (tensorPowerEnvelope s f 0).object) (S : Finset ι)
    (hS : ∀ i ∉ S, envelopeTaylorCoeff s f y (Finsupp.single i 1) = 0) :
    letI := tensorPowerEnvelopeAlgebraInstance s f 0
    dividedPowerDifferential (A := (s.A : Type u)) (tensorPowerEnvelope s f 0).object.dividedPowers
        y =
      -∑ i ∈ S, envelopeTaylorCoeff s f y (Finsupp.single i 1) •
        dividedPowerDifferential (A := (s.A : Type u))
          (tensorPowerEnvelope s f 0).object.dividedPowers
          ((tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i))) :=
  dividedPowerDifferential_eq_neg_sum_aux s f y S hS

end Crystalline

end

module

public import StacksFrontier.RingTheory.RelativeKoszulResolution

/-!
# Comparing the relative Koszul complex with the Koszul complex of the base

Let `A` be a commutative ring, `E` a type, `T = A[E]` and `S = T[E]`, and let `V` be a
`T`-module.  The degree-`j` term of the relative Koszul complex of `V`
(`MvPolynomial.relKoszulTerm`) is `(⋀_S^j (E →₀ S)) ⊗[T] V`, regarded as a `T`-module through
`MvPolynomial.diagShift`.

Let `X` be a `T`-module on which every variable acts by zero.  Tensoring the base-change map
`MvPolynomial.koszulBaseChange` with `X` on the left and `V` on the right then gives an
`A`-linear isomorphism
`X ⊗[A] ((⋀_T^j (E →₀ T)) ⊗[T] V) ≃ X ⊗[T] relKoszulTerm A E V j`
in every degree, and it is a map of complexes up to the sign `-1`.

## Main definitions

* `MvPolynomial.relKoszulCompareEquiv`: The comparison isomorphism in a single degree.

## Main results

* `MvPolynomial.exists_relKoszulCompareDegree`: Tensoring the base-change map with `X` and `V`
  is an `A`-linear isomorphism in each degree.
* `MvPolynomial.relKoszulCompareEquiv_chain_apply`: The comparison isomorphism carries the
  differential of the relative Koszul complex to the negative of the Koszul differential of `T`.
* `MvPolynomial.relKoszulCompareEquiv_naturality_apply`: The comparison isomorphism is natural
  in the module `V`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace MvPolynomial

/-! ### The base-change map on the chosen bases -/

section Base

variable (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]

omit [LinearOrder E] in
/-- The coefficient inclusion `(E →₀ T) → (E →₀ S)` sends the basis vector `single e 1` to
`single e 1`. -/
lemma coeffFinsuppMap_single_one (e : E) :
    coeffFinsuppMap A E (Finsupp.single e 1) =
      Finsupp.single e (1 : MvPolynomial E (MvPolynomial E A)) := by
  change Finsupp.mapRange
      (algebraMap (MvPolynomial E A) (MvPolynomial E (MvPolynomial E A))) (map_zero _)
      (Finsupp.single e 1) = _
  rw [Finsupp.mapRange_single, map_one]

/-- The base-change map sends the exterior-power basis vector of `⋀_T^j (E →₀ T)` attached to a
finset `s` to the one of `⋀_S^j (E →₀ S)` attached to the same finset. -/
lemma koszulBaseChange_exteriorBasis (j : ℕ) (s : {s : Finset E // s.card = j}) :
    koszulBaseChange A E j
        ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j s) =
      (Finsupp.basisSingleOne (R := MvPolynomial E (MvPolynomial E A))
        (ι := E)).exteriorPower j s := by
  have h1 : koszulBaseChange A E j
        ⟨ExteriorAlgebra.ιMulti (MvPolynomial E A) j
            (fun k => Finsupp.single (s.1.orderEmbOfFin s.2 k) (1 : MvPolynomial E A)),
          Koszul.ιMulti_mem j _⟩ =
      ⟨ExteriorAlgebra.ιMulti (MvPolynomial E (MvPolynomial E A)) j
          (coeffFinsuppMap A E ∘
            fun k => Finsupp.single (s.1.orderEmbOfFin s.2 k) (1 : MvPolynomial E A)),
        Koszul.ιMulti_mem j _⟩ :=
    Koszul.baseChangeMap_mk (coeffFinsuppMap A E) j _ _
  have h2 : (coeffFinsuppMap A E ∘
        fun k => Finsupp.single (s.1.orderEmbOfFin s.2 k) (1 : MvPolynomial E A)) =
      fun k : Fin j => Finsupp.single (s.1.orderEmbOfFin s.2 k)
        (1 : MvPolynomial E (MvPolynomial E A)) := by
    funext k
    exact coeffFinsuppMap_single_one A E _
  rw [variableExteriorBasis_apply A E j s, h1, h2,
    variableExteriorBasis_apply (MvPolynomial E A) E j s]

end Base

/-! ### The tensored contracting homotopy -/

section Homotopy

variable (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
  (X : Type max u v) [AddCommGroup X] [Module A X]

/-- The tensored contracting homotopy of the Koszul complex, in positive degree. -/
lemma lTensor_koszulTensorContract_homotopy_map (q n : ℕ) :
    (LinearMap.lTensor X
        (((Koszul.d (variableKoszulDual A E) (q + 1)).rTensor
          (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
            Ideal (MvPolynomial E A))).restrictScalars A)).comp
        (LinearMap.lTensor X (koszulTensorContract A E (q + 1) n)) +
      (LinearMap.lTensor X (koszulTensorContract A E q n)).comp
        (LinearMap.lTensor X
          (((Koszul.d (variableKoszulDual A E) q).rTensor
            (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) :
              Ideal (MvPolynomial E A))).restrictScalars A)) =
      LinearMap.lTensor X
        ((TensorProduct.map LinearMap.id
          (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ n) :
            Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) ≤
              Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n))
            ).restrictScalars A) := by
  rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_add]
  exact congrArg (fun f => LinearMap.lTensor X f) (koszulTensorContract_homotopy_map A E q n)

/-- The tensored contracting homotopy of the Koszul complex, in degree zero. -/
lemma lTensor_koszulTensorContract_homotopy_zero_map (n : ℕ) :
    (LinearMap.lTensor X
        (((Koszul.d (variableKoszulDual A E) 0).rTensor
          (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
            Ideal (MvPolynomial E A))).restrictScalars A)).comp
        (LinearMap.lTensor X (koszulTensorContract A E 0 n)) =
      LinearMap.lTensor X
        ((TensorProduct.map LinearMap.id
          (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ n) :
            Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) ≤
              Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n))
            ).restrictScalars A) := by
  rw [← LinearMap.lTensor_comp]
  exact congrArg (fun f => LinearMap.lTensor X f)
    (koszulTensorContract_homotopy_zero_map A E n)

end Homotopy

/-! ### The comparison in a single degree -/

section Compare

variable (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
  (V : Type max u v) [AddCommGroup V] [Module A V] [Module (MvPolynomial E A) V]
    [IsScalarTower A (MvPolynomial E A) V]
  (X : Type max u v) [AddCommGroup X] [Module A X] [Module (MvPolynomial E A) X]
    [IsScalarTower A (MvPolynomial E A) X]

/-- The degree-`j` term of the relative Koszul complex, as a `T`-module through `diagShift`, has
the same underlying additive group as `MvPolynomial.relKoszulType`; this is the identity, as an
additive equivalence. -/
def toRelKoszulTerm (j : ℕ) : relKoszulType A E V j ≃+ (relKoszulTerm A E V j) :=
  AddEquiv.refl _

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- `toRelKoszulTerm` carries the action of `diagShift A E t` to the action of `t`. -/
@[simp]
lemma toRelKoszulTerm_smul (j : ℕ) (t : MvPolynomial E A) (z : relKoszulType A E V j) :
    toRelKoszulTerm A E V j (diagShift A E t • z) = t • toRelKoszulTerm A E V j z := rfl

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] [Module A X]
  [IsScalarTower A (MvPolynomial E A) X] in
/-- If every variable of `T` kills `X`, then an element of the degree-`j` Koszul term over `S`
lying in the ideal generated by the `diagShift`-images of the variables dies in
`X ⊗[T] relKoszulTerm A E V j`. -/
lemma tmul_tmul_eq_zero_of_mem_diagShift_smul_top
    (hX : ∀ (e : E) (x : X), (MvPolynomial.X e : MvPolynomial E A) • x = 0)
    (j : ℕ) (x : X) (v : V)
    (η : ⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A)))
    (hη : η ∈ (Ideal.span (Set.range fun e : E => diagShift A E (MvPolynomial.X e))) •
      (⊤ : Submodule (MvPolynomial E (MvPolynomial E A))
        (⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A))))) :
    x ⊗ₜ[MvPolynomial E A] (toRelKoszulTerm A E V j (η ⊗ₜ[MvPolynomial E A] v)) = 0 := by
  let F : (relKoszulTerm A E V j) →ₗ[MvPolynomial E A]
      (X ⊗[MvPolynomial E A] (relKoszulTerm A E V j)) :=
    (TensorProduct.mk (MvPolynomial E A) X (relKoszulTerm A E V j)) x
  change F (toRelKoszulTerm A E V j (η ⊗ₜ[MvPolynomial E A] v)) = 0
  have hF : ∀ z : relKoszulTerm A E V j, F z = x ⊗ₜ[MvPolynomial E A] z := fun _ => rfl
  have hgen : ∀ r ∈ (Ideal.span (Set.range fun e : E => diagShift A E (MvPolynomial.X e))),
      ∀ n : ⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A)),
      F (toRelKoszulTerm A E V j ((r • n) ⊗ₜ[MvPolynomial E A] v)) = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, rfl⟩ := hy
      intro n
      change F (toRelKoszulTerm A E V j
        ((diagShift A E (MvPolynomial.X e) • n) ⊗ₜ[MvPolynomial E A] v)) = 0
      rw [show ((diagShift A E (MvPolynomial.X e) • n) ⊗ₜ[MvPolynomial E A] v :
            relKoszulType A E V j) =
          diagShift A E (MvPolynomial.X e) • (n ⊗ₜ[MvPolynomial E A] v) from
        (TensorProduct.smul_tmul' _ _ _).symm,
        toRelKoszulTerm_smul, map_smul, hF, TensorProduct.smul_tmul', hX e x,
        TensorProduct.zero_tmul]
    | zero =>
      intro n
      rw [zero_smul, TensorProduct.zero_tmul]
      exact F.map_zero
    | add a b _ _ ha hb =>
      intro n
      rw [add_smul, TensorProduct.add_tmul, map_add, map_add, ha n, hb n, add_zero]
    | smul c a _ ha =>
      intro n
      rw [smul_eq_mul, mul_smul, smul_comm]
      exact ha (c • n)
  refine Submodule.smul_induction_on hη (fun r hr n _ => hgen r hr n) ?_
  intro p q hp hq
  rw [TensorProduct.add_tmul, map_add, map_add, hp, hq, add_zero]

/-- **The comparison isomorphism in one degree.** Tensoring the base-change map with `X` and `V`
is an `A`-linear isomorphism from `X ⊗[A] ((⋀_T^j (E →₀ T)) ⊗[T] V)` onto
`X ⊗[T] relKoszulTerm A E V j`, sending `x ⊗ (ω ⊗ v)` to `x ⊗ (koszulBaseChange A E j ω ⊗ v)`.
-/
theorem exists_relKoszulCompareDegree (j : ℕ) :
    ∃ Φ : (X ⊗[A] ((⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A] V))
        ≃ₗ[A] (X ⊗[MvPolynomial E A] (relKoszulTerm A E V j)),
      ∀ (x : X) (ω : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) (v : V),
        Φ (x ⊗ₜ (ω ⊗ₜ v)) =
          x ⊗ₜ (toRelKoszulTerm A E V j ((koszulBaseChange A E j ω) ⊗ₜ v)) := by
  classical
  obtain ⟨ec, hecsmul, hecbasis⟩ := exists_relKoszulCoordEquiv A E j V
  let bT : Module.Basis {s : Finset E // s.card = j} (MvPolynomial E A)
      (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) :=
    (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j
  have hbase : ∀ s : {s : Finset E // s.card = j},
      koszulBaseChange A E j (bT s) =
        (Finsupp.basisSingleOne (R := MvPolynomial E (MvPolynomial E A))
          (ι := E)).exteriorPower j s := fun s => koszulBaseChange_exteriorBasis A E j s
  have hcoord : ∀ (g : {s : Finset E // s.card = j} →₀ MvPolynomial E A) (w : V)
      (i : {s : Finset E // s.card = j}),
      ec ((koszulBaseChange A E j (Finsupp.linearCombination (MvPolynomial E A) bT g)) ⊗ₜ w) i =
        (1 : MvPolynomial E A) ⊗ₜ (g i • w) := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero =>
      intro w i
      simp only [LinearMap.map_zero, TensorProduct.zero_tmul, LinearEquiv.map_zero,
        Finsupp.zero_apply, zero_smul, TensorProduct.tmul_zero]
    | add g₁ g₂ h₁ h₂ =>
      intro w i
      rw [map_add, map_add, TensorProduct.add_tmul, map_add, Finsupp.add_apply, h₁ w i, h₂ w i,
        Finsupp.add_apply, add_smul, TensorProduct.tmul_add]
    | single s t =>
      intro w i
      rw [Finsupp.linearCombination_single, map_smul, hbase s, TensorProduct.smul_tmul,
        hecbasis s (t • w)]
      by_cases h : s = i
      · subst h
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne' h, Finsupp.single_eq_of_ne' h, zero_smul,
          TensorProduct.tmul_zero]
  have hcoord' : ∀ (ω : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) (w : V)
      (i : {s : Finset E // s.card = j}),
      ec ((koszulBaseChange A E j ω) ⊗ₜ w) i =
        (1 : MvPolynomial E A) ⊗ₜ (bT.repr ω i • w) := by
    intro ω w i
    have h := hcoord (bT.repr ω) w i
    rw [bT.linearCombination_repr ω] at h
    exact h
  let ec' : (relKoszulTerm A E V j) ≃ₗ[MvPolynomial E A]
      ({s : Finset E // s.card = j} →₀ (MvPolynomial E A ⊗[A] V)) :=
    { toFun := ec.toFun
      map_add' := ec.map_add'
      map_smul' := hecsmul
      invFun := ec.invFun
      left_inv := ec.left_inv
      right_inv := ec.right_inv }
  let Ψ : (X ⊗[MvPolynomial E A] (relKoszulTerm A E V j)) ≃ₗ[MvPolynomial E A]
      ({s : Finset E // s.card = j} →₀ (X ⊗[A] V)) :=
    ((LinearEquiv.lTensor X ec').trans
        (TensorProduct.finsuppRight (MvPolynomial E A) (MvPolynomial E A) X
          (MvPolynomial E A ⊗[A] V) {s : Finset E // s.card = j})).trans
      (Finsupp.mapRange.linearEquiv
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial E A)
          (MvPolynomial E A) X V))
  let cT : ((⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A] V)
      ≃ₗ[MvPolynomial E A] ({s : Finset E // s.card = j} →₀ V) :=
    (LinearEquiv.rTensor V bT.repr).trans
      (TensorProduct.finsuppScalarLeft (MvPolynomial E A) V {s : Finset E // s.card = j})
  let Ω : (X ⊗[A] ((⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A] V))
      ≃ₗ[A] ({s : Finset E // s.card = j} →₀ (X ⊗[A] V)) :=
    (LinearEquiv.lTensor X (cT.restrictScalars A)).trans
      (TensorProduct.finsuppRight A A X V {s : Finset E // s.card = j})
  refine ⟨Ω.trans (Ψ.restrictScalars A).symm, fun x ω v => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  refine Finsupp.ext fun i => ?_
  have hΩ : Ω (x ⊗ₜ (ω ⊗ₜ v)) i = x ⊗ₜ (bT.repr ω i • v) := by
    change (TensorProduct.finsuppRight A A X V {s : Finset E // s.card = j})
        (LinearEquiv.lTensor X (cT.restrictScalars A) (x ⊗ₜ (ω ⊗ₜ v))) i = _
    rw [LinearEquiv.lTensor_tmul, TensorProduct.finsuppRight_apply_tmul_apply]
    congr 1
    change (TensorProduct.finsuppScalarLeft (MvPolynomial E A) V {s : Finset E // s.card = j})
      (LinearEquiv.rTensor V bT.repr (ω ⊗ₜ v)) i = _
    rw [LinearEquiv.rTensor_tmul, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  have hΨ : (Ψ.restrictScalars A)
      (x ⊗ₜ (toRelKoszulTerm A E V j ((koszulBaseChange A E j ω) ⊗ₜ v))) i =
      x ⊗ₜ (bT.repr ω i • v) := by
    change (Finsupp.mapRange.linearEquiv
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial E A)
          (MvPolynomial E A) X V))
        ((TensorProduct.finsuppRight (MvPolynomial E A) (MvPolynomial E A) X
            (MvPolynomial E A ⊗[A] V) {s : Finset E // s.card = j})
          (LinearEquiv.lTensor X ec'
            (x ⊗ₜ (toRelKoszulTerm A E V j ((koszulBaseChange A E j ω) ⊗ₜ v))))) i = _
    rw [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply, LinearEquiv.lTensor_tmul,
      TensorProduct.finsuppRight_apply_tmul_apply]
    change TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial E A)
        (MvPolynomial E A) X V (x ⊗ₜ (ec ((koszulBaseChange A E j ω) ⊗ₜ v) i)) = _
    rw [hcoord' ω v i, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [hΩ, hΨ]

/-- The comparison isomorphism in a single degree. -/
def relKoszulCompareEquiv (j : ℕ) :
    (X ⊗[A] ((⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A] V))
      ≃ₗ[A] (X ⊗[MvPolynomial E A] (relKoszulTerm A E V j)) :=
  (exists_relKoszulCompareDegree A E V X j).choose

/-- The comparison isomorphism sends `x ⊗ (ω ⊗ v)` to `x ⊗ (koszulBaseChange A E j ω ⊗ v)`.
-/
lemma relKoszulCompareEquiv_tmul (j : ℕ) (x : X)
    (ω : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) (v : V) :
    relKoszulCompareEquiv A E V X j (x ⊗ₜ (ω ⊗ₜ v)) =
      x ⊗ₜ (toRelKoszulTerm A E V j ((koszulBaseChange A E j ω) ⊗ₜ v)) :=
  (exists_relKoszulCompareDegree A E V X j).choose_spec x ω v

/-- The comparison isomorphism carries the differential of the relative Koszul complex to the
negative of the Koszul differential of the base. -/
lemma relKoszulCompareEquiv_chain
    (hX : ∀ (e : E) (x : X), (MvPolynomial.X e : MvPolynomial E A) • x = 0)
    (j : ℕ) (x : X) (ω : ⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A)) (v : V) :
    LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulDiff A E V j))).hom)
        (relKoszulCompareEquiv A E V X (j + 1) (x ⊗ₜ (ω ⊗ₜ v))) =
      - relKoszulCompareEquiv A E V X j
        (x ⊗ₜ ((Koszul.d (variableKoszulDual A E) j ω) ⊗ₜ v)) := by
  have hd : ∀ z : relKoszulType A E V (j + 1),
      (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulDiff A E V j))).hom)
        (toRelKoszulTerm A E V (j + 1) z) =
        toRelKoszulTerm A E V j (relKoszulDiff A E V j z) := fun _ => rfl
  have hvanish : x ⊗ₜ[MvPolynomial E A] (toRelKoszulTerm A E V j
      ((Koszul.d (diagShiftVariableDual A E) j
        (koszulBaseChange A E (j + 1) ω)) ⊗ₜ[MvPolynomial E A] v)) = 0 := by
    refine tmul_tmul_eq_zero_of_mem_diagShift_smul_top A E V X hX j x v _ ?_
    refine Koszul.d_mem_smul_top
      (Ideal.span (Set.range fun e : E => diagShift A E (MvPolynomial.X e)))
      (diagShiftVariableDual A E) (fun w => ?_) j (koszulBaseChange A E (j + 1) ω)
    change (Finsupp.linearCombination _ fun e => diagShift A E (MvPolynomial.X e)) w ∈ _
    rw [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.smul_mem _ _ (Ideal.subset_span ⟨e, rfl⟩)
  have htsub : ∀ a b : relKoszulTerm A E V j,
      x ⊗ₜ[MvPolynomial E A] (a - b) =
        x ⊗ₜ[MvPolynomial E A] a - x ⊗ₜ[MvPolynomial E A] b := fun a b =>
    map_sub (TensorProduct.mk (MvPolynomial E A) X (relKoszulTerm A E V j) x) a b
  have hmain : x ⊗ₜ[MvPolynomial E A] (toRelKoszulTerm A E V j
        (relKoszulDiff A E V j
          ((koszulBaseChange A E (j + 1) ω) ⊗ₜ[MvPolynomial E A] v))) =
      - (x ⊗ₜ[MvPolynomial E A] (toRelKoszulTerm A E V j
        ((koszulBaseChange A E j (Koszul.d (variableKoszulDual A E) j ω))
          ⊗ₜ[MvPolynomial E A] v))) := by
    rw [relKoszulDiff_tmul, koszul_d_variableKoszulDual_eq, TensorProduct.sub_tmul, map_sub,
      htsub, hvanish, zero_sub, koszulBaseChange_d]
  exact ((congrArg (LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
        (ModuleCat.ofHom (relKoszulDiff A E V j))).hom))
      (relKoszulCompareEquiv_tmul A E V X (j + 1) x ω v)).trans
    ((congrArg (fun z : relKoszulTerm A E V j => x ⊗ₜ[MvPolynomial E A] z)
      (hd ((koszulBaseChange A E (j + 1) ω) ⊗ₜ[MvPolynomial E A] v))).trans
      hmain)).trans
    (congrArg (fun y : X ⊗[MvPolynomial E A] (relKoszulTerm A E V j) => -y)
      (relKoszulCompareEquiv_tmul A E V X j x (Koszul.d (variableKoszulDual A E) j ω) v).symm)


/-- The chain property, at a pure tensor with a general element of the Koszul term. -/
lemma relKoszulCompareEquiv_chain_tmul
    (hX : ∀ (e : E) (x : X), (MvPolynomial.X e : MvPolynomial E A) • x = 0)
    (j : ℕ) (x : X) (w : (⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A))
      ⊗[MvPolynomial E A] V) :
    LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulDiff A E V j))).hom)
        (relKoszulCompareEquiv A E V X (j + 1) (x ⊗ₜ w)) =
      - relKoszulCompareEquiv A E V X j
        (LinearMap.lTensor X
          (((Koszul.d (variableKoszulDual A E) j).rTensor V).restrictScalars A) (x ⊗ₜ w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul ω v =>
    simp only [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars, LinearMap.rTensor_tmul]
    exact relKoszulCompareEquiv_chain A E V X hX j x ω v
  | add a b ha hb =>
    simp only [TensorProduct.tmul_add, map_add, neg_add]
    exact congr (congrArg (· + ·) ha) hb

/-- The comparison isomorphism carries the differential of the relative Koszul complex to the
negative of the Koszul differential of the base, on an arbitrary element. -/
lemma relKoszulCompareEquiv_chain_apply
    (hX : ∀ (e : E) (x : X), (MvPolynomial.X e : MvPolynomial E A) • x = 0)
    (j : ℕ) (z : X ⊗[A] ((⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A))
      ⊗[MvPolynomial E A] V)) :
    LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulDiff A E V j))).hom)
        (relKoszulCompareEquiv A E V X (j + 1) z) =
      - relKoszulCompareEquiv A E V X j
        (LinearMap.lTensor X
          (((Koszul.d (variableKoszulDual A E) j).rTensor V).restrictScalars A) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x w => exact relKoszulCompareEquiv_chain_tmul A E V X hX j x w
  | add a b ha hb =>
    simp only [map_add, neg_add]
    exact congr (congrArg (· + ·) ha) hb

/-- Naturality in the second variable, at a pure tensor with a general element. -/
lemma relKoszulCompareEquiv_naturality_tmul
    (V' : Type max u v) [AddCommGroup V'] [Module A V'] [Module (MvPolynomial E A) V']
      [IsScalarTower A (MvPolynomial E A) V']
    (f : V →ₗ[MvPolynomial E A] V') (j : ℕ) (x : X)
    (w : (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A] V) :
    LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulMapTerm A E f j))).hom)
        (relKoszulCompareEquiv A E V X j (x ⊗ₜ w)) =
      relKoszulCompareEquiv A E V' X j
        (LinearMap.lTensor X
          ((TensorProduct.map (LinearMap.id (R := MvPolynomial E A)) f).restrictScalars A)
          (x ⊗ₜ w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul ω v =>
    have hd : (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulMapTerm A E f j))).hom)
        (toRelKoszulTerm A E V j
          ((koszulBaseChange A E j ω) ⊗ₜ[MvPolynomial E A] v)) =
        toRelKoszulTerm A E V' j
          ((koszulBaseChange A E j ω) ⊗ₜ[MvPolynomial E A] (f v)) := rfl
    have hlt : LinearMap.lTensor X
        ((TensorProduct.map (LinearMap.id (R := MvPolynomial E A)) f).restrictScalars A)
        (x ⊗ₜ[A] (ω ⊗ₜ[MvPolynomial E A] v)) =
        x ⊗ₜ[A] (ω ⊗ₜ[MvPolynomial E A] (f v)) := rfl
    exact ((congrArg (LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulMapTerm A E f j))).hom))
        (relKoszulCompareEquiv_tmul A E V X j x ω v)).trans
      ((congrArg (fun z : relKoszulTerm A E V' j => x ⊗ₜ[MvPolynomial E A] z) hd).trans
        ((relKoszulCompareEquiv_tmul A E V' X j x ω (f v)).symm.trans
          (congrArg (relKoszulCompareEquiv A E V' X j) hlt.symm))))
  | add a b ha hb =>
    simp only [TensorProduct.tmul_add, map_add]
    exact congr (congrArg (· + ·) ha) hb

/-- The comparison isomorphism is natural in the second variable, on an arbitrary element. -/
lemma relKoszulCompareEquiv_naturality_apply
    (V' : Type max u v) [AddCommGroup V'] [Module A V'] [Module (MvPolynomial E A) V']
      [IsScalarTower A (MvPolynomial E A) V']
    (f : V →ₗ[MvPolynomial E A] V') (j : ℕ)
    (z : X ⊗[A] ((⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A] V)) :
    LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulMapTerm A E f j))).hom)
        (relKoszulCompareEquiv A E V X j z) =
      relKoszulCompareEquiv A E V' X j
        (LinearMap.lTensor X
          ((TensorProduct.map (LinearMap.id (R := MvPolynomial E A)) f).restrictScalars A) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x w => exact relKoszulCompareEquiv_naturality_tmul A E V X V' f j x w
  | add a b ha hb =>
    simp only [map_add]
    exact congr (congrArg (· + ·) ha) hb

/-- Transfer of the cycle condition: if the comparison image of `z` is a cycle for the relative
Koszul differential, then `z` is a cycle for the Koszul differential of the base. -/
lemma relKoszulCompareEquiv_symm_cycle
    (hX : ∀ (e : E) (x : X), (MvPolynomial.X e : MvPolynomial E A) • x = 0) (j : ℕ)
    (x : X ⊗[MvPolynomial E A] (relKoszulTerm A E V (j + 1)))
    (hx : LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
        (ModuleCat.ofHom (relKoszulDiff A E V j))).hom) x = 0) :
    LinearMap.lTensor X
        (((Koszul.d (variableKoszulDual A E) j).rTensor V).restrictScalars A)
        ((relKoszulCompareEquiv A E V X (j + 1)).symm x) = 0 := by
  have hd := relKoszulCompareEquiv_chain_apply A E V X hX j
    ((relKoszulCompareEquiv A E V X (j + 1)).symm x)
  have h0 := (congrArg (LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
      (ModuleCat.ofHom (relKoszulDiff A E V j))).hom))
    ((relKoszulCompareEquiv A E V X (j + 1)).apply_symm_apply x)).trans hx
  exact (relKoszulCompareEquiv A E V X j).map_eq_zero_iff.mp
    (neg_eq_zero.mp (hd.symm.trans h0))

/-- Identification of a boundary: a contraction of the base Koszul complex which, after the
inclusion, splits the differential produces a boundary for the relative Koszul complex. -/
lemma relKoszulCompareEquiv_boundary
    (V' : Type max u v) [AddCommGroup V'] [Module A V'] [Module (MvPolynomial E A) V']
      [IsScalarTower A (MvPolynomial E A) V']
    (f : V →ₗ[MvPolynomial E A] V')
    (hX : ∀ (e : E) (x : X), (MvPolynomial.X e : MvPolynomial E A) • x = 0) (j : ℕ)
    (c : (X ⊗[A] ((⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A] V)) →ₗ[A]
      (X ⊗[A] ((⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A))
        ⊗[MvPolynomial E A] V')))
    (x : X ⊗[MvPolynomial E A] (relKoszulTerm A E V j))
    (hc : LinearMap.lTensor X
        (((Koszul.d (variableKoszulDual A E) j).rTensor V').restrictScalars A)
        (c ((relKoszulCompareEquiv A E V X j).symm x)) =
      LinearMap.lTensor X
        ((TensorProduct.map (LinearMap.id (R := MvPolynomial E A)) f).restrictScalars A)
        ((relKoszulCompareEquiv A E V X j).symm x)) :
    LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
          (ModuleCat.ofHom (relKoszulDiff A E V' j))).hom)
        (- relKoszulCompareEquiv A E V' X (j + 1)
          (c ((relKoszulCompareEquiv A E V X j).symm x))) =
      LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
        (ModuleCat.ofHom (relKoszulMapTerm A E f j))).hom) x := by
  have hchain := relKoszulCompareEquiv_chain_apply A E V' X hX j
    (c ((relKoszulCompareEquiv A E V X j).symm x))
  have hnat := relKoszulCompareEquiv_naturality_apply A E V X V' f j
    ((relKoszulCompareEquiv A E V X j).symm x)
  exact (map_neg _ _).trans ((congrArg Neg.neg hchain).trans ((neg_neg _).trans
    ((congrArg (relKoszulCompareEquiv A E V' X j) hc).trans
      (hnat.symm.trans
        (congrArg (LinearMap.lTensor X (((ModuleCat.restrictScalars (diagShift A E)).map
            (ModuleCat.ofHom (relKoszulMapTerm A E f j))).hom))
          ((relKoszulCompareEquiv A E V X j).apply_symm_apply x))))))

end Compare

end MvPolynomial

end

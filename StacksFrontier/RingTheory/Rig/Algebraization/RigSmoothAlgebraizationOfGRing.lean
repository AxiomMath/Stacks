module

public import StacksFrontier.RingTheory.Rig.Algebraization.RigSmoothAlgebraization
import all StacksFrontier.RingTheory.Rig.Algebraization.RigSmoothAlgebraization
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianGRing

/-!
# Algebraization of rig-smooth algebras over a Noetherian G-ring

Let `A` be a Noetherian G-ring and `I` an ideal of `A`. If `B` is an `I`-adically complete
`A`-algebra topologically of finite type which is rig-smooth over `(A, I)`, and presentations of
rig-smooth objects over `(A, I)` present the same algebra after a small enough perturbation
(`Rig.PerturbationStableQuotients A I`), then `B` is the `I`-adic completion of a finite type
`A`-algebra.

## Main results

* `Rig.perturbationStableQuotients_of_pow_eq_bot`: `Rig.PerturbationStableQuotients` holds for
  a nilpotent ideal, in particular for the zero ideal.
* `Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth'`: over a Noetherian G-ring, a
  rig-smooth `B` satisfying `Rig.PerturbationStableQuotients` is the completion of a finite type
  algebra.

## References

* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 0AH5](https://stacks.math.columbia.edu/tag/0AH5)
* [Stacks Project, Tag 0GAR](https://stacks.math.columbia.edu/tag/0GAR)
* [Stacks Project, Tag 0GAT](https://stacks.math.columbia.edu/tag/0GAT)
-/

@[expose] public section

universe u v

namespace Rig

open AdicFiniteTypeAlgebra

/-! ### Perturbation-stable quotients for a nilpotent ideal -/

/-- `Rig.PerturbationStableQuotients A I` holds for a nilpotent ideal `I`, that is, whenever
`I ^ N = ⊥` for some `N`. -/
public theorem perturbationStableQuotients_of_pow_eq_bot (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (N : ℕ) (hN : I ^ N = ⊥) :
    PerturbationStableQuotients.{u, v} A I := by
  intro r m t B g K _ hpres _
  refine ⟨N, fun g' K' _ hg _ ↦ ?_⟩
  obtain ⟨e⟩ := hpres
  have hle : (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ N ≤ ⊥ :=
    le_of_eq (by rw [← Ideal.map_pow, hN, Ideal.map_bot])
  have hgg : g = g' := LinearMap.ext fun x ↦ sub_eq_zero.mp (Ideal.mem_bot.mp (hle (hg x)))
  exact ⟨hgg ▸ e.symm⟩

/-! ### Approximation over the henselization -/

/-- Precomposing a ring hom compatible with `f` and sending `I` into `J` with a map of `R`-algebras
preserves both properties. -/
private theorem comp_mem_comap_of_comp_algebraMap_eq {R S S' T : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [CommRing T] [Algebra R S] [Algebra R S'] {I : Ideal R} {J : Ideal T}
    {f : R →+* T} {k : S →+* S'} (hk : k.comp (algebraMap R S) = algebraMap R S') {g : S' →+* T}
    (hg : g.comp (algebraMap R S') = f ∧ I.map (algebraMap R S') ≤ J.comap g) :
    (g.comp k).comp (algebraMap R S) = f ∧ I.map (algebraMap R S) ≤ J.comap (g.comp k) := by
  refine ⟨by rw [RingHom.comp_assoc, hk, hg.1], ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have := (Ideal.map_le_iff_le_comap.mp hg.2) hx
  rwa [Ideal.mem_comap, ← hk] at this

/-- The henselization of `(R, I)` is initial among henselian pairs under `(R, I)`. -/
private theorem existsUnique_lift_henselization (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ (T : Type u) (_ : CommRing T) (J : Ideal T), HenselianPair T J →
      ∀ f : R →+* T, I ≤ J.comap f →
        ∃! q : (henselization R I : Type u) →+* T,
          q.comp (algebraMap R (henselization R I : Type u)) = f ∧
            I.map (algebraMap R (henselization R I : Type u)) ≤ J.comap q := by
  intro T hT J hJ f hf
  let : CommRing T := hT
  obtain ⟨H₀, hH₀ring, ι₀, hH₀pair, hH₀up⟩ := exists_henselization R I
  let : CommRing H₀ := hH₀ring
  let : Algebra R H₀ := ι₀.toAlgebra
  have hH₀pair' : HenselianPair H₀ (I.map (algebraMap R H₀)) := by
    simpa only [RingHom.algebraMap_toAlgebra] using hH₀pair
  obtain ⟨eH⟩ := nonempty_algEquiv_henselization (R := R) (I := I) H₀ hH₀pair' hH₀up
  let H := (henselization R I : Type u)
  have hbase : eH.toRingEquiv.toRingHom.comp (algebraMap R H) = algebraMap R H₀ :=
    RingHom.ext eH.commutes
  have hbaseSymm : eH.symm.toRingEquiv.toRingHom.comp (algebraMap R H₀) = algebraMap R H :=
    RingHom.ext eH.symm.commutes
  obtain ⟨g₀, hg₀, huniq₀⟩ := hH₀up T hT J hJ f hf
  refine ⟨g₀.comp eH.toRingEquiv.toRingHom, comp_mem_comap_of_comp_algebraMap_eq hbase hg₀,
    fun g' hg' ↦ ?_⟩
  exact RingHom.ext fun x ↦ by
    simpa using congrArg (fun k : H₀ →+* T ↦ k (eH x))
      (huniq₀ _ (comp_mem_comap_of_comp_algebraMap_eq hbaseSymm hg'))

/-- Over a Noetherian henselian pair `(H, J)` with ind-smooth completion map, a solution in
`H^∧` of the bilinear system `∑ᵢ xᵢ yⱼᵢ = 0` is approximated modulo `J ^ N` by one in `H`. -/
private theorem exists_approx_sum_mul_eq_zero {H : Type u} [CommRing H] [IsNoetherianRing H]
    {J : Ideal H} (hJ : HenselianPair H J)
    (hind : Stacks.Smoothing.IsIndSmoothAdicCompletion H J) {m t : ℕ}
    (x : Fin m → AdicCompletion J H) (y : Fin t → Fin m → AdicCompletion J H)
    (hxy : ∀ j, ∑ i, x i * y j i = 0) {N : ℕ} (hN : N ≠ 0) :
    ∃ (x' : Fin m → H) (y' : Fin t → Fin m → H), (∀ j, ∑ i, x' i * y' j i = 0) ∧
      (∀ i, x i - algebraMap H (AdicCompletion J H) (x' i) ∈
        (J ^ N).map (algebraMap H (AdicCompletion J H))) ∧
      ∀ j i, y j i - algebraMap H (AdicCompletion J H) (y' j i) ∈
        (J ^ N).map (algebraMap H (AdicCompletion J H)) := by
  classical
  let e : Fin m ⊕ Fin (m * t) ≃ Fin (m + m * t) := finSumFinEquiv
  let gi (i : Fin m) : Fin (m + m * t) := e (Sum.inl i)
  let ri (i : Fin m) (j : Fin t) : Fin (m + m * t) := e (Sum.inr (finProdFinEquiv (i, j)))
  let eqs : Fin t → MvPolynomial (Fin (m + m * t)) H := fun j ↦
    ∑ i, MvPolynomial.X (gi i) * MvPolynomial.X (ri i j)
  let z : Fin (m + m * t) → AdicCompletion J H := fun q ↦
    match e.symm q with
    | Sum.inl i => x i
    | Sum.inr k => y k.modNat k.divNat
  have hprod (i : Fin m) (j : Fin t) :
      finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) := finProdFinEquiv.left_inv _
  have hprodMod (i : Fin m) (j : Fin t) : (finProdFinEquiv (i, j)).modNat = j :=
    congrArg Prod.snd (hprod i j)
  have hprodDiv (i : Fin m) (j : Fin t) : (finProdFinEquiv (i, j)).divNat = i :=
    congrArg Prod.fst (hprod i j)
  have hgi (i : Fin m) : z (gi i) = x i := by simp [z, gi, e]
  have hri (i : Fin m) (j : Fin t) : z (ri i j) = y j i := by
    simp [z, ri, e, hprodMod, hprodDiv]
  obtain ⟨a, haClose, haEq⟩ := Stacks.Smoothing.exists_solution_of_henselianPair hJ hind eqs z
    (fun j ↦ by simpa [eqs, hgi, hri] using hxy j) hN
  exact ⟨fun i ↦ a (gi i), fun j i ↦ a (ri i j), fun j ↦ by simpa [eqs] using haEq j,
    fun i ↦ by simpa only [hgi] using haClose (gi i),
    fun j i ↦ by simpa only [hri] using haClose (ri i j)⟩

/-- Along an `A`-algebra isomorphism `P ≃ H^∧` with the `I H`-adic completion of `H`, the
quotient of `P` by the image of an ideal `J` of `H` is the `I`-adic completion of `H ⧸ J`. -/
private theorem nonempty_quotient_algEquiv_adicCompletion
    {A H P : Type u} [CommRing A] [CommRing H] [IsNoetherianRing H] [CommRing P]
    [Algebra A H] [Algebra A P] (I : Ideal A) (K : Ideal H) (hK : K = I.map (algebraMap A H))
    (e : P ≃ₐ[A] AdicCompletion K H) (J : Ideal H) :
    Nonempty ((P ⧸ (J.map (algebraMap H (AdicCompletion K H))).map
        e.symm.toRingEquiv.toRingHom) ≃ₐ[A]
      AdicCompletion (I.map (algebraMap A (H ⧸ J))) (H ⧸ J)) := by
  let eHQH := adicCompletionQuotientAlgEquiv K J
  have hc (c : A) : algebraMap A (AdicCompletion (K.map (algebraMap H (H ⧸ J))) (H ⧸ J)) c =
      algebraMap H (AdicCompletion (K.map (algebraMap H (H ⧸ J))) (H ⧸ J))
        (algebraMap A H c) := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rfl
  have hKJ : K.map (algebraMap H (H ⧸ J)) = I.map (algebraMap A (H ⧸ J)) := by
    rw [hK, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let eHQ : (AdicCompletion K H ⧸ J.map (algebraMap H (AdicCompletion K H))) ≃ₐ[A]
      AdicCompletion (K.map (algebraMap H (H ⧸ J))) (H ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := eHQH.toRingEquiv) fun c ↦ by
      rw [hc]
      exact eHQH.commutes _
  exact ⟨(Ideal.quotientEquivAlg _ _ e.symm rfl).symm.trans
    (eHQ.trans (adicCompletionAlgEquivOfIdealEq _ _ hKJ))⟩

/-- Let `(H, I H)` be a Noetherian henselian pair with ind-smooth completion map and `P ≃ H^∧`. A
system `∑ᵢ genᵢ relⱼᵢ = 0` in `P` is approximated modulo `(I P) ^ n0` by one whose generators
present the completion of a quotient of `H`. -/
private theorem exists_approx_quotient_algEquiv_adicCompletion
    {A H P : Type u} [CommRing A] [CommRing H] [IsNoetherianRing H] [CommRing P]
    [Algebra A H] [Algebra A P] (I : Ideal A) (IH : Ideal H)
    (hIH : IH = I.map (algebraMap A H)) (hH : HenselianPair H IH)
    (hind : Stacks.Smoothing.IsIndSmoothAdicCompletion H IH)
    (e : P ≃ₐ[A] AdicCompletion IH H) {m t : ℕ} (gen : Fin m → P)
    (rel : Fin t → Fin m → P) (hrel : ∀ j, ∑ i, gen i * rel j i = 0) (n0 : ℕ) :
    ∃ (gen' : Fin m → P) (rel' : Fin t → Fin m → P),
      (∀ j, ∑ i, gen' i * rel' j i = 0) ∧
      (∀ i, gen i - gen' i ∈ I.map (algebraMap A P) ^ n0) ∧
      (∀ j i, rel j i - rel' j i ∈ I.map (algebraMap A P) ^ n0) ∧
      ∃ J : Ideal H, Nonempty ((P ⧸ Ideal.span (Set.range gen')) ≃ₐ[A]
        AdicCompletion (I.map (algebraMap A (H ⧸ J))) (H ⧸ J)) := by
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_approx_sum_mul_eq_zero hH hind (fun i ↦ e (gen i))
    (fun j i ↦ e (rel j i))
    (fun j ↦ by simpa only [map_sum, map_mul, map_zero] using congrArg e (hrel j))
    (N := max n0 1) (by lia)
  have hφ : (e.symm.toRingEquiv.toRingHom.comp (algebraMap H (AdicCompletion IH H))).comp
      (algebraMap A H) = algebraMap A P :=
    RingHom.ext e.symm.commutes
  have hIdeal : ((IH ^ max n0 1).map (algebraMap H (AdicCompletion IH H))).map
      e.symm.toRingEquiv.toRingHom = I.map (algebraMap A P) ^ max n0 1 := by
    rw [Ideal.map_map, Ideal.map_pow, ← hφ, ← Ideal.map_map (algebraMap A H), ← hIH]
  have hclose (z : AdicCompletion IH H) (w : H)
      (hz : z - algebraMap H (AdicCompletion IH H) w ∈
        (IH ^ max n0 1).map (algebraMap H (AdicCompletion IH H))) :
      e.symm z - e.symm (algebraMap H (AdicCompletion IH H) w) ∈
        I.map (algebraMap A P) ^ n0 := by
    have hm := Ideal.mem_map_of_mem e.symm.toRingEquiv.toRingHom hz
    rw [map_sub, hIdeal] at hm
    exact Ideal.pow_le_pow_right (le_max_left n0 1) (by simpa using hm)
  refine ⟨fun i ↦ e.symm (algebraMap H (AdicCompletion IH H) (x i)),
    fun j i ↦ e.symm (algebraMap H (AdicCompletion IH H) (y j i)), fun j ↦ ?_,
    fun i ↦ by simpa using hclose _ _ (hx i), fun j i ↦ by simpa using hclose _ _ (hy j i),
    Ideal.span (Set.range x), ?_⟩
  · simpa only [map_sum, map_mul, map_zero] using
      congrArg (fun z ↦ e.symm (algebraMap H (AdicCompletion IH H) z)) (hxy j)
  · obtain ⟨eJ⟩ := nonempty_quotient_algEquiv_adicCompletion I IH hIH e (Ideal.span (Set.range x))
    refine ⟨(Ideal.quotientEquivAlgOfEq A ?_).trans eJ⟩
    rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl

/-- Let `A` be a Noetherian G-ring, `P = A[x₁, …, x_r]^∧` the `I`-adically completed polynomial
algebra, and `∑ᵢ genᵢ relⱼᵢ = 0` a system in `P`. It is approximated modulo `(I P) ^ n0` by a
system `∑ᵢ gen'ᵢ rel'ⱼᵢ = 0` such that `P / (gen')` is the `I`-adic completion of a finite type
`A`-algebra. -/
private theorem exists_approximated_presentation'
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsGRing A) (I : Ideal A)
    (r m t : ℕ) (gen : Fin m → completedPolynomialAlgebra I r)
    (rel : Fin t → Fin m → completedPolynomialAlgebra I r)
    (hrel : ∀ j, ∑ i, gen i * rel j i = 0) (n0 : ℕ) :
    ∃ (gen' : Fin m → completedPolynomialAlgebra I r)
      (rel' : Fin t → Fin m → completedPolynomialAlgebra I r),
      (∀ j, ∑ i, gen' i * rel' j i = 0) ∧
      (∀ i, gen i - gen' i ∈
        (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n0) ∧
      (∀ (j : Fin t) (i : Fin m), rel j i - rel' j i ∈
        (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n0) ∧
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C),
        Nonempty ((completedPolynomialAlgebra I r ⧸ Ideal.span (Set.range gen'))
          ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  classical
  let R := MvPolynomial (Fin r) A
  let IR : Ideal R := I.map (MvPolynomial.C : A →+* R)
  let P := AdicCompletion IR R
  let H := (henselization R IR : Type u)
  let : Algebra A H := ((algebraMap R H).comp (algebraMap A R)).toAlgebra
  have : IsScalarTower A R H := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let IH : Ideal H := IR.map (algebraMap R H)
  have hHP' : HenselianPair H IH := by
    simpa only [IH] using henselianPair_henselization R IR
  have hHup := existsUnique_lift_henselization R IR
  have : IsNoetherianRing H :=
    (henselization_isNoetherian_and_completion_equiv R IR H hHP' hHup).2.1
  have hGR : IsGRing H :=
    isGRing_henselization (isGRing_of_essFiniteType hA) IR H hHP' hHup
  let Q := AdicCompletion IH H
  let completionEquiv : P ≃+* Q :=
    RingEquiv.ofBijective (adicCompletionMap (algebraMap R H) IR IH le_rfl)
      (henselization_isNoetherian_and_completion_equiv R IR H hHP' hHup).1
  have hcR (x : R) : completionEquiv (algebraMap R P x) = algebraMap H Q (algebraMap R H x) :=
    congrArg (fun k : R →+* Q ↦ k x)
      (adicCompletionMap_comp_algebraMap (algebraMap R H) IR IH le_rfl)
  have hcompletionAlgebra (a : A) : completionEquiv (algebraMap A P a) = algebraMap A Q a := by
    rw [IsScalarTower.algebraMap_apply A R P, hcR]
    rfl
  have hIRH : IH = I.map (algebraMap A H) := by
    change (I.map (MvPolynomial.C : A →+* R)).map (algebraMap R H) = _
    rw [Ideal.map_map]
    congr 1
  obtain ⟨gen', rel', hrelZero, hgenClose, hrelClose, JH, ⟨ePQ⟩⟩ :=
    exists_approx_quotient_algEquiv_adicCompletion I IH hIRH hHP'
      (Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing hGR IH)
      (AlgEquiv.ofRingEquiv (f := completionEquiv) hcompletionAlgebra) gen rel hrel n0
  have : Algebra.FiniteType A R := inferInstance
  obtain ⟨C₀, hC₀ring, hC₀alg, hC₀ft, ⟨eGAS⟩⟩ :=
    exists_finiteType_adicCompletion_algEquiv_henselization_quotient.{u, u} A R I JH
  let : CommRing C₀ := hC₀ring
  let : Algebra A C₀ := hC₀alg
  let eGAS' : AdicCompletion (I.map (algebraMap A C₀)) C₀ ≃ₐ[A]
      AdicCompletion (I.map (algebraMap A (H ⧸ JH))) (H ⧸ JH) := eGAS
  exact ⟨gen', rel', hrelZero, hgenClose, hrelClose, C₀, inferInstance, inferInstance, hC₀ft,
    ⟨ePQ.trans eGAS'.symm⟩⟩

/-! ### Algebraization -/

/-- Let `I` be an ideal of a Noetherian G-ring `A` and let `B` be an `I`-adically complete
`A`-algebra topologically of finite type. If `B` is rig-smooth over `(A, I)` and
`Rig.PerturbationStableQuotients A I` holds, then there is a finite type `A`-algebra `C` and an
isomorphism `B ≅ C^∧` of `A`-algebras. -/
public theorem exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth'
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsGRing A) (I : Ideal A)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigSmooth B)
    (hGAR : PerturbationStableQuotients.{u, v} A I) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  classical
  obtain ⟨r, L, ⟨eB⟩⟩ :=
    exists_adicCompletion_mvPolynomial_quotient_equiv I (Ideal.fg_of_isNoetherianRing I) B
  have : IsNoetherianRing (completedPolynomialAlgebra I r) :=
    AdicCompletion.isNoetherianRing _
  obtain ⟨m, t, gen, rel, hK, ⟨eP⟩⟩ :=
    exists_finite_presentation_algEquiv (A := A) (R := completedPolynomialAlgebra I r) L eB
  obtain ⟨n0, hGARn⟩ := hGAR r m t B (Fintype.linearCombination _ gen)
    (Fintype.linearCombination _ rel) hK ⟨eP⟩ hB
  obtain ⟨gen', rel', hrelZero, hgenClose, hrelClose, C₀, hC₀ring, hC₀alg, hC₀ft, ⟨eC⟩⟩ :=
    exists_approximated_presentation' A hA I r m t gen rel
      (sum_mul_eq_zero_of_range_eq gen rel hK) n0
  let : CommRing C₀ := hC₀ring
  let : Algebra A C₀ := hC₀alg
  obtain ⟨eB'⟩ := hGARn (Fintype.linearCombination _ gen')
    (Fintype.linearCombination _ rel')
    (linearCombination_comp_eq_zero gen' rel' hrelZero)
    (fun x ↦ sub_mem_linearCombination _ gen gen' hgenClose x)
    (fun x i ↦ sub_mem_linearCombination_apply _ rel rel' hrelClose x i)
  let eGen := Ideal.quotientEquivAlgOfEq A (span_range_linearCombination gen').symm
  let C := ULift.{max u v} C₀
  have hCft : Algebra.FiniteType A C := Algebra.FiniteType.equiv hC₀ft ULift.algEquiv.symm
  exact ⟨C, inferInstance, inferInstance, hCft, ⟨eB'.trans (eGen.trans (eC.trans
    (adicCompletionCongr I (ULift.algEquiv.symm : C₀ ≃ₐ[A] C))))⟩⟩

end Rig

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Rig.Algebraization.GRing
public import StacksFrontier.RingTheory.Rig.Category
public import StacksFrontier.RingTheory.Rig.PresentationGenerators
public import StacksFrontier.RingTheory.Rig.RigSmoothDefs
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianPair

/-!
# Algebraization of rig-smooth algebras over a G-ring

Let `I` be an ideal of a Noetherian G-ring `A` and let `B` be an `I`-adically complete
`A`-algebra with `B ⧸ IB` of finite type over `A ⧸ I`, i.e. an object of the category of
Tag 0AL4.  If `B` is rig-smooth over `(A, I)`, then `B` is the `I`-adic completion of a
finite type `A`-algebra.

## The source's proof

The source argument runs as follows.

1. Present `B` as a quotient `P ⧸ L` of `P = A[x₁, …, x_r]^∧` (Tag 0AJP).
2. Choose a finite free resolution `P^⊕t --K--> P^⊕m --g--> P → B → 0` of that quotient,
   which exists because `P` is Noetherian.
3. Let `H` be the henselization of the pair `(A[x₁, …, x_r], I · A[x₁, …, x_r])`.  Since `A`
   is a Noetherian G-ring, so is the polynomial algebra (Tag 07PV), hence so is `H`
   (Tag 0AH3), and `H` has the same adic completion `P` as the polynomial algebra
   (Tag 0AGV).
4. The equations `∑_j kᵢⱼ gⱼ = 0` are a system of polynomial equations over `H` with a
   solution in `P = H^∧`, so the approximation property of Tag 0AH5 produces a solution
   over `H` itself, congruent to the given one modulo `Iⁿ` for any prescribed `n`.
5. For `n` large, Tag 0GAR identifies `B` with `P ⧸ (g'₁, …, g'_m)` for the approximated
   generators `g'ᵢ`, which come from `H`; so `B` is the completion of a quotient of `H`.
6. Tag 0GAS turns the completion of a quotient of a henselization into the completion of a
   finite type `A`-algebra.

Proposition 0GAT is `Rig.exists_finiteType_adicCompletion_algEquiv_of_isGRing_of_isRigSmooth`.
This file states Lemma 0GAR in the source's own formulation as the property
`Rig.PerturbationStableQuotients` of the pair `(A, I)`.

## Main definitions

* `Rig.PerturbationStableQuotients` — Lemma 0GAR as a property of the pair `(A, I)`.

## Main results

* `Rig.perturbationStableQuotients_bot` — that property holds for the zero ideal.

## References

* [Stacks Project, Tag 0GAT](https://stacks.math.columbia.edu/tag/0GAT)
* [Stacks Project, Tag 0GAR](https://stacks.math.columbia.edu/tag/0GAR)
* [Stacks Project, Tag 0GAS](https://stacks.math.columbia.edu/tag/0GAS)
* [Stacks Project, Tag 0AH5](https://stacks.math.columbia.edu/tag/0AH5)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
-/

@[expose] public section

universe u v

namespace Rig

open AdicFiniteTypeAlgebra

/-! ### Generic plumbing -/

section Plumbing

/-- A finitely generated ideal of a Noetherian ring has a presentation by a two-term complex
of finite free modules: generators `gen` and generators `rel` of the module of relations
between them. -/
@[ega "0 1.0.5" "Ideals as modules", ega "0 1.3.5" "special case"]
private theorem exists_finite_presentation_ideal
    {R : Type u} [CommRing R] [IsNoetherianRing R] (L : Ideal R) :
    ∃ (m t : ℕ) (gen : Fin m → R) (rel : Fin t → Fin m → R),
      (Fintype.linearCombination R rel).range = (Fintype.linearCombination R gen).ker ∧
        Ideal.span (Set.range (Fintype.linearCombination R gen)) = L := by
  classical
  obtain ⟨m, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian L)
  let g : (Fin m → R) →ₗ[R] R := Fintype.linearCombination R gen
  have hgRange : g.range = L := by
    change (Fintype.linearCombination R gen).range = L
    rw [Fintype.range_linearCombination, hgen]
  have hker : g.ker.FG := IsNoetherian.noetherian g.ker
  obtain ⟨t, rel, hrel⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  refine ⟨m, t, gen, rel, ?_, ?_⟩
  · change (Fintype.linearCombination R rel).range = g.ker
    rw [Fintype.range_linearCombination, hrel]
  · apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact hgRange ▸ LinearMap.mem_range_self g x
    · intro x hx
      obtain ⟨y, hy⟩ := hgRange.symm ▸ hx
      rw [← hy]
      exact Ideal.subset_span ⟨y, rfl⟩

/-- Transport of `exists_finite_presentation_ideal` across an identification of the quotient
`R ⧸ L` with a given algebra. -/
private theorem exists_finite_presentation_algEquiv
    {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] (L : Ideal R)
    {B : Type v} [CommRing B] [Algebra A B] (e : (R ⧸ L) ≃ₐ[A] B) :
    ∃ (m t : ℕ) (gen : Fin m → R) (rel : Fin t → Fin m → R),
      let g : (Fin m → R) →ₗ[R] R := Fintype.linearCombination R gen
      let K : (Fin t → R) →ₗ[R] (Fin m → R) := Fintype.linearCombination R rel
      K.range = g.ker ∧ Nonempty ((R ⧸ Ideal.span (Set.range g)) ≃ₐ[A] B) := by
  obtain ⟨m, t, gen, rel, hK, hspan⟩ := exists_finite_presentation_ideal L
  exact ⟨m, t, gen, rel, hK, ⟨(Ideal.quotientEquivAlgOfEq A hspan).trans e⟩⟩

/-- Two linear combinations with coefficientwise close vectors are close. -/
private theorem sub_mem_linearCombination
    {R : Type*} [CommRing R] (J : Ideal R) {m : ℕ} (gen gen' : Fin m → R)
    (h : ∀ i, gen i - gen' i ∈ J) (x : Fin m → R) :
    Fintype.linearCombination R gen x - Fintype.linearCombination R gen' x ∈ J := by
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply,
    ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [show x i • gen i - x i • gen' i = x i * (gen i - gen' i) by
    simp only [smul_eq_mul, mul_sub]]
  exact Ideal.mul_mem_left J (x i) (h i)

/-- The coordinatewise version of `sub_mem_linearCombination` for a matrix of coefficients. -/
private theorem sub_mem_linearCombination_apply
    {R : Type*} [CommRing R] (J : Ideal R) {t m : ℕ} (rel rel' : Fin t → Fin m → R)
    (h : ∀ j i, rel j i - rel' j i ∈ J) (x : Fin t → R) (i : Fin m) :
    Fintype.linearCombination R rel x i - Fintype.linearCombination R rel' x i ∈ J := by
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, Finset.sum_apply,
    Finset.sum_apply, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [show (x j • rel j) i - (x j • rel' j) i = x j * (rel j i - rel' j i) by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub]]
  exact Ideal.mul_mem_left J (x j) (h j i)

/-- If every relation vector annihilates the generators, the two-term complex of linear
combinations is a complex. -/
private theorem linearCombination_comp_eq_zero
    {R : Type*} [CommRing R] {t m : ℕ} (gen : Fin m → R) (rel : Fin t → Fin m → R)
    (h : ∀ j, ∑ i, gen i * rel j i = 0) :
    (Fintype.linearCombination R gen).comp (Fintype.linearCombination R rel) = 0 := by
  refine LinearMap.ext fun x => ?_
  show Fintype.linearCombination R gen (Fintype.linearCombination R rel x) = 0
  rw [Fintype.linearCombination_apply]
  calc
    ∑ i, Fintype.linearCombination R rel x i • gen i
        = ∑ i, ∑ j, x j * rel j i * gen i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fintype.linearCombination_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by
            simp only [Pi.smul_apply, smul_eq_mul]
    _ = ∑ j, ∑ i, x j * rel j i * gen i := Finset.sum_comm
    _ = ∑ j, x j * ∑ i, gen i * rel j i := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by simp only [h, mul_zero, Finset.sum_const_zero]

/-- Exactness of the two-term complex of linear combinations makes each relation vector
annihilate the generators. -/
private theorem sum_mul_eq_zero_of_range_eq
    {R : Type*} [CommRing R] {t m : ℕ} (gen : Fin m → R) (rel : Fin t → Fin m → R)
    (hK : LinearMap.range (Fintype.linearCombination R rel) =
      LinearMap.ker (Fintype.linearCombination R gen)) (j : Fin t) :
    ∑ i, gen i * rel j i = 0 := by
  classical
  have hmem : Fintype.linearCombination R rel (Pi.single j 1) ∈
      LinearMap.ker (Fintype.linearCombination R gen) := by
    rw [← hK]
    exact LinearMap.mem_range_self _ _
  rw [Fintype.linearCombination_apply_single, one_smul] at hmem
  have h0 := LinearMap.mem_ker.mp hmem
  rw [Fintype.linearCombination_apply] at h0
  rw [← h0]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

/-- The ideal generated by a finite family is the ideal generated by the range of the
associated linear combination map. -/
private theorem span_range_linearCombination
    {R : Type*} [CommRing R] {m : ℕ} (gen : Fin m → R) :
    Ideal.span (Set.range gen) =
      Ideal.span (Set.range (Fintype.linearCombination R gen)) := by
  classical
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    refine Ideal.subset_span ⟨Pi.single i 1, ?_⟩
    rw [Fintype.linearCombination_apply_single, one_smul]
  · rintro _ ⟨v, rfl⟩
    rw [Fintype.linearCombination_apply]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [smul_eq_mul]
    exact Ideal.mul_mem_left _ (v i) (Ideal.subset_span ⟨i, rfl⟩)

/-- Equal ideals have equal adic completions. -/
private noncomputable def adicCompletionAlgEquivOfIdealEq
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] (J K : Ideal R) (h : J = K) :
    AdicCompletion J R ≃ₐ[A] AdicCompletion K R := by
  let e (n : ℕ) : (R ⧸ J ^ n) ≃ₐ[A] (R ⧸ K ^ n) := Ideal.quotientEquivAlgOfEq A (by rw [h])
  refine adicCompletionAlgEquivOfQuotientEquiv J K e ?_
  intro m n hmn x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- If a ring map `g` sends the extension of `I` along `f'` into `J`, then `g.comp e` does so
along any `f` with `e.comp f = f'`. -/
private theorem map_le_comap_comp
    {R S S' T : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
    (e : S →+* S') (f : R →+* S) (f' : R →+* S') (hf : e.comp f = f') (I : Ideal R)
    (J : Ideal T) (g : S' →+* T) (h : I.map f' ≤ J.comap g) : I.map f ≤ J.comap (g.comp e) := by
  rw [Ideal.map_le_iff_le_comap] at h ⊢
  rw [Ideal.comap_comap, RingHom.comp_assoc, hf]
  exact h

/-- A relation `∑ xᵢ yᵢ = 0` is preserved by ring maps. -/
private theorem sum_mul_map_eq_zero
    {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') {m : ℕ} (x y : Fin m → S)
    (h : ∑ i, x i * y i = 0) : ∑ i, f (x i) * f (y i) = 0 := by
  simp only [← map_mul, ← map_sum, h, map_zero]

end Plumbing

/-! ### Lemma 0GAR as a hypothesis -/

/-- **Lemma 0GAR**, read as a property of the pair `(A, I)`.

Let `P = A[x₁, …, x_r]^∧` and let `J = IP`.  Given a resolution
`P^⊕t --K--> P^⊕m --g--> P → B → 0` of a rig-smooth object `B` of the category of Tag 0AL4,
there is an `n` such that every complex `P^⊕t --K'--> P^⊕m --g'--> P` whose maps agree with
`K` and `g` modulo `Jⁿ` presents the same `A`-algebra `B`.

This is the statement of the source's Lemma 0GAR verbatim.  It is a hypothesis of
`Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth'`; this library's form of
Tag 0GAR is `Rig.PerturbedPresentation.exists_algEquiv_of_perturbation`. -/
public def PerturbationStableQuotients (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) : Prop :=
  ∀ (r m t : ℕ) (B : AdicFiniteTypeAlgebra.{u, v} A I)
      (g : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
        completedPolynomialAlgebra I r)
      (K : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
        (Fin m → completedPolynomialAlgebra I r)),
    LinearMap.range K = LinearMap.ker g →
    Nonempty ((completedPolynomialAlgebra I r ⧸ Ideal.span (Set.range g)) ≃ₐ[A] B.carrier) →
    IsRigSmooth B →
    ∃ n : ℕ, ∀ (g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          completedPolynomialAlgebra I r)
        (K' : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          (Fin m → completedPolynomialAlgebra I r)),
      g'.comp K' = 0 →
      (∀ x : Fin m → completedPolynomialAlgebra I r,
        g x - g' x ∈ (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n) →
      (∀ (x : Fin t → completedPolynomialAlgebra I r) (i : Fin m),
        K x i - K' x i ∈ (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n) →
      Nonempty (B.carrier ≃ₐ[A]
        (completedPolynomialAlgebra I r ⧸ Ideal.span (Set.range g')))

/-- `Rig.PerturbationStableQuotients` is not vacuous: it holds for the zero ideal, where at
precision one no perturbation of the presentation is possible at all. -/
public theorem perturbationStableQuotients_bot (A : Type u) [CommRing A] [IsNoetherianRing A] :
    PerturbationStableQuotients.{u, v} A ⊥ := by
  intro r m t B g K _ hpres _
  refine ⟨1, fun g' K' _ hg _ => ?_⟩
  obtain ⟨e⟩ := hpres
  have hle : ((⊥ : Ideal A).map
      (algebraMap A (completedPolynomialAlgebra (⊥ : Ideal A) r))) ^ 1 ≤ ⊥ := by
    rw [pow_one]
    exact Ideal.map_le_iff_le_comap.mpr bot_le
  have hgg : g = g' :=
    LinearMap.ext fun x => sub_eq_zero.mp (Ideal.mem_bot.mp (hle (hg x)))
  exact ⟨hgg ▸ e.symm⟩

/-! ### Proposition 0GAT -/

/-- Steps 3 to 6 of the source's proof of Proposition 0GAT, for a fixed completed polynomial
presentation.  Given generators `gen` of an ideal of `P = A[x₁, …, x_r]^∧` and a family `rel`
of relations between them, the henselization `H` of `(A[x₁, …, x_r], I A[x₁, …, x_r])` is a
G-ring with completion `P`, so the approximation property moves the system `∑ᵢ genᵢ relⱼᵢ = 0`
from `P` into `H`; the approximated generators `gen'` present a quotient of `P` that is the
completion of a quotient of `H`, which Tag 0GAS algebraizes. -/
private theorem exists_approximated_presentation
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsGRing A) (I : Ideal A)
    (h07GC : ∀ (D : Type u) [CommRing D] (J : Ideal D),
      IsRegularRingHom (algebraMap D (AdicCompletion J D)) →
        Stacks.Smoothing.IsIndSmoothAdicCompletion D J)
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
  letI : IsNoetherianRing P := AdicCompletion.isNoetherianRing IR
  -- Step 3: the henselization `H` of `(R, IR)`, its G-ring property and its completion.
  let H := (henselization R IR : Type u)
  letI : Algebra A H := ((algebraMap R H).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let IH : Ideal H := IR.map (algebraMap R H)
  have hHP' : HenselianPair H IH := by
    simpa only [IH] using henselianPair_henselization R IR
  obtain ⟨H₀, hH₀ring, ι₀, hH₀pair, hH₀up⟩ := exists_henselization R IR
  letI : CommRing H₀ := hH₀ring
  letI : Algebra R H₀ := ι₀.toAlgebra
  have hH₀pair' : HenselianPair H₀ (IR.map (algebraMap R H₀)) := by
    simpa only [RingHom.algebraMap_toAlgebra] using hH₀pair
  obtain ⟨eH⟩ := nonempty_algEquiv_henselization (R := R) (I := IR) H₀ hH₀pair' hH₀up
  have hbase : eH.toRingEquiv.toRingHom.comp (algebraMap R H) = algebraMap R H₀ := by
    apply RingHom.ext
    intro x
    exact eH.commutes x
  have hbaseSymm : eH.symm.toRingEquiv.toRingHom.comp (algebraMap R H₀) = algebraMap R H := by
    apply RingHom.ext
    intro x
    exact eH.symm.commutes x
  have hι₀ : algebraMap R H₀ = ι₀ := by
    apply RingHom.ext
    intro x
    rfl
  have hHup : ∀ (T : Type u) (_ : CommRing T) (Jt : Ideal T),
      HenselianPair T Jt → ∀ f : R →+* T, IR ≤ Jt.comap f →
        ∃! q : H →+* T, q.comp (algebraMap R H) = f ∧ IH ≤ Jt.comap q := by
    intro T hT Jt hTpair f hf
    letI : CommRing T := hT
    obtain ⟨g₀, hg₀, huniq₀⟩ := hH₀up T hT Jt hTpair f hf
    let gH : H →+* T := g₀.comp eH.toRingEquiv.toRingHom
    have hbaseH : gH.comp (algebraMap R H) = f := by
      rw [RingHom.comp_assoc, hbase, hι₀, hg₀.1]
    refine ⟨gH, ⟨hbaseH, map_le_comap_comp _ _ _ hbase _ _ _ hg₀.2⟩, ?_⟩
    intro g' hg'
    let g₀' : H₀ →+* T := g'.comp eH.symm.toRingEquiv.toRingHom
    have hbase₀' : g₀'.comp (algebraMap R H₀) = f := by
      rw [RingHom.comp_assoc, hbaseSymm, hg'.1]
    have heq := huniq₀ g₀' ⟨hbase₀', map_le_comap_comp _ _ _ hbaseSymm _ _ _ hg'.2⟩
    apply RingHom.ext
    intro x
    have hx := congrArg (fun k : H₀ →+* T => k (eH x)) heq
    simpa [gH, g₀'] using hx
  haveI : IsNoetherianRing H :=
    (henselization_isNoetherian_and_completion_equiv R IR H hHP' hHup).2.1
  have hGR : IsGRing H :=
    isGRing_henselization (isGRing_of_essFiniteType hA) IR H hHP' hHup
  let Q := AdicCompletion IH H
  letI : Algebra A Q := Algebra.compHom Q (algebraMap A H)
  haveI : IsScalarTower A H Q := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A R Q := IsScalarTower.of_algebraMap_eq' rfl
  let completionMap : P →+* Q := adicCompletionMap (algebraMap R H) IR IH le_rfl
  have hcompletionMap : Function.Bijective completionMap :=
    (henselization_isNoetherian_and_completion_equiv R IR H hHP' hHup).1
  let completionEquiv : P ≃+* Q := RingEquiv.ofBijective completionMap hcompletionMap
  have hcR (x : R) : completionEquiv (algebraMap R P x) = algebraMap H Q (algebraMap R H x) :=
    congrArg (fun k : R →+* Q => k x)
      (adicCompletionMap_comp_algebraMap (algebraMap R H) IR IH le_rfl)
  have hcompletionAlgebra : ∀ a : A,
      completionEquiv (algebraMap A P a) = algebraMap A Q a := by
    intro a
    calc
      completionEquiv (algebraMap A P a)
          = completionEquiv (algebraMap R P (algebraMap A R a)) := by
            rw [IsScalarTower.algebraMap_apply A R P]
      _ = algebraMap H Q (algebraMap R H (algebraMap A R a)) := hcR _
      _ = algebraMap R Q (algebraMap A R a) := by
            rw [IsScalarTower.algebraMap_apply R H Q]
      _ = algebraMap A Q a := by rw [IsScalarTower.algebraMap_apply A R Q]
  -- Step 4: the relations as a polynomial system over `H`, solved in `Q = H^∧ = P`.
  let nVars := m + m * t
  let blockEquiv : Fin m ⊕ Fin (m * t) ≃ Fin nVars := finSumFinEquiv
  let genIndex (i : Fin m) : Fin nVars := blockEquiv (Sum.inl i)
  let relIndex (i : Fin m) (j : Fin t) : Fin nVars :=
    blockEquiv (Sum.inr (finProdFinEquiv (i, j)))
  let equations : Fin t → MvPolynomial (Fin nVars) H := fun j =>
    ∑ i, MvPolynomial.X (genIndex i) * MvPolynomial.X (relIndex i j)
  let ahat : Fin nVars → Q := fun q =>
    match blockEquiv.symm q with
    | Sum.inl i => completionEquiv (gen i)
    | Sum.inr z => completionEquiv (rel z.modNat z.divNat)
  have hprod (i : Fin m) (j : Fin t) :
      finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) := finProdFinEquiv.left_inv _
  have hprodMod (i : Fin m) (j : Fin t) : (finProdFinEquiv (i, j)).modNat = j :=
    congrArg Prod.snd (hprod i j)
  have hprodDiv (i : Fin m) (j : Fin t) : (finProdFinEquiv (i, j)).divNat = i :=
    congrArg Prod.fst (hprod i j)
  have hf : ∀ j, MvPolynomial.aeval ahat (equations j) = 0 := by
    intro j
    have hev : MvPolynomial.aeval ahat (equations j) =
        ∑ i, completionEquiv (gen i) * completionEquiv (rel j i) := by
      simp [equations, ahat, genIndex, relIndex, blockEquiv, hprodMod, hprodDiv]
    rw [hev]
    exact sum_mul_map_eq_zero completionEquiv.toRingHom _ _ (hrel j)
  let precision := max n0 1
  have hprecision : precision ≠ 0 := by
    simp only [precision]
    omega
  obtain ⟨a, haClose, haEq⟩ :=
    Stacks.Smoothing.exists_solution_of_henselianPair (A := H) (I := IH) hHP'
      (h07GC H IH (isRegularRingHom_algebraMap_adicCompletion hGR IH)) equations ahat hf
      hprecision
  -- Step 5: the approximated generators present `B`, and come from `H`.
  let JP : Ideal P := I.map (algebraMap A P)
  have hIRP : IR.map (algebraMap R P) = JP := by
    change (I.map (MvPolynomial.C : A →+* R)).map (algebraMap R P) = _
    rw [Ideal.map_map]
    congr 1
  have hcompR : completionEquiv.symm.toRingHom.comp (algebraMap R Q) = algebraMap R P := by
    apply RingHom.ext
    intro x
    apply completionEquiv.injective
    calc
      completionEquiv (completionEquiv.symm (algebraMap R Q x)) = algebraMap R Q x :=
        completionEquiv.apply_symm_apply _
      _ = completionEquiv (algebraMap R P x) := by
        rw [IsScalarTower.algebraMap_apply R H Q x]
        exact (hcR x).symm
  have hIHQ : (IH ^ precision).map (algebraMap H Q) =
      (IR ^ precision).map (algebraMap R Q) := by
    change ((IR.map (algebraMap R H)) ^ precision).map (algebraMap H Q) = _
    rw [Ideal.map_pow, Ideal.map_pow, Ideal.map_map]
    congr 1
  have hIdeal : ((IH ^ precision).map (algebraMap H Q)).map completionEquiv.symm.toRingHom =
      JP ^ precision := by
    rw [hIHQ, Ideal.map_map, hcompR]
    calc
      (IR ^ precision).map (algebraMap R P) = (IR.map (algebraMap R P)) ^ precision := by
        rw [Ideal.map_pow]
      _ = JP ^ precision := congrArg (fun J : Ideal P => J ^ precision) hIRP
  let gen' : Fin m → P := fun i => completionEquiv.symm (algebraMap H Q (a (genIndex i)))
  let rel' : Fin t → Fin m → P := fun j i =>
    completionEquiv.symm (algebraMap H Q (a (relIndex i j)))
  have hgenIndex (i : Fin m) : ahat (genIndex i) = completionEquiv (gen i) := by
    simp [ahat, genIndex, blockEquiv]
  have hrelIndex (i : Fin m) (j : Fin t) :
      ahat (relIndex i j) = completionEquiv (rel j i) := by
    simp [ahat, relIndex, blockEquiv, hprodMod, hprodDiv]
  have hclose (q : Fin nVars) (x : P) (hx : ahat q = completionEquiv x) :
      x - completionEquiv.symm (algebraMap H Q (a q)) ∈ JP ^ precision := by
    have hm := Ideal.mem_map_of_mem completionEquiv.symm.toRingHom (haClose q)
    rw [map_sub, hx, hIdeal] at hm
    simpa [Q] using hm
  have hpolyRel (j : Fin t) : ∑ i, a (genIndex i) * a (relIndex i j) = 0 := by
    simpa [equations] using haEq j
  let fromH : H →+* P := completionEquiv.symm.toRingHom.comp (algebraMap H Q)
  have hrelZero (j : Fin t) : ∑ i, gen' i * rel' j i = 0 :=
    sum_mul_map_eq_zero fromH (fun i => a (genIndex i)) (fun i => a (relIndex i j)) (hpolyRel j)
  -- The quotient of `P` by the approximated generators is the completion of a quotient of `H`.
  let genH : Fin m → H := fun i => a (genIndex i)
  let JH : Ideal H := Ideal.span (Set.range genH)
  let JQ : Ideal Q := JH.map (algebraMap H Q)
  let Jgen : Ideal P := Ideal.span (Set.range gen')
  have hgenSet : Set.range gen' =
      completionEquiv.symm.toRingHom '' ((algebraMap H Q) '' Set.range genH) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨algebraMap H Q (genH i), ⟨genH i, ⟨i, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨y, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hJgen : Jgen = JQ.map completionEquiv.symm.toRingHom := by
    dsimp only [Jgen, JQ, JH]
    rw [Ideal.map_span, Ideal.map_span, ← hgenSet]
  let eCP : P ≃ₐ[A] Q := AlgEquiv.ofRingEquiv (f := completionEquiv) hcompletionAlgebra
  let ePQ : (P ⧸ Jgen) ≃ₐ[A] (Q ⧸ JQ) :=
    (Ideal.quotientEquivAlg JQ Jgen eCP.symm hJgen).symm
  have hIRH : IR.map (algebraMap R H) = I.map (algebraMap A H) := by
    change (I.map (MvPolynomial.C : A →+* R)).map (algebraMap R H) = _
    rw [Ideal.map_map]
    congr 1
  letI : Algebra A (H ⧸ JH) := Algebra.compHom (H ⧸ JH) (algebraMap A H)
  haveI : IsScalarTower A H (H ⧸ JH) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A H (Q ⧸ JQ) := IsScalarTower.of_algebraMap_eq' rfl
  have hIHquot : IH.map (algebraMap H (H ⧸ JH)) = I.map (algebraMap A (H ⧸ JH)) := by
    change (IR.map (algebraMap R H)).map (algebraMap H (H ⧸ JH)) = _
    rw [hIRH, Ideal.map_map]
    congr 1
  have hCompletionAlgMap (c : A) :
      algebraMap A (AdicCompletion (IH.map (algebraMap H (H ⧸ JH))) (H ⧸ JH)) c =
        algebraMap H (AdicCompletion (IH.map (algebraMap H (H ⧸ JH))) (H ⧸ JH))
          (algebraMap A H c) := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rfl
  let eHQH := adicCompletionQuotientAlgEquiv IH JH
  let eHQ : (Q ⧸ JQ) ≃ₐ[A]
      AdicCompletion (IH.map (algebraMap H (H ⧸ JH))) (H ⧸ JH) :=
    AlgEquiv.ofRingEquiv (f := eHQH.toRingEquiv) fun c => by
      calc
        eHQH (algebraMap A (Q ⧸ JQ) c)
            = eHQH (algebraMap H (Q ⧸ JQ) (algebraMap A H c)) := by
              rw [IsScalarTower.algebraMap_apply A H (Q ⧸ JQ)]
        _ = algebraMap H (AdicCompletion (IH.map (algebraMap H (H ⧸ JH))) (H ⧸ JH))
              (algebraMap A H c) := eHQH.commutes _
        _ = algebraMap A (AdicCompletion (IH.map (algebraMap H (H ⧸ JH))) (H ⧸ JH)) c :=
              (hCompletionAlgMap c).symm
  let eHQ' : (Q ⧸ JQ) ≃ₐ[A] AdicCompletion (I.map (algebraMap A (H ⧸ JH))) (H ⧸ JH) :=
    eHQ.trans (adicCompletionAlgEquivOfIdealEq _ _ hIHquot)
  -- Step 6: algebraize the quotient of the henselization (Tag 0GAS).
  haveI : Algebra.FiniteType A R := inferInstance
  obtain ⟨C₀, hC₀ring, hC₀alg, hC₀ft, ⟨eGAS⟩⟩ :=
    exists_finiteType_adicCompletion_algEquiv_henselization_quotient.{u, u} A R I JH
  letI : CommRing C₀ := hC₀ring
  letI : Algebra A C₀ := hC₀alg
  let eGAS' : AdicCompletion (I.map (algebraMap A C₀)) C₀ ≃ₐ[A]
      AdicCompletion (I.map (algebraMap A (H ⧸ JH))) (H ⧸ JH) := eGAS
  have hJPle : JP ^ precision ≤ JP ^ n0 := Ideal.pow_le_pow_right (Nat.le_max_left n0 1)
  exact ⟨gen', rel', hrelZero, fun i => hJPle (hclose _ _ (hgenIndex i)),
    fun j i => hJPle (hclose _ _ (hrelIndex i j)), C₀, inferInstance, inferInstance, hC₀ft,
    ⟨ePQ.trans (eHQ'.trans eGAS'.symm)⟩⟩

end Rig

end

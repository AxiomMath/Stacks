module

public import StacksFrontier.RingTheory.Henselian.Pair.Criteria.ProductDecomposition

@[expose] public section

/-!
# Characterizations of henselian pairs

For a commutative ring `A` and an ideal `I`, being a henselian pair is equivalent to lifting
`A`-algebra maps from étale `A`-algebras to `A ⧸ I`, to reduction modulo the extended ideal
inducing a bijection on idempotents of every finite `A`-algebra, to the same for every integral
`A`-algebra, and to Gabber's root criterion for the polynomials `X ^ n (X - 1) + ∑ aᵢ X ^ i` with
`aᵢ ∈ I`.

## Main results

* `henselianPair_tfae`: the five characterizations, in the order of the source.
* `henselianPair_of_henselianRing`: a henselian ring in the sense of `HenselianRing A I` forms a
  henselian pair with `I`.

## Implementation notes

Reduction modulo `I` maps polynomial coefficients along `Ideal.Quotient.mk I`, and the extension of
`I` to an algebra `B` is `I.map (algebraMap A B)`. The coefficients of Gabber's polynomial are
indexed by `Fin (n + 1)`, and the source's existence claim together with its subsequent uniqueness
assertion are combined into a single `ExistsUnique`.

## References

* [Stacks: Tag 09XD](https://stacks.math.columbia.edu/tag/09XD)
* [Stacks: Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
* Raynaud, *Anneaux locaux henséliens*, Chapter XI
* Gabber, *Affine analog of the proper base change theorem*, Proposition 1
-/

open Polynomial

universe u v w x

section

/-- The idempotent criterion for integral algebras implies the criterion for finite algebras. -/
private theorem finite_idempotents_of_integral_idempotents
    (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      InducesBijectionOnIdempotents (I.map (algebraMap A B))) :
    ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] [Module.Finite A B],
      InducesBijectionOnIdempotents (I.map (algebraMap A B)) := by
  intro B _ _ _
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  exact h B

/-- Extending a Jacobson ideal along an integral algebra preserves Jacobson containment. -/
private theorem jacobson_map_le_of_isIntegral
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B]
    (I : Ideal A) (hI : I ≤ (⊥ : Ideal A).jacobson) :
    I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  apply Ideal.mem_sInf.mpr
  intro M hM
  have : M.IsMaximal := hM.2
  have hcomap : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have ha' : a ∈ M.comap (algebraMap A B) :=
    (Ideal.mem_sInf.mp (hI ha)) ⟨bot_le, hcomap⟩
  exact ha'

/-- Lifting sections of étale algebras in a larger universe gives it for `Type u` algebras. -/
private theorem exists_section_of_etale_section_lifting
    (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
      ∀ σ : A' →ₐ[A] A ⧸ I,
        ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ)
    (A' : Type u) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (σ : A' →ₐ[A] A ⧸ I) :
    ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ := by
  let e : ULift.{v} A' ≃ₐ[A] A' := ULift.algEquiv
  have : Algebra.Etale A (ULift.{v} A') := Algebra.Etale.of_equiv e.symm
  obtain ⟨τ, hτ⟩ := h _ (σ.comp e.toAlgHom)
  exact ⟨τ.comp e.symm.toAlgHom,
    AlgHom.ext fun x => by simpa using DFunLike.congr_fun hτ (e.symm x)⟩

/-- A quotient by an ideal inside the Jacobson radical of a nontrivial ring is nontrivial. -/
private theorem nontrivial_quotient_of_le_jacobson_bot
    {A : Type u} [CommRing A] [Nontrivial A] {I : Ideal A} (hI : I ≤ (⊥ : Ideal A).jacobson) :
    Nontrivial (A ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr fun ht => by
    have ht' : (⊥ : Ideal A).jacobson = ⊤ := top_le_iff.mp (ht ▸ hI)
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp ht')

/-- The extension of an ideal lies in the kernel of an algebra map killing the ideal. -/
private theorem map_le_ker_of_algHom
    {A : Type u} {B : Type v} {D : Type w} [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] (I : Ideal A) (g : B →ₐ[A] D) (h : ∀ a ∈ I, algebraMap A D a = 0) :
    I.map (algebraMap A B) ≤ RingHom.ker g := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change g (algebraMap A B a) = 0
  rw [g.commutes]
  exact h a ha

/-- Lifting sections of all étale algebras forces the ideal into the Jacobson radical. -/
@[ega "IV 18.5.7" "more general"]
private theorem jacobson_of_etale_section_lifting
    (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
      ∀ σ : A' →ₐ[A] A ⧸ I,
        ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    I ≤ (⊥ : Ideal A).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  let f : A := x * y + 1
  have hf : (Ideal.Quotient.mk I) f = 1 := by
    simp [f, (Ideal.Quotient.eq_zero_iff_mem).2 hx]
  let C := Localization.Away f
  have : Algebra.Etale A C := Algebra.Etale.of_isLocalizationAway f
  have hfunit : IsUnit ((Ideal.Quotient.mkₐ A I) f) := by simp [hf]
  let σ₀ : C →ₐ[A] A ⧸ I := IsLocalization.Away.liftAlgHom f hfunit
  obtain ⟨τ, _⟩ := exists_section_of_etale_section_lifting A I h C σ₀
  have hA : IsUnit f := by
    have ht := (IsLocalization.Away.algebraMap_isUnit (S := C) f).map τ.toRingHom
    change IsUnit (τ (algebraMap A C f)) at ht
    rwa [τ.commutes] at ht
  simpa [f, add_comm] using hA

/-- Sections of étale algebras descend the idempotent lift supplied after the étale base
change of Stacks 07M4. -/
private theorem integral_idempotents_of_etale_section_lifting
    (A : Type u) [CommRing A] (I : Ideal A)
    (h : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
      ∀ σ : A' →ₐ[A] A ⧸ I,
        ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      InducesBijectionOnIdempotents (I.map (algebraMap A B)) := by
  intro B _ _ _
  let K : Ideal B := I.map (algebraMap A B)
  have hJ : K ≤ (⊥ : Ideal B).jacobson :=
    jacobson_map_le_of_isIntegral I (jacobson_of_etale_section_lifting A I h)
  refine ⟨idemMap_injective K hJ, ?_⟩
  intro e
  obtain ⟨A', instR, instAlg, e', hetale, hbijection, he', hmap⟩ :=
    exists_etale_baseChange_idempotent_lift (A := A) (B := B) I e e.property
  let J : Ideal A' := I.map (algebraMap A A')
  let q : A ⧸ I →ₐ[A] A' ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId A A') Ideal.le_comap_map
  have hq : Function.Bijective q := hbijection
  let qEquiv : (A ⧸ I) ≃ₐ[A] A' ⧸ J := AlgEquiv.ofBijective q hq
  let σ : A' →ₐ[A] A ⧸ I :=
    qEquiv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A J)
  obtain ⟨τ, hτ⟩ := exists_section_of_etale_section_lifting A I h A' σ
  let D : TensorProduct A B A' →ₐ[A] B :=
    Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp τ)
      (fun _ _ => Commute.all _ _)
  let ι : B →+* TensorProduct A B A' := Algebra.TensorProduct.includeLeftRingHom
  let JT : Ideal (TensorProduct A B A') := K.map ι
  have hdι : D.toRingHom.comp ι = RingHom.id B := by
    ext b
    simp [D, ι]
  have hmapJ : JT.map D.toRingHom ≤ K := by
    show (K.map ι).map D.toRingHom ≤ K
    rw [Ideal.map_map, hdι]
    simp
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective e.val
  have hmap' : Ideal.Quotient.mk JT (ι b) = Ideal.Quotient.mk JT e' := by
    rw [← hb] at hmap
    simpa only [Ideal.quotientMap_mk] using hmap
  have hmem : e' - ι b ∈ JT := Ideal.Quotient.eq.mp hmap'.symm
  have hmemD : D (e' - ι b) ∈ K :=
    hmapJ (Ideal.mem_map_of_mem D.toRingHom hmem)
  have hbD : D (ι b) = b := by
    have hh := congrArg (fun F : B →+* B => F b) hdι
    simpa using hh
  have hfinal : Ideal.Quotient.mk K (D e') = Ideal.Quotient.mk K b := by
    apply Ideal.Quotient.eq.mpr
    simpa [map_sub, hbD] using hmemD
  refine ⟨⟨D e', ?_⟩, ?_⟩
  · exact he'.map D.toRingHom
  · exact Subtype.ext (hfinal.trans hb)

/-- An integral étale factor whose reduction is the base quotient gives a section. -/
private theorem etale_section_lifting_of_gabber_root_condition
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson)
    (hroot : ∀ (f : A[X]), f.Monic → ∀ (n : ℕ), 1 ≤ n →
      ∀ a : Fin (n + 1) → I,
        f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ) →
          ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (σ : A' →ₐ[A] A ⧸ I) :
    ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ := by
  obtain ⟨B, C, _, _, _, _, e, q, hint, hsurj, hker, hcomp⟩ :=
    exists_integral_factor_decomposition_of_gabber_root_condition A I hI hroot A' σ
  have : Algebra.IsIntegral A B := hint
  have : Algebra.Etale A (B × C) := Algebra.Etale.of_equiv e
  let : Algebra (B × C) B := (RingHom.fst B C).toAlgebra
  have : IsScalarTower A (B × C) B := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale A B := Algebra.Etale.comp A (B × C) B
  let J := I.map (algebraMap A B)
  let F : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J (algebraMap A B) Ideal.le_comap_map
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hab : algebraMap A B (a - b) ∈ J := by
        simpa [F, map_sub] using Ideal.Quotient.eq.mp hxy
      rw [show J = RingHom.ker q from hker.symm] at hab
      have hh : q (algebraMap A B (a - b)) = 0 := hab
      simpa [map_sub, sub_eq_zero] using hh
    · intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (q b)
      refine ⟨Ideal.Quotient.mk I a, Ideal.Quotient.eq.mpr ?_⟩
      rw [show J = RingHom.ker q from hker.symm]
      show q (algebraMap A B a - b) = 0
      simp [ha]
  have hbij := bijective_algebraMap_of_bijective_quotientMap I hI hF
  let base : A ≃ₐ[A] B := AlgEquiv.ofBijective (Algebra.ofId A B) hbij
  have hq : (Ideal.Quotient.mkₐ A I).comp base.symm.toAlgHom = q := by
    ext b
    obtain ⟨a, rfl⟩ := base.surjective b
    show Ideal.Quotient.mk I (base.symm (base a)) = q (algebraMap A B a)
    rw [base.symm_apply_apply, q.commutes]
    rfl
  refine ⟨base.symm.toAlgHom.comp ((AlgHom.fst A B C).comp e.toAlgHom), ?_⟩
  rw [← AlgHom.comp_assoc, hq, hcomp]

private theorem gabber_roots_of_henselianPair
    {A : Type*} [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (f : A[X]) (hf : f.Monic) (n : ℕ) (a : Fin (n + 1) → I)
    (hform : f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ)) :
    ∃! α : A, α - 1 ∈ I ∧ f.IsRoot α := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨1, ⟨by simp, by simp [IsRoot, Subsingleton.elim f 0]⟩,
      fun _ _ => Subsingleton.elim _ _⟩
  have : Nontrivial (A ⧸ I) := nontrivial_quotient_of_le_jacobson_bot hI.1
  have hmap : f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) := by
    simp [hform, Polynomial.map_sum, (Ideal.Quotient.eq_zero_iff_mem).mpr (a _).property]
  have hcop : IsCoprime (X ^ n : (A ⧸ I)[X]) (X - 1) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - 1) from ⟨1, -1, by ring⟩).pow_left
  obtain ⟨g, h, hg, hh, hfac, hgm, hhm⟩ := hI.2 f hf (X ^ n) (X - 1)
    (monic_X.pow n) (by simpa using monic_X_sub_C (1 : A ⧸ I)) hmap hcop
  have hdeg : h.natDegree = 1 := by
    rw [← hh.natDegree_map (Ideal.Quotient.mk I), hhm]
    simpa using natDegree_X_sub_C (1 : A ⧸ I)
  have heq : h = X + C (h.coeff 0) := hh.eq_X_add_C hdeg
  have hcoeff : Ideal.Quotient.mk I (h.coeff 0) = -1 := by
    simpa using congrArg (fun p : (A ⧸ I)[X] => p.coeff 0) hhm
  have hα : -h.coeff 0 - 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [hcoeff]
  refine ⟨-h.coeff 0, ⟨hα, ?_⟩, ?_⟩
  · rw [IsRoot, hfac, eval_mul, heq]
    simp
  · intro β hβ
    have hβq : Ideal.Quotient.mk I β = 1 := by
      simpa only [map_sub, map_one, sub_eq_zero] using (Ideal.Quotient.eq_zero_iff_mem).mpr hβ.1
    have hgeval : Ideal.Quotient.mk I (g.eval β) = 1 := by
      rw [← eval₂_at_apply, ← eval_map, hgm]
      simp [hβq]
    have hgunit : IsUnit (g.eval β) :=
      Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hI.1 (by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simp [hgeval]))
    have hhβ : h.eval β = 0 := by
      have hzero : g.eval β * h.eval β = 0 := by simpa [IsRoot, hfac] using hβ.2
      exact hgunit.mul_left_cancel (by simpa using hzero)
    rw [heq, eval_add, eval_X, eval_C] at hhβ
    exact eq_neg_of_add_eq_zero_left hhβ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem idempotents_of_algEquiv
    {A : Type u} {B : Type v} {D : Type w} [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] (I : Ideal A) (e : B ≃ₐ[A] D)
    (h : InducesBijectionOnIdempotents (I.map (algebraMap A D))) :
    InducesBijectionOnIdempotents (I.map (algebraMap A B)) := by
  let K := I.map (algebraMap A B)
  let L := I.map (algebraMap A D)
  have hmap : L = K.map e.toRingHom := by
    dsimp [K, L]
    rw [Ideal.map_map]
    congr 1
    ext a
    exact (e.commutes a).symm
  let E : B ⧸ K ≃+* D ⧸ L := Ideal.quotientEquiv K L e.toRingEquiv hmap
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply e.injective
    have hx : idemMap L ⟨e x.val, x.property.map e.toRingHom⟩ =
        idemMap L ⟨e y.val, y.property.map e.toRingHom⟩ := by
      apply Subtype.ext
      have heq := congrArg (fun z => E z.val) hxy
      change E (Ideal.Quotient.mk K x.val) = E (Ideal.Quotient.mk K y.val) at heq
      rw [show E (Ideal.Quotient.mk K x.val) = Ideal.Quotient.mk L (e x.val) from
        Ideal.quotientEquiv_mk K L e.toRingEquiv hmap x.val,
        show E (Ideal.Quotient.mk K y.val) = Ideal.Quotient.mk L (e y.val) from
        Ideal.quotientEquiv_mk K L e.toRingEquiv hmap y.val] at heq
      exact heq
    exact congrArg Subtype.val (h.1 hx)
  · intro x
    obtain ⟨y, hy⟩ := h.2 ⟨E x.val, x.property.map E.toRingHom⟩
    refine ⟨⟨e.symm y.val, y.property.map e.symm.toRingHom⟩, ?_⟩
    apply Subtype.ext
    apply E.injective
    show E (Ideal.Quotient.mk K (e.symm y.val)) = E x.val
    rw [show E (Ideal.Quotient.mk K (e.symm y.val)) = Ideal.Quotient.mk L y.val by
      dsimp [E]
      rw [Ideal.quotientEquiv_mk]; simp]
    exact congrArg Subtype.val hy

private theorem finite_idempotents_universe
    (A : Type u) [CommRing A] (I : Ideal A)
    (H : ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] [Module.Finite A B],
      InducesBijectionOnIdempotents (I.map (algebraMap A B)))
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] :
    InducesBijectionOnIdempotents (I.map (algebraMap A B)) :=
  idempotents_of_algEquiv I (ULift.algEquiv (R := A)).symm (H (ULift.{v} B))

private theorem jacobson_of_finite_idempotents
    (A : Type u) [CommRing A] (I : Ideal A)
    (H : ∀ (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B],
      InducesBijectionOnIdempotents (I.map (algebraMap A B))) :
    I ≤ (⊥ : Ideal A).jacobson := by
  intro a ha
  apply Ideal.mem_sInf.mpr
  intro M hM
  have : M.IsMaximal := hM.2
  by_contra haM
  let B := A ⧸ M
  let : Field B := Ideal.Quotient.field M
  have haunit : IsUnit (Ideal.Quotient.mk M a) :=
    isUnit_iff_ne_zero.mpr (fun hz => haM (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have htop : I.map (algebraMap A B) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha) haunit
  have heq : (⟨0, IsIdempotentElem.zero⟩ : {b : B // IsIdempotentElem b}) =
      ⟨1, IsIdempotentElem.one⟩ := by
    apply (H B).1
    apply Subtype.ext
    show Ideal.Quotient.mk (I.map (algebraMap A B)) 0 =
      Ideal.Quotient.mk (I.map (algebraMap A B)) 1
    rw [htop]
    exact Subsingleton.elim _ _
  exact zero_ne_one (congrArg Subtype.val heq)

private theorem gabber_root_of_finite_idempotents
    {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson)
    (H : ∀ (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B],
      InducesBijectionOnIdempotents (I.map (algebraMap A B)))
    (f : A[X]) (hf : f.Monic) (n : ℕ) (a : Fin (n + 1) → I)
    (hform : f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ)) :
    ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α := by
  classical
  let B := AdjoinRoot f
  have : Module.Finite A B := hf.finite_adjoinRoot
  have : Module.Free A B := hf.free_adjoinRoot
  let K := I.map (algebraMap A B)
  let r : B ⧸ K := Ideal.Quotient.mk K (AdjoinRoot.root f)
  have hz : aeval r f = 0 := AdjoinRoot.aeval_algHom_eq_zero f (Ideal.Quotient.mkₐ A K)
  have hr : r ^ n * (r - 1) = 0 := by
    have ha : ∀ i, algebraMap A (B ⧸ K) (a i : A) = 0 := by
      intro i
      show Ideal.Quotient.mk K (algebraMap A B (a i : A)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (a i).property)
    simpa [hform, ha] using hz
  have hmul : r ^ n * r = r ^ n := by linear_combination hr
  have hpow : ∀ k : ℕ, r ^ n * r ^ k = r ^ n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hmul]
  have hidem : IsIdempotentElem (r ^ n) := hpow n
  obtain ⟨e, he⟩ := (H B).2 ⟨r ^ n, hidem⟩
  have hemap : Ideal.Quotient.mk K e.val = r ^ n := congrArg Subtype.val he
  let J : Ideal B := Ideal.span {1 - e.val}
  let C := B ⧸ J
  have : IsLocalization.Away e.val C := IsLocalization.Away.quotient_of_isIdempotentElem e.property
  have : Algebra.FinitePresentation B C := IsLocalization.Away.finitePresentation e.val
  have : Algebra.FinitePresentation A C := Algebra.FinitePresentation.trans A B C
  have : Module.Flat B C := IsLocalization.flat C (Submonoid.powers e.val)
  have : Module.Flat A C := Module.Flat.trans A B C
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let L := I.map (algebraMap A C)
  let q : B →ₐ[A] C := Ideal.Quotient.mkₐ A J
  let φ : B →ₐ[A] C ⧸ L := (Ideal.Quotient.mkₐ A L).comp q
  let x : C ⧸ L := φ (AdjoinRoot.root f)
  let ψ : B ⧸ K →ₐ[A] C ⧸ L := Ideal.Quotient.liftₐ K φ <|
    map_le_ker_of_algHom I φ fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  have heone : q e.val = 1 := by
    apply (sub_eq_zero.mp : q e.val - 1 = 0 → q e.val = 1)
    show Ideal.Quotient.mk J (e.val - 1) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : 1 - e.val ∈ J := Ideal.subset_span (Set.mem_singleton _)
    simpa only [neg_sub] using J.neg_mem hm
  have hxpow : x ^ n = 1 := by
    have h := congrArg ψ hemap
    simpa [ψ, φ, x, r, ← map_pow, heone] using h.symm
  have hxmul : x ^ n * (x - 1) = 0 := by
    simpa [ψ, x, r] using congrArg ψ hr
  have hx : x = 1 := by
    rw [hxpow, one_mul] at hxmul
    exact sub_eq_zero.mp hxmul
  let F : A ⧸ I →+* C ⧸ L := Ideal.quotientMap L (algebraMap A C) Ideal.le_comap_map
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    refine ⟨Ideal.Quotient.mk I (p.eval 1), ?_⟩
    show algebraMap A (C ⧸ L) (p.eval 1) = φ (AdjoinRoot.mk f p)
    rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply]
    show algebraMap A (C ⧸ L) (p.eval 1) = aeval x p
    rw [hx]
    simp [aeval_def]
  have hred : aeval (1 : A ⧸ I) f = 0 := by
    simp [hform, (Ideal.Quotient.eq_zero_iff_mem).mpr (a _).property]
  let ε : B →ₐ[A] A ⧸ I := AdjoinRoot.liftAlgHom f (Algebra.ofId A (A ⧸ I)) 1 hred
  have hεroot : ε (AdjoinRoot.root f) = 1 :=
    AdjoinRoot.liftAlgHom_root f (Algebra.ofId A (A ⧸ I)) 1 hred
  have hker : ∀ a ∈ I, algebraMap A (A ⧸ I) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let εbar : B ⧸ K →ₐ[A] A ⧸ I := Ideal.Quotient.liftₐ K ε (map_le_ker_of_algHom I ε hker)
  have hεe : ε e.val = 1 := by
    have h := congrArg εbar hemap
    simp only [map_pow] at h
    change ε e.val = ε (AdjoinRoot.root f) ^ n at h
    simpa only [hεroot, one_pow] using h
  have hεJ : J ≤ RingHom.ker ε := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show ε (1 - e.val) = 0
    simp [hεe]
  let εC : C →ₐ[A] A ⧸ I := Ideal.Quotient.liftₐ J ε hεJ
  let εQ : C ⧸ L →ₐ[A] A ⧸ I := Ideal.Quotient.liftₐ L εC (map_le_ker_of_algHom I εC hker)
  have hleft : εQ.toRingHom.comp F = RingHom.id _ := by
    ext a
    simp [F, εQ, εC]
  have hFinj : Function.Injective F := by
    intro z w hzw
    have hz := congrArg εQ hzw
    change (εQ.toRingHom.comp F) z = (εQ.toRingHom.comp F) w at hz
    simpa only [hleft, RingHom.id_apply] using hz
  have hbij := bijective_algebraMap_of_bijective_quotientMap I hI ⟨hFinj, hFsurj⟩
  obtain ⟨α, hα⟩ := hbij.2 (q (AdjoinRoot.root f))
  refine ⟨α, ?_, ?_⟩
  · have h := congrArg εC hα
    have hαq : Ideal.Quotient.mk I α = 1 := by
      rw [εC.commutes] at h
      change Ideal.Quotient.mk I α = ε (AdjoinRoot.root f) at h
      exact h.trans hεroot
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simp [hαq])
  · have h := AdjoinRoot.aeval_algHom_eq_zero f q
    rw [← hα, aeval_algebraMap_apply] at h
    exact hbij.1 (by simpa using h)

private theorem monic_factor_lifting_of_etale_section_lifting
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson)
    (H : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
      ∀ σ : A' →ₐ[A] A ⧸ I,
        ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ) :
    HenselianPair A I := by
  refine ⟨hI, ?_⟩
  intro f hf g h hg hh hfac hcop
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have : Nontrivial (A ⧸ I) := nontrivial_quotient_of_le_jacobson_bot hI
  let n := f.natDegree
  let m := g.natDegree
  let k := h.natDegree
  have hn : n = m + k := by
    simpa [n, m, k, hg.natDegree_mul hh, hf.natDegree_map] using congrArg natDegree hfac
  let p : MonicDegreeEq A n := .mk f hf rfl
  let B := UniversalCoprimeFactorizationRing m k hn p
  let φ : B →ₐ[A] A ⧸ I :=
    (UniversalCoprimeFactorizationRing.homEquiv _ m k hn p).symm
      ⟨(.mk g hg rfl, .mk h hh rfl), hfac.symm, hcop⟩
  obtain ⟨τ, hτ⟩ := exists_section_of_etale_section_lifting A I H B φ
  let factors := UniversalCoprimeFactorizationRing.homEquiv A m k hn p τ
  refine ⟨factors.1.1.1, factors.1.2.1, factors.1.1.monic, factors.1.2.monic, ?_, ?_, ?_⟩
  · simpa [p] using factors.2.1.symm
  · have hh := UniversalCoprimeFactorizationRing.homEquiv_comp_fst A m k hn p τ
      (Ideal.Quotient.mkₐ A I)
    rw [hτ] at hh
    have heq := congrArg Subtype.val hh.symm
    change (factors.1.1.1).map (Ideal.Quotient.mk I) =
      ((UniversalCoprimeFactorizationRing.homEquiv _ m k hn p) φ).1.1.1 at heq
    rw [show ((UniversalCoprimeFactorizationRing.homEquiv _ m k hn p) φ).1.1.1 = g by
      unfold φ
      rw [Equiv.apply_symm_apply]
      rfl] at heq
    exact heq
  · have hh := UniversalCoprimeFactorizationRing.homEquiv_comp_snd A m k hn p τ
      (Ideal.Quotient.mkₐ A I)
    rw [hτ] at hh
    have heq := congrArg Subtype.val hh.symm
    change (factors.1.2.1).map (Ideal.Quotient.mk I) =
      ((UniversalCoprimeFactorizationRing.homEquiv _ m k hn p) φ).1.2.1 at heq
    rw [show ((UniversalCoprimeFactorizationRing.homEquiv _ m k hn p) φ).1.2.1 = h by
      unfold φ
      rw [Equiv.apply_symm_apply]
      rfl] at heq
    exact heq

/-- The five characterizations of a henselian pair: lifting maps from étale algebras,
bijectivity on idempotents for finite or integral algebras, and Gabber's unique-root criterion. -/
@[stacks 09XI]
public theorem henselianPair_tfae (A : Type u) [CommRing A] (I : Ideal A) :
    List.TFAE
      [HenselianPair A I,
        ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
          ∀ σ : A' →ₐ[A] A ⧸ I,
            ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ,
        ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] [Module.Finite A B],
          InducesBijectionOnIdempotents (I.map (algebraMap A B)),
        ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
          InducesBijectionOnIdempotents (I.map (algebraMap A B)),
        IsContainedInJacobson I ∧
          ∀ (f : A[X]), f.Monic →
            ∀ (n : ℕ), 1 ≤ n →
              ∀ a : Fin (n + 1) → I,
                f = X ^ n * (X - 1) +
                    ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ) →
                  ∃! α : A, α - 1 ∈ I ∧ f.IsRoot α] := by
  tfae_have 1 → 5
  | h => by
    refine ⟨h.1, ?_⟩
    intro f hf n _ a hform
    exact gabber_roots_of_henselianPair I h f hf n a hform
  tfae_have 5 → 2
  | h => by
    exact etale_section_lifting_of_gabber_root_condition A I h.1
      (fun f hf n hn a hform => (h.2 f hf n hn a hform).exists)
  tfae_have 2 → 4
  | h => by exact integral_idempotents_of_etale_section_lifting A I h
  tfae_have 4 → 3
  | h => by exact finite_idempotents_of_integral_idempotents A I h
  tfae_have 3 → 2
  | h => by
    have hsmall := finite_idempotents_universe A I h
    have hI := jacobson_of_finite_idempotents A I hsmall
    exact etale_section_lifting_of_gabber_root_condition A I hI
      (fun f hf n _ a hform => gabber_root_of_finite_idempotents I hI hsmall f hf n a hform)
  tfae_have 2 → 1
  | h => by
    exact monic_factor_lifting_of_etale_section_lifting A I
      (jacobson_of_etale_section_lifting A I h) h
  tfae_finish

/-- A ring `A` that is henselian with respect to `I` in the sense of `HenselianRing A I` forms a
henselian pair with `I`. -/
public theorem henselianPair_of_henselianRing (A : Type u) [CommRing A] (I : Ideal A)
    [HenselianRing A I] : HenselianPair A I := by
  apply ((henselianPair_tfae.{u, u} A I).out 5 1).mp
  refine ⟨HenselianRing.jac, ?_⟩
  intro f hf n hn a hfa
  have hf1 : f.eval 1 ∈ I := by
    rw [hfa]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_finsetSum, Polynomial.eval_C, one_pow, sub_self, mul_zero,
      zero_add, mul_one]
    exact I.sum_mem fun i _ ↦ (a i).property
  have hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    have hsum : Polynomial.eval 1
        (Polynomial.derivative (∑ i : Fin (n + 1),
          Polynomial.C (a i : A) * Polynomial.X ^ (i : ℕ))) ∈ I := by
      rw [map_sum, Polynomial.eval_finsetSum]
      apply Submodule.sum_mem
      intro i _
      simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
        Polynomial.derivative_pow, zero_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
      exact I.mul_mem_right _ (a i).property
    have heq : Ideal.Quotient.mk I (f.derivative.eval 1) = 1 := by
      rw [hfa]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X, Polynomial.derivative_sub, Polynomial.derivative_one,
        zero_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
        one_pow, sub_self, mul_zero, one_mul, map_add]
      rw [show Ideal.Quotient.mk I
          (Polynomial.eval 1 (Polynomial.derivative
            (∑ i : Fin (n + 1), Polynomial.C (a i : A) * Polynomial.X ^ (i : ℕ)))) = 0 by
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hsum]
      simp
    rw [heq]
    exact isUnit_one
  obtain ⟨α, hroot, hα⟩ := HenselianRing.is_henselian f hf 1 hf1 hder
  refine ⟨α, ⟨hα, hroot⟩, ?_⟩
  intro β hβ
  obtain ⟨k, hk⟩ := f.binomExpansion α (β - α)
  rw [add_sub_cancel] at hk
  rw [Polynomial.IsRoot] at hroot hβ
  rw [hroot, hβ.2, zero_add] at hk
  set y := β - α with hy
  have hymem : y ∈ I := by
    rw [hy, show β - α = (β - 1) - (α - 1) by ring]
    exact I.sub_mem hβ.1 hα
  have hfactor : y * (f.derivative.eval α + k * y) = 0 := by
    linear_combination -hk
  have hsα : IsUnit (f.derivative.eval α) := by
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I HenselianRing.jac
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    have hαeq : Ideal.Quotient.mk I α = Ideal.Quotient.mk I 1 := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hα
    rw [← Polynomial.eval_map_apply, hαeq, Polynomial.eval_map_apply]
    exact hder
  have hunit : IsUnit (f.derivative.eval α + k * y) := by
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I HenselianRing.jac
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    have hyq : Ideal.Quotient.mk I y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hymem
    rw [map_add, map_mul, hyq, mul_zero, add_zero]
    exact hsα.map (Ideal.Quotient.mk I)
  have hy0 : y = 0 := (IsUnit.mul_left_eq_zero hunit).mp hfactor
  rw [hy] at hy0
  exact sub_eq_zero.mp hy0

end

end

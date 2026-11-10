module

public import Mathlib.RingTheory.Ideal.IdempotentFG
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria.IntegralClosureSplitting
import all StacksFrontier.RingTheory.Henselian.Pair.Criteria.IntegralClosureSplitting

@[expose] public section

/-!
# Henselian pair criteria: product decompositions of reductions

Product decompositions `A ⧸ I × C` of the reduction of an algebra modulo the extended ideal: the
decomposition attached to an idempotent, its transport to the integral closure, the decomposition
coming from a section of an étale algebra, and Gabber's root criterion for the polynomials
`X ^ n (X - 1) + ∑ aᵢ X ^ i` with `aᵢ ∈ I`, under which the first factor can be taken integral.

## Main results

* `exists_quotient_algEquiv_prod_of_etale_section`: a section of an étale algebra splits its
  reduction as `A ⧸ I × C`.
* `exists_integral_factor_decomposition_of_gabber_root_condition`: under Gabber's criterion the
  first factor can be taken integral over `A`.
* `exists_integralClosure_quotient_algEquiv_prod`: the same decomposition stated as an algebra
  equivalence.
* `prodQuotientOfIsIdempotentElem_apply_idempotent_mod`: the product decomposition attached to an
  idempotent sends that idempotent to `(1, 0)`.

## Implementation notes

Reduction modulo `I` maps polynomial coefficients along `Ideal.Quotient.mk I`, and the extension of
`I` to an algebra `B` is `I.map (algebraMap A B)`.

## References

* [Stacks: Tag 09XD](https://stacks.math.columbia.edu/tag/09XD)
* [Stacks: Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
* Raynaud, *Anneaux locaux henséliens*, Chapter XI
* Gabber, *Affine analog of the proper base change theorem*, Proposition 1
-/

add_to_stacks 0EM4 "product decomposition by complementary idempotents"
  AlgEquiv.prodQuotientOfIsIdempotentElem

open Polynomial

universe u v w x

section

/-- The canonical `A / I`-algebra product decomposition of `B / IB` associated to an idempotent is
induced by the two quotient maps and sends that idempotent to `(1, 0)`. -/
@[stacks 0EM5]
theorem prodQuotientOfIsIdempotentElem_apply_idempotent_mod
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) b)) :
    let Q := B ⧸ I.map (algebraMap A B)
    let bbar : Q := Ideal.Quotient.mk (I.map (algebraMap A B)) b
    let e : Q ≃ₐ[A ⧸ I]
        (Q ⧸ Ideal.span {1 - bbar}) × (Q ⧸ Ideal.span {bbar}) :=
      AlgEquiv.prodQuotientOfIsIdempotentElem (A ⧸ I)
        (e := 1 - bbar) (f := bbar) hb.one_sub hb (by simp) hb.one_sub_mul_self
    e bbar = (1, 0) := by
  dsimp
  rw [AlgEquiv.prodQuotientOfIsIdempotentElem_apply]
  ext
  · rw [Ideal.Quotient.mk_eq_one_iff_sub_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩
  · simp

end

section

/-- The first projection of a product decomposition of `B ⧸ IB` over `A ⧸ I`, composed with the
map from `B ⧸ IB` induced by the algebra map, is finite. -/
private lemma finite_fst_comp_quotientMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {C : Type w} [CommRing C] [Algebra (A ⧸ I) C]
    (e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] ((A ⧸ I) × C)) :
    ((RingHom.fst (A ⧸ I) C).comp (e.toRingEquiv.toRingHom.comp
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))).Finite := by
  convert RingHom.Finite.id (A ⧸ I)
  ext r
  exact congrArg Prod.fst (e.commutes r)

/-- If the reduction of a finite type `A`-algebra `B` modulo `I` decomposes as `(A ⧸ I) × C`, then
the reduction of the integral closure of `A` in `B` has a compatible decomposition `(A ⧸ I) × C'`.
Compatibility is expressed using the canonical map induced by the inclusion
`integralClosure A B → B`. -/
@[stacks 0EM3]
theorem exists_integralClosure_quotient_algEquiv_prod
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.FiniteType A B]
    (C : Type w) [CommRing C] [Algebra (A ⧸ I) C]
    (e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] ((A ⧸ I) × C)) :
    let B' := integralClosure A B
    let IB' := I.map (algebraMap A B')
    let IB := I.map (algebraMap A B)
    let toReduction : (B' ⧸ IB') →+* (B ⧸ IB) :=
      Ideal.quotientMap IB (B'.val : B' →+* B) (by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        change ((B'.val : B' →+* B) (algebraMap A B' a)) ∈ IB
        change algebraMap A B a ∈ IB
        exact Ideal.mem_map_of_mem (algebraMap A B) ha)
    ∃ (C' : Type (max u v)) (hC' : CommRing C'),
      let _ := hC'
      ∃ hAlg : Algebra (A ⧸ I) C',
        let _ := hAlg
        ∃ (e' : (B' ⧸ IB') ≃ₐ[A ⧸ I] ((A ⧸ I) × C'))
          (k : C' →ₐ[A ⧸ I] C),
          ∀ x, e (toReduction x) = ((e' x).1, k (e' x).2) := by
  intro B' IB' IB toReduction
  obtain ⟨C', hC', e', k, hcompat, -⟩ :=
    exists_integralClosure_quotient_prod_and_awayMap_bijective I
      e.toRingEquiv (finite_fst_comp_quotientMap I e)
  let := hC'
  let D := ULift.{u} C'
  let : CommRing D := inferInstance
  let eD : ((integralClosure A B) ⧸ I.map (algebraMap A (integralClosure A B))) ≃+*
      ((A ⧸ I) × D) := e'.trans
    (RingEquiv.prodCongr (RingEquiv.refl (A ⧸ I)) ULift.ringEquiv.symm)
  let kD : D →+* C := k.comp ULift.ringEquiv.toRingHom
  have hcompatD (z) : e (toReduction z) =
      ((eD z).1, kD (eD z).2) := by
    simpa [eD, kD] using hcompat z
  let : Algebra (A ⧸ I) D := ((RingHom.snd (A ⧸ I) D).comp
    (eD.toRingHom.comp (algebraMap (A ⧸ I) _))).toAlgebra
  have hto (r : A ⧸ I) : toReduction
      (algebraMap (A ⧸ I) ((integralClosure A B) ⧸
        I.map (algebraMap A (integralClosure A B))) r) =
      algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)) r := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.quotientMap_mk
  have heD (r : A ⧸ I) : eD (algebraMap (A ⧸ I) _ r) =
      (r, algebraMap (A ⧸ I) D r) := by
    apply Prod.ext
    · have h := congrArg Prod.fst (hcompatD (algebraMap (A ⧸ I) _ r))
      rw [hto, e.commutes] at h
      exact h.symm
    · rfl
  let eAlg : ((integralClosure A B) ⧸ I.map (algebraMap A (integralClosure A B)))
      ≃ₐ[A ⧸ I] ((A ⧸ I) × D) :=
    { eD with commutes' := heD }
  have hkD (r : A ⧸ I) : kD (algebraMap (A ⧸ I) D r) =
      algebraMap (A ⧸ I) C r := by
    have h := congrArg Prod.snd (hcompatD (algebraMap (A ⧸ I) _ r))
    rw [hto, e.commutes] at h
    rw [heD] at h
    change algebraMap (A ⧸ I) C r = kD (algebraMap (A ⧸ I) D r) at h
    exact h.symm
  let kAlg : D →ₐ[A ⧸ I] C := { kD with commutes' := hkD }
  exact ⟨D, inferInstance, inferInstance, eAlg, kAlg, hcompatD⟩

end

section

/-- Let `A'` be an étale `A`-algebra and let `A' → A/I` be an `A`-algebra map. Then `A'/IA'` is
isomorphic, as an `A/I`-algebra, to a product `A/I × C`. Under this isomorphism, the map to the
first factor is the map induced by the given section. -/
@[stacks 0EM1]
theorem exists_quotient_algEquiv_prod_of_etale_section
    (A : Type u) [CommRing A] (A' : Type v) [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (I : Ideal A) (retraction : A' →ₐ[A] A ⧸ I) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra (A ⧸ I) C)
      (e : (A' ⧸ I.map (algebraMap A A')) ≃ₐ[A ⧸ I] ((A ⧸ I) × C)),
      ∀ x : A', (e (Ideal.Quotient.mk (I.map (algebraMap A A')) x)).1 = retraction x := by
  let B := A' ⧸ I.map (algebraMap A A')
  let R := A ⧸ I
  have hkill : ∀ x ∈ I.map (algebraMap A A'), retraction x = 0 := by
    intro x hx
    rw [← RingHom.mem_ker]
    exact (Ideal.map_le_iff_le_comap.mpr (by
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr ha))) hx
  let sigmaRing : B →+* R := Ideal.Quotient.lift (I.map (algebraMap A A'))
    retraction.toRingHom hkill
  have hlift (x : A') : sigmaRing (Ideal.Quotient.mk _ x) = retraction x := rfl
  let sigma : B →ₐ[R] R :=
    { sigmaRing with
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact (hlift (algebraMap A A' a)).trans (retraction.commutes a) }
  have hsigma : ∀ x : A', sigma (Ideal.Quotient.mk _ x) = retraction x := hlift
  have hsurj : Function.Surjective sigma := by
    intro r
    exact ⟨algebraMap R B r, by simp⟩
  have : Algebra.Etale R B :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).symm
  let : Algebra B R := sigma.toRingHom.toAlgebra
  have : IsScalarTower R B R := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R R x = sigma (algebraMap R B x)
    simp
  have : Algebra.FormallyEtale B R :=
    Algebra.FormallyEtale.of_restrictScalars (R := R) (A := B) (B := R)
  have hidem : IsIdempotentElem (RingHom.ker (sigma : B →+* R)) := by
    have h := (Algebra.FormallyEtale.iff_of_surjective hsurj).mp inferInstance
    exact h
  have hfg : (RingHom.ker (sigma : B →+* R)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective sigma hsurj
  obtain ⟨e, he, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hidem
  let split := AlgEquiv.prodQuotientOfIsIdempotentElem (R := R) he he.one_sub
    (by simp) (by simp [he])
  have hspanKill : ∀ x ∈ Ideal.span {e}, sigma.toRingHom x = 0 := by
    intro x hx
    exact (show x ∈ RingHom.ker (sigma : B →+* R) from hspan.symm ▸ hx)
  let firstHom : (B ⧸ Ideal.span {e}) →ₐ[R] R :=
    Ideal.Quotient.liftₐ (Ideal.span {e}) sigma hspanKill
  have hfirst_mk (b : B) : firstHom (Ideal.Quotient.mk _ b) = sigma b :=
    AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (Ideal.span {e}) sigma hspanKill) b
  have hfirstSurj : Function.Surjective firstHom := by
    intro r
    obtain ⟨b, rfl⟩ := hsurj r
    exact ⟨Ideal.Quotient.mk _ b, hfirst_mk b⟩
  have hfirstInj : Function.Injective firstHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hfirst_mk] at hx
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    have hbker : b ∈ RingHom.ker (sigma : B →+* R) := hx
    rw [hspan] at hbker
    exact hbker
  let first : (B ⧸ Ideal.span {e}) ≃ₐ[R] R :=
    AlgEquiv.ofBijective firstHom ⟨hfirstInj, hfirstSurj⟩
  let C := B ⧸ Ideal.span {1 - e}
  let equiv : B ≃ₐ[R] R × C := split.trans (AlgEquiv.prodCongr first AlgEquiv.refl)
  refine ⟨C, inferInstance, inferInstance, equiv, ?_⟩
  intro x
  change (equiv (Ideal.Quotient.mk _ x)).1 = retraction x
  change first (Ideal.Quotient.mk (Ideal.span {e}) (Ideal.Quotient.mk _ x)) = retraction x
  change firstHom (Ideal.Quotient.mk (Ideal.span {e}) (Ideal.Quotient.mk _ x)) = retraction x
  rw [hfirst_mk]
  exact hsigma x

end

section

set_option backward.isDefEq.respectTransparency false in
private lemma exists_finite_subalgebra_awayMap_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (b : S) (hb : IsIntegral R b)
    (h : ∀ x : S, ∃ n : ℕ, IsIntegral R (b ^ n * x)) :
    ∃ T : Subalgebra R S, T.toSubmodule.FG ∧ ∃ r : T,
      (r : S) = b ∧ Function.Bijective (Localization.awayMap T.val.toRingHom r) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose m hm using h
  let t := insert b { b ^ m x * x | x ∈ s }
  let r : Algebra.adjoin R t := ⟨b, Algebra.subset_adjoin (by simp [t])⟩
  refine ⟨Algebra.adjoin R t, fg_adjoin_of_finite ?_ ?_, r, rfl, ?_, ?_⟩
  · simp only [t, Set.finite_insert]
    exact s.finite_toSet.image (fun x ↦ b ^ m x * x)
  · rintro a (rfl | ⟨x, hx, rfl⟩)
    · exact hb
    · exact hm x
  · exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective
  · have hrange : (IsScalarTower.toAlgHom R S (Localization.Away b)).range ≤
        (Localization.awayMapₐ (Algebra.adjoin R t).val r).range := by
      rw [← Algebra.map_top, ← hs, Subalgebra.map_le, Algebra.adjoin_le_iff]
      intro x hx
      suffices ∃ a ∈ Algebra.adjoin R t, ∃ n, b ^ n ∈ Algebra.adjoin R t ∧
          ∃ k, b ^ k * a = b ^ k * (x * b ^ n) by
        simpa [(IsLocalization.mk'_surjective (.powers r)).exists,
          (IsLocalization.mk'_surjective (.powers b)).forall, Localization.awayMapₐ,
          IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
          Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
          IsLocalization.eq_iff_exists (.powers b), Subalgebra.val, IsLocalization.Away.mapₐ, r]
      exact ⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, mul_comm _ _⟩),
        m x, pow_mem r.property _, 1, rfl⟩
    intro x
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
      (.powers ((Algebra.adjoin R t).val.toRingHom r)) x
    obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := hrange ⟨x, rfl⟩
    refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
    simp only [map_mul, map_pow, hy]
    simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
      IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
      ← IsLocalization.mk'_pow, r]

private lemma exists_monic_isRoot_of_quotient_prod
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    {C : Type w} [CommRing C] [Algebra (A ⧸ I) C]
    (e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] ((A ⧸ I) × C)) :
    ∃ (b : B) (d : ℕ) (f : A[X]), 1 ≤ d ∧ f.Monic ∧
      aeval b f = 0 ∧ f.map (Ideal.Quotient.mk I) = (X - 1) * X ^ d ∧
      e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0) ∧
      ∀ x : B, ∃ n : ℕ, IsIntegral A (b ^ n * x) := by
  let J := I.map (algebraMap A B)
  let π : B →+* (A ⧸ I) × C := e.toRingHom.comp (Ideal.Quotient.mk J)
  obtain ⟨C', hC', e', k, hcompat, b, hb, hbij⟩ :=
    exists_integralClosure_quotient_prod_and_awayMap_bijective I
      e.toRingEquiv (finite_fst_comp_quotientMap I e)
  let := hC'
  have hbπ : π (b : B) = (1, 0) := by
    have hh := hcompat (Ideal.Quotient.mk _ b)
    rw [hb] at hh
    simpa [π, J] using hh
  have hclear (x : B) : ∃ n : ℕ, IsIntegral A ((b : B) ^ n * x) := by
    obtain ⟨a, n, ha⟩ := Localization.awayMap_surjective_iff.mp hbij.2 x
    exact ⟨n, ha ▸ a.property⟩
  obtain ⟨S, hS, r, hr, hrbij⟩ :=
    exists_finite_subalgebra_awayMap_bijective (b : B) b.property hclear
  let : Module.Finite A S := ⟨(Submodule.fg_top _).mpr hS⟩
  have hπsurj : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hπker : RingHom.ker π = J :=
    (RingHom.ker_comp_of_injective _ e.injective).trans Ideal.mk_ker
  have hmap : (I.map (algebraMap A S)).map S.val.toRingHom = J := by
    rw [Ideal.map_map]
    rfl
  obtain ⟨D, hD, ε, kD, hε, c, hc, hcbij⟩ :=
    exists_prod_equiv_of_awayMap_bijective S.val.toRingHom
      (I.map (algebraMap A S)) π hπsurj (hπker.trans hmap.symm) r
      (by change π (r : B) = _; rw [hr]; exact hbπ) hrbij
  let := hD
  let : Algebra (A ⧸ I) D := ((RingHom.snd (A ⧸ I) D).comp
    (ε.toRingHom.comp (algebraMap (A ⧸ I) (S ⧸ I.map (algebraMap A S))))).toAlgebra
  have hεfst (a : A ⧸ I) :
      (ε (algebraMap (A ⧸ I) (S ⧸ I.map (algebraMap A S)) a)).1 = a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hh := congrArg Prod.fst (hε (algebraMap A S a))
    have he := congrArg Prod.fst (e.commutes (Ideal.Quotient.mk I a))
    exact hh.symm.trans he
  let εₐ : (S ⧸ I.map (algebraMap A S)) ≃ₐ[A ⧸ I] ((A ⧸ I) × D) :=
    { ε with commutes' := fun a ↦ Prod.ext (hεfst a) rfl }
  obtain ⟨d, f, hd, hf, hfc, hfmap⟩ :=
    exists_monic_isRoot_map_eq_X_sub_one_mul_X_pow I hI
      (A ⧸ I) D εₐ Function.surjective_id c hc
  refine ⟨(c : B), d, f, hd, hf, ?_, hfmap, ?_, ?_⟩
  · have hz : aeval c f = 0 := by simpa only [IsRoot, eval_map, aeval_def] using hfc
    change aeval (S.val c) f = 0
    rw [aeval_algHom_apply, hz, map_zero]
  · have hh := hε c
    rw [hc] at hh
    simpa [π, J] using hh
  · intro x
    obtain ⟨a, n, ha⟩ := Localization.awayMap_surjective_iff.mp hcbij.2 x
    exact ⟨n, ha ▸ (Algebra.IsIntegral.isIntegral a).map S.val⟩

private lemma exists_root_of_map_eq_X_sub_one_mul_X_pow
    {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (hroot : ∀ (f : A[X]), f.Monic → ∀ (n : ℕ), 1 ≤ n →
      ∀ a : Fin (n + 1) → I,
        f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ) →
          ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (f : A[X]) (hf : f.Monic) (n : ℕ) (hn : 1 ≤ n)
    (hmap : f.map (Ideal.Quotient.mk I) = (X - 1) * X ^ n) :
    ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨1, by simp, Subsingleton.elim _ _⟩
  have hproper : I ≠ ⊤ := fun ht ↦ by
    have ht' : (⊥ : Ideal A).jacobson = ⊤ := top_le_iff.mp (ht ▸ hI)
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp ht')
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let p : A[X] := X ^ n * (X - 1)
  have hp : p.Monic := (monic_X_pow n).mul (by simpa using monic_X_sub_C (1 : A))
  have hpmap : p.map (Ideal.Quotient.mk I) = (X - 1) * X ^ n := by
    simp [p, mul_comm]
  have hdeg : f.natDegree = p.natDegree := by
    rw [← hf.natDegree_map (Ideal.Quotient.mk I), hmap, ← hpmap,
      hp.natDegree_map]
  have hpdeg : p.degree = (n + 1 : ℕ) := by
    dsimp only [p]
    rw [(show (X - 1 : A[X]).Monic by simpa using monic_X_sub_C (1 : A)).degree_mul]
    rw [show (X - 1 : A[X]).degree = 1 by simpa using degree_X_sub_C (1 : A)]
    simp
  have hlt : (f - p).degree < (n + 1 : ℕ) := by
    have heq : f.degree = p.degree := by
      rw [degree_eq_natDegree hf.ne_zero, degree_eq_natDegree hp.ne_zero, hdeg]
    rw [← hpdeg, ← heq]
    exact degree_sub_lt_left heq hf.ne_zero (hf.trans hp.symm)
  have hcoeff (i : ℕ) : (f - p).coeff i ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← coeff_map]
    simp [Polynomial.map_sub, hmap, hpmap]
  let a : Fin (n + 1) → I := fun i ↦ ⟨(f - p).coeff i, hcoeff i⟩
  apply hroot f hf n hn a
  have hsum : (∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ)) = f - p := by
    dsimp only [a]
    rw [Polynomial.sum_fin (fun i c ↦ C c * X ^ i) (by simp) hlt,
      Polynomial.sum_C_mul_X_pow_eq]
  rw [hsum]
  dsimp only [p]
  ring

private lemma exists_isCoprime_factor_of_root
    {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (f : A[X]) (n : ℕ)
    (hmap : f.map (Ideal.Quotient.mk I) = (X - 1) * X ^ n)
    (a : A) (ha : a - 1 ∈ I) (hfa : f.IsRoot a) :
    ∃ g : A[X], f = (X - C a) * g ∧ IsCoprime (X - C a) g := by
  obtain ⟨g, hg⟩ := (dvd_iff_isRoot).mpr hfa
  have haq : Ideal.Quotient.mk I a = 1 := (Ideal.Quotient.mk_eq_mk_iff_sub_mem a 1).mpr ha
  have hmapg : g.map (Ideal.Quotient.mk I) = X ^ n := by
    have hm := congrArg (Polynomial.map (Ideal.Quotient.mk I)) hg
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, haq, hmap, C_1] at hm
    have hd := congrArg (fun p : (A ⧸ I)[X] ↦ p /ₘ (X - 1)) hm
    have hmonic : (X - 1 : (A ⧸ I)[X]).Monic := by
      simpa using monic_X_sub_C (1 : A ⧸ I)
    rw [mul_divByMonic_cancel_left _ hmonic, mul_divByMonic_cancel_left _ hmonic] at hd
    exact hd.symm
  have hgeval : Ideal.Quotient.mk I (g.eval a) = 1 := by
    rw [← eval₂_at_apply, ← eval_map, hmapg]
    simp [haq]
  have hgunit : IsUnit (g.eval a) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hI (by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp [hgeval]))
  obtain ⟨q, hq⟩ : X - C a ∣ g - C (g.eval a) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot]
  obtain ⟨u, hu⟩ := hgunit
  refine ⟨g, hg, C (↑u⁻¹ : A) * (-q), C (↑u⁻¹ : A), ?_⟩
  calc
    C (↑u⁻¹ : A) * (-q) * (X - C a) + C (↑u⁻¹ : A) * g =
        C (↑u⁻¹ : A) * (g - (X - C a) * q) := by ring
    _ = C (↑u⁻¹ : A) * C (g.eval a) := by rw [← hq]; ring
    _ = 1 := by rw [← hu, ← C_mul]; simp

private lemma prod_quotient_bijective_of_isCoprime_of_mul_eq_zero
    {R : Type u} [CommRing R] {x y : R} (hxy : IsCoprime x y) (hzero : x * y = 0) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {x})).prod
      (Ideal.Quotient.mk (Ideal.span {y}))) := by
  obtain ⟨u, v, huv⟩ := hxy
  let q₁ := Ideal.Quotient.mk (Ideal.span {x})
  let q₂ := Ideal.Quotient.mk (Ideal.span {y})
  have hx : q₁ x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hy : q₂ y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hv : q₁ (v * y) = 1 := by
    have hh := congrArg q₁ huv
    simpa [map_add, map_mul, hx] using hh
  have hu : q₂ (u * x) = 1 := by
    have hh := congrArg q₂ huv
    simpa [map_add, map_mul, hy] using hh
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm _ bot_le
    intro z hz
    have hz₁ : q₁ z = 0 := congrArg Prod.fst hz
    have hz₂ : q₂ z = 0 := congrArg Prod.snd hz
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz₁)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz₂)
    change z = 0
    calc
      z = (u * x + v * y) * z := by rw [huv, one_mul]
      _ = u * (x * y) * b + v * (x * y) * a := by
        conv_lhs => rw [add_mul]; arg 1; rw [hb]
        conv_lhs => arg 2; rw [ha]
        ring
      _ = 0 := by rw [hzero]; ring
  · rintro ⟨z₁, z₂⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z₁
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z₂
    refine ⟨v * y * a + u * x * b, Prod.ext ?_ ?_⟩
    · change q₁ (v * y * a + u * x * b) = q₁ a
      simp only [map_add, map_mul, hx, mul_zero, zero_mul, add_zero]
      rw [← map_mul, hv, one_mul]
    · change q₂ (v * y * a + u * x * b) = q₂ b
      simp only [map_add, map_mul, hy, mul_zero, zero_mul, zero_add]
      rw [← map_mul, hu, one_mul]

/-- Under Gabber's Jacobson-radical and root-lifting conditions, a section modulo `I` of an
étale `A`-algebra comes from a product decomposition whose first factor is integral over `A`
and has reduction `A ⧸ I`. -/
@[stacks 0EM2]
theorem exists_integral_factor_decomposition_of_gabber_root_condition
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (hroot : ∀ (f : A[X]), f.Monic →
      ∀ (n : ℕ), 1 ≤ n →
        ∀ a : Fin (n + 1) → I,
          f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ) →
            ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (A' : Type (max u v)) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (σ : A' →ₐ[A] A ⧸ I) :
    ∃ (A₁ A₂ : Type (max u v))
      (_ : CommRing A₁) (_ : CommRing A₂)
      (_ : Algebra A A₁) (_ : Algebra A A₂)
      (e : A' ≃ₐ[A] A₁ × A₂) (q : A₁ →ₐ[A] A ⧸ I),
      Algebra.IsIntegral A A₁ ∧
        Function.Surjective q ∧
        RingHom.ker q = I.map (algebraMap A A₁) ∧
        q.comp ((AlgHom.fst A A₁ A₂).comp e.toAlgHom) = σ := by
  classical
  obtain ⟨C, hC, hAC, ε, hε⟩ :=
    exists_quotient_algEquiv_prod_of_etale_section A A' I σ
  let := hC
  let := hAC
  obtain ⟨b, n, f, hn, hf, hfb, hfmap, hb, hclear⟩ :=
    exists_monic_isRoot_of_quotient_prod I hI ε
  obtain ⟨a, ha, hfa⟩ :=
    exists_root_of_map_eq_X_sub_one_mul_X_pow I hI hroot f hf n hn hfmap
  obtain ⟨g, hfg, hcop⟩ := exists_isCoprime_factor_of_root I hI f n hfmap a ha hfa
  have haunit : IsUnit a := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hI ha)
  obtain ⟨u, hu⟩ := haunit
  let x : A' := b - algebraMap A A' a
  let y : A' := aeval b g
  have hxy : IsCoprime x y := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, aeval_X, aeval_C]
      using hcop.map (aeval b).toRingHom
  have hzero : x * y = 0 := by
    simpa only [hfg, map_mul, map_sub, aeval_X, aeval_C] using hfb
  let K : Ideal A' := Ideal.span {x}
  let L : Ideal A' := Ideal.span {y}
  let Q := A' ⧸ K
  let p : A' →ₐ[A] Q := Ideal.Quotient.mkₐ A K
  let e : A' ≃ₐ[A] Q × (A' ⧸ L) := AlgEquiv.ofBijective
    (p.prod (Ideal.Quotient.mkₐ A L))
    (prod_quotient_bijective_of_isCoprime_of_mul_eq_zero hxy hzero)
  have hpa : p b = algebraMap A Q a := by
    have hx : p x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    simpa only [x, map_sub, p.commutes, sub_eq_zero] using hx
  have haq : Ideal.Quotient.mk I a = 1 := (Ideal.Quotient.mk_eq_mk_iff_sub_mem a 1).mpr ha
  have hσb : σ b = 1 := by
    rw [← hε b, hb]
  have hKσ : K ≤ RingHom.ker σ := by
    apply Ideal.span_le.mpr
    rintro z rfl
    change σ (b - algebraMap A A' a) = 0
    rw [map_sub, σ.commutes, hσb]
    exact sub_eq_zero.mpr haq.symm
  let q : Q →ₐ[A] A ⧸ I := Ideal.Quotient.liftₐ K σ (fun z hz ↦ hKσ hz)
  have hqp (z : A') : q (p z) = σ z := rfl
  refine ⟨Q, A' ⧸ L, inferInstance, inferInstance, inferInstance, inferInstance,
    e, q, ?_, ?_, ?_, ?_⟩
  · constructor
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨k, hk⟩ := hclear z
    have hint : IsIntegral A (p z * (p b) ^ k) := by
      simpa only [map_mul, map_pow, mul_comm] using hk.map p
    apply IsIntegral.of_mul_unit (r := (↑u⁻¹ : A) ^ k) (y := (p b) ^ k) _ hint
    rw [hpa, ← hu, ← map_pow, ← map_mul]
    simp [← mul_pow]
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap A Q a, q.commutes a⟩
  · apply le_antisymm
    · intro z hz
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hσz : σ z = 0 := hz
      let J := I.map (algebraMap A A')
      have hmem : b * z ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        apply ε.injective
        rw [map_zero, map_mul, map_mul, hb]
        apply Prod.ext
        · change 1 * (ε (Ideal.Quotient.mk _ z)).1 = 0
          rw [one_mul]
          exact (hε z).trans hσz
        · simp
      have hmap : J.map p.toRingHom = I.map (algebraMap A Q) := by
        rw [Ideal.map_map]
        rfl
      have hpz : p (b * z) ∈ I.map (algebraMap A Q) := by
        rw [← hmap]
        exact Ideal.mem_map_of_mem p hmem
      have hmul := (I.map (algebraMap A Q)).mul_mem_left (algebraMap A Q (↑u⁻¹ : A)) hpz
      change p z ∈ I.map (algebraMap A Q)
      convert hmul using 1
      rw [map_mul, hpa, ← hu, ← mul_assoc, ← map_mul]
      simp
    · apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change q (algebraMap A Q a) = 0
      rw [q.commutes]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  · ext z
    exact hqp z

end

end

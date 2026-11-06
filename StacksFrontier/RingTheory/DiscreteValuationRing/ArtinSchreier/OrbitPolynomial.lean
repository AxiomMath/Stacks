module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.RamificationCases

/-!
# Eliminating degree-prime ramification: orbit polynomials

Orbit polynomials `∏_{v ∈ V} (X - v)` of finite translation subgroups, the Eisenstein and Galois
properties of their Artin--Schreier-type translates, Artin--Schreier generators of degree-`p`
Galois extensions in characteristic `p`, and total ramification criteria via ideal powers.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-! ### Eliminating degree-prime ramification in equal characteristic -/

/-- Over a discrete valuation ring, the length-theoretic ramification index of a maximal ideal
of an integral Dedekind extension equals its ideal-power ramification index over the maximal
ideal. -/
private theorem ramificationIdx_eq_ramificationIdx'_maximalIdeal
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    [Algebra.IsIntegral R S] (q : Ideal S) [q.IsMaximal] :
    q.ramificationIdx R = (IsLocalRing.maximalIdeal R).ramificationIdx' q := by
  have : q.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨((IsLocalRing.isMaximal_iff R).mp
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q)).symm⟩
  exact (Ideal.ramificationIdx'_eq_ramificationIdx _ q
    (IsDiscreteValuationRing.not_a_field R)).symm

private theorem isIntegral_map_of_comp_eq {A K₁ B L₁ : Type*} [CommRing A] [CommRing K₁]
    [CommRing B] [CommRing L₁] [Algebra A K₁] [Algebra B L₁]
    (g : A →+* B) (f : K₁ →+* L₁)
    (hfg : (algebraMap B L₁).comp g = f.comp (algebraMap A K₁)) {x : K₁}
    (hx : IsIntegral A x) : IsIntegral B (f x) := by
  obtain ⟨P, hmonic, hP⟩ := hx
  refine ⟨P.map g, hmonic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hfg, ← Polynomial.hom_eval₂, hP, map_zero]

/-- The reduced compositum `(L ⊗[K] K₁)_red` with the integral closures of `A` in `K₁` and of
`B` in the compositum, as in Tag 09EM. -/
private noncomputable def integralClosureBaseChangeOfFinite
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁] :
    IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁}
      A B K L K₁ :=
  let T := L ⊗[K] K₁
  let R := T ⧸ nilradical T
  letI algK₁T : Algebra K₁ T := Algebra.TensorProduct.rightAlgebra
  let fK₁ : K₁ →+* R := algebraMap K₁ R
  have towerK : IsScalarTower K K₁ R := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap K R x = Ideal.Quotient.mk _ (1 ⊗ₜ algebraMap K K₁ x)
    rw [← Algebra.TensorProduct.algebraMap_apply']; rfl
  have hcomp : (algebraMap B R).comp (algebraMap A B) = fK₁.comp (algebraMap A K₁) := by
    ext a
    change algebraMap B R (algebraMap A B a) = algebraMap K₁ R (algebraMap A K₁ a)
    rw [IsScalarTower.algebraMap_apply B L R, ← IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L R,
      IsScalarTower.algebraMap_apply A K K₁, ← IsScalarTower.algebraMap_apply K K₁ R]
  let g : integralClosure A K₁ →+* integralClosure B R :=
    { toFun := fun x =>
        ⟨fK₁ (x : K₁), isIntegral_map_of_comp_eq (algebraMap A B) fK₁ hcomp x.2⟩
      map_one' := Subtype.ext (map_one fK₁)
      map_mul' := fun x y => Subtype.ext (map_mul fK₁ (x : K₁) y)
      map_zero' := Subtype.ext (map_zero fK₁)
      map_add' := fun x y => Subtype.ext (map_add fK₁ (x : K₁) y) }
  letI algA₁ : Algebra (integralClosure A K₁) (integralClosure B R) := g.toAlgebra
  letI algAB₁ : Algebra A (integralClosure B R) :=
    ((algebraMap B (integralClosure B R)).comp (algebraMap A B)).toAlgebra
  have towerAB : IsScalarTower A B (integralClosure B R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towerAA₁ : IsScalarTower A (integralClosure A K₁) (integralClosure B R) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext
      (DFunLike.congr_fun hcomp a)
  { L₁ := R
    A₁ := integralClosure A K₁
    B₁ := integralClosure B R
    eL₁ := AlgEquiv.refl
    eL₁_left := fun _ => rfl
    eL₁_right := fun _ => rfl
    ringSquare := fun _ => rfl }

private noncomputable def orbitPolynomial {Base : Type*} [CommRing Base]
    (translations : AddSubgroup Base) [Fintype translations] : Base[X] :=
  ∏ element : translations, (X - C (element : Base))

private theorem orbitPolynomial_eval_add {Base : Type*} [CommRing Base]
    (translations : AddSubgroup Base) [Fintype translations]
    (point : Base) (shift : translations) :
    (orbitPolynomial translations).eval (point + shift) =
      (orbitPolynomial translations).eval point := by
  classical
  simp only [orbitPolynomial, eval_prod, eval_sub, eval_X, eval_C]
  apply Fintype.prod_equiv (Equiv.subRight shift)
  intro element
  simp only [Equiv.subRight_apply, AddSubgroup.coe_sub]
  ring


private theorem orbitPolynomial_eval₂_add {Base Extension : Type*}
    [CommRing Base] [CommRing Extension]
    (embedding : Base →+* Extension)
    (translations : AddSubgroup Base) [Fintype translations]
    (point : Extension) (shift : translations) :
    (orbitPolynomial translations).eval₂ embedding (point + embedding shift) =
      (orbitPolynomial translations).eval₂ embedding point := by
  classical
  simp only [orbitPolynomial, eval₂_finsetProd, eval₂_sub, eval₂_X, eval₂_C]
  apply Fintype.prod_equiv (Equiv.subRight shift)
  intro element
  simp only [Equiv.subRight_apply, AddSubgroup.coe_sub, map_sub]
  ring

/-- Translating a point by the image of distinct elements of `translations` gives distinct
points. -/
private theorem injective_add_embedding {Base Extension : Type*}
    [CommRing Base] [CommRing Extension] (embedding : Base →+* Extension)
    (embedding_injective : Function.Injective embedding)
    (translations : AddSubgroup Base) (root : Extension) :
    Function.Injective (fun element : translations => root + embedding element) := fun _ _ eq =>
  Subtype.ext (embedding_injective (add_left_cancel eq))

private theorem orbitPolynomial_natDegree {Base : Type*} [CommRing Base] [Nontrivial Base]
    (translations : AddSubgroup Base) [Fintype translations] :
    (orbitPolynomial translations).natDegree = Fintype.card translations := by
  simp [orbitPolynomial]

private theorem orbitPolynomial_sub_C_monic {Base : Type*} [CommRing Base] [Nontrivial Base]
    (translations : AddSubgroup Base) [Fintype translations] (constant : Base) :
    (orbitPolynomial translations - C constant).Monic :=
  (monic_prod_X_sub_C _ _).sub_of_left (lt_of_le_of_lt degree_C_le
    (natDegree_pos_iff_degree_pos.mp
      ((orbitPolynomial_natDegree translations).symm ▸ Fintype.card_pos)))

private theorem orbitPolynomial_sub_C_factorization {Base Extension : Type*}
    [CommRing Base] [Nontrivial Base] [Field Extension]
    (embedding : Base →+* Extension)
    (embedding_injective : Function.Injective embedding)
    (translations : AddSubgroup Base) [Fintype translations]
    (constant : Base) (root : Extension)
    (root_equation : (orbitPolynomial translations).eval₂ embedding root =
      embedding constant) :
    (orbitPolynomial translations - C constant).map embedding =
      ∏ element : translations, (X - C (root + embedding element)) := by
  classical
  apply eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _)
    ((orbitPolynomial_sub_C_monic translations constant).map embedding)
  · apply Fintype.prod_dvd_of_coprime
      (pairwise_coprime_X_sub_C (injective_add_embedding embedding embedding_injective _ root))
    intro element
    rw [dvd_iff_isRoot, IsRoot.def, eval_map, eval₂_sub, eval₂_C,
      orbitPolynomial_eval₂_add, root_equation, sub_self]
  · exact natDegree_map_le.trans (by simp only [natDegree_sub_C, orbitPolynomial_natDegree,
      natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, le_refl])

private theorem orbitPolynomial_sub_C_splits_separable {Base Extension : Type*}
    [Field Base] [Field Extension]
    (embedding : Base →+* Extension)
    (translations : AddSubgroup Base) [Fintype translations]
    (constant : Base) (root : Extension)
    (root_equation : (orbitPolynomial translations).eval₂ embedding root =
      embedding constant) :
    ((orbitPolynomial translations - C constant).map embedding).Splits ∧
      (orbitPolynomial translations - C constant).Separable := by
  classical
  have factorization := orbitPolynomial_sub_C_factorization embedding embedding.injective
    translations constant root
    root_equation
  constructor
  · rw [factorization]
    exact Splits.prod (fun _ _ => Splits.X_sub_C _)
  · apply (separable_map embedding).mp
    rw [factorization, separable_prod_X_sub_C_iff]
    exact injective_add_embedding embedding embedding.injective _ root


/-- `AdjoinRoot f` is Galois over a field once `f` is irreducible, separable and splits there. -/
private theorem isGalois_adjoinRoot_of_splits_separable {F : Type*} [Field F] (f : F[X])
    [Fact (Irreducible f)] (splits : (f.map (algebraMap F (AdjoinRoot f))).Splits)
    (separable : f.Separable) : IsGalois F (AdjoinRoot f) := by
  let _ : f.IsSplittingField F (AdjoinRoot f) := by
    constructor
    · exact splits
    · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (Fact.out : Irreducible f).ne_zero,
        aeval_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]
  exact IsGalois.of_separable_splitting_field separable

private theorem orbitPolynomial_sub_C_adjoinRoot_isGalois {Base : Type*} [Field Base]
    (translations : AddSubgroup Base) [Fintype translations] (constant : Base)
    [Fact (Irreducible (orbitPolynomial translations - C constant))] :
    IsGalois Base (AdjoinRoot (orbitPolynomial translations - C constant)) := by
  let polynomial := orbitPolynomial translations - C constant
  let extension := AdjoinRoot polynomial
  have root_equation : (orbitPolynomial translations).eval₂ (algebraMap Base extension)
      (AdjoinRoot.root polynomial) = algebraMap Base extension constant := by
    have equation := AdjoinRoot.eval₂_root polynomial
    change (orbitPolynomial translations - C constant).eval₂ _ _ = 0 at equation
    rw [eval₂_sub, eval₂_C] at equation
    exact sub_eq_zero.mp equation
  have splitting := orbitPolynomial_sub_C_splits_separable
    (algebraMap Base extension) translations constant (AdjoinRoot.root polynomial) root_equation
  exact isGalois_adjoinRoot_of_splits_separable polynomial splitting.1 splitting.2


private theorem orbitPolynomial_eval_zero {Base : Type*} [CommRing Base]
    (translations : AddSubgroup Base) [Fintype translations] :
    (orbitPolynomial translations).eval 0 = 0 := by
  classical
  simp only [orbitPolynomial, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : translations))
  simp

private theorem orbitPolynomial_map_quotient {Base : Type*} [CommRing Base]
    (translations : AddSubgroup Base) [Fintype translations]
    (ideal : Ideal Base) (contained : ∀ element : translations, (element : Base) ∈ ideal) :
    (orbitPolynomial translations).map (Ideal.Quotient.mk ideal) =
      X ^ Fintype.card translations := by
  classical
  have vanishes : ∀ element : translations, Ideal.Quotient.mk ideal element = 0 :=
    fun element => Ideal.Quotient.eq_zero_iff_mem.mpr (contained element)
  simp only [orbitPolynomial, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, vanishes, C_0, sub_zero, Finset.prod_const, Finset.card_univ]

private theorem orbitPolynomial_sub_C_isEisensteinAt {Base : Type*}
    [CommRing Base] [Nontrivial Base]
    (translations : AddSubgroup Base) [Fintype translations]
    (ideal : Ideal Base) (proper : ideal ≠ ⊤)
    (contained : ∀ element : translations, (element : Base) ∈ ideal)
    (constant : Base) (constant_mem : constant ∈ ideal)
    (constant_not_mem : constant ∉ ideal ^ 2) :
    (orbitPolynomial translations - C constant).IsEisensteinAt ideal := by
  classical
  apply (orbitPolynomial_sub_C_monic translations constant).isEisensteinAt_of_mem_of_notMem proper
  · intro index below
    rw [natDegree_sub_C, orbitPolynomial_natDegree] at below
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have quotient_equation :
        (orbitPolynomial translations - C constant).map (Ideal.Quotient.mk ideal) =
          X ^ Fintype.card translations := by
      rw [Polynomial.map_sub, Polynomial.map_C,
        orbitPolynomial_map_quotient translations ideal contained,
        Ideal.Quotient.eq_zero_iff_mem.mpr constant_mem, C_0, sub_zero]
    have coefficient_equation :=
      congrArg (fun polynomial : (Base ⧸ ideal)[X] => polynomial.coeff index)
      quotient_equation
    simpa only [coeff_map, coeff_X_pow, ite_eq_right (ne_of_lt below)] using coefficient_equation
  · have constant_coefficient :
        (orbitPolynomial translations - C constant).coeff 0 = -constant := by
      rw [coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, orbitPolynomial_eval_zero, zero_sub]
    simpa only [constant_coefficient, Ideal.neg_mem_iff] using constant_not_mem


private theorem exists_finite_translation_subgroup_in_power {Constants Base : Type*}
    [Field Constants] [Fintype Constants] [CommRing Base] [IsDomain Base]
    [Algebra Constants Base]
    (parameter : Base) (parameter_ne : parameter ≠ 0) (parameter_nonunit : ¬ IsUnit parameter)
    (depth rank : ℕ) :
    ∃ translations : AddSubgroup Base, ∃ _ : Fintype translations,
      Fintype.card translations = Fintype.card Constants ^ rank ∧
        ∀ element : translations, (element : Base) ∈ Ideal.span {parameter ^ depth} := by
  classical
  have evaluation_injective :
      Function.Injective (aeval parameter : Constants[X] →ₐ[Constants] Base) := by
    apply transcendental_iff_injective.mp
    intro algebraic
    exact parameter_nonunit (algebraic.isIntegral.isUnit parameter_ne)
  let embedding : degreeLT Constants rank →+ Base :=
    { toFun := fun polynomial => parameter ^ depth * aeval parameter (polynomial : Constants[X])
      map_zero' := by simp
      map_add' := by intros; simp [mul_add] }
  have embedding_injective : Function.Injective embedding := by
    intro first second equation
    apply Subtype.ext
    apply evaluation_injective
    exact mul_left_cancel₀ (pow_ne_zero depth parameter_ne) equation
  let translations := embedding.range
  let equivalence : degreeLT Constants rank ≃ translations :=
    Equiv.ofInjective embedding embedding_injective
  let _ : Fintype (degreeLT Constants rank) :=
    Fintype.ofEquiv (Fin rank → Constants) (degreeLTEquiv Constants rank).symm.toEquiv
  let _ : Fintype translations := Fintype.ofEquiv _ equivalence
  refine ⟨translations, inferInstance, ?_, ?_⟩
  · calc
      Fintype.card translations = Fintype.card (degreeLT Constants rank) :=
        Fintype.card_congr equivalence.symm
      _ = Fintype.card (Fin rank → Constants) :=
        Fintype.card_congr (degreeLTEquiv Constants rank).toEquiv
      _ = Fintype.card Constants ^ rank := by simp
  · intro element
    obtain ⟨polynomial, equation⟩ := element.property
    rw [← equation]
    exact Ideal.mem_span_singleton.mpr ⟨aeval parameter (polynomial : Constants[X]), rfl⟩


private theorem orbitPolynomial_sub_C_map_adjoinRoot_isGalois {Base Fraction : Type*}
    [CommRing Base] [IsDomain Base] [Field Fraction] [Algebra Base Fraction]
    (base_injective : Function.Injective (algebraMap Base Fraction))
    (translations : AddSubgroup Base) [Fintype translations] (constant : Base)
    [Fact (Irreducible
      ((orbitPolynomial translations - C constant).map (algebraMap Base Fraction)))] :
    IsGalois Fraction
      (AdjoinRoot
        ((orbitPolynomial translations - C constant).map (algebraMap Base Fraction))) := by
  classical
  let polynomial := (orbitPolynomial translations - C constant).map (algebraMap Base Fraction)
  let extension := AdjoinRoot polynomial
  let embedding : Base →+* extension :=
    (algebraMap Fraction extension).comp (algebraMap Base Fraction)
  have embedding_injective : Function.Injective embedding :=
    (algebraMap Fraction extension).injective.comp base_injective
  have root_equation : (orbitPolynomial translations).eval₂ embedding
      (AdjoinRoot.root polynomial) = embedding constant := by
    have equation := AdjoinRoot.eval₂_root polynomial
    change ((orbitPolynomial translations - C constant).map
      (algebraMap Base Fraction)).eval₂ _ _ = 0
      at equation
    rw [eval₂_map, eval₂_sub, eval₂_C] at equation
    exact sub_eq_zero.mp equation
  have factorization : polynomial.map (algebraMap Fraction extension) =
      ∏ element : translations, (X - C (AdjoinRoot.root polynomial + embedding element)) := by
    simpa only [polynomial, Polynomial.map_map] using
      orbitPolynomial_sub_C_factorization embedding embedding_injective translations constant
        (AdjoinRoot.root polynomial) root_equation
  have separable : polynomial.Separable := by
    apply (separable_map (algebraMap Fraction extension)).mp
    rw [factorization, separable_prod_X_sub_C_iff]
    exact injective_add_embedding embedding embedding_injective _ _
  exact isGalois_adjoinRoot_of_splits_separable polynomial
    (by rw [factorization]; exact Splits.prod (fun _ _ => Splits.X_sub_C _)) separable

/-- A Galois extension of prime degree `p` in characteristic `p` is Artin--Schreier: it is
generated by an element `z` with `z ^ p - z` in the base field (Tag 09DY). -/
private theorem exists_artinSchreier_generator_of_finrank_eq_prime
    (L M : Type*) [Field L] [Field M] [Algebra L M]
    (p : ℕ) (hp : p.Prime) [CharP L p] [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p) :
    ∃ z : M, Algebra.adjoin L {z} = ⊤ ∧ z ^ p - z ∈ (algebraMap L M).range := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb, hab⟩ :=
    IsGalois.exists_artinSchreier_of_finrank_eq_char (F := L) (K := M) hdegree
  refine ⟨b, ?_, hab⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (IsAlgebraic.of_finite L b), hb]
  exact IntermediateField.top_toSubalgebra

/-- Under the hypotheses of Tag 09F1, the extension `M / L` is generated by a root `z` of
`X ^ p - X - ξ` for some `ξ ∈ L`, in the form used by Tag 09F0. -/
theorem exists_artinSchreier_presentation_of_charP
    (K L M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M]
    (p : ℕ) (hp : p.Prime) [CharP K p] [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p) :
    ∃ (ξ : L) (z : M), z ^ p - z = algebraMap L M ξ ∧ Algebra.adjoin L {z} = ⊤ := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  obtain ⟨z, hgen, ξ, hξ⟩ := exists_artinSchreier_generator_of_finrank_eq_prime L M p hp hdegree
  exact ⟨ξ, z, hξ.symm, hgen⟩

open IsLocalRing in
/-- The trivial extension `K / K` is totally ramified with respect to `A`. -/
private theorem isTotallyRamified_self (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Stacks.KummerExtension.IsTotallyRamified A K K := by
  set S := integralClosure A K
  let e : S ≃ₐ[A] A := IsIntegralClosure.equiv A S K A
  have hsurj : Function.Surjective (algebraMap A S) := fun s =>
    ⟨e s, by simpa using (e.symm.commutes (e s)).symm.trans (by simp)⟩
  have : IsLocalRing S := e.symm.toRingEquiv.isLocalRing
  have hover : (maximalIdeal S).LiesOver (maximalIdeal A) :=
    ⟨((isMaximal_iff A).mp
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (maximalIdeal S))).symm⟩
  refine ⟨maximalIdeal S, inferInstance, hover, fun m' hm' _ => eq_maximalIdeal hm', ?_⟩
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field _
  let := Ideal.Quotient.algebraOfLiesOver (maximalIdeal S) (maximalIdeal A)
  let : Module.Free (A ⧸ maximalIdeal A) (S ⧸ maximalIdeal S) :=
    Module.Free.of_divisionRing _ _
  have hq : Function.Surjective (algebraMap (A ⧸ maximalIdeal A) (S ⧸ maximalIdeal S)) := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hsurj s
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hone : Module.finrank (A ⧸ maximalIdeal A) (S ⧸ maximalIdeal S) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨RingHom.injective (algebraMap (A ⧸ maximalIdeal A) (S ⧸ maximalIdeal S)), hq⟩
  simpa using hone


/-- In a Dedekind domain, if the extension of `p` lies in `P ^ n` for a nonzero prime `P`, then
the ramification index of `P` over `p` is at least `n`. -/
private theorem le_ramificationIdx'_of_map_le_pow {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] {p : Ideal R} {P : Ideal S} [hP : P.IsPrime]
    (hp0 : Ideal.map (algebraMap R S) p ≠ ⊥) (hP0 : P ≠ ⊥) {n : ℕ}
    (hle : Ideal.map (algebraMap R S) p ≤ P ^ n) : n ≤ Ideal.ramificationIdx' p P := by
  classical
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0,
    Multiset.le_count_iff_replicate_le]
  have hdvd : P ^ n ∣ Ideal.map (algebraMap R S) p := Ideal.dvd_iff_le.mpr hle
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
    (pow_ne_zero _ hP0) hp0, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hPirr, normalize_eq,
    Multiset.nsmul_singleton] at hdvd
  exact hdvd

/-- A finite separable extension `L / K` is totally ramified with respect to `A` as soon as the
maximal ideal of `A` extends into `P ^ [L : K]` for some maximal ideal `P` of the integral
closure: the fundamental identity `∑ e f = [L : K]` then leaves room for no other prime and for
no residue extension.

Not `private`: this is the general criterion behind every total-ramification claim in the
development that goes through an ideal computation, and the Eisenstein extensions of
`StacksFrontier/RingTheory/DiscreteValuationRing/Kummer/Eisenstein.lean` need it too. Within this
file it has one call site.

Two things about the hypotheses are worth recording, because a reader comparing this with
`Kummer.lean` will notice them. First, `Algebra.IsSeparable K L` is **not** needed for the
conclusion: `Stacks.KummerExtension.isTotallyRamified_K1` reaches total ramification with no
  separability
hypothesis at all, by the same fundamental identity, and its docstring says so explicitly. The
hypothesis here is an artifact of the route this proof takes and could be removed. Second, `P` is
an input rather than produced, so a caller must already know a maximal ideal of the integral
closure; when the integral closure is a discrete valuation ring the maximal ideal is the only
choice. -/
theorem isTotallyRamified_of_map_le_pow_finrank
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (hle : Ideal.map (algebraMap A (integralClosure A L)) (IsLocalRing.maximalIdeal A) ≤
      P ^ Module.finrank K L) :
    Stacks.KummerExtension.IsTotallyRamified A K L := by
  classical
  let B := integralClosure A L
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let _ : Module.Finite A B := IsIntegralClosure.finite A K L B
  let _ : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have hinj : Function.Injective (algebraMap A B) := by
    intro x y h
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa [IsScalarTower.algebraMap_apply A K L] using congrArg Subtype.val h
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hpne : mA ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hmapne : Ideal.map (algebraMap A B) mA ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hpne
  have hd : 0 < Module.finrank K L := Module.finrank_pos
  have hP0 : P ≠ ⊥ := fun h => hmapne (le_bot_iff.mp (by
    simpa [h, Ideal.bot_pow hd.ne'] using hle))
  have hlies : P.LiesOver mA := ⟨((IsLocalRing.isMaximal_iff A).mp
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P)).symm⟩
  have heP : Module.finrank K L ≤ Ideal.ramificationIdx' mA P :=
    le_ramificationIdx'_of_map_le_pow hmapne hP0 hle
  have heP' : Module.finrank K L ≤ P.ramificationIdx A := by
    rwa [Ideal.ramificationIdx'_eq_ramificationIdx mA P hpne] at heP
  obtain ⟨-, -, -, -, n, ms, hmsmax, hmsiff, -, -, hsum, -, -⟩ :=
    integralClosure_finite_dedekind_and_degree_eq_sum_ramification_inertia A K L
  have hepos : ∀ i, 0 < (ms i).ramificationIdx A := fun i => by
    let : (ms i).IsPrime := (hmsmax i).isPrime
    exact (ms i).ramificationIdx_pos A
  have hfpos : ∀ i, 0 < (ms i).inertiaDeg A := fun i => by
    let : (ms i).IsPrime := (hmsmax i).isPrime
    exact (ms i).inertiaDeg_pos A
  obtain ⟨i₀, hi₀, -⟩ := (hmsiff P).mp ‹P.IsMaximal›
  have hfP : 0 < P.inertiaDeg A := hi₀ ▸ hfpos i₀
  have hsplit : (∑ i ∈ Finset.univ.erase i₀,
        (ms i).ramificationIdx A * (ms i).inertiaDeg A) +
        (ms i₀).ramificationIdx A * (ms i₀).inertiaDeg A =
      ∑ i, (ms i).ramificationIdx A * (ms i).inertiaDeg A :=
    Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i₀)
  have hPterm : Module.finrank K L ≤
      (ms i₀).ramificationIdx A * (ms i₀).inertiaDeg A := by
    rw [hi₀]
    exact (Nat.le_mul_of_pos_right _ hfP).trans (Nat.mul_le_mul_right _ heP')
  have hrest : ∑ i ∈ Finset.univ.erase i₀,
      (ms i).ramificationIdx A * (ms i).inertiaDeg A = 0 := by omega
  have hef : P.ramificationIdx A * P.inertiaDeg A = Module.finrank K L := by
    rw [← hi₀]
    omega
  have hf1 : P.inertiaDeg A = 1 := by
    have h1 : Module.finrank K L * P.inertiaDeg A ≤
        P.ramificationIdx A * P.inertiaDeg A := Nat.mul_le_mul_right _ heP'
    have h2 : Module.finrank K L * P.inertiaDeg A ≤ Module.finrank K L * 1 := by
      rw [mul_one]
      exact h1.trans_eq hef
    have h3 := Nat.le_of_mul_le_mul_left h2 hd
    omega
  refine ⟨P, inferInstance, hlies, fun Q hQ hQlies => ?_, ?_⟩
  · by_contra hne
    obtain ⟨j, hj, -⟩ := (hmsiff Q).mp hQ
    have hjne : j ≠ i₀ := fun h => hne (by rw [← hj, h, hi₀])
    have hz := (Finset.sum_eq_zero_iff.mp hrest) j
      (Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ j⟩)
    rcases Nat.mul_eq_zero.mp hz with h | h
    · exact absurd h (hepos j).ne'
    · exact absurd h (hfpos j).ne'
  · rw [Ideal.inertiaDeg_eq_of_isMaximal mA P] at hf1
    simpa using hf1

end IsDiscreteValuationRing

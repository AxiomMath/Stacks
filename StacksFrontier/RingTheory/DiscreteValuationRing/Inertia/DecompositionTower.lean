module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Inertia.InvariantRing

/-!
# The decomposition, inertia and wild inertia tower

The fixed fields, invariant rings, contracted primes, local rings, ramification indices and
residue fields of the wild inertia, inertia and decomposition groups at a maximal ideal form the
standard ramification tower (Tag 0BU6).
-/

@[expose] public section

open scoped Pointwise

namespace IsDiscreteValuationRing

section DecompositionTower

private theorem isGalois_and_exists_quotientEquiv
    (G A B C : Type*) [Group G] [Finite G]
    [Field A] [Field B] [Field C] [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] [MulSemiringAction G C] [IsGaloisGroup G A C]
    (N : Subgroup G) [N.Normal] [IsGaloisGroup N B C] :
    IsGalois A B ∧ ∃ e : Gal(B/A) ≃* G ⧸ N,
      ∀ (g : G) (x : B), algebraMap B C (e.symm (QuotientGroup.mk' N g) x) =
        g • algebraMap B C x := by
  let :=  IsGaloisGroup.mulSemiringActionOfNormal G B C N
  let :=  IsGaloisGroup.mulSemiringActionQuotient G B C N
  have := IsGaloisGroup.smulCommClassQuotient G A B C N
  have := IsGaloisGroup.quotient G A B C N
  have := IsGaloisGroup.isGalois (G ⧸ N) A B
  have := IsGaloisGroup.finiteDimensional (G ⧸ N) A B
  exact ⟨inferInstance, (IsGaloisGroup.quotientMulEquiv G Gal(B/A) A B C N).symm,
    fun g x ↦ IsGaloisGroup.algebraMap_quotientMulEquiv_smul G Gal(B/A) A B C N g x⟩

private theorem eq_of_under_eq_fixedPoints
    (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    (m : Ideal B) [m.IsPrime] (H : Subgroup G)
    (hH : H ≤ MulAction.stabilizer G m)
    (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.under (FixedPoints.subalgebra A B H) =
      m.under (FixedPoints.subalgebra A B H)) : Q = m := by
  have : Algebra.IsInvariant (FixedPoints.subalgebra A B H) B H :=
    ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (FixedPoints.subalgebra A B H) B H m Q hQ.symm
  exact hg.trans (hH g.property)

private theorem exists_isIntegralClosure_fixedPoints
    (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    (H : Subgroup Gal(L/K)) [MulSemiringAction Gal(L/K) B]
    [SMulCommClass Gal(L/K) A B] [SMulDistribClass Gal(L/K) B L] :
    ∃ j : FixedPoints.subalgebra A B H →ₐ[A] IntermediateField.fixedField H,
      (∀ b, (j b : L) = algebraMap B L b) ∧
      (let :=  j.toAlgebra
       IsIntegralClosure (FixedPoints.subalgebra A B H) A (IntermediateField.fixedField H)) := by
  let C := FixedPoints.subalgebra A B H
  let F := IntermediateField.fixedField H
  have : IsScalarTower A F L := .of_algebraMap_eq (fun _ ↦ rfl)
  let f : C →ₐ[A] L := (IsScalarTower.toAlgHom A B L).comp C.val
  let j : C →ₐ[A] F := f.codRestrict (F.toSubalgebra.restrictScalars A) (fun b ↦ by
    intro g
    change (g : Gal(L/K)) • algebraMap B L (b : B) = algebraMap B L (b : B)
    rw [← algebraMap.smul']
    exact congrArg (algebraMap B L) (b.property g))
  refine ⟨j, fun _ ↦ rfl, ?_⟩
  let :=  j.toAlgebra
  refine ⟨fun x y h ↦ Subtype.ext (IsIntegralClosure.algebraMap_injective B A L
    (congrArg (fun z : F ↦ (z : L)) h)), fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (hx.map (IsScalarTower.toAlgHom A F L))
    have hfix : b ∈ C := by
      intro g
      apply IsIntegralClosure.algebraMap_injective B A L
      rw [algebraMap.smul', hb]
      exact x.property g
    exact ⟨⟨b, hfix⟩, Subtype.ext hb⟩
  · rintro ⟨b, rfl⟩
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F L) (algebraMap F L).injective).mp
      (IsIntegralClosure.isIntegral_iff.mpr ⟨b.val, rfl⟩)

private theorem quotient_equiv_of_mulExact
    {G T : Type*} [Group G] [Group T] (P : Subgroup G) [P.Normal]
    (f : G →* T) (hex : Function.MulExact P.subtype f) (hf : Function.Surjective f) :
    Nonempty (G ⧸ P ≃* T) := by
  have hker : P = f.ker := by
    ext x
    simpa using (hex x).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

private theorem coprime_div_ringChar_factorization
    (k : Type*) [Field k] (n : ℕ) (hn : n ≠ 0) :
    Nat.Coprime (n / ringChar k ^ n.factorization (ringChar k)) (ringExpChar k) := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · rw [ringExpChar, max_eq_left hp.one_le]
    exact (Nat.coprime_ordCompl hp hn).symm
  · simp [ringExpChar, hp]

private theorem eq_of_under_eq_of_unique_liesOver
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [FaithfulSMul B C] [Algebra.IsIntegral B C]
    (m : Ideal C) (h : ∀ Q : Ideal C, Q.IsPrime → Q.under A = m.under A → Q = m)
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.under A = m.under A) : Q = m.under B := by
  obtain ⟨Q', _, hQ', hQ'Q⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    Q (⊥ : Ideal C) (by simp [← RingHom.ker_eq_comap_bot])
  change Q'.under B = Q at hQ'Q
  have : Q'.under A = m.under A := by
    rwa [← Ideal.under_under (A := A) (B := B) Q', hQ'Q]
  exact hQ'Q.symm.trans (congrArg (Ideal.under B) (h Q' hQ' this))


private theorem quotientMap_surjective_of_inertia_eq_top
    (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Fintype G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    (m : Ideal B) (hI : m.inertia G = ⊤) (hG : IsUnit (Fintype.card G : A)) :
    Function.Surjective (algebraMap (A ⧸ m.under A) (B ⧸ m)) := by
  classical
  obtain ⟨u, hu⟩ := hG
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) (∑ g : G, g • b) (fun g ↦ by
    rw [Finset.smul_sum]
    have he : (∑ i : G, (g * i) • b) = ∑ i : G, i • b :=
      Equiv.sum_comp (Equiv.mulLeft g) (fun i : G ↦ i • b)
    simpa only [mul_smul] using he)
  have hsum : Ideal.Quotient.mk m (algebraMap A B a) =
      (Fintype.card G : B ⧸ m) * Ideal.Quotient.mk m b := by
    rw [ha, map_sum]
    have hfixed (g : G) : Ideal.Quotient.mk m (g • b) = Ideal.Quotient.mk m b := by
      apply Ideal.Quotient.eq.mpr
      exact (show g ∈ m.inertia G by rw [hI]; trivial) b
    simp only [hfixed, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨Ideal.Quotient.mk (m.under A) (↑(u⁻¹) * a), ?_⟩
  change Ideal.Quotient.mk m (algebraMap A B (↑(u⁻¹) * a)) = _
  simp only [map_mul]
  rw [hsum, ← mul_assoc]
  have hu' : (Ideal.Quotient.mk m (algebraMap A B (↑(u⁻¹) : A))) *
      (Fintype.card G : B ⧸ m) = 1 := by
    simpa only [map_mul, map_one, hu, map_natCast] using
      congrArg (fun a : A ↦ Ideal.Quotient.mk m (algebraMap A B a)) (Units.inv_mul u)
  rw [hu', one_mul]

private theorem ramificationIdx_mul_inertiaDeg_of_unique_liesOver
    (A B G : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (m : Ideal B) [m.IsPrime]
    (hm : ∀ Q : Ideal B, Q.IsPrime → Q.under A = m.under A → Q = m) :
    m.ramificationIdx A * m.inertiaDeg A = Nat.card G := by
  have hsingle : (m.under A).primesOver B = {m} := by
    ext Q
    constructor
    · rintro ⟨hQ, hQm⟩
      exact Set.mem_singleton_iff.mpr (hm Q hQ hQm.over.symm)
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (m.under A) B G
  rwa [hsingle, Set.ncard_singleton, one_mul,
    Ideal.ramificationIdxIn_eq_ramificationIdx (m.under A) m G,
    Ideal.inertiaDegIn_eq_inertiaDeg (m.under A) m G] at h

private theorem finrank_eq_one_of_algebraMap_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (h : Function.Surjective (algebraMap K L)) : Module.finrank K L = 1 := by
  let e : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L) ⟨(algebraMap K L).injective, h⟩
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

private theorem ramificationIdx_eq_card_and_quotientMap_surjective
    (A B G : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    [Group G] [Fintype G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (m : Ideal B) [m.IsMaximal] (hI : m.inertia G = ⊤)
    (hG : IsUnit (Fintype.card G : A)) :
    m.ramificationIdx A = Nat.card G ∧
      Function.Surjective (algebraMap (A ⧸ m.under A) (B ⧸ m)) := by
  have hsurj := quotientMap_surjective_of_inertia_eq_top A B G m hI hG
  have hm : ∀ Q : Ideal B, Q.IsPrime → Q.under A = m.under A → Q = m := by
    intro Q hQ hQm
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G m Q hQm.symm
    exact hg.trans (Ideal.inertia_le_stabilizer m (show g ∈ m.inertia G by rw [hI]; trivial))
  have : (m.under A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  let : Field (A ⧸ m.under A) := Ideal.Quotient.field (m.under A)
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have hf : m.inertiaDeg A = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal (m.under A) m]
    exact finrank_eq_one_of_algebraMap_surjective _ _ hsurj
  refine ⟨?_, hsurj⟩
  have he := ramificationIdx_mul_inertiaDeg_of_unique_liesOver A B G m hm
  simpa only [hf, mul_one] using he

private theorem ramificationIdx_and_inertiaDeg_eq_one_of_stabilizer
    (A C B G : Type*) [CommRing A] [CommRing C] [CommRing B]
    [IsDomain A] [IsDomain C] [IsDomain B]
    [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]
    [Module.Finite A B] [Module.Flat A B] [Module.Finite C B] [Module.Flat C B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (m : Ideal B) [m.IsPrime] [IsGaloisGroup (MulAction.stabilizer G m) C B] :
    (m.under C).ramificationIdx A = 1 ∧ (m.under C).inertiaDeg A = 1 := by
  have hm : ∀ Q : Ideal B, Q.IsPrime → Q.under C = m.under C → Q = m := by
    intro Q hQ hQm
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq C B
      (MulAction.stabilizer G m) m Q hQm.symm
    exact hg.trans g.property
  have ht := ramificationIdx_mul_inertiaDeg_of_unique_liesOver C B
    (MulAction.stabilizer G m) m hm
  have hb := card_stabilizer_eq_ramificationIdx_mul_inertiaDeg A B G m
  have he := Ideal.ramificationIdx_tower (R := A) (m.under C) m
  have hf := Ideal.inertiaDeg_tower (R := A) (m.under C) m
  have hh : ((m.under C).ramificationIdx A * (m.under C).inertiaDeg A) *
      (m.ramificationIdx C * m.inertiaDeg C) =
      1 * (m.ramificationIdx C * m.inertiaDeg C) := by
    calc
      _ = m.ramificationIdx A * m.inertiaDeg A := by rw [he, hf]; ring
      _ = Nat.card (MulAction.stabilizer G m) := hb.symm
      _ = _ := by rw [one_mul, ht]
  have hc := Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (Ideal.ramificationIdx_pos m C) (Ideal.inertiaDeg_pos m C)) hh
  exact ⟨Nat.eq_one_of_mul_eq_one_right hc, Nat.eq_one_of_mul_eq_one_left hc⟩

section ResidueFields

attribute [local instance] Ideal.Quotient.field

private theorem exists_residue_quotientEquiv
    (A C B G : Type*) [CommRing A] [CommRing C] [CommRing B] [IsDomain B]
    [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]
    [FaithfulSMul C B] [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (N : Subgroup G) [N.Normal] [IsGaloisGroup N C B]
    (m : Ideal B) [m.IsMaximal] (p : Ideal A) [p.IsMaximal]
    (q : Ideal C) [q.IsMaximal] [m.LiesOver p] [m.LiesOver q] [q.LiesOver p]
    (hD : MulAction.stabilizer G m = ⊤) (hI : m.inertia G = N) :
    Normal (A ⧸ p) (C ⧸ q) ∧ ∃ e : Gal((C ⧸ q)/(A ⧸ p)) ≃* G ⧸ N,
      ∀ (g : G) (c : C),
        algebraMap (C ⧸ q) (B ⧸ m) (e.symm (QuotientGroup.mk' N g) (Ideal.Quotient.mk q c)) =
          Ideal.Quotient.mk m (g • algebraMap C B c) := by
  let := IsGaloisGroup.mulSemiringActionOfNormal G C B N
  let := IsGaloisGroup.mulSemiringActionQuotient G C B N
  have := IsGaloisGroup.smulCommClassQuotient G A C B N
  have := IsGaloisGroup.quotient G A C B N
  have hDq : MulAction.stabilizer (G ⧸ N) q = ⊤ := by
    rw [Ideal.stabilizer_quotient N q m, hD]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
  have hIq : q.inertia (G ⧸ N) = ⊥ := by
    rw [Ideal.inertia_quotient N q m, hI]
    exact (Subgroup.map_eq_bot_iff N).mpr (by simp)
  let j : (G ⧸ N) →* MulAction.stabilizer (G ⧸ N) q :=
    (MonoidHom.id _).codRestrict _ (fun g ↦ hDq.symm ▸ Subgroup.mem_top g)
  let f := (Ideal.Quotient.stabilizerHom q p (G ⧸ N)).comp j
  have hf : Function.Bijective f := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff f).mp
      apply le_antisymm _ bot_le
      intro g hg
      have h : j g ∈ q.inertia (MulAction.stabilizer (G ⧸ N) q) := by
        rw [← Ideal.Quotient.ker_stabilizerHom q p (G ⧸ N)]
        exact hg
      have h' : g ∈ q.inertia (G ⧸ N) := h
      simpa [hIq] using h'
    · intro σ
      obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective (G ⧸ N) p q σ
      exact ⟨g.val, hg⟩
  let e := MulEquiv.ofBijective f hf
  refine ⟨Ideal.Quotient.normal (G ⧸ N) p q, e.symm, ?_⟩
  intro g c
  change Ideal.Quotient.mk m (algebraMap C B ((QuotientGroup.mk' N g) • c)) = _
  change Ideal.Quotient.mk m (algebraMap C B ((g : G ⧸ N) • c)) = _
  rw [IsGaloisGroup.mulSemiringActionQuotient_smul_def G C B N, algebraMap.smul']

private theorem quotient_isSeparable_of_isUnramifiedAt
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.EssFiniteType A C] (p : Ideal A) [p.IsMaximal]
    (q : Ideal C) [q.IsMaximal] [q.LiesOver p] [Algebra.IsUnramifiedAt A q] :
    Algebra.IsSeparable (A ⧸ p) (C ⧸ q) := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  infer_instance
private theorem isUnit_natCast_of_coprime_ringExpChar
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) (hn : n ≠ 0)
    (hc : Nat.Coprime n (ringExpChar (IsLocalRing.ResidueField A))) : IsUnit (n : A) := by
  apply isUnit_of_map_unit (IsLocalRing.residue A)
  rw [map_natCast]
  rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField A)
    (ringChar (IsLocalRing.ResidueField A)) with hp | hp
  · rw [ringExpChar, max_eq_left hp.one_le] at hc
    exact (CharP.isUnit_natCast_iff hp).mpr ((hp.coprime_iff_not_dvd).mp hc.symm)
  · have : CharP (IsLocalRing.ResidueField A) 0 := hp ▸ inferInstance
    have : CharZero (IsLocalRing.ResidueField A) := CharP.charP_to_charZero _
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
end ResidueFields

private theorem isScalarTower_quotient
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [P.LiesOver p] [Q.LiesOver P] [Q.LiesOver p] :
    IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) :=
  IsScalarTower.of_algebraMap_eq' <| Ideal.Quotient.ringHom_ext <| RingHom.ext fun x ↦ by
    change Ideal.Quotient.mk Q (algebraMap R T x) =
      Ideal.Quotient.mk Q (algebraMap S T (algebraMap R S x))
    rw [IsScalarTower.algebraMap_apply R S T]

private theorem nonempty_algEquiv_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p]
    (h : Function.Surjective (algebraMap (R ⧸ P.under R) (S ⧸ P))) :
    Nonempty ((R ⧸ p) ≃ₐ[R ⧸ p] (S ⧸ P)) := by
  obtain rfl : p = P.under R := Ideal.LiesOver.over
  let := Ideal.Quotient.field (P.under R)
  let := Ideal.Quotient.field P
  exact ⟨AlgEquiv.ofBijective (Algebra.ofId _ _)
    ⟨(algebraMap (R ⧸ P.under R) (S ⧸ P)).injective, h⟩⟩

private theorem nonempty_algEquiv_of_inertiaDeg_eq_one
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] (h : P.inertiaDeg R = 1) :
    Nonempty ((R ⧸ p) ≃ₐ[R ⧸ p] (S ⧸ P)) := by
  let := Ideal.Quotient.field p
  let := Ideal.Quotient.field P
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P, Algebra.finrank_eq_one_iff_bijective_algebraMap] at h
  exact ⟨AlgEquiv.ofBijective (Algebra.ofId _ _) h⟩

private theorem isSeparable_of_nonempty_algEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] (h : Nonempty (F ≃ₐ[F] E)) :
    Algebra.IsSeparable F E :=
  AlgEquiv.Algebra.isSeparable h.some

private theorem ramificationIdx_eq_card_quotient_and_surjective
    (C E B G : Type*) [CommRing C] [CommRing E] [CommRing B] [IsDomain C] [IsDomain E]
    [IsDomain B] [Algebra C E] [Algebra C B] [Algebra E B] [IsScalarTower C E B]
    [FaithfulSMul E B] [Algebra.IsIntegral E B] [Module.Finite C E] [Module.Flat C E]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G C B]
    (N : Subgroup G) [N.Normal] [IsGaloisGroup N E B]
    (m : Ideal B) [m.IsMaximal] (hI : m.inertia G = ⊤)
    (hG : IsUnit (Nat.card (G ⧸ N) : C)) :
    (m.under E).ramificationIdx C = Nat.card (G ⧸ N) ∧
      Function.Surjective (algebraMap (C ⧸ (m.under E).under C) (E ⧸ m.under E)) := by
  classical
  let := IsGaloisGroup.mulSemiringActionOfNormal G E B N
  let := IsGaloisGroup.mulSemiringActionQuotient G E B N
  have := IsGaloisGroup.smulCommClassQuotient G C E B N
  have := IsGaloisGroup.quotient G C E B N
  let := Fintype.ofFinite (G ⧸ N)
  have : (m.under E).IsMaximal := Ideal.IsMaximal.under E m
  have hIq : (m.under E).inertia (G ⧸ N) = ⊤ := by
    rw [Ideal.inertia_quotient N (m.under E) m, hI]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
  rw [Nat.card_eq_fintype_card] at hG
  exact ramificationIdx_eq_card_and_quotientMap_surjective C E (G ⧸ N) (m.under E) hIq hG

private theorem smulCommClass_integralClosure
    (A K L B : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L]
    [IsScalarTower A K L] [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass Gal(L/K) A B := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun g a b ↦ ?_⟩
  simp only [Algebra.smul_def]
  change galRestrict A K L B g (algebraMap A B a * b) =
    algebraMap A B a * galRestrict A K L B g b
  rw [map_mul, AlgEquiv.commutes]

private theorem isGaloisGroup_subgroupOf_of_le
    {G : Type*} (A B : Type*) [Group G] [CommRing A] [CommRing B] [Algebra A B]
    [MulSemiringAction G B] {D I : Subgroup G} (hID : I ≤ D) [IsGaloisGroup I A B] :
    IsGaloisGroup (I.subgroupOf D) A B :=
  .of_mulEquiv (Subgroup.subgroupOfEquivOfLe hID) (fun _ _ ↦ rfl)

private theorem isGaloisGroup_of_map_subtype
    {G : Type*} (A B : Type*) [Group G] [CommRing A] [CommRing B] [Algebra A B]
    [MulSemiringAction G B] {I : Subgroup G} (P : Subgroup I)
    [IsGaloisGroup (P.map I.subtype) A B] : IsGaloisGroup P A B :=
  .of_mulEquiv (P.equivMapOfInjective I.subtype Subtype.val_injective) (fun _ _ ↦ rfl)

private theorem fixedPoints_isDedekindDomain_and_finite
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L] (H : Subgroup Gal(L/K)) :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B := smulCommClass_integralClosure A K L B
    IsDedekindDomain (FixedPoints.subalgebra A B H) ∧
      Module.Finite A (FixedPoints.subalgebra A B H) := by
  intro B
  let := IsIntegralClosure.MulSemiringAction A K L B
  have : SMulCommClass Gal(L/K) A B := smulCommClass_integralClosure A K L B
  obtain ⟨j, -, hc⟩ := exists_isIntegralClosure_fixedPoints A K L B H
  let := j.toAlgebra
  have := hc
  have : IsScalarTower A (FixedPoints.subalgebra A B H) (IntermediateField.fixedField H) :=
    .of_algebraMap_eq fun a ↦ (j.commutes a).symm
  have : Algebra.IsSeparable K (IntermediateField.fixedField H) :=
    Algebra.isSeparable_tower_bot_of_isSeparable K _ L
  exact ⟨IsIntegralClosure.isDedekindDomain A K (IntermediateField.fixedField H) _,
    IsIntegralClosure.finite A K (IntermediateField.fixedField H) _⟩

set_option maxHeartbeats 3200000 in
-- The tower carries many dependent algebra structures.
private theorem exists_wildInertia_fixedField_tower
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B := smulCommClass_integralClosure A K L B
    let D := MulAction.stabilizer Gal(L/K) m
    let I := m.inertia Gal(L/K)
    let hID : I ≤ D := Ideal.inertia_le_stabilizer (M := Gal(L/K)) m
    let iID : I →* D := I.subtype.codRestrict D (fun σ ↦ hID σ.property)
    ∃ (P : Subgroup I) (hP : P.Normal),
      let PG : Subgroup Gal(L/K) := P.map I.subtype
      let PD : Subgroup D := P.map iID
      (∀ σ : D, σ ∈ PD ↔ (σ : Gal(L/K)) ∈ I ∧
        ∀ b : B, b ∈ m → (σ : Gal(L/K)) • b - b ∈ m ^ 2) ∧
      let ID : Subgroup D := I.subgroupOf D
      let LD := IntermediateField.fixedField D
      let LI := IntermediateField.fixedField I
      let LP := IntermediateField.fixedField PG
      let BD := FixedPoints.subalgebra A B D
      let BI := FixedPoints.subalgebra A B I
      let BP := FixedPoints.subalgebra A B PG
      let hPGI : PG ≤ I := fun σ hσ ↦ by
        obtain ⟨τ, -, rfl⟩ := hσ
        exact τ.property
      let BD_BI : BD →ₐ[A] BI :=
    Subalgebra.inclusion <| fun b hb σ ↦ hb ⟨σ, hID σ.property⟩
      let BI_BP : BI →ₐ[A] BP := Subalgebra.inclusion <| fun b hb σ ↦
        hb ⟨σ, hPGI σ.property⟩
      let BD_BP : BD →ₐ[A] BP := BI_BP.comp BD_BI
      letI := BD_BI.toAlgebra
      letI := BI_BP.toAlgebra
      letI := BD_BP.toAlgebra
      letI : IsScalarTower BD BI BP := .of_algebraMap_eq (fun _ ↦ rfl)
      letI : IsScalarTower BD BI B := .of_algebraMap_eq (fun _ ↦ rfl)
      letI : IsScalarTower BI BP B := .of_algebraMap_eq (fun _ ↦ rfl)
      letI : IsScalarTower BD BP B := .of_algebraMap_eq (fun _ ↦ rfl)
      let mD := m.under BD
      let mI := m.under BI
      let mP := m.under BP
      let LD_LI : LD →ₐ[K] LI := IntermediateField.inclusion
        (IntermediateField.fixedField_le hID)
      let LI_LP : LI →ₐ[K] LP := IntermediateField.inclusion
        (IntermediateField.fixedField_le hPGI)
      let LD_LP : LD →ₐ[K] LP := LI_LP.comp LD_LI
      letI := LD_LI.toAlgebra
      letI := LI_LP.toAlgebra
      letI := LD_LP.toAlgebra
      letI : mI.LiesOver mD := ⟨by
        change m.under BD = (m.under BI).under BD
        symm
        exact Ideal.under_under (A := BD) (B := BI) m⟩
      letI : mP.LiesOver mI := ⟨by
        change m.under BI = (m.under BP).under BI
        symm
        exact Ideal.under_under (A := BI) (B := BP) m⟩
      letI : mP.LiesOver mD := ⟨by
        change m.under BD = (m.under BP).under BD
        symm
        exact Ideal.under_under (A := BD) (B := BP) m⟩
      letI := Localization.AtPrime.algebraOfLiesOver mD mI
      ∃ (hIDn : ID.Normal) (hPDn : PD.Normal),
      letI := hIDn
      letI := hPDn
      ∃ (jD : BD →ₐ[A] LD) (jI : BI →ₐ[A] LI) (jP : BP →ₐ[A] LP),
      let BD_LI : BD →ₐ[A] LI := jI.comp BD_BI
      let BI_LP : BI →ₐ[A] LP := jP.comp BI_BP
      let BD_LP : BD →ₐ[A] LP := jP.comp BD_BP
      letI := jD.toAlgebra
      letI := jI.toAlgebra
      letI := jP.toAlgebra
      letI := BD_LI.toAlgebra
      letI := BI_LP.toAlgebra
      letI := BD_LP.toAlgebra
      (∀ b : BD, ((jD b : LD) : L) = ((b : B) : L)) ∧
      (∀ b : BI, ((jI b : LI) : L) = ((b : B) : L)) ∧
      (∀ b : BP, ((jP b : LP) : L) = ((b : B) : L)) ∧
      IsIntegralClosure BD A LD ∧
      IsIntegralClosure BI A LI ∧
      IsIntegralClosure BP A LP ∧
      IsIntegralClosure BI BD LI ∧
      IsIntegralClosure BP BI LP ∧
      IsIntegralClosure BP BD LP ∧
      (0 < ringChar (IsLocalRing.ResidueField A) →
        IsPGroup (ringChar (IsLocalRing.ResidueField A)) P) ∧
      (ringChar (IsLocalRing.ResidueField A) = 0 → P = ⊥) ∧
      IsCyclic (I ⧸ P) ∧
      Nat.Coprime (Nat.card (I ⧸ P)) (ringExpChar (IsLocalRing.ResidueField A)) ∧
      IsGalois LD LI ∧
      (∃ eDI : Gal(LI/LD) ≃* D ⧸ ID,
        ∀ (σ : D) (x : LI),
          ((eDI.symm (QuotientGroup.mk' ID σ)) x : L) = (σ : Gal(L/K)) (x : L)) ∧
      IsGalois LI LP ∧
      (∃ eIP : Gal(LP/LI) ≃* I ⧸ P,
        ∀ (σ : I) (x : LP),
          ((eIP.symm (QuotientGroup.mk' P σ)) x : L) = (σ : Gal(L/K)) (x : L)) ∧
      IsGalois LD LP ∧
      (∃ eDP : Gal(LP/LD) ≃* D ⧸ PD,
        ∀ (σ : D) (x : LP),
          ((eDP.symm (QuotientGroup.mk' PD σ)) x : L) = (σ : Gal(L/K)) (x : L)) := by
  classical
  let B := integralClosure A L
  let := IsIntegralClosure.MulSemiringAction A K L B
  have : SMulCommClass Gal(L/K) A B := smulCommClass_integralClosure A K L B
  let D := MulAction.stabilizer Gal(L/K) m
  let I := m.inertia Gal(L/K)
  have hID : I ≤ D := Ideal.inertia_le_stabilizer m
  let iID : I →* D := I.subtype.codRestrict D (fun σ ↦ hID σ.property)
  obtain ⟨P, hP, hPDn, hPi, hchar, hpgroup, hpzero, _, θ, _, hex, hθ, hcyc, hcard, _⟩ :=
    exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity A K L m
  have := hP
  let PG := P.map I.subtype
  let PD := P.map iID
  let ID := I.subgroupOf D
  have hIDn : ID.Normal := inferInstanceAs (m.inertia D).Normal
  let LD := IntermediateField.fixedField D
  let LI := IntermediateField.fixedField I
  let LP := IntermediateField.fixedField PG
  let BD := FixedPoints.subalgebra A B D
  let BI := FixedPoints.subalgebra A B I
  let BP := FixedPoints.subalgebra A B PG
  have hPGI : PG ≤ I := by
    rintro σ ⟨τ, _, rfl⟩
    exact τ.property
  let BD_BI : BD →ₐ[A] BI :=
    Subalgebra.inclusion <| fun b hb σ ↦ hb ⟨σ, hID σ.property⟩
  let BI_BP : BI →ₐ[A] BP :=
    Subalgebra.inclusion <| fun b hb σ ↦ hb ⟨σ, hPGI σ.property⟩
  let BD_BP : BD →ₐ[A] BP := BI_BP.comp BD_BI
  let := BD_BI.toAlgebra
  let := BI_BP.toAlgebra
  let := BD_BP.toAlgebra
  have : IsScalarTower BD BI BP := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower BD BI B := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower BI BP B := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower BD BP B := .of_algebraMap_eq (fun _ ↦ rfl)
  let mD := m.under BD
  let mI := m.under BI
  let mP := m.under BP
  let LD_LI : LD →ₐ[K] LI := IntermediateField.inclusion (IntermediateField.fixedField_le hID)
  let LI_LP : LI →ₐ[K] LP := IntermediateField.inclusion (IntermediateField.fixedField_le hPGI)
  let LD_LP : LD →ₐ[K] LP := LI_LP.comp LD_LI
  let := LD_LI.toAlgebra
  let := LI_LP.toAlgebra
  let := LD_LP.toAlgebra
  have : IsScalarTower LD LI L := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower LI LP L := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower LD LP L := .of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨jD, hjD, hcD⟩ := exists_isIntegralClosure_fixedPoints A K L B D
  obtain ⟨jI, hjI, hcI⟩ := exists_isIntegralClosure_fixedPoints A K L B I
  obtain ⟨jP, hjP, hcP⟩ := exists_isIntegralClosure_fixedPoints A K L B PG
  have : IsGaloisGroup D LD L := IsGaloisGroup.subgroup Gal(L/K) K L D
  have : IsGaloisGroup I LI L := IsGaloisGroup.subgroup Gal(L/K) K L I
  have : IsGaloisGroup PG LP L := IsGaloisGroup.subgroup Gal(L/K) K L PG
  have : IsGaloisGroup ID LI L := isGaloisGroup_subgroupOf_of_le LI L hID
  have : IsGaloisGroup P LP L := isGaloisGroup_of_map_subtype LP L P
  have hiinj : Function.Injective iID := fun _ _ h ↦
    Subtype.ext (congrArg (fun x : D ↦ (x : Gal(L/K))) h)
  have : IsGaloisGroup PD LP L :=
    .of_mulEquiv (P.equivMapOfInjective iID hiinj).symm (fun g x ↦ by
      have h := congrArg (fun y : PD ↦ ((y : D) : Gal(L/K)))
        ((P.equivMapOfInjective iID hiinj).apply_symm_apply g)
      change (((P.equivMapOfInjective iID hiinj).symm g : I) : Gal(L/K)) x = _
      exact congrArg (fun f : Gal(L/K) ↦ f x) h)
  have := hIDn
  have := hPDn
  have hgDI := isGalois_and_exists_quotientEquiv D LD LI L ID
  have hgIP := isGalois_and_exists_quotientEquiv I LI LP L P
  have hgDP := isGalois_and_exists_quotientEquiv D LD LP L PD
  have : Module.Finite A B :=
    (integralClosure_finite_dedekind_and_degree_eq_sum_ramification_inertia A K L).1
  obtain ⟨e⟩ := quotient_equiv_of_mulExact P θ hex hθ
  have := hcyc
  have hcyclic : IsCyclic (I ⧸ P) := isCyclic_of_injective e.toMonoidHom e.injective
  have hcoprime : Nat.Coprime (Nat.card (I ⧸ P))
      (ringExpChar (IsLocalRing.ResidueField A)) := by
    rw [Nat.card_congr e.toEquiv, hcard]
    exact coprime_div_ringChar_factorization _ _ (Ideal.ramificationIdx_pos m A).ne'
  let BD_LI : BD →ₐ[A] LI := jI.comp BD_BI
  let BI_LP : BI →ₐ[A] LP := jP.comp BI_BP
  let BD_LP : BD →ₐ[A] LP := jP.comp BD_BP
  let := jD.toAlgebra
  let := jI.toAlgebra
  let := jP.toAlgebra
  let := BD_LI.toAlgebra
  let := BI_LP.toAlgebra
  let := BD_LP.toAlgebra
  have := hcD
  have := hcI
  have := hcP
  have : Algebra.IsIntegral A BD := ⟨fun b ↦
    (isIntegral_algHom_iff BD.val Subtype.val_injective).mp
      (IsIntegralClosure.isIntegral A L (b : B))⟩
  have : Algebra.IsIntegral A BI := ⟨fun b ↦
    (isIntegral_algHom_iff BI.val Subtype.val_injective).mp
      (IsIntegralClosure.isIntegral A L (b : B))⟩
  have hcIBD : IsIntegralClosure BI BD LI := IsIntegralClosure.tower_top (R := A)
  have hcPBI : IsIntegralClosure BP BI LP := IsIntegralClosure.tower_top (R := A)
  have hcPBD : IsIntegralClosure BP BD LP := IsIntegralClosure.tower_top (R := A)
  exact ⟨P, hP, hchar, hIDn, hPDn, jD, jI, jP, hjD, hjI, hjP, hcD, hcI, hcP,
    hcIBD, hcPBI, hcPBD, hpgroup, hpzero, hcyclic, hcoprime,
    hgDI.1, hgDI.2, hgIP.1, hgIP.2, hgDP.1, hgDP.2⟩
end DecompositionTower

set_option maxHeartbeats 3200000 in
-- The tower carries many dependent algebra structures.
/-- **Stacks Tag 0BU6.** The fixed fields, invariant rings, contracted primes, localized
rings, and residue fields attached to the wild inertia, inertia, and decomposition groups of
a maximal ideal in a finite Galois extension form the standard ramification tower. -/
@[stacks 0BU6]
theorem decomposition_inertia_wildInertia_tower
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B :=
      ⟨fun g a b ↦ by
        simp only [Algebra.smul_def]
        change galRestrict A K L B g (algebraMap A B a * b) =
          algebraMap A B a * galRestrict A K L B g b
        rw [map_mul, AlgEquiv.commutes]⟩
    let D := MulAction.stabilizer Gal(L/K) m
    let I := m.inertia Gal(L/K)
    let hID : I ≤ D := Ideal.inertia_le_stabilizer (M := Gal(L/K)) m
    let iID : I →* D := I.subtype.codRestrict D (fun σ ↦ hID σ.property)
    ∃ (P : Subgroup I) (hP : P.Normal),
      let PG : Subgroup Gal(L/K) := P.map I.subtype
      let PD : Subgroup D := P.map iID
      (∀ σ : D, σ ∈ PD ↔ (σ : Gal(L/K)) ∈ I ∧
        ∀ b : B, b ∈ m → (σ : Gal(L/K)) • b - b ∈ m ^ 2) ∧
      let ID : Subgroup D := I.subgroupOf D
      let LD := IntermediateField.fixedField D
      let LI := IntermediateField.fixedField I
      let LP := IntermediateField.fixedField PG
      let BD := FixedPoints.subalgebra A B D
      let BI := FixedPoints.subalgebra A B I
      let BP := FixedPoints.subalgebra A B PG
      let hPGI : PG ≤ I := fun σ hσ ↦ by
        obtain ⟨τ, -, rfl⟩ := hσ
        exact τ.property
      let BD_BI : BD →ₐ[A] BI := Subalgebra.inclusion <| fun b hb σ ↦ hb ⟨σ, hID σ.property⟩
      let BI_BP : BI →ₐ[A] BP := Subalgebra.inclusion <| fun b hb σ ↦
        hb ⟨σ, hPGI σ.property⟩
      let BD_BP : BD →ₐ[A] BP := BI_BP.comp BD_BI
      letI := BD_BI.toAlgebra
      letI := BI_BP.toAlgebra
      letI := BD_BP.toAlgebra
      letI : IsScalarTower BD BI BP := .of_algebraMap_eq (fun _ ↦ rfl)
      letI : IsScalarTower BD BI B := .of_algebraMap_eq (fun _ ↦ rfl)
      letI : IsScalarTower BI BP B := .of_algebraMap_eq (fun _ ↦ rfl)
      letI : IsScalarTower BD BP B := .of_algebraMap_eq (fun _ ↦ rfl)
      let mD := m.under BD
      let mI := m.under BI
      let mP := m.under BP
      let LD_LI : LD →ₐ[K] LI := IntermediateField.inclusion
        (IntermediateField.fixedField_le hID)
      let LI_LP : LI →ₐ[K] LP := IntermediateField.inclusion
        (IntermediateField.fixedField_le hPGI)
      let LD_LP : LD →ₐ[K] LP := LI_LP.comp LD_LI
      letI := LD_LI.toAlgebra
      letI := LI_LP.toAlgebra
      letI := LD_LP.toAlgebra
      letI : mI.LiesOver mD := ⟨by
        change m.under BD = (m.under BI).under BD
        symm
        exact Ideal.under_under (A := BD) (B := BI) m⟩
      letI : mP.LiesOver mI := ⟨by
        change m.under BI = (m.under BP).under BI
        symm
        exact Ideal.under_under (A := BI) (B := BP) m⟩
      letI : mP.LiesOver mD := ⟨by
        change m.under BD = (m.under BP).under BD
        symm
        exact Ideal.under_under (A := BD) (B := BP) m⟩
      letI := Localization.AtPrime.algebraOfLiesOver mD mI
      ∃ (hIDn : ID.Normal) (hPDn : PD.Normal),
      letI := hIDn
      letI := hPDn
      ∃ (jD : BD →ₐ[A] LD) (jI : BI →ₐ[A] LI) (jP : BP →ₐ[A] LP),
      let BD_LI : BD →ₐ[A] LI := jI.comp BD_BI
      let BI_LP : BI →ₐ[A] LP := jP.comp BI_BP
      let BD_LP : BD →ₐ[A] LP := jP.comp BD_BP
      letI := jD.toAlgebra
      letI := jI.toAlgebra
      letI := jP.toAlgebra
      letI := BD_LI.toAlgebra
      letI := BI_LP.toAlgebra
      letI := BD_LP.toAlgebra
      (∀ b : BD, ((jD b : LD) : L) = ((b : B) : L)) ∧
      (∀ b : BI, ((jI b : LI) : L) = ((b : B) : L)) ∧
      (∀ b : BP, ((jP b : LP) : L) = ((b : B) : L)) ∧
      IsIntegralClosure BD A LD ∧
      IsIntegralClosure BI A LI ∧
      IsIntegralClosure BP A LP ∧
      IsIntegralClosure BI BD LI ∧
      IsIntegralClosure BP BI LP ∧
      IsIntegralClosure BP BD LP ∧
      (0 < ringChar (IsLocalRing.ResidueField A) →
        IsPGroup (ringChar (IsLocalRing.ResidueField A)) P) ∧
      (ringChar (IsLocalRing.ResidueField A) = 0 → P = ⊥) ∧
      IsCyclic (I ⧸ P) ∧
      Nat.Coprime (Nat.card (I ⧸ P)) (ringExpChar (IsLocalRing.ResidueField A)) ∧
      IsGalois LD LI ∧
      (∃ eDI : Gal(LI/LD) ≃* D ⧸ ID,
        ∀ (σ : D) (x : LI),
          ((eDI.symm (QuotientGroup.mk' ID σ)) x : L) = (σ : Gal(L/K)) (x : L)) ∧
      IsGalois LI LP ∧
      (∃ eIP : Gal(LP/LI) ≃* I ⧸ P,
        ∀ (σ : I) (x : LP),
          ((eIP.symm (QuotientGroup.mk' P σ)) x : L) = (σ : Gal(L/K)) (x : L)) ∧
      IsGalois LD LP ∧
      (∃ eDP : Gal(LP/LD) ≃* D ⧸ PD,
        ∀ (σ : D) (x : LP),
          ((eDP.symm (QuotientGroup.mk' PD σ)) x : L) = (σ : Gal(L/K)) (x : L)) ∧
      (∀ Q : Ideal BI, Q.IsPrime → Q.under BD = mD → Q = mI) ∧
      (∀ Q : Ideal BP, Q.IsPrime → Q.under BI = mI → Q = mP) ∧
      (∀ Q : Ideal B, Q.IsPrime → Q.under BP = mP → Q = m) ∧
      (∀ Q : Ideal BP, Q.IsPrime → Q.under BD = mD → Q = mP) ∧
      (∀ Q : Ideal B, Q.IsPrime → Q.under BI = mI → Q = m) ∧
      (∀ Q : Ideal B, Q.IsPrime → Q.under BD = mD → Q = m) ∧
      (mD.under A).IsMaximal ∧ mD.IsMaximal ∧ mI.IsMaximal ∧ mP.IsMaximal ∧
      Algebra.Etale A (Localization.AtPrime mD) ∧
      Algebra.Etale (Localization.AtPrime mD) (Localization.AtPrime mI) ∧
      Algebra.Etale A (Localization.AtPrime mI) ∧
      (∀ (hmA : (mD.under A).IsMaximal) (hmD : mD.IsMaximal)
          (hmI : mI.IsMaximal) (hmP : mP.IsMaximal),
        letI : (mD.under A).IsMaximal := hmA
        letI : mD.IsMaximal := hmD
        letI : mI.IsMaximal := hmI
        letI : mP.IsMaximal := hmP
        letI : Field (A ⧸ mD.under A) := Ideal.Quotient.field (mD.under A)
        letI : Field (BD ⧸ mD) := Ideal.Quotient.field mD
        letI : Field (BI ⧸ mI) := Ideal.Quotient.field mI
        letI : Field (BP ⧸ mP) := Ideal.Quotient.field mP
        let qI : BI ⧸ mI →+* B ⧸ m :=
          Ideal.quotientMap m (Subalgebra.val BI).toRingHom (fun _ hx ↦ hx)
        Nonempty ((A ⧸ mD.under A) ≃ₐ[A ⧸ mD.under A] (BD ⧸ mD)) ∧
        IsGalois (BD ⧸ mD) (BI ⧸ mI) ∧
        (∃ eRes : Gal((BI ⧸ mI)/(BD ⧸ mD)) ≃* D ⧸ ID,
          ∀ (σ : D) (b : BI),
            qI (eRes.symm (QuotientGroup.mk' ID σ) (Ideal.Quotient.mk mI b)) =
              Ideal.Quotient.mk m ((σ : Gal(L/K)) • (b : B))) ∧
        Nonempty ((BI ⧸ mI) ≃ₐ[BI ⧸ mI] (BP ⧸ mP)) ∧
        Algebra.IsSeparable (BD ⧸ mD) (BP ⧸ mP) ∧
        Algebra.IsSeparable (A ⧸ mD.under A) (BP ⧸ mP)) ∧
      mP.ramificationIdx BI = Nat.card (I ⧸ P) ∧
      Nat.Coprime (mP.ramificationIdx BI)
        (ringExpChar (IsLocalRing.ResidueField A)) ∧
      mP.ramificationIdx BD = Nat.card (I ⧸ P) ∧
      Nat.Coprime (mP.ramificationIdx BD)
        (ringExpChar (IsLocalRing.ResidueField A)) ∧
      mP.ramificationIdx A = Nat.card (I ⧸ P) ∧
      Nat.Coprime (mP.ramificationIdx A)
        (ringExpChar (IsLocalRing.ResidueField A)) := by
  intro B D I hID iID
  obtain ⟨P, hP, hcrit, hrest⟩ := exists_wildInertia_fixedField_tower A K L m
  refine ⟨P, hP, ?_⟩
  intro PG PD
  refine ⟨hcrit, ?_⟩
  intro ID LD LI LP BD BI BP hPGI BD_BI BI_BP BD_BP mD mI mP LD_LI LI_LP
    LD_LP
  obtain ⟨hIDn, hPDn, jD, jI, jP, hjD, hjI, hjP, hcD, hcI, hcP, hcIBD, hcPBI,
    hcPBD, hpg, hpz, hcyc, hcop, g1, e1, g2, e2, g3, e3⟩ := hrest
  refine ⟨hIDn, hPDn, jD, jI, jP, ?_⟩
  intro BD_LI BI_LP BD_LP
  refine ⟨hjD, hjI, hjP, hcD, hcI, hcP, hcIBD, hcPBI,
    hcPBD, hpg, hpz, hcyc, hcop, g1, e1, g2, e2, g3, e3, ?_⟩
  classical
  let := IsIntegralClosure.MulSemiringAction A K L B
  have : SMulCommClass Gal(L/K) A B := smulCommClass_integralClosure A K L B
  let := BD_BI.toAlgebra
  let := BI_BP.toAlgebra
  let := BD_BP.toAlgebra
  have : IsScalarTower BD BI BP := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower BD BI B := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower BI BP B := .of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower BD BP B := .of_algebraMap_eq (fun _ ↦ rfl)
  have : mI.LiesOver mD := ⟨(Ideal.under_under (A := BD) (B := BI) m).symm⟩
  have : mP.LiesOver mI := ⟨(Ideal.under_under (A := BI) (B := BP) m).symm⟩
  have : mP.LiesOver mD := ⟨(Ideal.under_under (A := BD) (B := BP) m).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver mD mI
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := Module.IsTorsionFree.of_faithfulSMul B A L
  have : IsGaloisGroup Gal(L/K) A B := IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L
  have : Finite (PrimeSpectrum A) := finite_primeSpectrum_of_isDiscreteValuationRing A
  obtain ⟨_, _⟩ := fixedPoints_isDedekindDomain_and_finite A K L D
  obtain ⟨_, _⟩ := fixedPoints_isDedekindDomain_and_finite A K L I
  obtain ⟨_, _⟩ := fixedPoints_isDedekindDomain_and_finite A K L PG
  have : IsScalarTower A BD BI := .of_algebraMap_eq fun a ↦ (BD_BI.commutes a).symm
  have : IsScalarTower A BI BP := .of_algebraMap_eq fun a ↦ (BI_BP.commutes a).symm
  have : IsScalarTower A BD BP := .of_algebraMap_eq fun a ↦ (BD_BP.commutes a).symm
  have : FaithfulSMul BD BI := (faithfulSMul_iff_algebraMap_injective BD BI).mpr
    fun x y h ↦ Subtype.ext (congrArg (fun z : BI ↦ (z : B)) h)
  have : FaithfulSMul BI BP := (faithfulSMul_iff_algebraMap_injective BI BP).mpr
    fun x y h ↦ Subtype.ext (congrArg (fun z : BP ↦ (z : B)) h)
  have : FaithfulSMul BD BP := (faithfulSMul_iff_algebraMap_injective BD BP).mpr
    fun x y h ↦ Subtype.ext (congrArg (fun z : BP ↦ (z : B)) h)
  have : Module.Finite BD B := Module.Finite.of_restrictScalars_finite A BD B
  have : Module.Finite BI B := Module.Finite.of_restrictScalars_finite A BI B
  have : Module.Finite BP B := Module.Finite.of_restrictScalars_finite A BP B
  have : Module.Finite BD BI := Module.Finite.of_restrictScalars_finite A BD BI
  have : Module.Finite BI BP := Module.Finite.of_restrictScalars_finite A BI BP
  have : Module.Finite BD BP := Module.Finite.of_restrictScalars_finite A BD BP
  have : Module.IsTorsionFree A BD := Module.IsTorsionFree.of_faithfulSMul BD A B
  have : Module.IsTorsionFree A BI := Module.IsTorsionFree.of_faithfulSMul BI A B
  have : Module.IsTorsionFree A BP := Module.IsTorsionFree.of_faithfulSMul BP A B
  have : Module.IsTorsionFree BD B := inferInstance
  have : Module.IsTorsionFree BI B := inferInstance
  have : Module.IsTorsionFree BP B := inferInstance
  have : Module.IsTorsionFree BD BI := Module.IsTorsionFree.of_faithfulSMul BI BD B
  have : Module.IsTorsionFree BI BP := Module.IsTorsionFree.of_faithfulSMul BP BI B
  have : Module.IsTorsionFree BD BP := Module.IsTorsionFree.of_faithfulSMul BP BD B
  have : IsGaloisGroup D BD B := inferInstance
  have : IsGaloisGroup I BI B := inferInstance
  have : IsGaloisGroup PG BP B := inferInstance
  have : IsGaloisGroup ID BI B := isGaloisGroup_subgroupOf_of_le BI B hID
  have : IsGaloisGroup P BP B := isGaloisGroup_of_map_subtype BP B P
  have : Algebra.IsIntegral BD B := inferInstance
  have : Algebra.IsIntegral BI B := inferInstance
  have : Algebra.IsIntegral BP B := inferInstance
  have hmD : ∀ Q : Ideal B, Q.IsPrime → Q.under BD = mD → Q = m := fun Q _ hQ ↦
    eq_of_under_eq_fixedPoints A B Gal(L/K) m D le_rfl Q hQ
  have hmI : ∀ Q : Ideal B, Q.IsPrime → Q.under BI = mI → Q = m := fun Q _ hQ ↦
    eq_of_under_eq_fixedPoints A B Gal(L/K) m I hID Q hQ
  have hmP : ∀ Q : Ideal B, Q.IsPrime → Q.under BP = mP → Q = m := fun Q _ hQ ↦
    eq_of_under_eq_fixedPoints A B Gal(L/K) m PG (hPGI.trans hID) Q hQ
  have hu1 : ∀ Q : Ideal BI, Q.IsPrime → Q.under BD = mD → Q = mI := fun Q _ hQ ↦
    eq_of_under_eq_of_unique_liesOver BD BI B m hmD Q hQ
  have hu2 : ∀ Q : Ideal BP, Q.IsPrime → Q.under BI = mI → Q = mP := fun Q _ hQ ↦
    eq_of_under_eq_of_unique_liesOver BI BP B m hmI Q hQ
  have hu4 : ∀ Q : Ideal BP, Q.IsPrime → Q.under BD = mD → Q = mP := fun Q _ hQ ↦
    eq_of_under_eq_of_unique_liesOver BD BP B m hmD Q hQ
  have : mD.IsMaximal := Ideal.IsMaximal.under BD m
  have : mI.IsMaximal := Ideal.IsMaximal.under BI m
  have : mP.IsMaximal := Ideal.IsMaximal.under BP m
  have : (mD.under A).IsMaximal := Ideal.IsMaximal.under A mD
  have : mI.LiesOver (mD.under A) := Ideal.LiesOver.trans mI mD (mD.under A)
  have : mP.LiesOver (mD.under A) := Ideal.LiesOver.trans mP mD (mD.under A)
  have : Finite (PrimeSpectrum BD) := Algebra.QuasiFinite.finite_primeSpectrum A BD
  obtain ⟨heD, hfD⟩ := ramificationIdx_and_inertiaDeg_eq_one_of_stabilizer A BD B Gal(L/K) m
  have hresD := nonempty_algEquiv_of_inertiaDeg_eq_one (mD.under A) mD hfD
  have hsepD : Algebra.IsSeparable (A ⧸ mD.under A) (BD ⧸ mD) := by
    let := Ideal.Quotient.field (mD.under A)
    let := Ideal.Quotient.field mD
    exact isSeparable_of_nonempty_algEquiv hresD
  have hetD : Algebra.Etale A (Localization.AtPrime mD) :=
    etale_atPrime_of_ramificationIdx_eq_one (mD.under A) mD heD
  have hetI : Algebra.Etale A (Localization.AtPrime mI) :=
    (inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization A K L m).2
  have hetDI : Algebra.Etale (Localization.AtPrime mD) (Localization.AtPrime mI) :=
    Algebra.Etale.of_restrictScalars A _ _
  have : Algebra.IsUnramifiedAt A mI := inferInstance
  have heI : mI.ramificationIdx A = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hsepI : Algebra.IsSeparable (A ⧸ mD.under A) (BI ⧸ mI) := by
    let := Ideal.Quotient.field (mD.under A)
    let := Ideal.Quotient.field mI
    exact quotient_isSeparable_of_isUnramifiedAt A BI (mD.under A) mI
  have hcardpos : Nat.card (I ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hunit : IsUnit (Nat.card (I ⧸ P) : BI) := by
    simpa using (isUnit_natCast_of_coprime_ringExpChar A _ hcardpos hcop).map (algebraMap A BI)
  have hIt : m.inertia I = ⊤ :=
    top_unique fun g _ ↦ Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp g.property)
  obtain ⟨heP, hsurjP⟩ := ramificationIdx_eq_card_quotient_and_surjective BI BP B I P m hIt hunit
  have hresP := nonempty_algEquiv_of_surjective mI mP hsurjP
  have heDI : mI.ramificationIdx BD = 1 := by
    have h := Ideal.ramificationIdx_tower (R := A) mD mI
    rw [heI] at h
    exact Nat.eq_one_of_mul_eq_one_left h.symm
  have heBD : mP.ramificationIdx BD = Nat.card (I ⧸ P) := by
    rwa [Ideal.ramificationIdx_tower (R := BD) mI mP, heDI, one_mul]
  have heA : mP.ramificationIdx A = Nat.card (I ⧸ P) := by
    rwa [Ideal.ramificationIdx_tower (R := A) mI mP, heI, one_mul]
  refine ⟨hu1, hu2, hmP, hu4, hmI, hmD, inferInstance, inferInstance, inferInstance,
    inferInstance, hetD, hetDI, hetI, ?_, heP, heP ▸ hcop, heBD, heBD ▸ hcop, heA, heA ▸ hcop⟩
  intro _ _ _ _
  let := Ideal.Quotient.field (mD.under A)
  let := Ideal.Quotient.field mD
  let := Ideal.Quotient.field mI
  let := Ideal.Quotient.field mP
  have := isScalarTower_quotient (mD.under A) mD mI
  have := isScalarTower_quotient (mD.under A) mD mP
  have := isScalarTower_quotient mD mI mP
  have hsepDI : Algebra.IsSeparable (BD ⧸ mD) (BI ⧸ mI) :=
    Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ mD.under A) _ _
  have hDt : MulAction.stabilizer D m = ⊤ := top_unique fun g _ ↦ g.property
  obtain ⟨hnorm, eRes, heRes⟩ :=
    exists_residue_quotientEquiv BD BI B D ID m mD mI hDt rfl
  have hsepIP : Algebra.IsSeparable (BI ⧸ mI) (BP ⧸ mP) := isSeparable_of_nonempty_algEquiv hresP
  have hsepDP : Algebra.IsSeparable (BD ⧸ mD) (BP ⧸ mP) :=
    Algebra.IsSeparable.trans (BD ⧸ mD) (BI ⧸ mI) (BP ⧸ mP)
  have hgal : IsGalois (BD ⧸ mD) (BI ⧸ mI) := { }
  refine ⟨hresD, hgal, ⟨eRes, fun σ b ↦ heRes σ b⟩, hresP, hsepDP,
    Algebra.IsSeparable.trans (A ⧸ mD.under A) (BD ⧸ mD) (BP ⧸ mP)⟩

end IsDiscreteValuationRing

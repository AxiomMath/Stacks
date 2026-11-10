module

public import StacksFrontier.RingTheory.Branches.Henselization.Unibranch

/-!
# Numbers of branches and geometric branches of a local ring

The number of branches of a local ring `A` is the number of maximal ideals of the integral
closure `A'` of `A` in the total ring of fractions of its reduction, and the number of geometric
branches is the same count weighted by the separable degrees of the residue-field extensions.

## Main results

* `numberOfBranches_characterizations` (Stacks 0C37): characterizations of branch number one
  and formulas for ordinary and geometric branch counts using the normalization.

## Implementation notes

Branch counts take values in the extended natural numbers, measured by `Set.encard`, so
infinitely many minimal primes give the value infinity. In the geometric formula each
residue-field extension is given by the map induced by contraction of the corresponding maximal
ideal.

## References

* [The Stacks Project, Tag 0C37](https://stacks.math.columbia.edu/tag/0C37)
-/

@[expose] public section

universe u v

section BranchNumbers

open scoped TensorProduct

private theorem encard_eq_one_iff_existsUnique {X : Type*} (s : Set X) :
    s.encard = 1 ↔ ∃! x, x ∈ s := by
  rw [Set.encard_eq_one]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, Set.mem_singleton x, fun y hy => Set.mem_singleton_iff.mp hy⟩
  · rintro ⟨x, hx, hu⟩
    refine ⟨x, Set.Subset.antisymm (fun y hy => ?_) ?_⟩
    · exact Set.mem_singleton_iff.mpr (hu y hy)
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hx

private noncomputable def equivOfBijOn {X Y : Type*} {s : Set X} {t : Set Y}
    (f : X → Y) (h : Set.BijOn f s t) : s ≃ t where
  toFun x := ⟨f x, h.1 x.2⟩
  invFun y := ⟨Classical.choose (h.2.2 y.2), (Classical.choose_spec (h.2.2 y.2)).1⟩
  left_inv x := Subtype.ext (h.2.1
    (Classical.choose_spec (h.2.2 (h.1 x.2))).1 x.2
    (Classical.choose_spec (h.2.2 (h.1 x.2))).2)
  right_inv y := Subtype.ext (Classical.choose_spec (h.2.2 y.2)).2

private theorem encard_eq_of_bijOn {X Y : Type*} {s : Set X} {t : Set Y}
    (f : X → Y) (h : Set.BijOn f s t) : s.encard = t.encard :=
  Set.encard_congr (equivOfBijOn f h)

private theorem card_algHom_eq_sepDegreeToType
    (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [IsAlgClosed K] [Algebra.IsAlgebraic F E] :
    ENat.card (E →ₐ[F] K) = ENat.card (Field.sepDegree F E).ord.ToType := by
  rw [ENat.card_congr (Field.embEquivOfIsAlgClosed F E K).symm]
  rw [ENat.card, ENat.card, Cardinal.mk_toType, Cardinal.card_ord]
  rw [Field.Emb.cardinal_eq]
  dsimp only
  by_cases h : Cardinal.aleph0 ≤ Field.sepDegree F E
  · simp only [h, ↓reduceIte]
    rw [Cardinal.toENat_eq_top.mpr h,
      Cardinal.toENat_eq_top.mpr (h.trans (Cardinal.cantor _).le)]
  · simp only [h, ↓reduceIte]

private theorem RingHom.ker_isMaximal_of_range_contains_algebraic_field
    (F R K : Type*) [Field F] [CommRing R] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] (f : R →+* K)
    (h : ∀ x : F, algebraMap F K x ∈ f.range) : (RingHom.ker f).IsMaximal := by
  let S : Subalgebra F K :=
    { f.range with
      algebraMap_mem' := h }
  let g : R →+* S := f.codRestrict S fun x => ⟨x, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let : Field S := (Subalgebra.isField_of_algebraic S).toField
  have hker : RingHom.ker g = RingHom.ker f := by
    ext x
    change g x = 0 ↔ f x = 0
    exact Subtype.ext_iff
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective g hg

private theorem card_sigma_eq_of_card_fiber_eq
    {I : Type*} {X Y : I → Type*} [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (h : ∀ i, ENat.card (X i) = ENat.card (Y i)) :
    ENat.card (Σ i, X i) = ENat.card (Σ i, Y i) := by
  classical
  by_cases hi : Infinite I
  · let := hi
    have hX : Infinite (Σ i, X i) := Infinite.of_injective
      (fun i => ⟨i, Classical.choice (inferInstance : Nonempty (X i))⟩)
      (fun _ _ e => by simpa using congrArg Sigma.fst e)
    have hY : Infinite (Σ i, Y i) := Infinite.of_injective
      (fun i => ⟨i, Classical.choice (inferInstance : Nonempty (Y i))⟩)
      (fun _ _ e => by simpa using congrArg Sigma.fst e)
    exact ENat.card_eq_top.mpr hX |>.trans (ENat.card_eq_top.mpr hY).symm
  · let : Finite I := not_infinite_iff_finite.mp hi
    let := Fintype.ofFinite I
    by_cases hx : ∃ i, Infinite (X i)
    · obtain ⟨i, hiX⟩ := hx
      have hXi : ENat.card (X i) = ⊤ := ENat.card_eq_top.mpr hiX
      have hiY : Infinite (Y i) := ENat.card_eq_top.mp ((h i).symm.trans hXi)
      have hX : Infinite (Σ i, X i) := Infinite.of_injective
        (fun x : X i => ⟨i, x⟩) (fun _ _ e => by simpa using e)
      have hY : Infinite (Σ i, Y i) := Infinite.of_injective
        (fun y : Y i => ⟨i, y⟩) (fun _ _ e => by simpa using e)
      exact ENat.card_eq_top.mpr hX |>.trans (ENat.card_eq_top.mpr hY).symm
    · have hfinX : ∀ i, Finite (X i) := fun i =>
        not_infinite_iff_finite.mp (fun hiX => hx ⟨i, hiX⟩)
      have hfinY : ∀ i, Finite (Y i) := fun i =>
        not_infinite_iff_finite.mp fun hiY => by
          have := (h i).trans (ENat.card_eq_top.mpr hiY)
          exact hx ⟨i, ENat.card_eq_top.mp this⟩
      let : ∀ i, Finite (X i) := hfinX
      let : ∀ i, Finite (Y i) := hfinY
      rw [ENat.card_eq_coe_natCard, ENat.card_eq_coe_natCard,
        Nat.card_sigma, Nat.card_sigma]
      congr 1
      exact Finset.sum_congr rfl fun i _ =>
        ENat.natCast_inj.mp (by simpa [ENat.card_eq_coe_natCard] using h i)

private theorem minimalPrimes_infinite_of_faithfullyFlat
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (h : (minimalPrimes R).Infinite) :
    (minimalPrimes S).Infinite := by
  apply Set.not_finite.mp
  intro hfin
  apply h
  apply Set.Finite.of_surjOn (fun q => Ideal.comap (algebraMap R S) q) _ hfin
  intro p hp
  obtain ⟨P, hP⟩ :=
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S)) ⟨p, hp.isPrime⟩
  have hPas := congrArg PrimeSpectrum.asIdeal hP
  change Ideal.comap (algebraMap R S) P.asIdeal = p at hPas
  obtain ⟨q, hq, hqP⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal S)) (J := P.asIdeal) bot_le
  have hle : q.comap (algebraMap R S) ≤ p := hPas ▸ Ideal.comap_mono hqP
  exact ⟨q, hq, le_antisymm hle (hp.2 ⟨hq.isPrime.comap _, bot_le⟩ hle)⟩

private theorem integral_tensorProduct_rightAlgebra
    (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.IsIntegral R B] :
    let _ : Algebra S (B ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    Algebra.IsIntegral S (B ⊗[R] S) := by
  let : Algebra S (B ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  constructor
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b s =>
    have hb : IsIntegral S (b ⊗ₜ[R] (1 : S)) :=
      (Algebra.IsIntegral.isIntegral b).map_of_comp_eq
        (algebraMap R S) Algebra.TensorProduct.includeLeftRingHom
        Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
    simpa only [Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using
      hb.mul (isIntegral_algebraMap (R := S) (A := B ⊗[R] S) (x := s))
  | add x y hx hy => exact hx.add hy

private theorem maximal_eq_minimal_encard_of_incidence
    {R : Type*} [CommRing R]
    (hminmax : ∀ q ∈ minimalPrimes R, ∃! m : Ideal R, m.IsMaximal ∧ q ≤ m)
    (hmaxmin : ∀ m : Ideal R, m.IsMaximal →
      ∃! q : Ideal R, q ∈ minimalPrimes R ∧ q ≤ m) :
    Set.encard {m : Ideal R | m.IsMaximal} = (minimalPrimes R).encard := by
  let f : {q : Ideal R // q ∈ minimalPrimes R} → {m : Ideal R // m.IsMaximal} :=
    fun q => ⟨Classical.choose (hminmax q q.2),
      (Classical.choose_spec (hminmax q q.2)).1.1⟩
  let g : {m : Ideal R // m.IsMaximal} → {q : Ideal R // q ∈ minimalPrimes R} :=
    fun m => ⟨Classical.choose (hmaxmin m m.2),
      (Classical.choose_spec (hmaxmin m m.2)).1.1⟩
  exact (Set.encard_congr {
    toFun := f
    invFun := g
    left_inv := fun q => Subtype.ext
      ((Classical.choose_spec (hmaxmin (f q) (f q).2)).2 q
        ⟨q.2, (Classical.choose_spec (hminmax q q.2)).1.2⟩).symm
    right_inv := fun m => Subtype.ext
      ((Classical.choose_spec (hminmax (g m) (g m).2)).2 m
        ⟨m.2, (Classical.choose_spec (hmaxmin m m.2)).1.2⟩).symm }).symm

set_option maxHeartbeats 800000 in
-- Elaborating this proof needs more than the default heartbeat limit.
set_option synthInstance.maxHeartbeats 100000 in
/-- The numbers of branches and geometric branches of a local ring are infinite if the ring has
infinitely many minimal primes, and they equal one exactly for unibranch and geometrically
unibranch rings, respectively. If the ring has finitely many minimal primes, its branches are
the maximal ideals of the normalization of its reduction, with geometric branches weighted by
the separable degrees of the corresponding residue-field extensions. -/
@[stacks 0C37]
theorem numberOfBranches_characterizations
    (A Ah Ash : Type u) (ksep : Type v)
    [CommRing A] [IsLocalRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah]
    [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsLocalRing.IsHenselization A ksep Ash] :
    ((minimalPrimes A).Infinite →
        numberOfBranches A Ah = ⊤ ∧
          numberOfGeometricBranches A ksep Ash = ⊤) ∧
      (numberOfBranches A Ah = 1 ↔ IsUnibranch A) ∧
      (numberOfGeometricBranches A ksep Ash = 1 ↔
        IsGeometricallyUnibranch A) ∧
      ((minimalPrimes A).Finite →
        let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
        numberOfBranches A Ah =
            Set.encard {m' : Ideal A' | m'.IsMaximal} ∧
          ∃ hcontract : ∀ m' : MaximalSpectrum A',
              IsLocalRing.maximalIdeal A = m'.asIdeal.comap (algebraMap A A'),
            numberOfGeometricBranches A ksep Ash =
              ENat.card (Σ m' : MaximalSpectrum A',
                letI : Field (A' ⧸ m'.asIdeal) := Ideal.Quotient.field m'.asIdeal
                let f := Ideal.quotientMap m'.asIdeal (algebraMap A A')
                  (le_of_eq (hcontract m'))
                letI : Algebra (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) := f.toAlgebra
                (Field.sepDegree (IsLocalRing.ResidueField A)
                  (A' ⧸ m'.asIdeal)).ord.ToType)) := by
  let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
  let T := TensorProduct A A' Ah
  have : Module.Flat A Ah :=
    flat_of_isHenselization (L := IsLocalRing.ResidueField A)
  have : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := IsLocalRing.ResidueField A)
  have : Module.FaithfullyFlat A Ah :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Flat A Ash := flat_of_isHenselization (L := ksep)
  have : IsLocalHom (algebraMap A Ash) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ksep)
  have : Module.FaithfullyFlat A Ash :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    constructor
    · change (minimalPrimes Ah).encard = ⊤
      exact Set.encard_eq_top (minimalPrimes_infinite_of_faithfullyFlat h)
    · change (minimalPrimes Ash).encard = ⊤
      exact Set.encard_eq_top (minimalPrimes_infinite_of_faithfullyFlat h)
  · change (minimalPrimes Ah).encard = 1 ↔ _
    rw [encard_eq_one_iff_existsUnique]
    exact isUnibranch_iff_henselization_has_unique_minimalPrime A Ah |>.symm
  · change (minimalPrimes Ash).encard = 1 ↔ _
    rw [encard_eq_one_iff_existsUnique]
    exact isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
      A Ash ksep |>.symm
  · intro hfinite
    obtain ⟨hmax, hmin, hminmax, hmaxmin⟩ :=
      bijective_maximalIdeals_and_minimalPrimes_of_henselization A Ah hfinite
    have hord : (minimalPrimes Ah).encard = Set.encard {m : Ideal A' | m.IsMaximal} := by
      calc
        _ = (minimalPrimes (TensorProduct A A' Ah)).encard :=
          (encard_eq_of_bijOn _ hmin).symm
        _ = Set.encard {m : Ideal (TensorProduct A A' Ah) | m.IsMaximal} :=
          (maximal_eq_minimal_encard_of_incidence
            (R := TensorProduct A A' Ah) hminmax hmaxmin).symm
        _ = _ := encard_eq_of_bijOn _ hmax
    refine ⟨hord, ?_⟩
    let hcontract : ∀ m' : MaximalSpectrum A',
        IsLocalRing.maximalIdeal A = m'.asIdeal.comap (algebraMap A A') := fun m' => by
      symm
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m'.asIdeal)
    refine ⟨hcontract, ?_⟩
    obtain ⟨e, he⟩ := IsLocalRing.IsHenselization.exists_residueFieldEquiv
      (R := A) (L := ksep) (Rh := Ash)
    let kbar := AlgebraicClosure ksep
    have hc25 := geometric_branches_of_strictHenselization
      A Ash ksep kbar e he hfinite
    dsimp only at hc25
    obtain ⟨hfib, hminsh, hminmaxsh, hmaxminsh⟩ := hc25
    let Tsh := TensorProduct A A' Ash
    have hmaxfiber (m' : MaximalSpectrum A')
        (q : PrimeSpectrum Tsh)
        (hq : PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            A' →+* Tsh) q =
          m'.toPrimeSpectrum) : q.asIdeal.IsMaximal := by
      obtain ⟨hm, hint, E, hE⟩ := hfib m'
      let qs : {q : PrimeSpectrum Tsh // PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            A' →+* Tsh) q =
          m'.toPrimeSpectrum} := ⟨q, hq⟩
      let σ := E.symm qs
      obtain ⟨φ, hφ, hk, -⟩ := hE σ
      let φ' : Tsh →+* kbar := φ
      have hrange : ∀ x : ksep, ∃ y : Tsh,
          φ' y = algebraMap ksep kbar x := by
        intro x
        obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (e x)
        refine ⟨1 ⊗ₜ[A] b, ?_⟩
        rw [show φ' = φ from rfl, hφ]
        simp [hb]
      have hker : (RingHom.ker φ').IsMaximal :=
        RingHom.ker_isMaximal_of_range_contains_algebraic_field
          ksep Tsh kbar (f := φ') (fun x => by
            obtain ⟨y, hy⟩ := hrange x
            exact ⟨y, hy⟩)
      have heq : q.asIdeal = RingHom.ker φ' := by
        calc
          q.asIdeal = (E σ).1.asIdeal := by simp [σ, qs]
          _ = RingHom.ker φ := hk
          _ = _ := rfl
      exact heq.symm ▸ hker
    let : Algebra Ash Tsh := Algebra.TensorProduct.rightAlgebra
    let : Algebra.IsIntegral Ash Tsh := integral_tensorProduct_rightAlgebra A Ash A'
    have hcontraction (m : MaximalSpectrum Tsh) :
        (m.asIdeal.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            A' →+* Tsh)).IsMaximal := by
      let p := m.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom :
          A' →+* Tsh)
      let q := m.asIdeal.comap
        (Algebra.TensorProduct.includeRight : Ash →ₐ[A] Tsh).toRingHom
      have hq : q.IsMaximal :=
        Ideal.isMaximal_under_of_isIntegral_of_isMaximal
          (R := Ash) (S := Tsh) m.asIdeal
      have hqeq : q = IsLocalRing.maximalIdeal Ash := IsLocalRing.eq_maximalIdeal hq
      have hpcomap : p.comap (algebraMap A _) = IsLocalRing.maximalIdeal A := by
        rw [← IsLocalRing.maximalIdeal_comap (algebraMap A Ash), ← hqeq]
        ext x
        simp [p, q, Tsh]
      let : p.IsPrime := m.isMaximal.isPrime.comap _
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) p
      rw [Ideal.under, hpcomap]
      exact IsLocalRing.maximalIdeal.isMaximal A
    let maxEquivFiber : MaximalSpectrum Tsh ≃
        Σ m' : MaximalSpectrum A',
          {q : PrimeSpectrum Tsh // PrimeSpectrum.comap
            (Algebra.TensorProduct.includeLeftRingHom :
              A' →+* Tsh) q =
            m'.toPrimeSpectrum} :=
      { toFun := fun m => ⟨⟨_, hcontraction m⟩, ⟨m.toPrimeSpectrum, rfl⟩⟩
        invFun := fun z => ⟨z.2.1.asIdeal, hmaxfiber z.1 z.2.1 z.2.2⟩
        left_inv := fun m => by ext; rfl
        right_inv := fun z => by
          rcases z with ⟨⟨m, hm⟩, q, hq⟩
          have heq := congrArg PrimeSpectrum.asIdeal hq
          change q.asIdeal.comap Algebra.TensorProduct.includeLeftRingHom = m at heq
          subst m
          rfl }
    let (m' : MaximalSpectrum A') : Field (A' ⧸ m'.asIdeal) :=
      Ideal.Quotient.field m'.asIdeal
    let (m' : MaximalSpectrum A') : Algebra (IsLocalRing.ResidueField A)
        (A' ⧸ m'.asIdeal) :=
      (Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq (hcontract m'))).toAlgebra
    let (m' : MaximalSpectrum A') : Algebra.IsIntegral (IsLocalRing.ResidueField A)
        (A' ⧸ m'.asIdeal) := ⟨(hfib m').choose_spec.1⟩
    let fiberEquivAlgHom (m' : MaximalSpectrum A') :
        {q : PrimeSpectrum Tsh // PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            A' →+* Tsh) q =
          m'.toPrimeSpectrum} ≃
          ((A' ⧸ m'.asIdeal) →ₐ[IsLocalRing.ResidueField A] kbar) := by
      let hm := (hfib m').choose
      let E := (hfib m').choose_spec.2.choose
      let f := Ideal.quotientMap m'.asIdeal (algebraMap A _)
        (le_of_eq hm)
      let ringEquiv :
          { σ : (A' ⧸ m'.asIdeal) →+* kbar //
              σ.comp f = algebraMap (IsLocalRing.ResidueField A) kbar } ≃
            ((A' ⧸ m'.asIdeal) →ₐ[IsLocalRing.ResidueField A] kbar) :=
        { toFun := fun σ =>
            { σ.1 with
              commutes' := fun x => DFunLike.congr_fun σ.2 x }
          invFun := fun σ => ⟨σ.toRingHom, σ.comp_algebraMap⟩
          left_inv := fun σ => by ext; rfl
          right_inv := fun σ => by ext; rfl }
      exact E.symm.trans ringEquiv
    let (m' : MaximalSpectrum A') : FaithfulSMul (IsLocalRing.ResidueField A)
        (A' ⧸ m'.asIdeal) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
    let (m' : MaximalSpectrum A') : Nonempty
        ((A' ⧸ m'.asIdeal) →ₐ[IsLocalRing.ResidueField A] kbar) := ⟨IsAlgClosed.lift⟩
    let (m' : MaximalSpectrum A') : Nonempty
        (Field.sepDegree (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal)).ord.ToType :=
      Cardinal.nonempty_ord_toType (NeZero.ne _)
    calc
      (minimalPrimes Ash).encard = (minimalPrimes Tsh).encard :=
        (encard_eq_of_bijOn _ hminsh).symm
      _ = Set.encard {m : Ideal Tsh | m.IsMaximal} :=
        (maximal_eq_minimal_encard_of_incidence
          (R := Tsh) hminmaxsh hmaxminsh).symm
      _ = ENat.card (MaximalSpectrum Tsh) :=
        ENat.card_congr (MaximalSpectrum.equivSubtype Tsh).symm
      _ = ENat.card (Σ m' : MaximalSpectrum A',
          ((A' ⧸ m'.asIdeal) →ₐ[IsLocalRing.ResidueField A] kbar)) := by
        rw [ENat.card_congr maxEquivFiber]
        exact ENat.card_congr (Equiv.sigmaCongrRight fiberEquivAlgHom)
      _ = _ := by
        apply card_sigma_eq_of_card_fiber_eq
        intro m'
        simpa using card_algHom_eq_sepDegreeToType
          (IsLocalRing.ResidueField A)
          (A' ⧸ m'.asIdeal) kbar

end BranchNumbers

end

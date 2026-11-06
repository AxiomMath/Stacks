module

public import StacksFrontier.RingTheory.Branches.Henselization.BranchCorrespondence
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.LocalMinimalPrime

/-!
# Unibranch and geometrically unibranch local rings via henselization

A local ring `A` is unibranch exactly when a henselization `Aʰ` has a unique minimal prime, and
geometrically unibranch exactly when a strict henselization `Aˢʰ` has one. Both are deduced from
the branch correspondences between the normalization `A'` of `A` and `A' ⊗[A] Aʰ`, respectively
`A' ⊗[A] Aˢʰ`.

## Main results

* `isUnibranch_iff_henselization_has_unique_minimalPrime` (Stacks 0BQ0): a local ring is
  unibranch exactly when a henselization of it has a unique minimal prime.
* `isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime` (Stacks 06DM): a
  local ring is geometrically unibranch exactly when a strict henselization has a unique
  minimal prime.

## Implementation notes

Finiteness of the set of minimal primes is not needed for Tags 0BQ0 and 06DM. The two groups of
results use incompatible `open` directives and are kept in the sections `Unibranch` and
`GeometricallyUnibranch`.

## References

* [Grothendieck and Dieudonné, *Éléments de géométrie algébrique IV*][EGA4],
  Propositions 18.6.12 and 18.8.15
* [SGA 1, Exposé I, Lemma 2.2][Etale-coverings]
* [The Stacks Project, Tag 0BQ0](https://stacks.math.columbia.edu/tag/0BQ0)
* [The Stacks Project, Tag 06DM](https://stacks.math.columbia.edu/tag/06DM)
-/

@[expose] public section

universe u v

private theorem unique_maximal_iff_unique_minimal_of_incidence
    {R : Type*} [CommRing R]
    (hminmax : ∀ q ∈ minimalPrimes R, ∃! m : Ideal R, m.IsMaximal ∧ q ≤ m)
    (hmaxmin : ∀ m : Ideal R, m.IsMaximal →
      ∃! q : Ideal R, q ∈ minimalPrimes R ∧ q ≤ m) :
    (∃! m : Ideal R, m.IsMaximal) ↔ (∃! q : Ideal R, q ∈ minimalPrimes R) := by
  constructor
  · rintro ⟨m, hm, hmu⟩
    obtain ⟨q, hq, hqu⟩ := hmaxmin m hm
    refine ⟨q, hq.1, fun q' hq' => ?_⟩
    obtain ⟨m', hm', -⟩ := hminmax q' hq'
    have hmm' : m' = m := hmu m' hm'.1
    exact hqu q' ⟨hq', hmm' ▸ hm'.2⟩
  · rintro ⟨q, hq, hqu⟩
    obtain ⟨m, hm, hmu⟩ := hminmax q hq
    refine ⟨m, hm.1, fun m' hm' => ?_⟩
    obtain ⟨q', hq', -⟩ := hmaxmin m' hm'
    have hqq' : q' = q := hqu q' hq'.1
    exact hmu m' ⟨hm', hqq' ▸ hq'.2⟩

section Unibranch

open scoped TensorProduct

private theorem existsUnique_mem_of_bijOn {α β : Type*} {s : Set α} {t : Set β}
    {f : α → β} (h : Set.BijOn f s t) (ht : ∃! y, y ∈ t) : ∃! x, x ∈ s := by
  obtain ⟨y, hy, hyu⟩ := ht
  obtain ⟨x, hx, hxy⟩ := h.2.2 hy
  refine ⟨x, hx, fun z hz => ?_⟩
  exact h.2.1 hz hx ((hyu _ (h.1 hz)).trans (hyu _ (h.1 hx)).symm)

private theorem existsUnique_mem_of_bijOn_target {α β : Type*} {s : Set α} {t : Set β}
    {f : α → β} (h : Set.BijOn f s t) (hs : ∃! x, x ∈ s) : ∃! y, y ∈ t := by
  obtain ⟨x, hx, hxu⟩ := hs
  refine ⟨f x, h.1 hx, fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := h.2.2 hy
  exact congrArg f (hxu z hz)

private theorem finite_of_existsUnique_mem {α : Type*} {s : Set α} (h : ∃! x, x ∈ s) :
    s.Finite := by
  obtain ⟨x, hx, hxu⟩ := h
  have hs : s = {x} := by
    ext y
    constructor
    · intro hy
      simp [hxu y hy]
    · simp_all
  rw [hs]
  exact Set.finite_singleton x

private theorem isDomain_reduction_of_unique_minimalPrimes
    {R : Type*} [CommRing R] (h : ∃! p : Ideal R, p ∈ minimalPrimes R) :
    IsDomain (R ⧸ nilradical R) := by
  obtain ⟨p, hp, hpu⟩ := h
  have hnil : nilradical R = p := by
    have hrad : (⊥ : Ideal R).radical = nilradical R := rfl
    rw [← hrad, ← Ideal.sInf_minimalPrimes]
    exact le_antisymm (sInf_le hp) (le_sInf fun q hq => (hpu q hq).symm ▸ le_rfl)
  exact (Ideal.Quotient.isDomain_iff_prime (I := nilradical R)).mpr (hnil ▸ hp.isPrime)

/-- A commutative ring whose reduction is a domain has a unique minimal prime, namely its
nilradical. -/
public theorem unique_minimalPrimes_of_isDomain_reduction
    {R : Type*} [CommRing R] [IsDomain (R ⧸ nilradical R)] :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  have hnil : (nilradical R).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (I := nilradical R)).mp inferInstance
  refine ⟨nilradical R, ?_, fun p hp => ?_⟩
  · exact ⟨⟨hnil, bot_le⟩, fun q hq _ => @nilradical_le_prime R _ q hq.1⟩
  · exact le_antisymm
      (hp.2 ⟨hnil, bot_le⟩ (@nilradical_le_prime R _ p hp.isPrime))
      (@nilradical_le_prime R _ p hp.isPrime)

private noncomputable def integralClosureQuotientEquiv
    (R : Type*) [CommRing R] (K : Type*) [CommRing K]
    [Algebra (R ⧸ nilradical R) K] [Algebra R K]
    [IsScalarTower R (R ⧸ nilradical R) K] :
    integralClosure R K ≃+* integralClosure (R ⧸ nilradical R) K where
  toFun x := ⟨x.1, IsIntegral.tower_top (R := R) (A := R ⧸ nilradical R) x.2⟩
  invFun x := ⟨x.1, by
    let : Algebra.IsIntegral R (R ⧸ nilradical R) :=
      ⟨RingHom.isIntegral_of_surjective (Ideal.Quotient.mk (nilradical R))
        Ideal.Quotient.mk_surjective⟩
    exact isIntegral_trans (R := R) x.1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- A local ring is unibranch if and only if a henselization of it has a unique minimal prime. -/
@[stacks 0BQ0, ega "IV 18.6.12" "a) ⇔ c), irreducible"]
theorem isUnibranch_iff_henselization_has_unique_minimalPrime
    (A Ah : Type u) [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
    [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah] :
    IsUnibranch A ↔ ∃! p : Ideal Ah, p ∈ minimalPrimes Ah := by
  let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
  let T := TensorProduct A A' Ah
  let f : A' →+* T := Algebra.TensorProduct.includeLeftRingHom
  let g : Ah →+* T :=
    (Algebra.TensorProduct.includeRight : Ah →ₐ[A] T).toRingHom
  have : Module.Flat A Ah :=
    flat_of_isHenselization (L := IsLocalRing.ResidueField A)
  have : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := IsLocalRing.ResidueField A)
  have : Module.FaithfullyFlat A Ah :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · intro hA
    rcases hA with ⟨hred, hlocal⟩
    let : IsDomain (A ⧸ nilradical A) := hred
    let : IsLocalRing A' :=
      (integralClosureQuotientEquiv A (FractionRing (A ⧸ nilradical A))).symm.isLocalRing
    have hAmin := unique_minimalPrimes_of_isDomain_reduction (R := A)
    obtain ⟨hmax, hmin, hminmax, hmaxmin⟩ :=
      bijective_maximalIdeals_and_minimalPrimes_of_henselization
        A Ah (finite_of_existsUnique_mem hAmin)
    have hTmax : ∃! m : Ideal T, m.IsMaximal :=
      existsUnique_mem_of_bijOn hmax (IsLocalRing.maximal_ideal_unique A')
    have hTmin : ∃! q : Ideal T, q ∈ minimalPrimes T :=
      (unique_maximal_iff_unique_minimal_of_incidence (R := T) hminmax hmaxmin).mp hTmax
    exact existsUnique_mem_of_bijOn_target hmin hTmin
  · intro hAh
    have hAmin :=
      AlgebraicGeometry.existsUnique_minimalPrime_of_faithfullyFlat (R := A) (S := Ah) hAh
    let : IsDomain (A ⧸ nilradical A) :=
      isDomain_reduction_of_unique_minimalPrimes hAmin
    obtain ⟨hmax, hmin, hminmax, hmaxmin⟩ :=
      bijective_maximalIdeals_and_minimalPrimes_of_henselization
        A Ah (finite_of_existsUnique_mem hAmin)
    have hTmin : ∃! q : Ideal T, q ∈ minimalPrimes T :=
      existsUnique_mem_of_bijOn hmin hAh
    have hTmax : ∃! m : Ideal T, m.IsMaximal :=
      (unique_maximal_iff_unique_minimal_of_incidence (R := T) hminmax hmaxmin).mpr hTmin
    have hA'max : ∃! m : Ideal A', m.IsMaximal :=
      existsUnique_mem_of_bijOn_target hmax hTmax
    let : IsLocalRing A' := IsLocalRing.of_unique_max_ideal hA'max
    exact ⟨inferInstance,
      (integralClosureQuotientEquiv A (FractionRing (A ⧸ nilradical A))).isLocalRing⟩

end Unibranch


section GeometricallyUnibranch

open scoped TensorProduct

-- The image of a fibre map is a field: it contains the separable closure and is algebraic over it.
private theorem fibre_kernel_isMaximal
    {A A' Ash ksep kbar : Type*}
    [CommRing A] [CommRing A'] [CommRing Ash] [IsLocalRing Ash]
    [Field ksep] [Field kbar] [Algebra A A'] [Algebra A Ash]
    [Algebra ksep kbar]
    (m' : Ideal A') (σ : A' ⧸ m' →+* kbar) (e : ksep ≃+* IsLocalRing.ResidueField Ash)
    (φ : TensorProduct A A' Ash →+* kbar)
    (hφ : ∀ (a : A') (b : Ash),
      φ (a ⊗ₜ[A] b) = σ (Ideal.Quotient.mk m' a) *
        algebraMap ksep kbar (e.symm (IsLocalRing.residue Ash b)))
    (halg : Algebra.IsAlgebraic ksep kbar) : (RingHom.ker φ).IsMaximal := by
  let B : Subalgebra ksep kbar :=
    { φ.range with
      algebraMap_mem' := fun x => by
        obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (R := Ash) (e x)
        refine ⟨1 ⊗ₜ[A] b, ?_⟩
        rw [hφ, hb, e.symm_apply_apply]
        simp }
  let ψ : TensorProduct A A' Ash →+* B := φ.codRestrict B fun x => ⟨x, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let : Algebra.IsAlgebraic ksep kbar := halg
  let : Field B := (Subalgebra.isField_of_algebraic B).toField
  have hm := RingHom.ker_isMaximal_of_surjective ψ hψ
  have hker : RingHom.ker ψ = RingHom.ker φ := by
    ext x
    show ψ x = 0 ↔ φ x = 0
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  exact hker ▸ hm

private theorem tensor_includeRight_isIntegral
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.IsIntegral A B] :
    RingHom.IsIntegral
      (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A B C).toRingHom := by
  let : Algebra C (TensorProduct A B C) :=
    (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A B C).toRingHom.toAlgebra
  show ∀ x : TensorProduct A B C, IsIntegral C x
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | add x y hx hy => exact hx.add hy
  | tmul b c =>
      let : Algebra C (TensorProduct A C B) :=
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] TensorProduct A C B).toRingHom.toAlgebra
      have hbc : IsIntegral C (c ⊗ₜ[A] b : TensorProduct A C B) :=
        (Algebra.IsIntegral.isIntegral b).tmul c
      have hb : IsIntegral C (b ⊗ₜ[A] c : TensorProduct A B C) :=
        IsIntegral.map_of_comp_eq (RingHom.id C) (Algebra.TensorProduct.comm A C B).toRingHom
          (by ext; rfl) hbc
      exact hb

set_option maxHeartbeats 800000 in
-- Elaborating this proof needs more than the default heartbeat limit.
set_option synthInstance.maxHeartbeats 100000 in
-- The proof repeatedly instantiates the large dependent fibre package exported by `0C25`.
private theorem geometricallyUnibranch_iff_unique_minimalPrime_core
    (A Ash : Type u) [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash]
    [Algebra A Ash]
    (ksep : Type v) [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash]
    (kbar : Type*) [Field kbar] [Algebra (IsLocalRing.ResidueField A) kbar]
    [IsAlgClosure (IsLocalRing.ResidueField A) kbar]
    [Algebra ksep kbar] [IsScalarTower (IsLocalRing.ResidueField A) ksep kbar]
    (e : ksep ≃+* IsLocalRing.ResidueField Ash)
    (he : ∀ x : A,
      e (algebraMap (IsLocalRing.ResidueField A) ksep (IsLocalRing.residue A x)) =
        IsLocalRing.residue Ash (algebraMap A Ash x)) :
    IsGeometricallyUnibranch A ↔
      ∃! p : Ideal Ash, p ∈ minimalPrimes Ash := by
  let Ared := A ⧸ nilradical A
  let A' := integralClosure Ared (FractionRing Ared)
  let : Algebra.IsIntegral A Ared :=
    ⟨RingHom.isIntegral_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective⟩
  let : Algebra.IsIntegral A A' :=
    ⟨fun x => isIntegral_trans x (integralClosure.isIntegral x)⟩
  -- The unibranch definition uses the reduction as base, whereas 0C25 uses `A`.
  -- Restrict scalars before comparing the two subalgebras.
  have hclosure : (integralClosure Ared (FractionRing Ared)).restrictScalars A =
      integralClosure A (FractionRing Ared) := by
    ext x
    exact ⟨fun hx => isIntegral_trans (A := Ared) x hx, fun hx => hx.tower_top⟩
  have branches (hfinite : (minimalPrimes A).Finite) :=
    geometric_branches_of_strictHenselization A Ash ksep kbar e he hfinite
  rw [← hclosure] at branches
  let T := TensorProduct A A' Ash
  let : Algebra Ash T :=
    (Algebra.TensorProduct.includeRight : Ash →ₐ[A] T).toRingHom.toAlgebra
  let f : A' →+* T := Algebra.TensorProduct.includeLeftRingHom
  let g : Ash →+* T := algebraMap Ash T
  have : Module.Flat A Ash := flat_of_isHenselization (L := ksep)
  have : IsLocalHom (algebraMap A Ash) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ksep)
  have : Module.FaithfullyFlat A Ash := Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- Every fibre of `T → A'` over a maximal ideal `m'` consists of maximal ideals, and is nonempty.
  have fib (hfin : (minimalPrimes A).Finite) (m' : MaximalSpectrum A') :
      ∃ h : IsLocalRing.maximalIdeal A = m'.asIdeal.comap (algebraMap A A'),
        (Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq h)).IsIntegral ∧
        ∃ E : {σ : (A' ⧸ m'.asIdeal) →+* kbar //
              σ.comp (Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq h)) =
                algebraMap (IsLocalRing.ResidueField A) kbar} ≃
            {q : PrimeSpectrum T // PrimeSpectrum.comap f q = m'.toPrimeSpectrum},
          (∃ q : PrimeSpectrum T, PrimeSpectrum.comap f q = m'.toPrimeSpectrum) ∧
            ∀ s, (E s).1.asIdeal.IsMaximal := by
    let : m'.asIdeal.IsMaximal := m'.isMaximal
    let : Field (A' ⧸ m'.asIdeal) := Ideal.Quotient.field m'.asIdeal
    obtain ⟨hm, hint, E, hE⟩ := (branches hfin).1 m'
    let f₀ : IsLocalRing.ResidueField A →+* A' ⧸ m'.asIdeal :=
      Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq hm)
    let : Algebra (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) := f₀.toAlgebra
    let : Algebra.IsIntegral (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) := ⟨hint⟩
    let : FaithfulSMul (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
    let : IsAlgClosed kbar := IsAlgClosure.isAlgClosed (IsLocalRing.ResidueField A)
    let σ₀ : A' ⧸ m'.asIdeal →ₐ[IsLocalRing.ResidueField A] kbar := IsAlgClosed.lift
    refine ⟨hm, hint, E, ⟨(E ⟨σ₀.toRingHom, σ₀.comp_algebraMap⟩).1, (E _).2⟩, fun s => ?_⟩
    obtain ⟨φ, hφ, hk, -⟩ := hE s
    exact hk ▸ fibre_kernel_isMaximal m'.asIdeal s.1 e φ hφ
      (Algebra.IsAlgebraic.tower_top (K := IsLocalRing.ResidueField A) (L := ksep))
  constructor
  · rintro ⟨⟨hred, hlocal⟩, hpure⟩
    let : IsDomain Ared := hred
    let : IsLocalRing A' := hlocal
    have hAmin : ∃! p : Ideal A, p ∈ minimalPrimes A :=
      unique_minimalPrimes_of_isDomain_reduction
    have hfin := finite_of_existsUnique_mem hAmin
    let m' : MaximalSpectrum A' := ⟨IsLocalRing.maximalIdeal A', inferInstance⟩
    obtain ⟨-, hmin, hminmax, hmaxmin⟩ := branches hfin
    obtain ⟨hm, -, E, ⟨q, hq⟩, hmaxE⟩ := fib hfin m'
    let : m'.asIdeal.IsMaximal := m'.isMaximal
    let : Field (A' ⧸ m'.asIdeal) := Ideal.Quotient.field m'.asIdeal
    let f₀ : IsLocalRing.ResidueField A →+* A' ⧸ m'.asIdeal :=
      Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq hm)
    let : Algebra (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) := f₀.toAlgebra
    have : IsPurelyInseparable (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) :=
      hpure hred hlocal
    let σ := E.symm ⟨q, hq⟩
    have hqmax : q.asIdeal.IsMaximal := by simpa [σ] using hmaxE σ
    have hTmax : ∃! m : Ideal T, m.IsMaximal := by
      refine ⟨q.asIdeal, hqmax, fun m hmmax => ?_⟩
      let : Algebra.IsIntegral Ash T :=
        ⟨tensor_includeRight_isIntegral (A := A) (B := A') (C := Ash)⟩
      have hcAsh : (m.comap g).IsMaximal := by
        let : m.IsMaximal := hmmax
        exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := Ash) (S := T) g
          (tensor_includeRight_isIntegral (A := A) (B := A') (C := Ash)) m
      have hcA : (m.comap f).comap (algebraMap A A') = IsLocalRing.maximalIdeal A := by
        rw [Ideal.comap_comap]
        have hcomp : f.comp (algebraMap A A') = g.comp (algebraMap A Ash) := by
          ext x
          show (algebraMap A A' x) ⊗ₜ[A] 1 = 1 ⊗ₜ[A] (algebraMap A Ash x)
          exact Algebra.TensorProduct.tmul_one_eq_one_tmul x
        rw [hcomp, ← Ideal.comap_comap, IsLocalRing.eq_maximalIdeal hcAsh]
        ext x
        simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal]
        exact ⟨fun hx hxu => hx (hxu.map _),
          fun hx => map_nonunit (algebraMap A Ash) x hx⟩
      have hc : (m.comap f).IsMaximal := by
        apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) (m.comap f)
        rw [Ideal.under_def, hcA]
        exact IsLocalRing.maximalIdeal.isMaximal A
      have hcm : m.comap f = m'.asIdeal := IsLocalRing.eq_maximalIdeal hc
      let P : PrimeSpectrum T := ⟨m, hmmax.isPrime⟩
      have hP : PrimeSpectrum.comap f P = m'.toPrimeSpectrum := PrimeSpectrum.ext hcm
      let τ := E.symm ⟨P, hP⟩
      let τa : A' ⧸ m'.asIdeal →ₐ[IsLocalRing.ResidueField A] kbar :=
        { τ.1 with commutes' := fun x => DFunLike.congr_fun τ.2 x }
      let σa : A' ⧸ m'.asIdeal →ₐ[IsLocalRing.ResidueField A] kbar :=
        { σ.1 with commutes' := fun x => DFunLike.congr_fun σ.2 x }
      have ha : τa = σa := Subsingleton.elim τa σa
      have hτσ : τ = σ := Subtype.ext (congrArg AlgHom.toRingHom ha)
      simpa [τ, σ] using congrArg (fun x => (E x).1.asIdeal) hτσ
    have hTmin := (unique_maximal_iff_unique_minimal_of_incidence (R := T) hminmax hmaxmin).mp hTmax
    exact existsUnique_mem_of_bijOn_target hmin hTmin
  · intro hAsh
    have hAmin :=
      AlgebraicGeometry.existsUnique_minimalPrime_of_faithfullyFlat (R := A) (S := Ash) hAsh
    have hfin := finite_of_existsUnique_mem hAmin
    let : IsDomain Ared := isDomain_reduction_of_unique_minimalPrimes hAmin
    obtain ⟨-, hmin, hminmax, hmaxmin⟩ := branches hfin
    have hTmin : ∃! q : Ideal T, q ∈ minimalPrimes T :=
      existsUnique_mem_of_bijOn hmin hAsh
    have hTmax : ∃! m : Ideal T, m.IsMaximal :=
      (unique_maximal_iff_unique_minimal_of_incidence (R := T) hminmax hmaxmin).mpr hTmin
    have fibreMax (m' : MaximalSpectrum A') :
        ∃ q : PrimeSpectrum T,
          PrimeSpectrum.comap f q = m'.toPrimeSpectrum ∧ q.asIdeal.IsMaximal := by
      obtain ⟨_, _, E, ⟨q, hq⟩, hmaxE⟩ := fib hfin m'
      exact ⟨q, hq, by simpa using hmaxE (E.symm ⟨q, hq⟩)⟩
    obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A'
    have hA'max : ∃! m : Ideal A', m.IsMaximal := by
      refine ⟨m₀, hm₀, fun m hm => ?_⟩
      obtain ⟨q₀, hq₀, hq₀max⟩ := fibreMax ⟨m₀, hm₀⟩
      obtain ⟨q, hq, hqmax⟩ := fibreMax ⟨m, hm⟩
      have hqq : q = q₀ := PrimeSpectrum.ext (hTmax.unique hqmax hq₀max)
      have := congrArg PrimeSpectrum.asIdeal
        (hq.symm.trans ((congrArg (PrimeSpectrum.comap f) hqq).trans hq₀))
      exact this
    let : IsLocalRing A' := IsLocalRing.of_unique_max_ideal hA'max
    refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
    dsimp only
    intro _ _
    let m' : MaximalSpectrum A' := ⟨IsLocalRing.maximalIdeal A', inferInstance⟩
    let : m'.asIdeal.IsMaximal := m'.isMaximal
    let : Field (A' ⧸ m'.asIdeal) := Ideal.Quotient.field m'.asIdeal
    obtain ⟨hm, hint, E, -, hmaxE⟩ := fib hfin m'
    let f₀ : IsLocalRing.ResidueField A →+* A' ⧸ m'.asIdeal :=
      Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq hm)
    show f₀.IsPurelyInseparable
    rw [RingHom.IsPurelyInseparable]
    let : Algebra (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) := f₀.toAlgebra
    let : Algebra.IsIntegral (IsLocalRing.ResidueField A) (A' ⧸ m'.asIdeal) := ⟨hint⟩
    apply (isPurelyInseparable_iff_subsingleton_emb _ _).2
    constructor
    intro σ τ
    let K := AlgebraicClosure (A' ⧸ m'.asIdeal)
    let : IsAlgClosed kbar := IsAlgClosure.isAlgClosed (IsLocalRing.ResidueField A)
    let ρ : K →ₐ[IsLocalRing.ResidueField A] kbar := IsAlgClosed.lift
    let στ : {s : (A' ⧸ m'.asIdeal) →+* kbar // s.comp f₀ =
        algebraMap (IsLocalRing.ResidueField A) kbar} :=
      ⟨(ρ.comp σ).toRingHom, (ρ.comp σ).comp_algebraMap⟩
    let ττ : {s : (A' ⧸ m'.asIdeal) →+* kbar // s.comp f₀ =
        algebraMap (IsLocalRing.ResidueField A) kbar} :=
      ⟨(ρ.comp τ).toRingHom, (ρ.comp τ).comp_algebraMap⟩
    have hEq : E στ = E ττ :=
      Subtype.ext (PrimeSpectrum.ext (hTmax.unique (hmaxE στ) (hmaxE ττ)))
    have hs : στ = ττ := E.injective hEq
    exact AlgHom.ext fun x => ρ.injective (DFunLike.congr_fun (congrArg Subtype.val hs) x)

/-- A local ring is geometrically unibranch if and only if a strict henselization of it has a
unique minimal prime. -/
@[stacks 06DM, ega "IV 18.8.15" "a) ⇔ c), irreducible"]
theorem isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
    (A Ash : Type u) [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash]
    [Algebra A Ash]
    (ksep : Type v) [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash] :
    IsGeometricallyUnibranch A ↔
      ∃! p : Ideal Ash, p ∈ minimalPrimes Ash := by
  let kbar := AlgebraicClosure (IsLocalRing.ResidueField A)
  let : Algebra (IsLocalRing.ResidueField A) kbar := inferInstance
  let ι : ksep →ₐ[IsLocalRing.ResidueField A] kbar := IsAlgClosed.lift
  let : Algebra ksep kbar := ι.toRingHom.toAlgebra
  let : IsScalarTower (IsLocalRing.ResidueField A) ksep kbar :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  obtain ⟨e, he⟩ :=
    IsLocalRing.IsHenselization.exists_residueFieldEquiv (R := A) (L := ksep) (Rh := Ash)
  exact geometricallyUnibranch_iff_unique_minimalPrime_core A Ash ksep kbar e he

end GeometricallyUnibranch

end

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.TFAE

/-!
# Characterizations of henselian local rings

For a local ring `(R, 𝔪, κ)`, henselianness is equivalent to lifting relatively prime
factorizations from the residue field, to a decomposition of every module-finite algebra
into local factors, to a decomposition of the finite part of every finite type algebra,
and to a splitting property for pointed étale algebras.

## Main definitions

* `IsLocalRing.HasCoprimeFactorizationLifting` is the factorization-lifting condition.
* `IsLocalRing.FiniteAlgebrasSplitIntoLocalFactors` is the finite-algebra condition.
* `IsLocalRing.FiniteTypeAlgebrasSplitOffFiniteLocalFactors` is the finite-type condition.
* `IsLocalRing.PointedEtaleAlgebrasSplit` is the pointed étale condition.

## Main results

* `IsLocalRing.henselian_tfae` states that these four conditions and henselianness are
  equivalent.

## Implementation notes

Irreducible components of the closed fibre are represented by its minimal prime ideals;
the dimension of the component belonging to `p` is `ringKrullDim` of the quotient by `p`.
The residue-field isomorphism in the pointed étale condition is required to commute with
the canonical residue maps.

The equivalence is extracted from the thirteen-item list
`HenselianLocalRing.TFAE_factorization_etale_quasiFinite`, whose items are stated for
algebras in a single universe; the four conditions here quantify over algebras in
`Type (max u v)`, so each transfer passes through a `ULift` of the algebra concerned.

## References

* [Stacks Project, Tag 03QH](https://stacks.math.columbia.edu/tag/03QH)
-/

@[expose] public section

open IsLocalRing Polynomial TensorProduct

universe u v

namespace IsLocalRing

/-- The map of residue fields `κ(𝔪) → κ(n)` sends the class of `r : R` to the class of its image
in `A`. -/
private lemma residueMap_algebraMap_residue
    {R : Type u} {A : Type v} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] (n : Ideal A) [n.IsMaximal]
    (hnR : n.comap (algebraMap R A) = maximalIdeal R) (r : R) :
    Ideal.ResidueField.mapₐ (maximalIdeal R) n (Algebra.ofId R A) hnR.symm
        (algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R r)) =
      algebraMap (A ⧸ n) n.ResidueField (Ideal.Quotient.mk n (algebraMap R A r)) := by
  change Ideal.ResidueField.map (maximalIdeal R) n (Algebra.ofId R A).toRingHom
    (by simpa using hnR.symm) (algebraMap (R ⧸ maximalIdeal R) _ (Ideal.Quotient.mk _ r)) =
      algebraMap (A ⧸ n) _ (Ideal.Quotient.mk n (algebraMap R A r))
  rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk]
  exact Ideal.ResidueField.map_algebraMap _ _ _ (by simpa using hnR.symm) r

/-- From a residue-field identification `κ(R) ≃+* A ⧸ n` commuting with the residue maps,
the canonical map of residue fields `κ(𝔪) → κ(n)` is bijective. -/
private lemma residueMapBijective_of_residueQuotientEquiv
    {R : Type u} {A : Type v} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] (n : Ideal A) [hn : n.IsMaximal]
    (hnR : n.comap (algebraMap R A) = maximalIdeal R)
    (eκ : ResidueField R ≃+* A ⧸ n)
    (hκ : eκ.toRingHom.comp (residue R) =
      (Ideal.Quotient.mk n).comp (algebraMap R A)) :
    Function.Bijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) n (Algebra.ofId R A) hnR.symm) := by
  let qR : ResidueField R ≃+* Ideal.ResidueField (maximalIdeal R) :=
    RingEquiv.ofBijective (algebraMap _ _)
      (maximalIdeal R).bijective_algebraMap_quotient_residueField
  let qA : (A ⧸ n) ≃+* Ideal.ResidueField n :=
    RingEquiv.ofBijective (algebraMap _ _) n.bijective_algebraMap_quotient_residueField
  have hm : (Ideal.ResidueField.mapₐ (maximalIdeal R) n (Algebra.ofId R A) hnR.symm).toRingHom =
      qA.toRingHom.comp (eκ.toRingHom.comp qR.symm.toRingHom) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := qR.surjective x
    obtain ⟨r, rfl⟩ := residue_surjective y
    refine (residueMap_algebraMap_residue n hnR r).trans ?_
    change _ = qA (eκ (qR.symm (qR (residue R r))))
    rw [qR.symm_apply_apply]
    exact congrArg qA (RingHom.congr_fun hκ r).symm
  change Function.Bijective
    (Ideal.ResidueField.mapₐ (maximalIdeal R) n (Algebra.ofId R A) hnR.symm).toRingHom
  rw [hm]
  exact qA.bijective.comp (eκ.bijective.comp qR.symm.bijective)

/-- If the canonical map of residue fields `κ(𝔪) → κ(n)` is bijective, then `κ(R)` is
identified with `A ⧸ n` compatibly with the residue maps. -/
private lemma residueQuotientEquiv_of_residueMapBijective
    {R : Type u} {A : Type v} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] (n : Ideal A) [hn : n.IsMaximal]
    (hnR : n.comap (algebraMap R A) = maximalIdeal R)
    (hbij : Function.Bijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) n (Algebra.ofId R A)
        (by simpa using hnR.symm))) :
    ∃ eκ : ResidueField R ≃+* A ⧸ n,
      eκ.toRingHom.comp (residue R) =
        (Ideal.Quotient.mk n).comp (algebraMap R A) := by
  let qR : ResidueField R ≃+* Ideal.ResidueField (maximalIdeal R) :=
    RingEquiv.ofBijective (algebraMap _ _)
      (maximalIdeal R).bijective_algebraMap_quotient_residueField
  let qA : (A ⧸ n) ≃+* Ideal.ResidueField n :=
    RingEquiv.ofBijective (algebraMap _ _) n.bijective_algebraMap_quotient_residueField
  refine ⟨qR.trans ((RingEquiv.ofBijective _ hbij).trans qA.symm), ?_⟩
  ext r
  exact qA.symm_apply_eq.mpr (residueMap_algebraMap_residue n hnR r)

/-- An étale `R`-algebra `A` admitting an `R`-algebra retraction `τ` splits as `R × A'`,
with the first projection given by `τ` and with the preimage of an ideal `J` of `R` going
over to `J × A'`. -/
private lemma exists_algEquiv_prod_of_etale_retraction
    {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (J : Ideal R) (n : Ideal A) (τ : A →ₐ[R] R)
    (hτ : J.comap τ.toRingHom = n) :
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra R A'),
      ∃ e : A ≃ₐ[R] R × A', n.map e.toRingEquiv.toRingHom =
        Ideal.prod J ⊤ ∧ ∀ x, (e x).1 = τ x := by
  let : Algebra A R := τ.toRingHom.toAlgebra
  have : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq fun r => (τ.commutes r).symm
  have hsurj : Function.Surjective τ := fun r => ⟨algebraMap R A r, τ.commutes r⟩
  have : Algebra.FormallyEtale A R :=
    Algebra.FormallyEtale.of_restrictScalars (R := R) (A := A) (B := R)
  have hidem : IsIdempotentElem (RingHom.ker τ.toRingHom) :=
    (Algebra.FormallyEtale.iff_of_surjective hsurj).mp inferInstance
  have hfg : (RingHom.ker τ.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective τ hsurj
  obtain ⟨e₀, he₀, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hidem
  have hspan' : RingHom.ker τ = Ideal.span {e₀} := hspan
  let qeq : (A ⧸ Ideal.span {e₀}) ≃ₐ[R] R :=
    (Ideal.quotientEquivAlgOfEq R hspan'.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have hqeq (x : A) : qeq (Ideal.Quotient.mk _ x) = τ x := by
    simp [qeq, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  let split := AlgEquiv.prodQuotientOfIsIdempotentElem (R := R) he₀ he₀.one_sub
    (by ring) (by simp [he₀])
  let e0 : A ≃ₐ[R] R × (A ⧸ Ideal.span {1 - e₀}) :=
    split.trans (AlgEquiv.prodCongr qeq
      (AlgEquiv.refl : (A ⧸ Ideal.span {1 - e₀}) ≃ₐ[R] _))
  let e : A ≃ₐ[R] R × ULift.{max u v} (A ⧸ Ideal.span {1 - e₀}) :=
    e0.trans (AlgEquiv.prodCongr (AlgEquiv.refl : R ≃ₐ[R] R) ULift.algEquiv.symm)
  have hfst (x : A) : (e x).1 = τ x := by
    simp [e, e0, split, hqeq]
  refine ⟨ULift.{max u v} (A ⧸ Ideal.span {1 - e₀}), inferInstance, inferInstance,
    e, ?_, hfst⟩
  have heq : (Ideal.prod J ⊤).comap e.toRingEquiv.toRingHom = n := by
    rw [← hτ]
    ext x
    simp [Ideal.prod, hfst]
  rw [← heq]
  exact Ideal.map_comap_of_surjective e.toRingEquiv.toRingHom e.surjective _

/-- If a finite type `R`-algebra `B` is quasi-finite at no prime lying over the maximal
ideal of `R`, then every irreducible component of its closed fibre has dimension at least
one. -/
private lemma one_le_ringKrullDim_quotient_of_no_quasiFiniteAt
    {R : Type u} {B : Type v} [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (hB : ∀ (q : Ideal B) [q.IsPrime], q.LiesOver (maximalIdeal R) →
      ¬ Algebra.QuasiFiniteAt R q)
    (p : Ideal (ResidueField R ⊗[R] B))
    (hp : p ∈ minimalPrimes (ResidueField R ⊗[R] B)) :
    1 ≤ ringKrullDim ((ResidueField R ⊗[R] B) ⧸ p) := by
  by_contra hcon
  have hpp : p.IsPrime := hp.isPrime
  have hKD : Ring.KrullDimLE 0 ((ResidueField R ⊗[R] B) ⧸ p) :=
    Ring.krullDimLE_iff.mpr (Order.le_of_lt_succ (not_le.mp hcon))
  have hpmax : p.IsMaximal := by
    have hbot : (⊥ : Ideal ((ResidueField R ⊗[R] B) ⧸ p)).IsMaximal :=
      Ring.krullDimLE_zero_iff.mp hKD ⊥ inferInstance
    have hcm := Ideal.comap_isMaximal_of_surjective (K := (⊥ : Ideal _))
      (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcm
  have hsurjres : Function.Surjective (algebraMap R (maximalIdeal R).ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have hkerres :
      RingHom.ker (algebraMap R (maximalIdeal R).ResidueField) = maximalIdeal R := by
    ext x
    simp
  let β : ResidueField R ≃ₐ[R] (maximalIdeal R).ResidueField :=
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq hkerres.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurjres)) (fun _ => rfl)
  let Φ : (ResidueField R ⊗[R] B) ≃ₐ[R] (maximalIdeal R).Fiber B :=
    Algebra.TensorProduct.congr β AlgEquiv.refl
  let ee := PrimeSpectrum.comapEquiv (Φ.toRingEquiv)
  set P : PrimeSpectrum (ResidueField R ⊗[R] B) := ⟨p, hpp⟩
  set Q : PrimeSpectrum ((maximalIdeal R).Fiber B) := ee P
  have hminQ : IsMin Q := ee.isMin_apply.2 (PrimeSpectrum.isMin_iff.mpr hp)
  have hmaxQ : IsMax Q := ee.isMax_apply.2 (PrimeSpectrum.isMax_iff.mpr hpmax)
  have : IsNoetherianRing ((maximalIdeal R).Fiber B) :=
    Algebra.FiniteType.isNoetherianRing (maximalIdeal R).ResidueField _
  have : IsJacobsonRing ((maximalIdeal R).Fiber B) :=
    isJacobsonRing_of_finiteType (A := (maximalIdeal R).ResidueField)
  have hopen : IsOpen ({Q} : Set (PrimeSpectrum ((maximalIdeal R).Fiber B))) := by
    have htfae :=
      (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing Q).out 3 1
    refine htfae.mp ⟨(PrimeSpectrum.isClosed_singleton_iff_isMaximal Q).mpr
      (PrimeSpectrum.isMax_iff.mp hmaxQ), ?_⟩
    intro x y hyx hx
    rw [Set.mem_singleton_iff] at hx ⊢
    rw [hx] at hyx
    have hle : y ≤ Q := (PrimeSpectrum.le_iff_specializes y Q).mpr hyx
    exact le_antisymm hle (hminQ hle)
  have hqfQ : Algebra.QuasiFiniteAt ((maximalIdeal R).ResidueField) Q.asIdeal :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton Q hopen
  set q : Ideal B := Ideal.comap (Algebra.TensorProduct.includeRight.toRingHom) Q.asIdeal
    with hq
  have hlo : q.LiesOver (maximalIdeal R) := by
    refine ⟨?_⟩
    have h3 : (Algebra.TensorProduct.includeRight.toRingHom :
          B →+* (maximalIdeal R).Fiber B).comp (algebraMap R B)
        = algebraMap R ((maximalIdeal R).Fiber B) := by
      ext r
      simp
    have h2 : Ideal.under R q = Ideal.under R Q.asIdeal := by
      rw [hq, Ideal.under_def, Ideal.under_def, Ideal.comap_comap, h3]
    rw [h2]
    exact (inferInstance : Q.asIdeal.LiesOver (maximalIdeal R)).over
  exact hB q hlo
    (Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField (maximalIdeal R) q Q.asIdeal rfl)

/-- A module-finite algebra all of whose closed-fibre components have dimension at least
one is the zero ring: its closed fibre is Artinian, so has a component of dimension zero
unless it is trivial, and Nakayama then kills the algebra. -/
private lemma subsingleton_of_one_le_ringKrullDim_closedFibre
    {R : Type u} {C : Type v} [CommRing R] [IsLocalRing R]
    [CommRing C] [Algebra R C] [Module.Finite R C]
    (hpos : ∀ p ∈ minimalPrimes (ResidueField R ⊗[R] C),
      1 ≤ ringKrullDim ((ResidueField R ⊗[R] C) ⧸ p)) :
    Subsingleton C := by
  let F := ResidueField R ⊗[R] C
  have : IsArtinianRing F := IsArtinianRing.of_finite (ResidueField R) F
  have hF : Subsingleton F := by
    by_contra hF
    let : Nontrivial F := not_subsingleton_iff_nontrivial.mp hF
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal F)) bot_ne_top
    have : p.IsPrime := hp.isPrime
    have hdim : 1 ≤ ringKrullDim (F ⧸ p) := hpos p hp
    rw [ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp inferInstance)] at hdim
    norm_num at hdim
  exact (IsLocalRing.subsingleton_tensorProduct (R := R) (M := C)).mp hF

/-- Relatively prime factorizations of the reduction of a polynomial lift from the
residue field to the local ring. This is condition (2) of Tag 03QH. -/
abbrev HasCoprimeFactorizationLifting (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (f : R[X]) (g₀ h₀ : (ResidueField R)[X]),
    f.map (residue R) = g₀ * h₀ → IsCoprime g₀ h₀ →
      ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀

/-- Every module-finite algebra over `R` is a finite product of module-finite local
`R`-algebras. This is condition (3) of Tag 03QH. -/
abbrev FiniteAlgebrasSplitIntoLocalFactors
    (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Module.Finite R S],
    ∃ (n : ℕ) (A : Fin n → Type (max u v))
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i)),
      (∀ i, IsLocalRing (A i)) ∧ (∀ i, Module.Finite R (A i)) ∧
        Nonempty (S ≃ₐ[R] (∀ i, A i))

/-- Every finite type algebra over `R` splits into finitely many module-finite local
factors and a factor whose closed-fibre irreducible components have dimension at least
one. This is condition (4) of Tag 03QH. -/
abbrev FiniteTypeAlgebrasSplitOffFiniteLocalFactors
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    ∃ (n : ℕ) (A : Fin n → Type (max u v))
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i)),
      (∀ i, IsLocalRing (A i)) ∧ (∀ i, Module.Finite R (A i)) ∧
        ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C),
          (∀ p ∈ minimalPrimes (ResidueField R ⊗[R] C),
            1 ≤ ringKrullDim ((ResidueField R ⊗[R] C) ⧸ p)) ∧
          Nonempty (S ≃ₐ[R] (∀ i, A i) × C)

/-- A pointed étale algebra whose distinguished closed point has the same residue field
as `R` splits off a copy of `R`, with the distinguished ideal on that factor. This is
condition (5) of Tag 03QH. -/
abbrev PointedEtaleAlgebrasSplit
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (n : Ideal A) (_hn : n.IsMaximal)
    (_hnR : n.comap (algebraMap R A) = maximalIdeal R)
    (_hκ : ∃ eκ : ResidueField R ≃+* A ⧸ n,
      eκ.toRingHom.comp (residue R) =
        (Ideal.Quotient.mk n).comp (algebraMap R A)),
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra R A')
      (e : A ≃ₐ[R] R × A'),
      n.map e.toRingEquiv.toRingHom = Ideal.prod (maximalIdeal R) ⊤

/-- **Stacks 03QH.** The five standard characterizations of a henselian local ring:
henselianness, coprime factorization lifting, decomposition of module-finite algebras,
splitting the finite part of finite type algebras, and splitting pointed étale
algebras. -/
@[stacks 03QH,
  ega "IV 18.5.13" "a'') existence half",
  ega "IV 18.5.9" "(ii)",
  ega "IV 18.5.11" "a), a'), b)",
  sga "4 VIII 4.1" "(i), (iii), (iv)",
  sga "3 X 4.5" "special case",
  sga "7 IX 2.2.3" "(4), special case"]
theorem henselian_tfae (R : Type u) [CommRing R] [IsLocalRing R] :
    List.TFAE [HenselianLocalRing R,
      HasCoprimeFactorizationLifting R,
      FiniteAlgebrasSplitIntoLocalFactors.{u, v} R,
      FiniteTypeAlgebrasSplitOffFiniteLocalFactors.{u, v} R,
      PointedEtaleAlgebrasSplit.{u, v} R] := by
  have h := HenselianLocalRing.TFAE_factorization_etale_quasiFinite R
  tfae_have 1 ↔ 2 := by
    simpa [HasCoprimeFactorizationLifting] using h.out 1 5
  tfae_have 1 → 3 := fun _ S => exists_algEquiv_pi_isLocalRing R S
  tfae_have 3 → 1 := by
    refine fun h3 => (h.out 10 1).mp ?_
    intro S _ _ _
    obtain ⟨n, A, _, _, _, _, ⟨e⟩⟩ := h3 (ULift.{max u v, u} S)
    have : ∀ i, Small.{u} (A i) := fun i => Module.Finite.small R (A i)
    let A' : Fin n → Type u := fun i => Shrink.{u} (A i)
    let eA : (∀ i, A i) ≃ₐ[R] (∀ i, A' i) :=
      AlgEquiv.piCongrRight fun i => (Shrink.algEquiv R (A i)).symm
    let ι : Type u := ULift.{u} (Fin n)
    let eι : Fin n ≃ ι := Equiv.ulift.symm
    let A'' : ι → Type u := fun i => A' (eι.symm i)
    let : ∀ i, CommRing (A'' i) := fun i => inferInstance
    have : ∀ i, IsLocalRing (A'' i) := fun i =>
      (Shrink.algEquiv R (A (eι.symm i))).symm.toRingEquiv.isLocalRing
    exact ⟨ι, inferInstance, A'', inferInstance, inferInstance,
      ⟨((ULift.algEquiv.symm.trans e).trans eA).toRingEquiv.trans
        (RingEquiv.piCongrLeft' A' eι)⟩⟩
  tfae_have 1 → 4 := by
    intro hR S _ _ _
    obtain ⟨n, Af, hcommAf, halgAf, hlocAf, hfinAf, B, hcommB, halgB, hqf, ⟨e⟩⟩ :=
      exists_algEquiv_prod_of_henselianLocalRing R S
    have : Algebra.FiniteType R B := Algebra.FiniteType.of_surjective
      ((AlgHom.snd R (∀ i, Af i) B).comp (e : S →ₐ[R] (∀ i, Af i) × B))
      (Prod.snd_surjective.comp e.surjective)
    exact ⟨n, Af, hcommAf, halgAf, hlocAf, hfinAf, B, hcommB, halgB,
      one_le_ringKrullDim_quotient_of_no_quasiFiniteAt hqf, ⟨e⟩⟩
  tfae_have 4 → 3 := by
    intro h4 S _ _ _
    obtain ⟨n, A, hcomm, halg, hloc, hfinite, C, _, _, hdim, ⟨e⟩⟩ := h4 S
    have : Module.Finite R ((∀ i, A i) × C) := Module.Finite.equiv e.toLinearEquiv
    have : Module.Finite R C := Module.Finite.of_surjective
      (AlgHom.snd R (∀ i, A i) C).toLinearMap Prod.snd_surjective
    have : Subsingleton C := subsingleton_of_one_le_ringKrullDim_closedFibre hdim
    let : Unique C := uniqueOfSubsingleton (0 : C)
    exact ⟨n, A, hcomm, halg, hloc, hfinite,
      ⟨e.trans (AlgEquiv.prodUnique (R := R) (A := ∀ i, A i) (B := C))⟩⟩
  tfae_have 1 → 5 := by
    rintro hR A _ _ _ n hn hnR ⟨eκ, hκ⟩
    obtain ⟨τ, hτ⟩ := henselian_etale_retraction R A n hnR
      (residueMapBijective_of_residueQuotientEquiv n hnR eκ hκ)
    obtain ⟨A', _, _, e, he, -⟩ :=
      exists_algEquiv_prod_of_etale_retraction (maximalIdeal R) n τ hτ
    exact ⟨A', inferInstance, inferInstance, e, he⟩
  tfae_have 5 → 1 := by
    refine fun h5 => (h.out 7 1).mp ?_
    intro S _ algS _ q _ _ hbij
    have : q.IsMaximal := by
      have hsurj : Function.Surjective (algebraMap S q.ResidueField) := by
        intro x
        obtain ⟨y, hy⟩ := hbij.2 x
        obtain ⟨r, hr⟩ := (maximalIdeal R).algebraMap_residueField_surjective y
        refine ⟨algebraMap R S r, ?_⟩
        rw [← Ideal.ResidueField.map_algebraMap (maximalIdeal R) q
          (algebraMap R S) (q.over_def _) r, hr]
        exact hy
      rw [← Ideal.ker_algebraMap_residueField (I := q)]
      exact RingHom.ker_isMaximal_of_surjective _ hsurj
    have hnR : q.comap (algebraMap R S) = maximalIdeal R := (q.over_def _).symm
    let S' : Type (max u v) := ULift.{max u v, u} S
    let : CommRing S' := inferInstance
    let : Algebra R S' := @ULift.algebra R S _ _ algS
    let eULift : ULift.{max u v, u} S ≃ₐ[R] S := ULift.algEquiv (R := R) (A := S)
    have : Algebra.Etale R S' := Algebra.Etale.of_equiv eULift.symm
    let q' : Ideal S' := q.comap eULift.toRingHom
    have : q'.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (f := eULift.toRingHom) (K := q) eULift.surjective
    have hnR' : q'.comap (algebraMap R S') = maximalIdeal R := by
      ext r
      change eULift (algebraMap R S' r) ∈ q ↔ r ∈ maximalIdeal R
      rw [eULift.commutes]
      exact Iff.of_eq
        ((congrArg (fun I : Ideal R => r ∈ I) (q.over_def (maximalIdeal R))).symm)
    obtain ⟨eκ, heκ⟩ := residueQuotientEquiv_of_residueMapBijective
      (R := R) (A := S) q hnR hbij
    let eQ : S' ⧸ q' ≃+* S ⧸ q := Ideal.quotientEquiv q' q eULift.toRingEquiv
      (Ideal.map_comap_of_surjective eULift.toRingEquiv.toRingHom eULift.surjective q).symm
    let eκ' : ResidueField R ≃+* S' ⧸ q' := eκ.trans eQ.symm
    have heκ' : eκ'.toRingHom.comp (residue R) =
        (Ideal.Quotient.mk q').comp (algebraMap R S') := by
      refine RingHom.ext fun r => eQ.injective ?_
      change eQ (eκ' (residue R r)) = eQ (Ideal.Quotient.mk q' (algebraMap R S' r))
      rw [show eκ' (residue R r) = eQ.symm (eκ (residue R r)) from rfl,
        RingEquiv.apply_symm_apply]
      change eκ (residue R r) = Ideal.Quotient.mk q (eULift (algebraMap R S' r))
      rw [eULift.commutes]
      change eκ.toRingHom (residue R r) = Ideal.Quotient.mk q (algebraMap R S r)
      simpa only [RingHom.comp_apply] using congrArg (fun f : R →+* S ⧸ q => f r) heκ
    obtain ⟨A', _, _, e, _⟩ := h5 S' q' inferInstance hnR' ⟨eκ', heκ'⟩
    exact ⟨(AlgHom.fst R R A').comp e.toAlgHom |>.comp eULift.symm.toAlgHom⟩
  tfae_finish

end IsLocalRing

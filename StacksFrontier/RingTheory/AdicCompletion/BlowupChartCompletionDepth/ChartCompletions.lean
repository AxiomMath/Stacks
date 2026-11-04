module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationDimensionBounds
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineChart
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzZeroSchemeImprovementHypotheses
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibre
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.AdicCompletion.AdicCompletionMapUniqueness
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibreUniverse
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Dualizing.UbiquityStability
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.Catenary.Localization
import all StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibreUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Completions of an affine blowup chart and of its base

This file defines, for a prime `Q` of the affine blowup algebra `A[I/f]` lying over `𝔮 ⊂ A`, the
`I`-adic completions `R = (A_𝔮)^∧` and `R' = (A[I/f]_Q)^∧` and the map `φ : R → R'`, together with
the commutative algebra used to compare depth and dimension along `φ`: a one-dimensional quotient
cut out by an element of the Jacobson radical, localizations of birational algebras, the depth
formula (Stacks 0338) at a pair of primes where a map is flat, residue fields along residually
trivial maps, base change of an affine blowup algebra, and fibres of completions read through
an isomorphism.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.Algebraization

/-! ### A one-dimensional quotient cut out by an element of the Jacobson radical -/

/-- **A prime meeting `V(t)` only at one maximal ideal has a quotient of dimension at most one.**
Let `R` be Noetherian, `t` an element of the Jacobson radical and `𝔭` a prime such that every
prime containing `𝔭` and `t` is a fixed maximal ideal `𝔪`. Then `R ⧸ 𝔭` is local with maximal
ideal `𝔪 ⧸ 𝔭`, which is minimal over `t`, so `dim (R ⧸ 𝔭) ≤ 1` by Krull's principal ideal
theorem. -/
theorem ringKrullDim_quotient_le_one_of_le_jacobson {R : Type*} [CommRing R]
    [IsNoetherianRing R] {t : R} (ht : Ideal.span {t} ≤ Ideal.jacobson ⊥) (p : Ideal R)
    [p.IsPrime] (m : Ideal R) [m.IsMaximal]
    (h : ∀ P : Ideal R, P.IsPrime → p ≤ P → t ∈ P → P = m) :
    ringKrullDim (R ⧸ p) ≤ 1 := by
  have htJ : ∀ P : Ideal R, P.IsMaximal → t ∈ P := fun P hP =>
    Ideal.mem_sInf.mp (ht (Ideal.mem_span_singleton_self t)) ⟨bot_le, hP⟩
  have hpm : p ≤ m := by
    obtain ⟨P, hP, hpP⟩ := Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top ‹_›)
    exact h P hP.isPrime hpP (htJ P hP) ▸ hpP
  have hpne : p ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hpne
  have hmmap : (m.map (Ideal.Quotient.mk p)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hpm)
  have hcomap : ∀ P : Ideal (R ⧸ p), P.IsPrime → t ∈ P.comap (Ideal.Quotient.mk p) →
      P = m.map (Ideal.Quotient.mk p) := by
    intro P hP htP
    have hP' := h (P.comap (Ideal.Quotient.mk p)) (Ideal.IsPrime.comap _)
      (fun x hx => by
        show Ideal.Quotient.mk p x ∈ P
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P.zero_mem) htP
    rw [← hP', Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have : IsLocalRing (R ⧸ p) := by
    refine IsLocalRing.of_unique_max_ideal ⟨m.map (Ideal.Quotient.mk p), hmmap, fun P hP => ?_⟩
    refine hcomap P hP.isPrime ?_
    exact htJ _ (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hM : maximalIdeal (R ⧸ p) = m.map (Ideal.Quotient.mk p) :=
    (IsLocalRing.eq_maximalIdeal hmmap).symm
  have hle := ringKrullDim_quotient_le_one_of_forall_prime_eq (R := R ⧸ p) ⊥
    (a := Ideal.Quotient.mk p t) (by
      rw [hM]; exact Ideal.mem_map_of_mem _ (htJ m inferInstance))
    (fun P hP _ htP => by rw [hM]; exact hcomap P hP htP)
  rwa [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (R ⧸ p))] at hle

/-! ### Localizations of an algebra which is birational away from an element -/

/-- **A localization of an algebra birational away from `f` is a localization of the base.**
Let `T₀` be an `R`-algebra and `f : R` such that every element of `T₀` becomes an element of the
image of `R` after multiplication by a power of `f`, and such that an element of `R` dying in
`T₀` is killed by a power of `f`; that is, `R_f → T₀_f` is an isomorphism. Then for every prime
`P` of `T₀` not containing `f`, the localization `T₀_P` is the localization of `R` at the
contracted prime `P ∩ R`. -/
theorem isLocalization_atPrime_comap_of_pow_mul {R T₀ L : Type*} [CommRing R] [CommRing T₀]
    [CommRing L] [Algebra R T₀] [Algebra T₀ L] [Algebra R L] [IsScalarTower R T₀ L] (f : R)
    (h₁ : ∀ t : T₀, ∃ (n : ℕ) (r : R), algebraMap R T₀ (f ^ n) * t = algebraMap R T₀ r)
    (h₂ : ∀ r : R, algebraMap R T₀ r = 0 → ∃ n : ℕ, f ^ n * r = 0)
    (P : Ideal T₀) [P.IsPrime] (hf : algebraMap R T₀ f ∉ P) [IsLocalization.AtPrime L P] :
    IsLocalization.AtPrime L (P.comap (algebraMap R T₀)) := by
  have hsP : ∀ (u : P.primeCompl) (m : ℕ) (s : R), algebraMap R T₀ (f ^ m) * u =
      algebraMap R T₀ s → ∀ n : ℕ, algebraMap R T₀ (f ^ n * s) ∉ P := by
    intro u m s hs n
    rw [map_mul, ← hs, ← mul_assoc, ← map_mul, ← pow_add, map_pow]
    exact fun h => (‹P.IsPrime›.mem_or_mem h).elim
      (fun h' => hf (‹P.IsPrime›.mem_of_pow_mem _ h')) u.2
  refine ⟨fun s => ?_, fun z => ?_, fun {r₁ r₂} hr => ?_⟩
  · rw [IsScalarTower.algebraMap_apply R T₀ L]
    exact IsLocalization.map_units L (⟨algebraMap R T₀ s, s.2⟩ : P.primeCompl)
  · obtain ⟨⟨t, u⟩, htu⟩ := IsLocalization.surj P.primeCompl z
    obtain ⟨n, r, hr⟩ := h₁ t
    obtain ⟨m, s, hs⟩ := h₁ u
    refine ⟨⟨f ^ m * r, ⟨f ^ n * s, hsP u m s hs n⟩⟩, ?_⟩
    show z * algebraMap R L (f ^ n * s) = algebraMap R L (f ^ m * r)
    simp only [IsScalarTower.algebraMap_apply R T₀ L, map_mul]
    rw [← hs, ← hr]
    simp only [map_mul]
    rw [← htu]
    ring
  · have h0 : algebraMap R L (r₁ - r₂) = 0 := by rw [map_sub, hr, sub_self]
    rw [IsScalarTower.algebraMap_apply R T₀ L,
      IsLocalization.map_eq_zero_iff P.primeCompl] at h0
    obtain ⟨u, hu⟩ := h0
    obtain ⟨m, s, hs⟩ := h₁ u
    have hsr : algebraMap R T₀ (s * (r₁ - r₂)) = 0 := by
      rw [map_mul, ← hs, mul_assoc, hu, mul_zero]
    obtain ⟨k, hk⟩ := h₂ _ hsr
    refine ⟨⟨f ^ k * s, hsP u m s hs k⟩, ?_⟩
    show f ^ k * s * r₁ = f ^ k * s * r₂
    rw [← sub_eq_zero, ← mul_sub, mul_assoc, hk]

/-- **An algebra birational away from `f` is algebraic.** Let `R` be a domain and `f ≠ 0` an
element of `R` such that every element of `T₀` times a power of `f` lies
in the image of `R`. Then `T₀` is algebraic over `R`: `t` is a root of `fⁿ X - r`. -/
theorem isAlgebraic_of_pow_mul {R T₀ : Type*} [CommRing R] [CommRing T₀] [Algebra R T₀]
    [IsDomain R] {f : R} (hf : f ≠ 0)
    (h₁ : ∀ t : T₀, ∃ (n : ℕ) (r : R), algebraMap R T₀ (f ^ n) * t = algebraMap R T₀ r) :
    Algebra.IsAlgebraic R T₀ := by
  refine ⟨fun t => ?_⟩
  obtain ⟨n, r, hr⟩ := h₁ t
  refine ⟨Polynomial.C (f ^ n) * Polynomial.X - Polynomial.C r, fun h0 => ?_, ?_⟩
  · have := congrArg (Polynomial.coeff · 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      Polynomial.coeff_zero, one_ne_zero, if_false, sub_zero, if_true] at this
    exact pow_ne_zero n hf this
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [hr, sub_self]

/-! ### Depth along a map which is flat at a pair of primes -/

/-- **The depth formula at a pair of primes.** Let `φ : R → R'` be a map of Noetherian rings,
`𝔭'` a prime of `R'` and `𝔭 = φ⁻¹𝔭'`, and suppose `R_𝔭 → R'_{𝔭'}` is flat. Then for a finite
`R`-module `M`,
`depth (R' ⊗_R M)_{𝔭'} = depth M_𝔭 + depth (R'_{𝔭'}/𝔭R'_{𝔭'})`.

This is Stacks 0338 for the flat local homomorphism `R_𝔭 → R'_{𝔭'}`, read through the
identification `(R' ⊗_R M)_{𝔭'} = R'_{𝔭'} ⊗_{R_𝔭} M_𝔭`. -/
@[ega "IV 6.3.1" "special case",
  ega "IV 6.3.4" "(6.3.4.1) with N = B",
  sga "2 III 2.11" "special case"]
theorem depth_localizedModule_tensorProduct_eq_add {R R' : Type*} [CommRing R] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing R'] (φ : R →+* R') (p' : Ideal R') [p'.IsPrime]
    (hflat : (Localization.localRingHom (p'.comap φ) p' φ rfl).Flat)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    letI := φ.toAlgebra
    Module.depth (Localization.AtPrime p') (maximalIdeal _)
        (LocalizedModule p'.primeCompl (TensorProduct R R' M)) =
      Module.depth (Localization.AtPrime (p'.comap φ)) (maximalIdeal _)
          (LocalizedModule (p'.comap φ).primeCompl M) +
        Module.depth (Localization.AtPrime p') (maximalIdeal _)
          (Localization.AtPrime p' ⧸
            (p'.comap φ).map (algebraMap R (Localization.AtPrime p'))) := by
  let := φ.toAlgebra
  set p := p'.comap φ with hp
  let Rp := Localization.AtPrime p
  let S := Localization.AtPrime p'
  let : Algebra Rp S := (Localization.localRingHom p p' φ rfl).toAlgebra
  have : IsScalarTower R Rp S := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R S r = Localization.localRingHom p p' φ rfl (algebraMap R Rp r)
    rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R R' S]
    rfl
  have : Module.Flat Rp S := RingHom.flat_algebraMap_iff.mp hflat
  have : IsLocalHom (algebraMap Rp S) := Localization.isLocalHom_localRingHom _ _ _ _
  have : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing p'.primeCompl S inferInstance
  have h0338 := Module.depth_tensorProduct_of_flat (R := Rp) (S := S)
    (M := LocalizedModule p.primeCompl M) (N := S)
  let N := TensorProduct R R' M
  let e1 : TensorProduct R Rp M ≃ₗ[Rp] LocalizedModule p.primeCompl M :=
    (IsLocalizedModule.isBaseChange p.primeCompl Rp
      (LocalizedModule.mkLinearMap p.primeCompl M)).equiv
  let e2 : TensorProduct Rp S (TensorProduct R Rp M) ≃ₗ[S]
      TensorProduct Rp S (LocalizedModule p.primeCompl M) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e1
  let e3 : TensorProduct Rp S (TensorProduct R Rp M) ≃ₗ[S] TensorProduct R S M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp S S M
  let e4 : TensorProduct R' S (TensorProduct R R' M) ≃ₗ[S] TensorProduct R S M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R' S S M
  let e5 : TensorProduct R' S N ≃ₗ[S] LocalizedModule p'.primeCompl N :=
    (IsLocalizedModule.isBaseChange p'.primeCompl S
      (LocalizedModule.mkLinearMap p'.primeCompl N)).equiv
  let e : LocalizedModule p'.primeCompl N ≃ₗ[S]
      TensorProduct Rp S (LocalizedModule p.primeCompl M) :=
    e5.symm.trans (e4.trans (e3.symm.trans e2))
  have hfib : ((maximalIdeal Rp).map (algebraMap Rp S) • (⊤ : Submodule S S)) =
      (p.map (algebraMap R S) : Submodule S S) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [Module.depth_eq_depth_of_linearEquiv (maximalIdeal S) e, h0338,
    Module.depth_eq_depth_of_linearEquiv (maximalIdeal S) (Submodule.quotEquivOfEq _ _ hfib)]

/-! ### Flatness at a pair of primes through an intermediate localization -/

/-- **Flatness at a pair of primes through a ring that is a localization there.** Let
`R → T → R'` be ring maps with `ψ : T → R'` flat, let `𝔭'` be a prime of `R'`, `𝔭_T = ψ⁻¹𝔭'`
and `𝔭 = 𝔭_T ∩ R`, and suppose `T_{𝔭_T}` is the localization of `R` at `𝔭`. Then
`R_𝔭 → R'_{𝔭'}` is flat: it is `R_𝔭 ≅ T_{𝔭_T} → R'_{𝔭'}`, and the second map is a localization
of `ψ`. -/
theorem flat_localRingHom_comp_of_isLocalization {R T R' : Type*} [CommRing R] [CommRing T]
    [CommRing R'] [Algebra R T] (ψ : T →+* R') (hψ : ψ.Flat) (p' : Ideal R') [p'.IsPrime]
    [IsLocalization.AtPrime (Localization.AtPrime (p'.comap ψ))
      ((p'.comap ψ).comap (algebraMap R T))] :
    (Localization.localRingHom (p'.comap (ψ.comp (algebraMap R T))) p'
      (ψ.comp (algebraMap R T)) rfl).Flat := by
  set pT := p'.comap ψ
  set p := pT.comap (algebraMap R T)
  have hg1 : Function.Bijective (Localization.localRingHom p pT (algebraMap R T) rfl) := by
    have : Localization.localRingHom p pT (algebraMap R T) rfl =
        (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
          (Localization.AtPrime pT)).toRingEquiv.toRingHom := by
      refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun r => ?_)
      simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
      show _ = IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
        (Localization.AtPrime pT) (algebraMap R (Localization.AtPrime p) r)
      rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R T (Localization.AtPrime pT)]
    rw [this]
    exact (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime pT)).bijective
  have hcomp := Localization.localRingHom_comp p pT p' (algebraMap R T) rfl ψ rfl
  show (Localization.localRingHom p p' (ψ.comp (algebraMap R T)) _).Flat
  rw [hcomp]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective hg1) (hψ.localRingHom p' pT rfl)

/-- The ring map `B → R ⊗_A B` is flat when `R` is flat over `A`: it is the base change
`B → B ⊗_A R` followed by the commutativity isomorphism. -/
theorem flat_includeRight (A R B : Type*) [CommRing A] [CommRing R] [CommRing B] [Algebra A R]
    [Algebra A B] [Module.Flat A R] :
    (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A R B).toRingHom.Flat := by
  have h1 : (algebraMap B (TensorProduct A B R)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have h2 : (Algebra.TensorProduct.comm A B R).toRingEquiv.toRingHom.Flat :=
    RingHom.Flat.of_bijective (Algebra.TensorProduct.comm A B R).bijective
  have heq : (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A R B).toRingHom =
      (Algebra.TensorProduct.comm A B R).toRingEquiv.toRingHom.comp
        (algebraMap B (TensorProduct A B R)) := by
    ext b
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [heq]
  exact RingHom.Flat.comp h1 h2

/-! ### Residue fields along residually trivial maps -/

/-- **A residue field map is bijective when the target is congruent to fractions of the source.**
Let `φ : R → S` carry a prime `𝔭` to the contraction of a prime `𝔓`, and suppose every element
of `S` is congruent modulo `𝔓` to a fraction `φ a / φ t` with `t ∉ 𝔭`. Then
`κ(𝔭) → κ(𝔓)` is bijective: its image is a subfield containing the image of `S`, and `κ(𝔓)` is
the fraction field of `S ⧸ 𝔓`. -/
theorem bijective_residueFieldMap_of_forall_exists {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] (hp : p = P.comap φ)
    (h : ∀ s : S, ∃ a t : R, t ∉ p ∧ φ t * s - φ a ∈ P) :
    Function.Bijective (Ideal.ResidueField.map p P φ hp) := by
  refine ⟨RingHom.injective _, fun z => ?_⟩
  let F := (Ideal.ResidueField.map p P φ hp).fieldRange
  have hS : ∀ s : S, algebraMap S P.ResidueField s ∈ F := by
    intro s
    obtain ⟨a, t, ht, hmem⟩ := h s
    have htP : φ t ∉ P := fun h' => ht (hp ▸ h')
    have h0 : algebraMap S P.ResidueField (φ t * s - φ a) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hmem
    have hne : algebraMap S P.ResidueField (φ t) ≠ 0 :=
      fun h' => htP (Ideal.algebraMap_residueField_eq_zero.mp h')
    have hs : algebraMap S P.ResidueField s =
        algebraMap S P.ResidueField (φ a) * (algebraMap S P.ResidueField (φ t))⁻¹ := by
      rw [map_sub, map_mul, sub_eq_zero] at h0
      rw [← h0, mul_comm, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [hs]
    refine F.mul_mem ?_ (F.inv_mem ?_)
    · exact ⟨algebraMap R p.ResidueField a, Ideal.ResidueField.map_algebraMap _ _ _ _ _⟩
    · exact ⟨algebraMap R p.ResidueField t, Ideal.ResidueField.map_algebraMap _ _ _ _ _⟩
  have hz : z ∈ F := by
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ P) z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := hS x
    have hy := hS y
    rw [IsScalarTower.algebraMap_apply S (S ⧸ P) P.ResidueField] at hx hy
    exact F.div_mem hx hy
  exact RingHom.mem_fieldRange.mp hz

/-- **Residue field transcendence degrees across a square with residually trivial sides.** Given a
commutative square of rings `A → B`, `R → T` with `α : A → R` and `β : B → T`, primes
`Q ⊆ B` over `𝔮 ⊆ A` and `N ⊆ T` over `𝔪 ⊆ R` with `𝔮 = α⁻¹𝔪` and `Q = β⁻¹N`, if the residue
field maps `κ(𝔮) → κ(𝔪)` and `κ(Q) → κ(N)` are bijective, then
`trdeg_{κ(𝔮)} κ(Q) = trdeg_{κ(𝔪)} κ(N)`. -/
theorem trdeg_residueField_eq_of_bijective {A B R T : Type u} [CommRing A] [CommRing B]
    [CommRing R] [CommRing T] [Algebra A B] [Algebra R T] (α : A →+* R) (β : B →+* T)
    (hsq : β.comp (algebraMap A B) = (algebraMap R T).comp α)
    (q : Ideal A) (Q : Ideal B) (m : Ideal R) (N : Ideal T) [q.IsPrime] [Q.IsPrime]
    [m.IsPrime] [N.IsPrime] [Q.LiesOver q] [N.LiesOver m]
    (hq : q = m.comap α) (hQ : Q = N.comap β)
    (hbq : Function.Bijective (Ideal.ResidueField.map q m α hq))
    (hbQ : Function.Bijective (Ideal.ResidueField.map Q N β hQ)) :
    letI := Ideal.ResidueField.algebraOfLiesOver q Q
    letI := Ideal.ResidueField.algebraOfLiesOver m N
    Algebra.trdeg q.ResidueField Q.ResidueField = Algebra.trdeg m.ResidueField N.ResidueField := by
  let := Ideal.ResidueField.algebraOfLiesOver q Q
  let := Ideal.ResidueField.algebraOfLiesOver m N
  refine Algebra.trdeg_eq_of_ringEquiv (RingEquiv.ofBijective _ hbq)
    (RingEquiv.ofBijective _ hbQ) fun a => ?_
  show (Ideal.ResidueField.map Q N β hQ).comp
      (Ideal.ResidueField.map q Q (algebraMap A B) Ideal.LiesOver.over) a =
    (Ideal.ResidueField.map m N (algebraMap R T) Ideal.LiesOver.over).comp
      (Ideal.ResidueField.map q m α hq) a
  congr 1
  refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  exact congrArg (algebraMap T N.ResidueField) (RingHom.congr_fun hsq x)

/-! ### Base change of an affine blowup algebra, away from the denominator -/

section TensorAffineBlowup

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] (I : Ideal A) (f : A)

/-- Every element of `A[I/f]` becomes an element of the image of `A` after multiplication by a
power of `f`, since `A[I/f]` sits inside `A_f`. -/
theorem exists_pow_mul_eq_algebraMap_affineBlowup (b : affineBlowup I f) :
    ∃ (n : ℕ) (a : A), algebraMap A (affineBlowup I f) (f ^ n) * b =
      algebraMap A (affineBlowup I f) a := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ :=
    IsLocalization.surj (Submonoid.powers f) (b : Localization.Away f)
  refine ⟨n, a, Subtype.ext ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  rw [mul_comm]
  exact h

/-- **`R ⊗_A A[I/f]` is birational to `R` away from `f`, first half.** Every element of
`R ⊗_A A[I/f]` becomes an element of the image of `R` after multiplication by a power of `f`. -/
theorem exists_pow_mul_eq_algebraMap_tensorProduct_affineBlowup
    (t : TensorProduct A R (affineBlowup I f)) :
    ∃ (n : ℕ) (r : R), algebraMap R (TensorProduct A R (affineBlowup I f))
        (algebraMap A R f ^ n) * t = algebraMap R (TensorProduct A R (affineBlowup I f)) r := by
  have hal : ∀ x : R, algebraMap R (TensorProduct A R (affineBlowup I f)) x = x ⊗ₜ 1 :=
    fun x => by simp [Algebra.TensorProduct.algebraMap_apply]
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r b =>
    obtain ⟨n, a, hb⟩ := exists_pow_mul_eq_algebraMap_affineBlowup I f b
    refine ⟨n, algebraMap A R a * r, ?_⟩
    calc algebraMap R _ (algebraMap A R f ^ n) * (r ⊗ₜ b) = ((f ^ n) • r) ⊗ₜ b := by
          rw [hal, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_pow, Algebra.smul_def]
      _ = r ⊗ₜ ((f ^ n) • b) := TensorProduct.smul_tmul _ _ _
      _ = r ⊗ₜ (a • (1 : affineBlowup I f)) := by
          rw [Algebra.smul_def, hb, Algebra.algebraMap_eq_smul_one]
      _ = (a • r) ⊗ₜ 1 := (TensorProduct.smul_tmul _ _ _).symm
      _ = _ := by rw [hal, Algebra.smul_def]
  | add x y hx hy =>
    obtain ⟨n, r, hr⟩ := hx
    obtain ⟨m, s, hs⟩ := hy
    refine ⟨n + m, algebraMap A R f ^ m * r + algebraMap A R f ^ n * s, ?_⟩
    rw [show algebraMap R _ (algebraMap A R f ^ (n + m)) * (x + y) =
        algebraMap R _ (algebraMap A R f ^ m) * (algebraMap R _ (algebraMap A R f ^ n) * x) +
          algebraMap R _ (algebraMap A R f ^ n) * (algebraMap R _ (algebraMap A R f ^ m) * y) by
        rw [pow_add, map_mul]; ring, hr, hs, map_add, map_mul, map_mul]

/-- **`R ⊗_A A[I/f]` is birational to `R` away from `f`, second half.** An element of `R` dying
in `R ⊗_A A[I/f]` is killed by a power of `f`: the map `R ⊗_A A[I/f] → R_f`, induced by
`A[I/f] ⊆ A_f → R_f`, retracts `R → R_f` through `R ⊗_A A[I/f]`. -/
theorem exists_pow_mul_eq_zero_of_algebraMap_tensorProduct_affineBlowup (r : R)
    (hr : algebraMap R (TensorProduct A R (affineBlowup I f)) r = 0) :
    ∃ n : ℕ, algebraMap A R f ^ n * r = 0 := by
  let Rf := Localization.Away (algebraMap A R f)
  let γ : affineBlowup I f →ₐ[A] Rf :=
    { toRingHom := (IsLocalization.Away.map (Localization.Away f) Rf (algebraMap A R) f).comp
        (affineBlowup I f).val.toRingHom
      commutes' := fun a => by
        show IsLocalization.Away.map (Localization.Away f) Rf (algebraMap A R) f
          (algebraMap A (Localization.Away f) a) = _
        rw [IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply A R Rf] }
  let ρ := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom A R Rf) γ
  have h0 : algebraMap R Rf r = 0 := by
    have := congrArg ρ hr
    rw [map_zero] at this
    rw [← this]
    simp [ρ, Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A R f)) Rf r).mp h0
  exact ⟨n, hn⟩

end TensorAffineBlowup

/-! ### The completed local rings of an affine blowup chart and of its base -/

section Chart

variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (Q : Ideal (affineBlowup I f))
  [Q.IsPrime]

/-- The `I`-adic completion `(A_𝔮)^∧` of the local ring of `A` at `𝔮 = Q ∩ A`, for a prime `Q`
of the affine blowup algebra `A[I/f]`. It is a `def`, with the structure of the adic completion
recorded by the instances below, so that instance search does not unfold it. -/
def affineBlowupBaseCompletion : Type u :=
  AdicCompletion (I.map (algebraMap A (Localization.AtPrime (Q.under A))))
    (Localization.AtPrime (Q.under A))

/-- The ring structure of `(A_𝔮)^∧`. -/
noncomputable instance : CommRing (affineBlowupBaseCompletion I f Q) :=
  inferInstanceAs (CommRing (AdicCompletion (I.map (algebraMap A (Localization.AtPrime
    (Q.under A)))) (Localization.AtPrime (Q.under A))))

/-- The `A_𝔮`-algebra structure of `(A_𝔮)^∧`. -/
noncomputable instance : Algebra (Localization.AtPrime (Q.under A))
    (affineBlowupBaseCompletion I f Q) :=
  inferInstanceAs (Algebra _ (AdicCompletion (I.map (algebraMap A (Localization.AtPrime
    (Q.under A)))) (Localization.AtPrime (Q.under A))))

/-- The `A`-algebra structure of `(A_𝔮)^∧`. -/
noncomputable instance : Algebra A (affineBlowupBaseCompletion I f Q) :=
  inferInstanceAs (Algebra A (AdicCompletion (I.map (algebraMap A (Localization.AtPrime
    (Q.under A)))) (Localization.AtPrime (Q.under A))))

/-- The maps `A → A_𝔮 → (A_𝔮)^∧` form a scalar tower. -/
instance : IsScalarTower A (Localization.AtPrime (Q.under A)) (affineBlowupBaseCompletion I f Q) :=
  inferInstanceAs (IsScalarTower A _ (AdicCompletion (I.map (algebraMap A (Localization.AtPrime
    (Q.under A)))) (Localization.AtPrime (Q.under A))))

/-- The `I`-adic completion `(A[I/f]_Q)^∧` of the local ring of the affine blowup algebra
`A[I/f]` at a prime `Q`. It is a `def`, with the structure of the adic completion recorded by
the instances below, so that instance search does not unfold it. -/
def affineBlowupChartCompletion : Type u :=
  AdicCompletion (I.map (algebraMap A (Localization.AtPrime Q))) (Localization.AtPrime Q)

/-- The ring structure of `(A[I/f]_Q)^∧`. -/
noncomputable instance : CommRing (affineBlowupChartCompletion I f Q) :=
  inferInstanceAs (CommRing (AdicCompletion (I.map (algebraMap A (Localization.AtPrime Q)))
    (Localization.AtPrime Q)))

/-- The `A[I/f]_Q`-algebra structure of `(A[I/f]_Q)^∧`. -/
noncomputable instance : Algebra (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q) :=
  inferInstanceAs (Algebra _ (AdicCompletion (I.map (algebraMap A (Localization.AtPrime Q)))
    (Localization.AtPrime Q)))

/-- The `A`-algebra structure of `(A[I/f]_Q)^∧`. -/
noncomputable instance : Algebra A (affineBlowupChartCompletion I f Q) :=
  inferInstanceAs (Algebra A (AdicCompletion (I.map (algebraMap A (Localization.AtPrime Q)))
    (Localization.AtPrime Q)))

/-- The maps `A → A[I/f]_Q → (A[I/f]_Q)^∧` form a scalar tower. -/
instance : IsScalarTower A (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q) :=
  inferInstanceAs (IsScalarTower A _ (AdicCompletion (I.map (algebraMap A (Localization.AtPrime Q)))
    (Localization.AtPrime Q)))

/-- The local homomorphism `A_𝔮 → A[I/f]_Q` is compatible with the maps from `A`. -/
theorem localRingHom_under_algebraMap (a : A) :
    Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl
        (algebraMap A (Localization.AtPrime (Q.under A)) a) =
      algebraMap A (Localization.AtPrime Q) a := by
  rw [Localization.localRingHom_to_map,
    ← IsScalarTower.algebraMap_apply A (affineBlowup I f) (Localization.AtPrime Q)]

/-- The ideal `I A_𝔮` is carried onto `I A[I/f]_Q` by `A_𝔮 → A[I/f]_Q`. -/
theorem map_localRingHom_under_map :
    (I.map (algebraMap A (Localization.AtPrime (Q.under A)))).map
        (Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl) =
      I.map (algebraMap A (Localization.AtPrime Q)) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (localRingHom_under_algebraMap I f Q)

/-- The map `(A_𝔮)^∧ → (A[I/f]_Q)^∧` of `I`-adic completions induced by `A_𝔮 → A[I/f]_Q`. -/
noncomputable def affineBlowupCompletionMap :
    affineBlowupBaseCompletion I f Q →+* affineBlowupChartCompletion I f Q :=
  adicCompletionMap (Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl)
    _ _ (map_localRingHom_under_map I f Q).le

/-- On the image of `A_𝔮`, the completion map is `A_𝔮 → A[I/f]_Q`. -/
theorem affineBlowupCompletionMap_algebraMap (x : Localization.AtPrime (Q.under A)) :
    affineBlowupCompletionMap I f Q (algebraMap _ (affineBlowupBaseCompletion I f Q) x) =
      algebraMap (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q)
        (Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl x) :=
  RingHom.congr_fun
    (adicCompletionMap_comp_algebraMap _ _ _ (map_localRingHom_under_map I f Q).le) x

/-- The completion map is a map of `A`-algebras. -/
theorem affineBlowupCompletionMap_algebraMap_base (a : A) :
    affineBlowupCompletionMap I f Q (algebraMap A (affineBlowupBaseCompletion I f Q) a) =
      algebraMap A (affineBlowupChartCompletion I f Q) a := by
  rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime (Q.under A)),
    affineBlowupCompletionMap_algebraMap, localRingHom_under_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- The completion map as a map of `A`-algebras. -/
noncomputable def affineBlowupCompletionAlgHom :
    affineBlowupBaseCompletion I f Q →ₐ[A] affineBlowupChartCompletion I f Q where
  __ := affineBlowupCompletionMap I f Q
  commutes' := affineBlowupCompletionMap_algebraMap_base I f Q

/-- The map `A[I/f] → (A[I/f]_Q)^∧`, as a map of `A`-algebras. -/
noncomputable def affineBlowupChartAlgHom :
    affineBlowup I f →ₐ[A] affineBlowupChartCompletion I f Q :=
  (IsScalarTower.toAlgHom A (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q)).comp
    (IsScalarTower.toAlgHom A (affineBlowup I f) (Localization.AtPrime Q))

/-- The map `(A_𝔮)^∧ ⊗_A A[I/f] → (A[I/f]_Q)^∧` induced by the completion map and by
`A[I/f] → (A[I/f]_Q)^∧`. -/
noncomputable def affineBlowupTensorChartMap :
    TensorProduct A (affineBlowupBaseCompletion I f Q) (affineBlowup I f) →ₐ[A]
      affineBlowupChartCompletion I f Q :=
  Algebra.TensorProduct.productMap (affineBlowupCompletionAlgHom I f Q)
    (affineBlowupChartAlgHom I f Q)

/-- The map `(A_𝔮)^∧ ⊗_A A[I/f] → (A[I/f]_Q)^∧` sends `r ⊗ b` to the product of the images of `r`
and `b`. -/
theorem affineBlowupTensorChartMap_tmul (r : affineBlowupBaseCompletion I f Q)
    (b : affineBlowup I f) :
    affineBlowupTensorChartMap I f Q (r ⊗ₜ b) = affineBlowupCompletionMap I f Q r *
      algebraMap (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q)
        (algebraMap (affineBlowup I f) (Localization.AtPrime Q) b) :=
  rfl

end Chart

/-! ### The fibre of a completion read through an isomorphism -/

section FibreTransport

variable {R T R' T' : Type*} [CommRing R] [CommRing T] [CommRing R'] [CommRing T']
  [Algebra R T] [Algebra T T'] (φ : R →+* R') (ψ : T →+* R')
  (hφ : ψ.comp (algebraMap R T) = φ) (E : R' ≃+* T') (hE : ∀ t, E (ψ t) = algebraMap T T' t)
  (p' : Ideal R') [p'.IsPrime] [(p'.map E).IsPrime]

omit [p'.IsPrime] [(p'.map E).IsPrime] in
include hE in
/-- If `E : R' ≅ T'` identifies `ψ` with `T → T'`, then `ψ⁻¹𝔭'` is the contraction of `E𝔭'` to
`T`. -/
theorem comap_eq_comap_map_of_ringEquiv :
    p'.comap ψ = (p'.map E).comap (algebraMap T T') := by
  ext t
  show ψ t ∈ p' ↔ algebraMap T T' t ∈ p'.map E
  rw [← hE]
  conv_lhs => rw [← Ideal.comap_map_of_bijective E E.bijective (I := p')]
  rfl

include hφ hE in
/-- **The fibre of `R_𝔭 → R'_{𝔭'}` is the fibre of `T_{𝔭_T} → T'_{E𝔭'}`.** Let `R → T`,
`ψ : T → R'` and `φ = ψ ∘ (R → T)`, let `E : R' ≅ T'` identify `ψ` with a map `T → T'`, and let
`𝔭'` be a prime of `R'` such that `T_{𝔭_T}`, `𝔭_T = ψ⁻¹𝔭'`, is the localization of `R` at
`𝔭 = φ⁻¹𝔭'`. Then `R'_{𝔭'}/𝔭R'_{𝔭'}` and `T'_{E𝔭'}/𝔭_T T'_{E𝔭'}` have the same depth. -/
theorem depth_fibre_eq_of_ringEquiv
    [IsLocalization.AtPrime (Localization.AtPrime (p'.comap ψ))
      ((p'.comap ψ).comap (algebraMap R T))] :
    letI := φ.toAlgebra
    Module.depth (Localization.AtPrime p') (maximalIdeal _)
        (Localization.AtPrime p' ⧸ (p'.comap φ).map (algebraMap R (Localization.AtPrime p'))) =
      Module.depth (Localization.AtPrime (p'.map E)) (maximalIdeal _)
        (Localization.AtPrime (p'.map E) ⧸
          (p'.comap ψ).map (algebraMap T (Localization.AtPrime (p'.map E)))) := by
  let := φ.toAlgebra
  obtain ⟨L, hL⟩ := AdicCompletionFibreUniverse.exists_localizationAtPrime_ringEquiv E p'
    (p'.map E) rfl
  refine AdicCompletionFibreUniverse.depth_quotient_eq_of_ringEquiv L _ _ ?_
  have hpT := comap_eq_comap_map_of_ringEquiv ψ E hE p'
  have hp : p'.comap φ = (p'.comap ψ).comap (algebraMap R T) := by
    rw [← hφ, Ideal.comap_comap]
  have c1 : (L : Localization.AtPrime p' →+* Localization.AtPrime (p'.map E)).comp
      (algebraMap R (Localization.AtPrime p')) =
      (algebraMap T (Localization.AtPrime (p'.map E))).comp (algebraMap R T) := by
    ext r
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply R R' (Localization.AtPrime p'), hL]
    show algebraMap T' _ (E (φ r)) = _
    rw [← hφ, RingHom.comp_apply, hE, ← IsScalarTower.algebraMap_apply]
  let h := Localization.localRingHom (p'.comap ψ) (p'.map E) (algebraMap T T') hpT
  have c2 : h.comp (algebraMap T (Localization.AtPrime (p'.comap ψ))) =
      algebraMap T (Localization.AtPrime (p'.map E)) := by
    ext t
    simp only [RingHom.comp_apply]
    rw [Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply]
  have hmax : (p'.comap φ).map (algebraMap R (Localization.AtPrime (p'.comap ψ))) =
      (p'.comap ψ).map (algebraMap T (Localization.AtPrime (p'.comap ψ))) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, hp]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _
  rw [Ideal.map_map, c1, ← c2, ← Ideal.map_map _ h, ← hmax, Ideal.map_map, RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq]

end FibreTransport

/-- **Fibre depth plus dimension, through a completion.** In the situation of
`depth_fibre_eq_of_ringEquiv`, with `T` a Noetherian local ring with a dualizing complex,
`T' = T^∧_J` for an ideal `J` inside the maximal ideal and `E` an isomorphism, the depth of the
fibre of `R_𝔭 → R'_{𝔭'}` plus `dim (R'/𝔭')` is `dim (T/𝔭_T)`. Hence any formula
`dim (T/𝔭_T) + c = dim (R/𝔭)` gives `depth + dim (R'/𝔭') + c = dim (R/𝔭)`. -/
theorem depth_fibre_add_ringKrullDim_of_ringEquiv {R R' T : Type u} [CommRing R] [CommRing R']
    [CommRing T] [IsNoetherianRing T] [IsLocalRing T] [Algebra R T] (φ : R →+* R')
    (p' : Ideal R') [p'.IsPrime] {J : Ideal T} (hJ : J ≤ maximalIdeal T)
    (ψ : T →+* R') (hφ : ψ.comp (algebraMap R T) = φ) (E : R' ≃+* AdicCompletion J T)
    (hE : ∀ t, E (ψ t) = algebraMap T _ t) [(p'.map E).IsPrime]
    [IsLocalization.AtPrime (Localization.AtPrime (p'.comap ψ))
      ((p'.comap ψ).comap (algebraMap R T))]
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} T) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex T _ _ (HasDerivedCategory.standard (ModuleCat.{u} T)) K)
    (c : WithBot ℕ∞)
    (hdim : ringKrullDim (T ⧸ p'.comap ψ) + c =
      ringKrullDim (R ⧸ (p'.comap ψ).comap (algebraMap R T))) :
    letI := φ.toAlgebra
    ((Module.depth (Localization.AtPrime p') (maximalIdeal _)
        (Localization.AtPrime p' ⧸ (p'.comap φ).map (algebraMap R (Localization.AtPrime p'))) :
          ℕ∞) : WithBot ℕ∞) + (ringKrullDim (R' ⧸ p') + c) = ringKrullDim (R ⧸ p'.comap φ) := by
  let := φ.toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} T)
  obtain ⟨K, hK⟩ := hdual
  have hcat := Dualizing.isUniversallyCatenary_of_isDualizingComplex hK
  have : (p'.map E).LiesOver (p'.comap ψ) := ⟨comap_eq_comap_map_of_ringEquiv ψ E hE p'⟩
  have hp : p'.comap φ = (p'.comap ψ).comap (algebraMap R T) := by
    rw [← hφ, Ideal.comap_comap]
  rw [depth_fibre_eq_of_ringEquiv φ ψ hφ E hE p',
    AdicCompletionFibre.depth_fibre_localization_eq_height hK J (p'.comap ψ) (p'.map E),
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv p' (p'.map E) E rfl),
    ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hp), ← hdim,
    ← AdicCompletionDimension.height_add_ringKrullDim_quotient_eq_ringKrullDim_quotient hcat hJ
      (p'.comap ψ) (p'.map E), add_assoc]

end Stacks.Algebraization

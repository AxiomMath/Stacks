module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus

/-!
# A uniform bound on the cotangent cohomology of the algebraizations of `B ⧸ aⁿ B`

Let `B` be rig-étale over a Noetherian pair `(A, I)` and `a ∈ A`.  Fix a completed polynomial
presentation of `B` and an exponent `d` with `I ^ d` acting by zero on `NL^∧_{B/A}` in `D(B)`.
For every `n` and every finite type `Āₙ = A ⧸ (aⁿ)`-algebra `C`, étale off `V(I)`, whose
completion `C^∧` is `B ⧸ aⁿ B`, the same `I ^ d` kills `H¹(L_{C/Āₙ})` and `Ω_{C/Āₙ}`.

The proof runs in three steps.

* `B ⧸ aⁿ B` is the completed base change of `B` along `(A, I) → (Āₙ, I Āₙ)`
  (**Stacks 0AL6**, `Rig.tensor_quotient_completion_bijective`), so **Stacks 0AK2**
  (`Rig.smul_id_of_completedBaseChange`) carries the annihilation of `NL^∧_{B/A}` to that of
  `NL^∧_{C^∧/Āₙ}`, read on a presentation of `C^∧` completed from one of `C`.
* Annihilation in the derived category kills both cohomology modules, which are
  `C^∧ ⊗_C H¹(L_{C/Āₙ})` and `C^∧ ⊗_C Ω_{C/Āₙ}` (**Stacks 0GAF**, as in
  `Rig.isRigEtale_adicCompletionObj_iff`).
* Both modules are finite and supported in `V(I C)` because `C` is étale off `V(I)`, so a
  power of `I C` kills them; for such a module `M` the map `M → C^∧ ⊗_C M` is injective, so
  the annihilation descends to `M` itself.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Rig

universe u

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section Descent

/-- **Annihilation descends along completion for a module killed by a power of the ideal.**
If `Jᵏ` kills `M` and the image of `s` in `R^∧ = R^∧_J` kills `R^∧ ⊗_R M`, then `s` kills `M`:
`s • m` maps to zero in `M^∧_J`, hence lies in `Jᵏ M = 0`. -/
private theorem mem_annihilator_of_mem_annihilator_tensor_adicCompletion {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (J : Ideal R) {k : ℕ}
    (hk : J ^ k ≤ Module.annihilator R M) {s : R}
    (hs : algebraMap R (AdicCompletion J R) s ∈
      Module.annihilator (AdicCompletion J R) (AdicCompletion J R ⊗[R] M)) :
    s ∈ Module.annihilator R M := by
  refine Module.mem_annihilator.mpr fun m => ?_
  have hcompletion : AdicCompletion.of J M (s • m) = 0 := by
    simpa [AdicCompletion.ofTensorProduct_tmul, TensorProduct.smul_tmul',
      IsScalarTower.algebraMap_smul] using congrArg (AdicCompletion.ofTensorProduct J M)
        (Module.mem_annihilator.mp hs (1 ⊗ₜ[R] m))
  have heval := congrArg (AdicCompletion.eval J M k) hcompletion
  simp only [AdicCompletion.eval_of, map_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at heval
  have hle : (J ^ k • ⊤ : Submodule R M) = ⊥ := by
    rw [eq_bot_iff, Submodule.smul_le]
    exact fun r hr y _ => (Submodule.mem_bot R).mpr (Module.mem_annihilator.mp (hk hr) y)
  rwa [hle, Submodule.mem_bot] at heval

/-- **Annihilation descends along completion for a finite module supported in `V(J)`.**
If the image of `s` in `R^∧_J` kills `R^∧_J ⊗_R M`, then `s` kills `M`, since a power of `J`
kills `M` over a Noetherian ring. -/
private theorem mem_annihilator_of_support_subset_zeroLocus_of_tensor_adicCompletion
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (J : Ideal R)
    (hsupp : ∀ p : PrimeSpectrum R,
      p ∈ Module.support R M → p ∈ PrimeSpectrum.zeroLocus (J : Set R))
    {s : R}
    (hs : algebraMap R (AdicCompletion J R) s ∈
      Module.annihilator (AdicCompletion J R) (AdicCompletion J R ⊗[R] M)) :
    s ∈ Module.annihilator R M := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (I := J)
    (J := Module.annihilator R M)
    (by
      rw [Ideal.radical_eq_sInf]
      exact le_sInf fun p hp' => hsupp ⟨p, hp'.2⟩
        ((Module.mem_support_iff_of_finite (p := ⟨p, hp'.2⟩)).mpr hp'.1))
    (Ideal.fg_of_isNoetherianRing _)
  exact mem_annihilator_of_mem_annihilator_tensor_adicCompletion _ hc hs

end Descent

section Cohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {C : Type u} [CommRing C] [Algebra A C] [Algebra.FiniteType A C] {m : ℕ}
  (G : Algebra.Generators A C (Fin m))

/-- **Annihilation in `D` of `NL^∧_{C^∧/A}` kills `C^∧ ⊗_C H¹(L_{C/A})` and
`C^∧ ⊗_C Ω_{C/A}`.**  For a finite type `C` over a Noetherian `A`, a scalar of `C^∧` acting by
zero on the completed naive cotangent complex of the completion of a presentation of `C`
annihilates the two base-changed cotangent modules: a module-level two-sided splitting kills
the kernel and the cokernel of the differential, and these are the two base changes by
**Stacks 0GAF** and flatness of `C^∧` over `C`. -/
private theorem mem_annihilator_tensor_of_smul_id_eq_zero
    (f : (adicCompletionObj I (B := C)).carrier)
    (h : f • 𝟙 (derivedCompletedNaiveCotangentComplex (adicCompletionObj I (B := C))
      (presentationCompletion I G)) = 0) :
    f ∈ Module.annihilator (adicCompletionObj I (B := C)).carrier
        ((adicCompletionObj I (B := C)).carrier ⊗[C] Algebra.H1Cotangent A C) ∧
      f ∈ Module.annihilator (adicCompletionObj I (B := C)).carrier
        ((adicCompletionObj I (B := C)).carrier ⊗[C] Ω[C⁄A]) := by
  have hCnoeth : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  have hflat : Module.Flat C (adicCompletionObj I (B := C)).carrier :=
    inferInstanceAs (Module.Flat C (adicCompletionAlgebra I (B := C)))
  have hb₁ := bijective_completionComparison_f₁ I G
  have hb₀ := bijective_completionComparison_f₀ I G
  set K := completedNaiveCotangentComplex (adicCompletionObj I (B := C))
    (presentationCompletion I G)
  have hker : Module.annihilator (adicCompletionObj I (B := C)).carrier
        (LinearMap.ker K.differential) =
      Module.annihilator (adicCompletionObj I (B := C)).carrier
        ((adicCompletionObj I (B := C)).carrier ⊗[C] Algebra.H1Cotangent A C) :=
    ((LinearEquiv.ofBijective (NaiveCotangent.ChainMap.onH₁ (completionComparison I G))
      (NaiveCotangent.ChainMap.bijective_onH₁ _ hb₁ hb₀.1)).symm.trans
      ((LinearMap.tensorKerEquiv (adicCompletionObj I (B := C)).carrier
          (adicCompletionObj I (B := C)).carrier (presentationDifferential G)).symm.trans
        (LinearEquiv.baseChange C (adicCompletionObj I (B := C)).carrier _ _
          (presentationKerEquiv G)))).annihilator_eq
  have hcoker : Module.annihilator (adicCompletionObj I (B := C)).carrier
        ((Fin (presentationCompletion I G).variableCount →
            (adicCompletionObj I (B := C)).carrier) ⧸ LinearMap.range K.differential) =
      Module.annihilator (adicCompletionObj I (B := C)).carrier
        ((adicCompletionObj I (B := C)).carrier ⊗[C] Ω[C⁄A]) :=
    ((LinearEquiv.ofBijective (NaiveCotangent.ChainMap.onH₀ (completionComparison I G))
      (NaiveCotangent.ChainMap.bijective_onH₀ _ hb₁.2 hb₀)).symm.trans
      ((LinearMap.baseChangeCokerEquiv (adicCompletionObj I (B := C)).carrier
          (presentationDifferential G)).trans
        (LinearEquiv.baseChange C (adicCompletionObj I (B := C)).carrier _ _
          (presentationCokerEquiv G)))).annihilator_eq
  obtain ⟨σ, hσd, hdσ⟩ := exists_differential_section_of_smul_id_eq_zero _ _ f h
  rw [← hker, ← hcoker]
  refine ⟨Module.mem_annihilator.mpr fun z => ?_, Module.mem_annihilator.mpr fun z => ?_⟩
  · have hzero : f • (z : (presentationCompletion I G).extension.Cotangent) = 0 := by
      rw [← hσd z.1, LinearMap.mem_ker.mp z.2, map_zero]
    exact Subtype.ext ((Submodule.coe_smul f z).trans hzero)
  · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.differential) z
    have hz : Submodule.mkQ (LinearMap.range K.differential) (f • y) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact ⟨σ y, hdσ y⟩
    rwa [map_smul] at hz

end Cohomology

section Quotient

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- The uniform annihilation for one quotient `Ā = A ⧸ q` of the base, with `Ī = I Ā` and an
algebraization `C` of `B ⧸ q B`: a scalar `x ∈ A` acting by zero on `NL^∧_{B/A}` in `D(B)`
kills `H¹(L_{C/Ā})` and `Ω_{C/Ā}`. -/
private theorem annihilates_cotangent_of_algEquiv (B : AdicFiniteTypeAlgebra.{u, u} A I)
    (P : CompletedPolynomialPresentation I B) (q : Ideal A) (Ibar : Ideal (A ⧸ q))
    (hIbar : Ibar = I.map (Ideal.Quotient.mk q)) (C : Type u) [CommRing C]
    [Algebra (A ⧸ q) C] [Algebra A C] [IsScalarTower A (A ⧸ q) C]
    [Algebra.FiniteType (A ⧸ q) C] (hC : IsEtaleOutside Ibar C)
    (E : AdicCompletion (Ibar.map (algebraMap (A ⧸ q) C)) C ≃ₐ[A]
      B.carrier ⧸ q.map (algebraMap A B.carrier))
    (x : A) (hx : algebraMap A B.carrier x • 𝟙 (derivedCompletedNaiveCotangentComplex B P) = 0) :
    algebraMap A C x ∈ Module.annihilator C (Algebra.H1Cotangent (A ⧸ q) C) ∧
      algebraMap A C x ∈ Module.annihilator C Ω[C⁄A ⧸ q] := by
  have hCnoeth : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing (A ⧸ q) C
  let Ch := adicCompletionObj Ibar (B := C)
  let _ : Algebra A Ch.carrier :=
    inferInstanceAs (Algebra A (AdicCompletion (Ibar.map (algebraMap (A ⧸ q) C)) C))
  let _ : Algebra B.carrier Ch.carrier :=
    ((E.symm : _ →ₐ[A] AdicCompletion (Ibar.map (algebraMap (A ⧸ q) C)) C).toRingHom.comp
      (Ideal.Quotient.mk (q.map (algebraMap A B.carrier)))).toAlgebra
  have halgB : ∀ b : B.carrier, algebraMap B.carrier Ch.carrier b =
      E.symm (Ideal.Quotient.mk (q.map (algebraMap A B.carrier)) b) := fun _ => rfl
  have halgA : ∀ y : A, algebraMap A Ch.carrier y =
      AdicCompletion.of (Ibar.map (algebraMap (A ⧸ q) C)) C (algebraMap A C y) := fun _ => rfl
  have towerA : IsScalarTower A (A ⧸ q) Ch.carrier := IsScalarTower.of_algebraMap_eq fun y =>
    congrArg (AdicCompletion.of _ C) (IsScalarTower.algebraMap_apply A (A ⧸ q) C y)
  have hEA (y : A) : E.symm (algebraMap A (B.carrier ⧸ q.map (algebraMap A B.carrier)) y) =
      algebraMap A Ch.carrier y := E.symm.commutes y
  have towerB : IsScalarTower A B.carrier Ch.carrier :=
    IsScalarTower.of_algebraMap_eq fun y => by rw [halgB, ← hEA]; rfl
  -- `C^∧ ≅ B ⧸ q B ≅ B ⊗_A Ā ≅ (B ⊗_A Ā)^∧`, Stacks 0AL6.
  have hI1 : (I ^ 1).map (Ideal.Quotient.mk q) ≤ Ibar := by rw [pow_one, hIbar]
  have hIbar1 : Ibar ^ 1 ≤ I.map (Ideal.Quotient.mk q) := by rw [pow_one, hIbar]
  let qEquiv := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B.carrier q
  let φ : baseChangedAlgebra (A₂ := A ⧸ q) B →+*
      completedBaseChangedAlgebra (A₂ := A ⧸ q) (I₂ := Ibar) B :=
    algebraMap (baseChangedAlgebra (A₂ := A ⧸ q) B)
      (completedBaseChangedAlgebra (A₂ := A ⧸ q) (I₂ := Ibar) B)
  have hφ : ∀ t, φ t = AdicCompletion.of (baseChangedIdeal (A₂ := A ⧸ q) (I₂ := Ibar) B)
      (baseChangedAlgebra (A₂ := A ⧸ q) B) t := fun t => by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
  have hφbij : Function.Bijective φ := by
    rw [show (φ : _ → _) = _ from funext hφ]
    exact tensor_quotient_completion_bijective I q Ibar Nat.one_pos Nat.one_pos hI1 hIbar1 B
  let e : Ch.carrier ≃+* completedBaseChangedAlgebra (A₂ := A ⧸ q) (I₂ := Ibar) B :=
    (E.toRingEquiv.trans qEquiv.toRingEquiv).trans (RingEquiv.ofBijective φ hφbij)
  have he : ∀ z : Ch.carrier, e z = φ (qEquiv (E z)) := fun _ => rfl
  have heA : ∀ y : A ⧸ q, e (algebraMap (A ⧸ q) Ch.carrier y) =
      algebraMap (baseChangedAlgebra (A₂ := A ⧸ q) B)
        (completedBaseChangedAlgebra (A₂ := A ⧸ q) (I₂ := Ibar) B)
        (baseChangedRight (A ⧸ q) B y) := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [he]
    congr 1
    rw [show Ideal.Quotient.mk q y = algebraMap A (A ⧸ q) y from rfl,
      ← IsScalarTower.algebraMap_apply]
    change qEquiv (E (algebraMap A
      (AdicCompletion (Ibar.map (algebraMap (A ⧸ q) C)) C) y)) = _
    rw [E.commutes]
    change qEquiv (algebraMap B.carrier _ (algebraMap A B.carrier y)) = 1 ⊗ₜ[A] _
    rw [AlgEquiv.commutes]
    change (algebraMap A B.carrier y) ⊗ₜ[A] 1 = 1 ⊗ₜ[A] Ideal.Quotient.mk q y
    simpa only [← Ideal.Quotient.algebraMap_eq] using
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) y)
  have heB : ∀ b : B.carrier, e (algebraMap B.carrier Ch.carrier b) =
      algebraMap (baseChangedAlgebra (A₂ := A ⧸ q) B)
        (completedBaseChangedAlgebra (A₂ := A ⧸ q) (I₂ := Ibar) B)
        (baseChangedLeft (A ⧸ q) B b) := fun b => by
    rw [he, halgB, AlgEquiv.apply_symm_apply]
    congr 1
  -- Stacks 0AK2, on a presentation of `C^∧` completed from one of `C`.
  obtain ⟨m, ⟨G⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp ‹Algebra.FiniteType (A ⧸ q) C›
  have h₂ := smul_id_of_completedBaseChange (B₂ := Ch) Nat.one_pos
    (hI1 : (I ^ 1).map (algebraMap A (A ⧸ q)) ≤ Ibar) e heA heB P
    (presentationCompletion Ibar G) (algebraMap A B.carrier x) hx
  have hscal : algebraMap A Ch.carrier x =
      algebraMap C (AdicCompletion (Ibar.map (algebraMap (A ⧸ q) C)) C) (algebraMap A C x) := by
    rw [halgA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [← IsScalarTower.algebraMap_apply A B.carrier Ch.carrier, hscal] at h₂
  obtain ⟨h₁, h₀⟩ := mem_annihilator_tensor_of_smul_id_eq_zero Ibar G _ h₂
  -- Both modules are killed by a power of `I C`, as `C` is étale off `V(I)`.
  have hfin : Module.Finite C (Algebra.H1Cotangent (A ⧸ q) C) := finite_h1Cotangent
  have hsupp : ∀ p : PrimeSpectrum C,
      p ∈ Module.support C Ω[C⁄A ⧸ q] ∨ p ∈ Module.support C (Algebra.H1Cotangent (A ⧸ q) C) →
        p ∈ PrimeSpectrum.zeroLocus ((Ibar.map (algebraMap (A ⧸ q) C) : Ideal C) : Set C) := by
    intro p hp
    by_contra hnot
    have hlocus : p ∈ Algebra.etaleLocus (A ⧸ q) C := by
      refine (isEtaleOutside_iff Ibar C).mp hC p.asIdeal p.2 ?_
      rwa [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
        Ideal.map_le_iff_le_comap] at hnot
    rw [Algebra.etaleLocus_eq_compl_support] at hlocus
    exact hp.elim hlocus.1 hlocus.2
  exact ⟨mem_annihilator_of_support_subset_zeroLocus_of_tensor_adicCompletion _
      (fun p hp => hsupp p (.inr hp)) h₁,
    mem_annihilator_of_support_subset_zeroLocus_of_tensor_adicCompletion _
      (fun p hp => hsupp p (.inl hp)) h₀⟩

end Quotient

/-- **The uniform annihilation step of Stacks 0AKA.**  Let `B` be rig-étale over `(A, I)` and
`a ∈ A`.  There is one exponent `d` such that for every `n` and every finite type
`A ⧸ (aⁿ)`-algebra `C` which is étale over the complement of `V(I)` and whose `I`-adic completion
is `A`-isomorphic to `B ⧸ aⁿ B`, the ideal `I ^ d` kills `H¹(L_{C/(A/aⁿ)})` and `Ω_{C/(A/aⁿ)}`.

The exponent is the one for which `I ^ d` acts by zero on `NL^∧_{B/A}` in `D(B)`.  Since
`B ⧸ aⁿ B ≅ C^∧` is the completed base change of `B` to `A ⧸ (aⁿ)` (**Stacks 0AL6**),
**Stacks 0AK2** gives the same annihilation on `NL^∧_{C^∧}`, hence on its cohomology
`C^∧ ⊗_C H¹(L_{C/(A/aⁿ)})` and `C^∧ ⊗_C Ω_{C/(A/aⁿ)}` (**Stacks 0GAF**).  These modules are
killed by a power of `I C`, as `C` is étale off `V(I)`, and for such a module `M` the map
`M → C^∧ ⊗_C M` is injective. -/
public theorem exists_pow_annihilates_cotangent_of_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, u} A I) (hB : IsRigEtale B) (a : A) :
    ∃ d : ℕ, ∀ (n : ℕ) (C : Type u) [CommRing C] [Algebra (A ⧸ Ideal.span {a ^ n}) C]
      [Algebra A C] [IsScalarTower A (A ⧸ Ideal.span {a ^ n}) C]
      [Algebra.FiniteType (A ⧸ Ideal.span {a ^ n}) C],
      IsEtaleOutside (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))) C →
      (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A]
        B.carrier ⧸ (Ideal.span {a ^ n}).map (algebraMap A B.carrier)) →
      ∀ x ∈ I ^ d,
        algebraMap A C x ∈
            Module.annihilator C (Algebra.H1Cotangent (A ⧸ Ideal.span {a ^ n}) C) ∧
          algebraMap A C x ∈ Module.annihilator C Ω[C⁄A ⧸ Ideal.span {a ^ n}] := by
  obtain ⟨d, hd⟩ := hB (completedPolynomialPresentation I I.fg_of_isNoetherianRing B)
  refine ⟨d, fun n C _ _ _ _ _ hC E x hx => ?_⟩
  have hJ : I.map (algebraMap A C) = (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))).map
      (algebraMap (A ⧸ Ideal.span {a ^ n}) C) := by
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq A (A ⧸ Ideal.span {a ^ n}) C]
    rfl
  rw [hJ] at E
  exact annihilates_cotangent_of_algEquiv B _ _ _ rfl C hC E x (hd x hx)

end Rig

end

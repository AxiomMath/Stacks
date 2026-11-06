module

public import StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation.LocalizationColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of finite-presentation data: base change and Tag 00QV

Condition (4), that the base-change maps `S_i ⊗_{R_i} R_j → S_j` are localizations at a prime
(`Descent.cond4_baseChange`), the bundled descent (`Descent.systemBundle`, `descent_core`,
`descent_of_finitePresentation`), Stacks Tag 00QV (`main_theorem_00qv`), and the comparison of
`EssFinitePresentation` with neighbouring finiteness notions. Split from
`StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.cdot false

open scoped TensorProduct

universe u

namespace Descent

section

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] (φ : R →+* S)
variable {T : Type u} [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
variable {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
variable {Robj : Λ → Type u} [∀ i, CommRing (Robj i)] [∀ i, IsLocalRing (Robj i)]
variable (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
variable (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
variable (lam0 : Λ) (hbot : ∀ i, lam0 ≤ i)
variable (n m : ℕ) (frel : Fin m → MvPolynomial (Fin n) (Robj lam0))

variable (q : Ideal T) [hq : q.IsPrime]
variable (πT : ∀ i, Tobj fR lam0 hbot n m frel i →+* T)

-- this proof's elaboration needs more than the default heartbeat budget
/-- Given the base-change isomorphism `T_i ⊗_{R_i} R_j ≅ T_j` as the hypothesis `hbc`, conclude
condition (4): the canonical base-change map exhibits `S_j` as a localization of
`S_i ⊗_{R_i} R_j` at a prime.

This combines base change of the localization with the localization-of-localization identity; the
compatibility `q_i = fT⁻¹ q_j` of `qcon_compat` gives `fT (q_i.primeCompl) ⊆ q_j.primeCompl`, and
the witness prime is the contraction of `𝔪_{S_j}` along the base-change map. -/
lemma cond4_fromBaseChange (hqS : IsLocalization q.primeCompl S)
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (hfTR : ∀ i j (hij : i ≤ j),
      (fT i j hij).comp (RtoT fR lam0 hbot n m frel i)
        = (RtoT fR lam0 hbot n m frel j).comp (fR i j hij))
    (hfT : ∀ i j (hij : i ≤ j),
      fT i j hij = fTmap fR lam0 hbot n m frel hRdir i j hij)
    (i j : Λ) (hij : i ≤ j)
    (hbc : letI : Algebra (Robj i) (Robj j) := (fR i j hij).toAlgebra
      letI : Algebra (Robj i) (Tobj fR lam0 hbot n m frel i) :=
        (RtoT fR lam0 hbot n m frel i).toAlgebra
      letI : Algebra (Robj i) (Tobj fR lam0 hbot n m frel j) :=
        ((RtoT fR lam0 hbot n m frel j).comp (fR i j hij)).toAlgebra
      ∃ e : Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j
          ≃ₐ[Robj i] Tobj fR lam0 hbot n m frel j,
        (∀ t : Tobj fR lam0 hbot n m frel i,
          e (t ⊗ₜ[Robj i] (1 : Robj j)) = fT i j hij t) ∧
        (∀ r : Robj j,
          e ((1 : Tobj fR lam0 hbot n m frel i) ⊗ₜ[Robj i] r)
            = RtoT fR lam0 hbot n m frel j r)) :
    IsLocalizationAtPrimeOfBaseChange fR
      (fun i j h => fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h)
      (fun i => psiS fR lam0 hbot n m frel q πT i)
      (fun i j hij => psiS_comm fR lam0 hbot n m frel q πT fT hπcompat hfTR i j hij)
      i j hij := by
  obtain ⟨e, he, he2⟩ := hbc
  unfold IsLocalizationAtPrimeOfBaseChange
  intro g1 g2 can
  -- Step (b1)-flavored compatibility, from `Localization.localRingHom_to_map`:
  -- fSmap intertwines the canonical localization maps Tᵢ→Sᵢ, Tⱼ→Sⱼ with fT.
  have hfS : ∀ x : Tobj fR lam0 hbot n m frel i,
      fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij
          (algebraMap (Tobj fR lam0 hbot n m frel i)
            (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i)) x)
        = algebraMap (Tobj fR lam0 hbot n m frel j)
            (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT j)) (fT i j hij x) := by
    intro x
    rw [fSmap]
    exact Localization.localRingHom_to_map (qcon fR lam0 hbot n m frel q πT i)
      (qcon fR lam0 hbot n m frel q πT j) (fT i j hij)
      (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat i j hij) x
  -- Scalar tower Rᵢ → Tᵢ → Sᵢ (using the canonical localization Sᵢ = Loc(qcon i)).
  let instRiRj : Algebra (Robj i) (Robj j) := (fR i j hij).toAlgebra
  let instRiSi2 : Algebra (Robj i) (Sobj' fR lam0 hbot n m frel q πT i) :=
    (psiS fR lam0 hbot n m frel q πT i).toAlgebra
  let instRiTi : Algebra (Robj i) (Tobj fR lam0 hbot n m frel i) :=
    (RtoT fR lam0 hbot n m frel i).toAlgebra
  let instRiTj : Algebra (Robj i) (Tobj fR lam0 hbot n m frel j) :=
    ((RtoT fR lam0 hbot n m frel j).comp (fR i j hij)).toAlgebra
  let instRiSj : Algebra (Robj i) (Sobj' fR lam0 hbot n m frel q πT j) :=
    ((psiS fR lam0 hbot n m frel q πT j).comp (fR i j hij)).toAlgebra
  let instCan : Algebra (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j)
      (Sobj' fR lam0 hbot n m frel q πT j) := can.toRingHom.toAlgebra
  have instST_iSi : IsScalarTower (Robj i) (Tobj fR lam0 hbot n m frel i)
      (Sobj' fR lam0 hbot n m frel q πT i) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let Ψ : (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j) ⊗[Tobj fR lam0 hbot n m frel i]
        (Sobj' fR lam0 hbot n m frel q πT i)
      ≃ₐ[Tobj fR lam0 hbot n m frel i]
        (Sobj' fR lam0 hbot n m frel q πT i) ⊗[Robj i] Robj j :=
    (Algebra.TensorProduct.comm (Tobj fR lam0 hbot n m frel i)
        (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
        (Sobj' fR lam0 hbot n m frel q πT i)).trans
      (Algebra.TensorProduct.cancelBaseChange (Robj i) (Tobj fR lam0 hbot n m frel i)
        (Tobj fR lam0 hbot n m frel i)
        (Sobj' fR lam0 hbot n m frel q πT i) (Robj j))
  -- loc1: Tᵢ⊗Rⱼ localized at the image of (qcon i).primeCompl.
  have loc1 : IsLocalization
      (Algebra.algebraMapSubmonoid (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
        (qcon fR lam0 hbot n m frel q πT i).primeCompl)
      ((Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j) ⊗[Tobj fR lam0 hbot n m frel i]
        (Sobj' fR lam0 hbot n m frel q πT i)) :=
    IsLocalization.tensor (R := Tobj fR lam0 hbot n m frel i)
      (S := Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
      (Sobj' fR lam0 hbot n m frel q πT i)
      (qcon fR lam0 hbot n m frel q πT i).primeCompl
  -- the algebra structure (Tᵢ⊗Rⱼ) → (Sᵢ⊗Rⱼ) transported across Ψ.
  let instTiRjSiRj : Algebra (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
      (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j) :=
    (Ψ.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom
        (R := Tobj fR lam0 hbot n m frel i)
        (A := Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
        (B := Sobj' fR lam0 hbot n m frel q πT i))).toAlgebra
  have loc2 : IsLocalization
      (Algebra.algebraMapSubmonoid (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
        (qcon fR lam0 hbot n m frel q πT i).primeCompl)
      (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j) :=
    (IsLocalization.isLocalization_iff_of_ringEquiv _ Ψ.toRingEquiv).mp loc1
  -- base transport across e to base Tⱼ.
  let instTjSiRj : Algebra (Tobj fR lam0 hbot n m frel j)
      (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j) :=
    ((Ψ.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom
        (R := Tobj fR lam0 hbot n m frel i)
        (A := Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
        (B := Sobj' fR lam0 hbot n m frel q πT i))).comp
      e.symm.toRingHom).toAlgebra
  have loc3 : IsLocalization
      (Submonoid.map e.toRingEquiv.toMonoidHom
        (Algebra.algebraMapSubmonoid (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
          (qcon fR lam0 hbot n m frel q πT i).primeCompl))
      (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j) :=
    IsLocalization.isLocalization_of_base_ringEquiv _ _ e.toRingEquiv
  -- (b1) key ring-hom identity on generators of Tᵢ⊗Rⱼ.
  have hg2 : ∀ r : Robj j,
      algebraMap (Tobj fR lam0 hbot n m frel j)
          (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT j))
          (RtoT fR lam0 hbot n m frel j r)
        = g2 r := by
    intro r
    rfl
  have key : ∀ x : Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j,
      can (Ψ (Algebra.TensorProduct.includeLeftRingHom
        (R := Tobj fR lam0 hbot n m frel i)
        (A := Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
        (B := Sobj' fR lam0 hbot n m frel q πT i) x))
        = algebraMap (Tobj fR lam0 hbot n m frel j)
            (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT j)) (e x) := by
    intro x
    induction x with
    | add a b ha hb =>
        conv_rhs => rw [map_add, map_add]
        rw [map_add, map_add, map_add, ha, hb]
        abel
    | tmul t r =>
        rw [Algebra.TensorProduct.includeLeftRingHom_apply]
        show can (Ψ ((t ⊗ₜ[Robj i] r) ⊗ₜ[Tobj fR lam0 hbot n m frel i]
          (1 : Sobj' fR lam0 hbot n m frel q πT i))) = _
        rw [show Ψ ((t ⊗ₜ[Robj i] r) ⊗ₜ[Tobj fR lam0 hbot n m frel i]
              (1 : Sobj' fR lam0 hbot n m frel q πT i))
            = (algebraMap (Tobj fR lam0 hbot n m frel i)
                (Sobj' fR lam0 hbot n m frel q πT i) t) ⊗ₜ[Robj i] r from by
          simp only [Ψ, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
            Algebra.TensorProduct.cancelBaseChange_tmul,
            Algebra.smul_def, mul_one]]
        show can ((algebraMap (Tobj fR lam0 hbot n m frel i)
            (Sobj' fR lam0 hbot n m frel q πT i) t) ⊗ₜ[Robj i] r) = _
        rw [Algebra.TensorProduct.productMap_apply_tmul]
        -- e (t ⊗ₜ r) = e (t ⊗ₜ 1) * e (1 ⊗ₜ r)
        have het : e (t ⊗ₜ[Robj i] r)
            = e (t ⊗ₜ[Robj i] (1 : Robj j)) *
              e ((1 : Tobj fR lam0 hbot n m frel i) ⊗ₜ[Robj i] r) := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [het, map_mul, he t, he2 r]
        rw [← hfS t, ← hg2 r]
        rfl
  -- scalar tower Tⱼ → (Sᵢ⊗Rⱼ) → Sⱼ, from `key`.
  have instST : IsScalarTower (Tobj fR lam0 hbot n m frel j)
      (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j)
      (Sobj' fR lam0 hbot n m frel q πT j) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      have := key (e.symm x)
      rw [AlgEquiv.apply_symm_apply] at this
      exact this.symm)
  -- (b2) submonoid containment M₀ ≤ (qcon j).primeCompl.
  have hMle : Submonoid.map e.toRingEquiv.toMonoidHom
        (Algebra.algebraMapSubmonoid (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
          (qcon fR lam0 hbot n m frel q πT i).primeCompl)
      ≤ (qcon fR lam0 hbot n m frel q πT j).primeCompl := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    -- y = algebraMap Tᵢ (Tᵢ⊗Rⱼ) x = x ⊗ₜ 1, e (x⊗1) = fT x
    have hxe : e.toRingEquiv (algebraMap (Tobj fR lam0 hbot n m frel i)
        (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j) x)
          = fT i j hij x := by
      rw [Algebra.TensorProduct.algebraMap_apply]
      show e ((algebraMap (Tobj fR lam0 hbot n m frel i) (Tobj fR lam0 hbot n m frel i) x)
        ⊗ₜ[Robj i] (1 : Robj j)) = _
      rw [Algebra.algebraMap_self_apply, he x]
    show e.toRingEquiv (algebraMap (Tobj fR lam0 hbot n m frel i)
        (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j) x)
      ∈ (qcon fR lam0 hbot n m frel q πT j).primeCompl
    rw [hxe]
    -- x ∉ qcon i ⇒ fT x ∉ qcon j
    exact fun hmem => hx (by rwa [qcon_compat fR lam0 hbot n m frel q πT fT hπcompat i j hij])
  -- enlarge to (qcon j).primeCompl: Sⱼ is a localization of Sᵢ⊗Rⱼ.
  have loc4 : IsLocalization
      (Submonoid.map (algebraMap (Tobj fR lam0 hbot n m frel j)
        (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j))
        (qcon fR lam0 hbot n m frel q πT j).primeCompl)
      (Sobj' fR lam0 hbot n m frel q πT j) :=
    IsLocalization.isLocalization_of_submonoid_le
      (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j)
      (Sobj' fR lam0 hbot n m frel q πT j)
      (Submonoid.map e.toRingEquiv.toMonoidHom
        (Algebra.algebraMapSubmonoid (Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j)
          (qcon fR lam0 hbot n m frel q πT i).primeCompl))
      (qcon fR lam0 hbot n m frel q πT j).primeCompl hMle
  -- self-localization of the local ring Sⱼ at its maximal ideal.
  have instSelf : IsLocalization
      (IsLocalRing.maximalIdeal (Sobj' fR lam0 hbot n m frel q πT j)).primeCompl
      (Sobj' fR lam0 hbot n m frel q πT j) :=
    IsLocalization.of_le_isUnit fun x hx =>
      (IsUnit.mem_submonoid_iff _).mpr (IsLocalRing.notMem_maximalIdeal.mp hx)
  refine ⟨Ideal.comap can.toRingHom
    (IsLocalRing.maximalIdeal (Sobj' fR lam0 hbot n m frel q πT j)),
    Ideal.comap_isPrime _ _, ?_⟩
  exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.map (algebraMap (Tobj fR lam0 hbot n m frel j)
        (Sobj' fR lam0 hbot n m frel q πT i ⊗[Robj i] Robj j))
        (qcon fR lam0 hbot n m frel q πT j).primeCompl)
    (Sobj' fR lam0 hbot n m frel q πT j)
    (IsLocalRing.maximalIdeal (Sobj' fR lam0 hbot n m frel q πT j))

/-- Condition (4): for `i ≤ j`, the canonical base-change map exhibits `S_j` as a localization of
`S_i ⊗_{R_i} R_j` at a prime. It combines `baseChangeQuotient` (`T_i ⊗_{R_i} R_j ≅ T_j`) with
base change of the localization and localization of a localization. -/
lemma cond4_baseChange (hqS : IsLocalization q.primeCompl S)
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (hfTR : ∀ i j (hij : i ≤ j),
      (fT i j hij).comp (RtoT fR lam0 hbot n m frel i)
        = (RtoT fR lam0 hbot n m frel j).comp (fR i j hij))
    (hfT : ∀ i j (hij : i ≤ j),
      fT i j hij = fTmap fR lam0 hbot n m frel hRdir i j hij)
    (i j : Λ) (hij : i ≤ j) :
    IsLocalizationAtPrimeOfBaseChange fR
      (fun i j h => fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h)
      (fun i => psiS fR lam0 hbot n m frel q πT i)
      (fun i j hij => psiS_comm fR lam0 hbot n m frel q πT fT hπcompat hfTR i j hij)
      i j hij := by
  let : Algebra (Robj i) (Robj j) := (fR i j hij).toAlgebra
  let : Algebra (Robj i) (Tobj fR lam0 hbot n m frel i) :=
    (RtoT fR lam0 hbot n m frel i).toAlgebra
  let : Algebra (Robj i) (Tobj fR lam0 hbot n m frel j) :=
    ((RtoT fR lam0 hbot n m frel j).comp (fR i j hij)).toAlgebra
  obtain ⟨e, he, he2⟩ := baseChangeQuotient fR lam0 hbot n m frel hRdir i j hij rfl
  exact cond4_fromBaseChange fR lam0 hbot n m frel q πT hqS hRdir fT hπcompat hfTR hfT i j hij
    ⟨e, fun t => by rw [he t, hfT i j hij], he2⟩

/-- **The S-side over a pointed index, given the `T`-side colimit data.**

Taking as input the `T`-side directed system `Tobj i = R_i[x]/(images of frel)` together with its
structural maps `πT i : T_i → T`, the directed-system data, the compatibility
`πT j ∘ fT = πT i` and the colimit isomorphism `eT : colim T_i ≅ T` — all produced by
`colimQuotient` — this constructs the S-side `q_i = πT i ⁻¹ q ⊂ T_i`, `S_i = (T_i)_{q_i}`, the
local transition maps `fS` and the local maps `ψ`, and verifies conditions (1), (3) and (4).

The pointed hypothesis `hbot : ∀ i, lam0 ≤ i` ensures that every index is `≥ lam0`, so that the
relations descend canonically to every `T_i` and condition (4) is available for all `i ≤ j`. -/
lemma descendSPointedBundle
    (φ : R →+* S) (hφ : IsLocalHom φ) (hφalg : φ = algebraMap R S)
    (hTfp : Algebra.FinitePresentation R T)
    (Mmon : Submonoid T) (hM : IsLocalization Mmon S)
    (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (hRloc : ∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij))
    (hRess : ∀ i, Algebra.EssFiniteType ℤ (Robj i))
    (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
    (heR : ∀ i, IsLocalHom ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i)))
    (lam0 : Λ) (hbot : ∀ i, lam0 ≤ i)
    (q : Ideal T) (hq : q.IsPrime) (hqS : IsLocalization q.primeCompl S)
    (n m : ℕ) (frel : Fin m → MvPolynomial (Fin n) (Robj lam0))
    -- the `T`-side colimit data (from `colimQuotient`):
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (πT : ∀ i, Tobj fR lam0 hbot n m frel i →+* T)
    (hTdir : DirectedSystem (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j)))
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    -- `R`-compatibility of the `T`-side colimit data (also from `colimQuotient`):
    (hfTR : ∀ i j (hij : i ≤ j),
      (fT i j hij).comp (RtoT fR lam0 hbot n m frel i)
        = (RtoT fR lam0 hbot n m frel j).comp (fR i j hij))
    (hπR : ∀ i, (πT i).comp (RtoT fR lam0 hbot n m frel i)
        = (algebraMap R T).comp (RtoR fR eR i))
    (hfT : ∀ i j (hij : i ≤ j),
      fT i j hij = fTmap fR lam0 hbot n m frel hRdir i j hij)
    (eT : Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
        (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
        ≃+* T)
    (heT : ∀ i, eT.toRingHom.comp (Ring.DirectLimit.of _ _ i) = πT i) :
    ∃ (Sobj : Λ → Type u)
      (_ : ∀ i, CommRing (Sobj i)) (_ : ∀ i, IsLocalRing (Sobj i))
      (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
      (ψ : ∀ i, Robj i →+* Sobj i)
      (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i)),
      (DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j))) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fS i j hij)) ∧
      (∀ i, IsLocalHom (ψ i)) ∧
      (∃ (eS : Ring.DirectLimit Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) ≃+* S),
         φ.comp eR.toRingHom = eS.toRingHom.comp (Ring.DirectLimit.map ψ comm)) ∧
      (∀ i, (ψ i).EssFiniteType) ∧
      (∀ i j (hij : i ≤ j),
        IsLocalizationAtPrimeOfBaseChange fR fS ψ comm i j hij) := by
  -- Assemble the S-side from the concrete defs `Sobj'`/`fSmap`/`psiS` and the sub-lemmas
  -- (locality, `DirectedSystem`, `EssFiniteType`, `colimLocalization` for condition (1) and
  -- `cond4_baseChange` for condition (4)).
  have : q.IsPrime := hq
  refine ⟨Sobj' fR lam0 hbot n m frel q πT,
    fun i => Sobj'_commRing fR lam0 hbot n m frel q πT i,
    fun i => Sobj'_isLocalRing fR lam0 hbot n m frel q πT i,
    fun i j hij => fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij,
    fun i => psiS fR lam0 hbot n m frel q πT i,
    fun i j hij => psiS_comm fR lam0 hbot n m frel q πT fT hπcompat hfTR i j hij,
    Sobj'_directedSystem fR lam0 hbot n m frel q πT fT hTdir hπcompat,
    fun i j hij => fSmap_isLocalHom fR lam0 hbot n m frel q πT fT hπcompat i j hij,
    fun i => psiS_isLocalHom φ fR eR lam0 hbot n m frel q πT hφ hφalg hqS heR hπR i,
    ?_,
    fun i => psiS_essFiniteType fR lam0 hbot n m frel q πT i,
    fun i j hij =>
      cond4_baseChange fR lam0 hbot n m frel q πT hqS hRdir fT hπcompat hfTR hfT i j hij⟩
  exact colimLocalization φ fR eR lam0 hbot n m frel q πT hφ hφalg hqS fT hTdir hπcompat hfTR hπR
    eT heT

end

/-- **S-side descent over a pointed index.**

The index `Λ` carries a designated bottom element `lam0` (`hbot : ∀ i, lam0 ≤ i`) and the
descended relation data at `lam0` is given: the prime `q`, the localization datum, and the
relations `frel` over `Robj lam0` presenting `T`. Because `lam0 ≤ i` for every `i`, the
construction `T_i = R_i[x]/(image of frel under fR lam0 i)` is canonical for every `i`, so
condition (4), `IsLocalizationAtPrimeOfBaseChange`, holds for all `i ≤ j`. -/
lemma descendSystemPointed
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (φ : R →+* S) (hφ : IsLocalHom φ)
    (T : Type u) [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
    (hTfp : Algebra.FinitePresentation R T)
    (M : Submonoid T) (hM : IsLocalization M S)
    (hφalg : φ = algebraMap R S)
    -- the FIXED, concrete R-side from `tag_00QT R`:
    (Λ : Type u) (instPre : Preorder Λ) (instNe : Nonempty Λ)
    (instDir : @IsDirected Λ (· ≤ ·))
    (Robj : Λ → Type u) (instRC : ∀ i, CommRing (Robj i)) (instRL : ∀ i, IsLocalRing (Robj i))
    (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (hRloc : ∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij))
    (hRess : ∀ i, Algebra.EssFiniteType ℤ (Robj i))
    (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
    (heR : ∀ i, IsLocalHom ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i)))
    -- the designated bottom element of the (cofinal-tail) index:
    (lam0 : Λ) (hbot : ∀ i, lam0 ≤ i)
    -- the descended relation data at `lam0` (from `descendRelations`):
    (q : Ideal T) (hq : q.IsPrime) (hqS : IsLocalization q.primeCompl S)
    (n m : ℕ) (frel : Fin m → MvPolynomial (Fin n) (Robj lam0))
    (hpres : Nonempty (T ≃ₐ[R] MvPolynomial (Fin n) R ⧸
      Ideal.span (Set.range (fun j => MvPolynomial.map
        ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ lam0)) (frel j))))) :
    ∃ (Sobj : Λ → Type u)
      (_ : ∀ i, CommRing (Sobj i)) (_ : ∀ i, IsLocalRing (Sobj i))
      (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
      (ψ : ∀ i, Robj i →+* Sobj i)
      (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i)),
      (DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j))) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fS i j hij)) ∧
      (∀ i, IsLocalHom (ψ i)) ∧
      (∃ (eS : Ring.DirectLimit Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) ≃+* S),
         φ.comp eR.toRingHom = eS.toRingHom.comp (Ring.DirectLimit.map ψ comm)) ∧
      (∀ i, (ψ i).EssFiniteType) ∧
      (∀ i j (hij : i ≤ j),
        IsLocalizationAtPrimeOfBaseChange fR fS ψ comm i j hij) := by
  -- First `colimQuotient` (`colim_i T_i ≅ T`), then assemble the S-side via
  -- `descendSPointedBundle`, which uses `colimLocalization` for condition (1) and
  -- `baseChangeQuotient` for condition (4).
  obtain ⟨fT, πT, hTdir, hπcompat, hfTR, hπR, hfT, eT, heT⟩ :=
    Descent.colimQuotient fR eR lam0 hbot n m frel hRdir hTfp hpres
  exact Descent.descendSPointedBundle φ hφ hφalg hTfp M hM fR hRdir hRloc hRess eR heR
    lam0 hbot q hq hqS n m frel fT πT hTdir hπcompat hfTR hπR hfT eT heT

/-- **The full descent construction, bundled.**

The `R`-side comes from `tag_00QT R`; passing to the cofinal tail `{λ ≥ λ₀}` of the index makes it
pointed, and the S-side together with all four conditions then comes from
`descendSystemPointed`. -/
@[sga "3 X 4.4" "Proof step b)"]
theorem systemBundle
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (φ : R →+* S) (hφ : IsLocalHom φ)
    (T : Type u) [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
    (hTfp : Algebra.FinitePresentation R T)
    (M : Submonoid T) (hM : IsLocalization M S)
    (hφalg : φ = algebraMap R S) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Robj : Λ → Type u) (Sobj : Λ → Type u)
      (_ : ∀ i, CommRing (Robj i)) (_ : ∀ i, CommRing (Sobj i))
      (_ : ∀ i, IsLocalRing (Robj i)) (_ : ∀ i, IsLocalRing (Sobj i))
      (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
      (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
      (ψ : ∀ i, Robj i →+* Sobj i)
      (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i)),
      (DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j))) ∧
      (DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j))) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij)) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fS i j hij)) ∧
      (∀ i, IsLocalHom (ψ i)) ∧
      (∃ (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
         (eS : Ring.DirectLimit Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) ≃+* S),
         φ.comp eR.toRingHom = eS.toRingHom.comp (Ring.DirectLimit.map ψ comm)) ∧
      (∀ i, Algebra.EssFiniteType ℤ (Robj i)) ∧
      (∀ i, (ψ i).EssFiniteType) ∧
      (∀ i j (hij : i ≤ j),
        IsLocalizationAtPrimeOfBaseChange fR fS ψ comm i j hij) := by
  -- the concrete R-side colimit presentation of `R`.
  obtain ⟨Λ₀, instPre, instNe, instDir, Robj, instRC, instRL, fR, hRdir, hRloc, hRess,
      eR, heR⟩ := tag_00QT R
  -- Register the R-side instances so the subtype index inherits them.
  let : Preorder Λ₀ := instPre
  let : Nonempty Λ₀ := instNe
  let : IsDirected Λ₀ (· ≤ ·) := instDir
  let : ∀ i, CommRing (Robj i) := instRC
  let : ∀ i, IsLocalRing (Robj i) := instRL
  -- descend the relations to a single stage `lam0`.
  obtain ⟨q, hq, hqS, lam0, n, m, frel, hpres⟩ :=
    descendRelations R S T hTfp M hM Λ₀ Robj fR eR
  -- pass to the cofinal tail `{x // lam0 ≤ x}`, in which every index is `≥ lam0`.
  let Lam := {x : Λ₀ // lam0 ≤ x}
  let : Preorder Lam := inferInstance
  have : Nonempty Lam := ⟨⟨lam0, le_refl _⟩⟩
  have : IsDirected Lam (· ≤ ·) := ⟨fun a b =>
    let ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.val b.val
    ⟨⟨c, a.property.trans hac⟩, hac, hbc⟩⟩
  -- restricted R-side family over the tail
  let Robj' : Lam → Type u := fun i => Robj i.val
  let : ∀ i, CommRing (Robj' i) := fun i => instRC i.val
  let : ∀ i, IsLocalRing (Robj' i) := fun i => instRL i.val
  let fR' : ∀ i j, i ≤ j → Robj' i →+* Robj' j := fun i j h => fR i.val j.val h
  have hRdir' : DirectedSystem Robj' (fun i j h => (fR' i j h : Robj' i → Robj' j)) :=
    ⟨fun i x => hRdir.map_self (i := i.val) x,
      fun {k j i} hij hjk x => hRdir.map_map (k := k.val) (j := j.val) (i := i.val) hij hjk x⟩
  have hRloc' : ∀ i j (hij : i ≤ j), IsLocalHom (fR' i j hij) :=
    fun i j hij => hRloc i.val j.val hij
  have hRess' : ∀ i, Algebra.EssFiniteType ℤ (Robj' i) := fun i => hRess i.val
  -- the colimit over the tail is still `R`, with structural maps agreeing.
  obtain ⟨eR', heR', hcompat⟩ :=
    cofinalColimit R Λ₀ Robj fR hRdir eR heR lam0
  -- The bottom element of the tail; note `Robj' bot = Robj lam0` definitionally.
  let bot : Lam := ⟨lam0, le_refl _⟩
  -- Transport the presentation from `eR/lam0` (given by `descendRelations`) to the tail's
  -- `eR'/bot`, using the cofinality compatibility `hcompat bot` (the structural map of the tail
  -- at `bot` equals the original structural map at `lam0`).
  have hpres' : Nonempty (T ≃ₐ[R] MvPolynomial (Fin n) R ⧸
      Ideal.span (Set.range (fun j => MvPolynomial.map
        ((eR'.toRingHom).comp (Ring.DirectLimit.of Robj' _ bot)) (frel j)))) := by
    rw [hcompat bot]
    exact hpres
  -- build the S-side over the pointed tail index, where `∀ i, lam0' ≤ i`.
  obtain ⟨Sobj, instSC, instSL, fS, ψ, comm, hSdir, hSloc, hψloc, ⟨eS, hcomm⟩, hψess, hbc⟩ :=
    descendSystemPointed R S φ hφ T hTfp M hM hφalg Lam inferInstance inferInstance inferInstance
      Robj' (fun i => instRC i.val) (fun i => instRL i.val) fR' hRdir' hRloc' hRess' eR' heR'
      bot (fun i => i.property) q hq hqS n m frel hpres'
  exact ⟨Lam, inferInstance, inferInstance, inferInstance, Robj', Sobj,
    (fun i => instRC i.val), instSC, (fun i => instRL i.val), instSL, fR', fS, ψ,
    comm, hRdir', hSdir, hRloc', hSloc, hψloc, ⟨eR', eS, hcomm⟩, hRess', hψess, hbc⟩

end Descent

/-- **The descent, with the finite-presentation data spelled out.**

The conclusion is that of `descent_of_finitePresentation`, but the finite-presentation and
localization data for `S` as an `R`-algebra is given explicitly:

- `T` is a finitely *presented* `R`-algebra, with `IsScalarTower R T S`;
- a submonoid `M ≤ T` realizes `S` as the localization `T[M⁻¹]`;
- `φ = algebraMap R S` is the structure map, and it is local.

Proof outline. Write `R = colim_λ R_λ` using `tag_00QT R`. Refine the finite presentation of `T`
to a polynomial presentation `R[x₁, …, xₙ]/(f₁, …, f_m)` and descend the finitely many
coefficients of the `f_j` to a single stage `λ₀`; set `T_λ = R_λ[x]/(f_{j,λ})`, let `q_λ` be the
contraction of the prime `q ⊂ T` along `T_λ → T → S`, and put `S_λ = (T_λ)_{q_λ}`. Over the tail
`{λ ≥ λ₀}` this is a directed system, and `ψ_λ` and the transition maps are local because the
contractions are compatible. Condition (1) is that the colimit commutes with taking a polynomial
ring, a quotient and a localization; condition (3) is that `S_λ` is a localization of a
finite-type `R_λ`-algebra; condition (4) follows from `T_λ ⊗_{R_λ} R_μ ≅ T_μ`, where base change
commutes with a quotient of a polynomial ring by a finitely generated ideal, together with
localization of a localization. -/
@[sga "3 X 4.4" "Proof step b)"]
theorem descent_core
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (φ : R →+* S) (hφ : IsLocalHom φ)
    (T : Type u) [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
    (hTfp : Algebra.FinitePresentation R T)
    (M : Submonoid T) (hM : IsLocalization M S)
    (hφalg : φ = algebraMap R S) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Robj : Λ → Type u) (Sobj : Λ → Type u)
      (_ : ∀ i, CommRing (Robj i)) (_ : ∀ i, CommRing (Sobj i))
      (_ : ∀ i, IsLocalRing (Robj i)) (_ : ∀ i, IsLocalRing (Sobj i))
      (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
      (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
      (ψ : ∀ i, Robj i →+* Sobj i)
      (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i)),
      (DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j))) ∧
      (DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j))) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij)) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fS i j hij)) ∧
      (∀ i, IsLocalHom (ψ i)) ∧
      (∃ (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
         (eS : Ring.DirectLimit Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) ≃+* S),
         φ.comp eR.toRingHom = eS.toRingHom.comp (Ring.DirectLimit.map ψ comm)) ∧
      (∀ i, Algebra.EssFiniteType ℤ (Robj i)) ∧
      (∀ i, (ψ i).EssFiniteType) ∧
      (∀ i j (hij : i ≤ j),
        IsLocalizationAtPrimeOfBaseChange fR fS ψ comm i j hij) := by
  -- The system together with all four conditions is `Descent.systemBundle`, which has the
  -- same conclusion as `descent_core`.
  exact Descent.systemBundle R S φ hφ T hTfp M hM hφalg

/-- If `φ : R → S` is a local homomorphism of local rings and `S` is essentially of finite
presentation over `R` via `φ`, then `φ` is the filtered colimit of a directed system of local
homomorphisms `ψ_λ : R_λ → S_λ` of local rings satisfying conditions (1)–(4). -/
@[sga "3 X 4.4" "Proof of 4.4"]
theorem descent_of_finitePresentation
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) (hφ : IsLocalHom φ) (hfp : φ.EssFinitePresentation) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Robj : Λ → Type u) (Sobj : Λ → Type u)
      (_ : ∀ i, CommRing (Robj i)) (_ : ∀ i, CommRing (Sobj i))
      (_ : ∀ i, IsLocalRing (Robj i)) (_ : ∀ i, IsLocalRing (Sobj i))
      (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
      (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
      (ψ : ∀ i, Robj i →+* Sobj i)
      (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i)),
      (DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j))) ∧
      (DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j))) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij)) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fS i j hij)) ∧
      (∀ i, IsLocalHom (ψ i)) ∧
      (∃ (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
         (eS : Ring.DirectLimit Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) ≃+* S),
         φ.comp eR.toRingHom = eS.toRingHom.comp (Ring.DirectLimit.map ψ comm)) ∧
      (∀ i, Algebra.EssFiniteType ℤ (Robj i)) ∧
      (∀ i, (ψ i).EssFiniteType) ∧
      (∀ i j (hij : i ≤ j),
        IsLocalizationAtPrimeOfBaseChange fR fS ψ comm i j hij) := by
  -- Unfold `hfp` into the finite-presentation/localization data, then hand off to
  -- `descent_core`. The algebra structure on `S` is `φ.toAlgebra`, so `φ = algebraMap R S`
  -- holds by `rfl`.
  let := φ.toAlgebra
  obtain ⟨T, _, _, _, _, hTfp, M, hM⟩ := hfp
  exact descent_core R S φ hφ T hTfp M hM rfl

namespace Stacks.EssentialFiniteness.ColimitPresentation

/-- **Stacks Project, Tag 00QV (Lemma 10.127.11).**

Let `φ : R → S` be a local homomorphism of local rings. If `S` is essentially of finite
presentation over `R` (via `φ`), then `φ` is a filtered colimit of a directed system of local
homomorphisms `ψ_λ : R_λ → S_λ` between local rings, with local transition maps, such that:
(1) the colimit of the system is `φ`; (2) each `R_λ` is essentially of finite type over `ℤ`;
(3) each `ψ_λ` is essentially of finite type; (4) for `λ ≤ μ`, the canonical base-change map
`S_λ ⊗_{R_λ} R_μ → S_μ` exhibits `S_μ` as a localization of `S_λ ⊗_{R_λ} R_μ` at a prime. -/
@[stacks 00QV]
theorem main_theorem_00qv
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (hfp : φ.EssFinitePresentation) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Robj : Λ → Type u) (Sobj : Λ → Type u)
      (_ : ∀ i, CommRing (Robj i)) (_ : ∀ i, CommRing (Sobj i))
      (_ : ∀ i, IsLocalRing (Robj i)) (_ : ∀ i, IsLocalRing (Sobj i))
      (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
      (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
      (ψ : ∀ i, Robj i →+* Sobj i)
      (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i)),
      -- the transition maps form directed systems of rings
      (DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j))) ∧
      (DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j))) ∧
      -- all transition maps and all `ψ_λ` are local homomorphisms
      (∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij)) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fS i j hij)) ∧
      (∀ i, IsLocalHom (ψ i)) ∧
      -- (1) the colimit of the system `R_λ → S_λ` recovers `φ : R → S`
      (∃ (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
         (eS : Ring.DirectLimit Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) ≃+* S),
         φ.comp eR.toRingHom = eS.toRingHom.comp (Ring.DirectLimit.map ψ comm)) ∧
      -- (2) each `R_λ` is essentially of finite type over `ℤ`
      (∀ i, Algebra.EssFiniteType ℤ (Robj i)) ∧
      -- (3) each fiber map `ψ_λ` is essentially of finite type
      (∀ i, (ψ i).EssFiniteType) ∧
      -- (4) each transition map is a localization at a prime after base change
      (∀ i j (hij : i ≤ j),
        IsLocalizationAtPrimeOfBaseChange fR fS ψ comm i j hij) := by
  -- Stacks Tag 00QV is the descent of the finite-presentation data along the colimit
  -- presentation of `R` (Tag 00QT), which is `descent_of_finitePresentation`; condition (2),
  -- that each `R_λ` is essentially of finite type over `ℤ`, is supplied by `tag_00QT`.
  exact descent_of_finitePresentation R S φ hφ hfp

end Stacks.EssentialFiniteness.ColimitPresentation

/-! ### Comparison of `EssFinitePresentation` with the neighbouring finiteness notions -/

/-- Essentially of finite presentation implies essentially of finite type (Tag 00QM). -/
theorem essFinitePresentation_essFiniteType
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.EssFinitePresentation R S) : Algebra.EssFiniteType R S := by
  obtain ⟨T, _, _, _, _, hTfp, M, hM⟩ := h
  have : Algebra.FiniteType R T := Algebra.FiniteType.of_finitePresentation
  have : Algebra.EssFiniteType R T := Algebra.EssFiniteType.of_finiteType R T
  exact (Algebra.EssFiniteType.comp_iff R T S).mpr (.of_isLocalization S M)

/-- A finitely presented algebra is essentially of finite presentation: take the trivial
localization at `M = 1`. -/
theorem finitePresentation_essFinitePresentation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FinitePresentation R S) : Algebra.EssFinitePresentation R S :=
  ⟨S, inferInstance, inferInstance, Algebra.id S, IsScalarTower.right, h, ⊥,
    IsLocalization.self (by simp)⟩

end

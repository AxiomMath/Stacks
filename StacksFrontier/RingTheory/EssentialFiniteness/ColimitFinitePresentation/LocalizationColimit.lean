module

public import StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation.QuotientColimit

/-!
# Descent of finite-presentation data: the localization side

The local rings `S_i = (T_i)_{q_i}` over a pointed index, their transition and structure maps,
the colimit `colim_i S_i ≅ S` (`Descent.colimLocalization`, condition (1)), and the base-change
isomorphism `T_i ⊗_{R_i} R_j ≅ T_j` (`Descent.baseChangeQuotient`). Split from
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

/-!
### The S-side

Here `q : Ideal T` is the prime with `S = T_q` (`hqS : IsLocalization q.primeCompl S`) and
`πT i : T_i → T` is the structural map produced by `colimQuotient`. We set `q_i := πT i ⁻¹ q` and
`S_i := (T_i)_{q_i}`, mirroring the `T`-side above.
-/

variable (q : Ideal T) [hq : q.IsPrime]
variable (πT : ∀ i, Tobj fR lam0 hbot n m frel i →+* T)

/-- The contracted prime `q_i = πT i ⁻¹ q ⊂ T_i`. -/
noncomputable def qcon (i : Λ) : Ideal (Tobj fR lam0 hbot n m frel i) :=
  Ideal.comap (πT i) q

/-- `qcon i` is prime, being the contraction of the prime `q` along `πT i`. -/
instance qcon_isPrime (i : Λ) : (qcon fR lam0 hbot n m frel q πT i).IsPrime :=
  Ideal.IsPrime.comap (πT i)

/-- `S_i = (T_i)_{q_i}`, a local ring. -/
def Sobj' (i : Λ) : Type u :=
  Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i)

/-- The commutative ring structure on `S_i`. -/
noncomputable instance Sobj'_commRing (i : Λ) :
    CommRing (Sobj' fR lam0 hbot n m frel q πT i) :=
  inferInstanceAs (CommRing (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i)))

/-- `S_i` is a local ring. -/
noncomputable instance Sobj'_isLocalRing (i : Λ) :
    IsLocalRing (Sobj' fR lam0 hbot n m frel q πT i) :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i)))

/-- The `T_i`-algebra structure on `S_i`. -/
noncomputable instance Sobj'_algebra (i : Λ) :
    Algebra (Tobj fR lam0 hbot n m frel i) (Sobj' fR lam0 hbot n m frel q πT i) :=
  inferInstanceAs (Algebra (Tobj fR lam0 hbot n m frel i)
    (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i)))

/-- `S_i` is the localization of `T_i` at the prime `q_i`. -/
instance Sobj'_isLocalization (i : Λ) :
    IsLocalization (qcon fR lam0 hbot n m frel q πT i).primeCompl
      (Sobj' fR lam0 hbot n m frel q πT i) :=
  inferInstanceAs (IsLocalization (qcon fR lam0 hbot n m frel q πT i).primeCompl
    (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i)))

/-- Compatibility of the contracted primes: `q_i = (fT i j) ⁻¹ q_j`, from
`πT j ∘ fT i j = πT i`. -/
lemma qcon_compat
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (i j : Λ) (hij : i ≤ j) :
    qcon fR lam0 hbot n m frel q πT i
      = Ideal.comap (fT i j hij) (qcon fR lam0 hbot n m frel q πT j) := by
  unfold qcon
  rw [Ideal.comap_comap, hπcompat i j hij]

/-- The S-side transition map `S_i → S_j`, via `Localization.localRingHom` on the
contracted primes. -/
noncomputable def fSmap
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (i j : Λ) (hij : i ≤ j) :
    Sobj' fR lam0 hbot n m frel q πT i →+* Sobj' fR lam0 hbot n m frel q πT j :=
  Localization.localRingHom (qcon fR lam0 hbot n m frel q πT i)
    (qcon fR lam0 hbot n m frel q πT j) (fT i j hij)
    (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat i j hij)

/-- `fSmap` sends `algebraMap x` to `algebraMap (fT x)`. -/
private theorem fSmap_algebraMap
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (i j : Λ) (hij : i ≤ j) (x : Tobj fR lam0 hbot n m frel i) :
    fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij
        ((algebraMap (Tobj fR lam0 hbot n m frel i) (Sobj' fR lam0 hbot n m frel q πT i)) x)
      = (algebraMap (Tobj fR lam0 hbot n m frel j) (Sobj' fR lam0 hbot n m frel q πT j))
          (fT i j hij x) :=
  Localization.localRingHom_to_map _ _ (fT i j hij)
    (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat i j hij) x

/-- `ψ_i : R_i → T_i → S_i`. -/
noncomputable def psiS (i : Λ) :
    Robj i →+* Sobj' fR lam0 hbot n m frel q πT i :=
  (algebraMap (Tobj fR lam0 hbot n m frel i)
      (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i))).comp
    (RtoT fR lam0 hbot n m frel i)

/-- The commuting square `fS i j ∘ ψ i = ψ j ∘ fR i j`, from the analogous `T`-side square
`fT i j ∘ RtoT i = RtoT j ∘ fR i j` and functoriality of `Localization.localRingHom`. -/
lemma psiS_comm
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (hfTR : ∀ i j (hij : i ≤ j),
      (fT i j hij).comp (RtoT fR lam0 hbot n m frel i)
        = (RtoT fR lam0 hbot n m frel j).comp (fR i j hij))
    (i j : Λ) (hij : i ≤ j) :
    (psiS fR lam0 hbot n m frel q πT j).comp (fR i j hij)
      = (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij).comp
          (psiS fR lam0 hbot n m frel q πT i) := by
  apply RingHom.ext
  intro x
  show (algebraMap (Tobj fR lam0 hbot n m frel j)
        (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT j)))
        (RtoT fR lam0 hbot n m frel j (fR i j hij x))
    = (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij)
        ((algebraMap (Tobj fR lam0 hbot n m frel i)
          (Localization.AtPrime (qcon fR lam0 hbot n m frel q πT i)))
          (RtoT fR lam0 hbot n m frel i x))
  have hT : RtoT fR lam0 hbot n m frel j (fR i j hij x)
      = fT i j hij (RtoT fR lam0 hbot n m frel i x) :=
    (DFunLike.congr_fun (hfTR i j hij) x).symm
  rw [hT]
  exact (fSmap_algebraMap fR lam0 hbot n m frel q πT fT hπcompat i j hij _).symm

/-- `Localization.localRingHom` only depends on the underlying ring hom. -/
private theorem localRingHom_congr {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A)
    [I.IsPrime] (J : Ideal B) [J.IsPrime] {f g : A →+* B} (hf : I = J.comap f)
    (hg : I = J.comap g) (h : f = g) :
    Localization.localRingHom I J f hf = Localization.localRingHom I J g hg := by
  subst h
  rfl

/-- The S-side `DirectedSystem`. -/
lemma Sobj'_directedSystem
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hTdir : DirectedSystem (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j)))
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i) :
    DirectedSystem (Sobj' fR lam0 hbot n m frel q πT)
      (fun i j h => (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h :
        Sobj' fR lam0 hbot n m frel q πT i → Sobj' fR lam0 hbot n m frel q πT j)) := by
  refine ⟨?_, ?_⟩
  · -- map_self
    intro i x
    have hself : fSmap fR lam0 hbot n m frel q πT fT hπcompat i i le_rfl
        = RingHom.id (Sobj' fR lam0 hbot n m frel q πT i) := by
      have hfT : fT i i le_rfl = RingHom.id (Tobj fR lam0 hbot n m frel i) :=
        RingHom.ext fun y => hTdir.map_self y
      exact (localRingHom_congr _ _ _ _ hfT).trans (Localization.localRingHom_id _)
    exact congrFun (congrArg DFunLike.coe hself) x
  · -- map_map
    intro k j i hij hjk x
    have hmm : (fSmap fR lam0 hbot n m frel q πT fT hπcompat j k hjk).comp
          (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij)
        = fSmap fR lam0 hbot n m frel q πT fT hπcompat i k (le_trans hij hjk) := by
      have hfT : (fT j k hjk).comp (fT i j hij) = fT i k (le_trans hij hjk) :=
        RingHom.ext fun y => hTdir.map_map hij hjk y
      have hcomp := Localization.localRingHom_comp
          (qcon fR lam0 hbot n m frel q πT i)
          (qcon fR lam0 hbot n m frel q πT j)
          (qcon fR lam0 hbot n m frel q πT k)
          (fT i j hij)
          (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat i j hij)
          (fT j k hjk)
          (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat j k hjk)
      show (Localization.localRingHom (qcon fR lam0 hbot n m frel q πT j)
                (qcon fR lam0 hbot n m frel q πT k) (fT j k hjk)
                (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat j k hjk)).comp
            (Localization.localRingHom (qcon fR lam0 hbot n m frel q πT i)
                (qcon fR lam0 hbot n m frel q πT j) (fT i j hij)
                (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat i j hij))
          = Localization.localRingHom (qcon fR lam0 hbot n m frel q πT i)
                (qcon fR lam0 hbot n m frel q πT k) (fT i k (le_trans hij hjk))
                (qcon_compat fR lam0 hbot n m frel q πT fT hπcompat i k (le_trans hij hjk))
      exact hcomp.symm.trans
        (localRingHom_congr _ _ _ _ hfT)
    exact congrFun (congrArg DFunLike.coe hmm) x

/-- The S-side transition maps are local. -/
lemma fSmap_isLocalHom
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (i j : Λ) (hij : i ≤ j) :
    IsLocalHom (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij) := by
  unfold fSmap
  exact Localization.isLocalHom_localRingHom _ _ _ _

/-- `ψ_i` is local. -/
lemma psiS_isLocalHom (hφ : IsLocalHom φ) (hφalg : φ = algebraMap R S)
    (hqS : IsLocalization q.primeCompl S)
    (heR : ∀ i, IsLocalHom ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i)))
    (hπR : ∀ i, (πT i).comp (RtoT fR lam0 hbot n m frel i)
        = (algebraMap R T).comp (RtoR fR eR i))
    (i : Λ) :
    IsLocalHom (psiS fR lam0 hbot n m frel q πT i) := by
  unfold psiS
  set qc : Ideal (Tobj fR lam0 hbot n m frel i) := qcon fR lam0 hbot n m frel q πT i
  have hqcdef : qc = Ideal.comap (πT i) q := rfl
  set Si := Localization.AtPrime qc
  have : IsLocalization.AtPrime S q := hqS
  have hAtQ : Ideal.comap (algebraMap T S) (IsLocalRing.maximalIdeal S) = q := by
    simpa [Ideal.under] using IsLocalization.AtPrime.under_maximalIdeal S q
  have hRT : Ideal.comap (algebraMap R T) q = IsLocalRing.maximalIdeal R := by
    rw [← hAtQ, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R T S, ← hφalg]
    exact ((IsLocalRing.local_hom_TFAE φ).out 1 5).mp hφ
  have : IsLocalization.AtPrime Si qc :=
    inferInstanceAs (IsLocalization qc.primeCompl (Localization.AtPrime qc))
  have hAtQc : Ideal.comap (algebraMap (Tobj fR lam0 hbot n m frel i) Si)
      (IsLocalRing.maximalIdeal Si) = qc := by
    simpa [Ideal.under] using IsLocalization.AtPrime.under_maximalIdeal Si qc
  apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
  calc Ideal.comap ((algebraMap (Tobj fR lam0 hbot n m frel i) Si).comp
          (RtoT fR lam0 hbot n m frel i)) (IsLocalRing.maximalIdeal Si)
      = Ideal.comap (RtoT fR lam0 hbot n m frel i)
          (Ideal.comap (algebraMap (Tobj fR lam0 hbot n m frel i) Si)
            (IsLocalRing.maximalIdeal Si)) := by rw [← Ideal.comap_comap]
    _ = IsLocalRing.maximalIdeal (Robj i) := by
      rw [hAtQc, hqcdef, Ideal.comap_comap, hπR i, ← Ideal.comap_comap, hRT]
      exact ((IsLocalRing.local_hom_TFAE (RtoR fR eR i)).out 1 5).mp (heR i)

/-- `ψ_i` is essentially of finite type (cond 3): `S_i = (T_i)_{q_i}` is a localization
of the finite-type `R_i`-algebra `T_i`. -/
lemma psiS_essFiniteType (i : Λ) :
    (psiS fR lam0 hbot n m frel q πT i).EssFiniteType := by
  -- Algebra instances along R_i → T_i → S_i (use `RtoT i` for the R_i → T_i structure,
  -- matching the rest of the file; `Tobj`'s `CommRing` is its own instance).
  let instRiTi : Algebra (Robj i) (Tobj fR lam0 hbot n m frel i) :=
    (RtoT fR lam0 hbot n m frel i).toAlgebra
  let instRiSi : Algebra (Robj i) (Sobj' fR lam0 hbot n m frel q πT i) :=
    (psiS fR lam0 hbot n m frel q πT i).toAlgebra
  -- Unfold the `RingHom.EssFiniteType` goal into the algebra version.
  rw [RingHom.EssFiniteType]
  -- Scalar tower R_i → T_i → S_i (psiS = algebraMap_T_S ∘ RtoT, both algebraMaps are RtoT/psiS).
  have instST : IsScalarTower (Robj i) (Tobj fR lam0 hbot n m frel i)
      (Sobj' fR lam0 hbot n m frel q πT i) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Step 1: T_i is finite type over R_i (quotient of a polynomial ring).
  -- `mk : R_i[x] → T_i` as an `R_i`-algebra hom (commutes since `RtoT i = mk ∘ C`).
  have hRT_FT : Algebra.FiniteType (Robj i) (Tobj fR lam0 hbot n m frel i) := by
    let mkAlg : MvPolynomial (Fin n) (Robj i) →ₐ[Robj i] Tobj fR lam0 hbot n m frel i :=
      { Ideal.Quotient.mk (Irel fR lam0 hbot n m frel i) with
        commutes' := fun r => by
          show Ideal.Quotient.mk (Irel fR lam0 hbot n m frel i) (MvPolynomial.C r)
            = RtoT fR lam0 hbot n m frel i r
          rw [RtoT]; rfl }
    exact Algebra.FiniteType.of_surjective mkAlg Ideal.Quotient.mk_surjective
  have hRT : Algebra.EssFiniteType (Robj i) (Tobj fR lam0 hbot n m frel i) :=
    Algebra.EssFiniteType.of_finiteType (Robj i) (Tobj fR lam0 hbot n m frel i)
  -- Step 2: S_i = (T_i)_{q_i} is a localization of T_i, hence ess finite type.
  have hTS : Algebra.EssFiniteType (Tobj fR lam0 hbot n m frel i)
      (Sobj' fR lam0 hbot n m frel q πT i) :=
    Algebra.EssFiniteType.of_isLocalization (Sobj' fR lam0 hbot n m frel q πT i)
      (qcon fR lam0 hbot n m frel q πT i).primeCompl
  -- Step 3: compose.
  exact (Algebra.EssFiniteType.comp_iff (Robj i) (Tobj fR lam0 hbot n m frel i)
    (Sobj' fR lam0 hbot n m frel q πT i)).mpr hTS

/-- The composite `T_i → T → S` sends `(qcon i).primeCompl` into units of `S`. -/
lemma sigmaS_units (hqS : IsLocalization q.primeCompl S) (i : Λ)
    (y : (qcon fR lam0 hbot n m frel q πT i).primeCompl) :
    IsUnit (((algebraMap T S).comp (πT i)) (y : Tobj fR lam0 hbot n m frel i)) := by
  rw [RingHom.comp_apply]
  exact IsLocalization.map_units S
    (⟨(πT i) (y : Tobj fR lam0 hbot n m frel i), fun hmem => y.property hmem⟩ : q.primeCompl)

/-- The structural map `S_i = (T_i)_{q_i} → S`, factoring `T_i → T → S` through the
localization. -/
noncomputable def sigmaS (hqS : IsLocalization q.primeCompl S) (i : Λ) :
    Sobj' fR lam0 hbot n m frel q πT i →+* S :=
  IsLocalization.lift (M := (qcon fR lam0 hbot n m frel q πT i).primeCompl)
    (S := Sobj' fR lam0 hbot n m frel q πT i)
    (g := (algebraMap T S).comp (πT i)) (sigmaS_units fR lam0 hbot n m frel q πT hqS i)

/-- `sigmaS` on `algebraMap` images. -/
lemma sigmaS_algebraMap (hqS : IsLocalization q.primeCompl S) (i : Λ)
    (x : Tobj fR lam0 hbot n m frel i) :
    sigmaS fR lam0 hbot n m frel q πT hqS i
        ((algebraMap (Tobj fR lam0 hbot n m frel i)
          (Sobj' fR lam0 hbot n m frel q πT i)) x)
      = (algebraMap T S) ((πT i) x) := by
  rw [sigmaS]
  exact IsLocalization.lift_eq (sigmaS_units fR lam0 hbot n m frel q πT hqS i) x

/-- Membership: `y ∈ (qcon i).primeCompl ⟹ πT i y ∈ q.primeCompl`. -/
lemma piT_mem_primeCompl (i : Λ)
    {y : Tobj fR lam0 hbot n m frel i} (hy : y ∈ (qcon fR lam0 hbot n m frel q πT i).primeCompl) :
    (πT i) y ∈ q.primeCompl :=
  fun hmem => hy hmem

/-- `sigmaS i` sends `mk' xt y` to `mk' S (πT i xt) (πT i y)`. -/
lemma sigmaS_mk' (hqS : IsLocalization q.primeCompl S) (i : Λ)
    (xt : Tobj fR lam0 hbot n m frel i) (y : (qcon fR lam0 hbot n m frel q πT i).primeCompl) :
    sigmaS fR lam0 hbot n m frel q πT hqS i
        (IsLocalization.mk' (Sobj' fR lam0 hbot n m frel q πT i) xt y)
      = IsLocalization.mk' S ((πT i) xt)
          (⟨(πT i) (y : Tobj fR lam0 hbot n m frel i),
            piT_mem_primeCompl fR lam0 hbot n m frel q πT i y.2⟩ : q.primeCompl) := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have hspec : IsLocalization.mk' (Sobj' fR lam0 hbot n m frel q πT i) xt y
        * (algebraMap (Tobj fR lam0 hbot n m frel i)
            (Sobj' fR lam0 hbot n m frel q πT i)) (y : Tobj fR lam0 hbot n m frel i)
      = (algebraMap (Tobj fR lam0 hbot n m frel i)
            (Sobj' fR lam0 hbot n m frel q πT i)) xt :=
    IsLocalization.mk'_spec (Sobj' fR lam0 hbot n m frel q πT i) xt y
  calc sigmaS fR lam0 hbot n m frel q πT hqS i
          (IsLocalization.mk' (Sobj' fR lam0 hbot n m frel q πT i) xt y)
        * (algebraMap T S) ((πT i) (y : Tobj fR lam0 hbot n m frel i))
      = sigmaS fR lam0 hbot n m frel q πT hqS i
          (IsLocalization.mk' (Sobj' fR lam0 hbot n m frel q πT i) xt y)
        * sigmaS fR lam0 hbot n m frel q πT hqS i
          ((algebraMap (Tobj fR lam0 hbot n m frel i)
            (Sobj' fR lam0 hbot n m frel q πT i)) (y : Tobj fR lam0 hbot n m frel i)) := by
          rw [sigmaS_algebraMap]
    _ = sigmaS fR lam0 hbot n m frel q πT hqS i
          (IsLocalization.mk' (Sobj' fR lam0 hbot n m frel q πT i) xt y
            * (algebraMap (Tobj fR lam0 hbot n m frel i)
              (Sobj' fR lam0 hbot n m frel q πT i)) (y : Tobj fR lam0 hbot n m frel i)) := by
          rw [map_mul]
    _ = sigmaS fR lam0 hbot n m frel q πT hqS i
          ((algebraMap (Tobj fR lam0 hbot n m frel i)
            (Sobj' fR lam0 hbot n m frel q πT i)) xt) := by rw [hspec]
    _ = (algebraMap T S) ((πT i) xt) :=
          sigmaS_algebraMap fR lam0 hbot n m frel q πT hqS i xt

/-- Compatibility of the `sigmaS` maps with the S-side transition maps. -/
lemma sigmaS_compat (hqS : IsLocalization q.primeCompl S)
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (i j : Λ) (hij : i ≤ j) :
    (sigmaS fR lam0 hbot n m frel q πT hqS j).comp
        (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij)
      = sigmaS fR lam0 hbot n m frel q πT hqS i := by
  apply IsLocalization.ringHom_ext (qcon fR lam0 hbot n m frel q πT i).primeCompl
  apply RingHom.ext
  intro x
  -- both sides on `algebraMap (T_i) (S_i) x`
  show sigmaS fR lam0 hbot n m frel q πT hqS j
        (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j hij
          ((algebraMap (Tobj fR lam0 hbot n m frel i)
            (Sobj' fR lam0 hbot n m frel q πT i)) x))
      = sigmaS fR lam0 hbot n m frel q πT hqS i
          ((algebraMap (Tobj fR lam0 hbot n m frel i)
            (Sobj' fR lam0 hbot n m frel q πT i)) x)
  rw [fSmap_algebraMap, sigmaS_algebraMap, sigmaS_algebraMap]
  congr 1
  exact DFunLike.congr_fun (hπcompat i j hij) x

/-- The induced map `colim S_i → S`. -/
noncomputable def iotaS (hqS : IsLocalization q.primeCompl S)
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i) :
    Ring.DirectLimit (Sobj' fR lam0 hbot n m frel q πT)
      (fun i j h => (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h :
        Sobj' fR lam0 hbot n m frel q πT i → Sobj' fR lam0 hbot n m frel q πT j)) →+* S :=
  Ring.DirectLimit.lift _ _ _ (sigmaS fR lam0 hbot n m frel q πT hqS)
    (fun i j hij x => DFunLike.congr_fun
      (sigmaS_compat fR lam0 hbot n m frel q πT hqS fT hπcompat i j hij) x)

/-- `iotaS` restricted along the `i`-th structural map of the colimit is `sigmaS i`. -/
lemma iotaS_of (hqS : IsLocalization q.primeCompl S)
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (i : Λ) (x : Sobj' fR lam0 hbot n m frel q πT i) :
    iotaS fR lam0 hbot n m frel q πT hqS fT hπcompat
        (Ring.DirectLimit.of _ _ i x)
      = sigmaS fR lam0 hbot n m frel q πT hqS i x :=
   Ring.DirectLimit.lift_of _ _ _ _ _

/-- `πT k x = eT (of k x)`. -/
lemma piT_eq_eT
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (eT : Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
        (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
        ≃+* T)
    (heT : ∀ i, eT.toRingHom.comp (Ring.DirectLimit.of _ _ i) = πT i)
    (k : Λ) (x : Tobj fR lam0 hbot n m frel k) :
    (πT k) x = eT (Ring.DirectLimit.of _ _ k x) :=
  (DFunLike.congr_fun (heT k) x).symm

/-- Every `t : T` lifts to some `T_k` with `i ≤ k`. -/
private theorem exists_piT_eq
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (eT : Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
        (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
        ≃+* T)
    (heT : ∀ i, eT.toRingHom.comp (Ring.DirectLimit.of _ _ i) = πT i) (i : Λ) (t : T) :
    ∃ k, ∃ _ : i ≤ k, ∃ x : Tobj fR lam0 hbot n m frel k, (πT k) x = t := by
  obtain ⟨j, x, hx⟩ := Ring.DirectLimit.exists_of (eT.symm t)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  refine ⟨k, hik, fT j k hjk x, ?_⟩
  rw [← RingHom.comp_apply, hπcompat j k hjk, piT_eq_eT fR lam0 hbot n m frel πT fT eT heT j x, hx,
    eT.apply_symm_apply]

/-- `iotaS` is surjective. -/
lemma iotaS_surjective (hqS : IsLocalization q.primeCompl S)
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (eT : Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
        (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
        ≃+* T)
    (heT : ∀ i, eT.toRingHom.comp (Ring.DirectLimit.of _ _ i) = πT i) :
    Function.Surjective (iotaS fR lam0 hbot n m frel q πT hqS fT hπcompat) := by
  intro s
  obtain ⟨⟨t, u⟩, hs⟩ := IsLocalization.mk'_surjective q.primeCompl s
  obtain ⟨it, -, xt, hxt⟩ :=
    exists_piT_eq fR lam0 hbot n m frel πT fT hπcompat eT heT lam0 t
  obtain ⟨i, hiti, XU, hpiXU⟩ :=
    exists_piT_eq fR lam0 hbot n m frel πT fT hπcompat eT heT it (u : T)
  have hpiXT : (πT i) (fT it i hiti xt) = t := (RingHom.congr_fun (hπcompat it i hiti) xt).trans hxt
  have hXUmem : XU ∈ (qcon fR lam0 hbot n m frel q πT i).primeCompl := by
    show (πT i) XU ∈ q.primeCompl
    rw [hpiXU]
    exact u.property
  refine ⟨Ring.DirectLimit.of _ _ i
      (IsLocalization.mk' (Sobj' fR lam0 hbot n m frel q πT i) (fT it i hiti xt) ⟨XU, hXUmem⟩), ?_⟩
  rw [iotaS_of, sigmaS_mk', ← hs]
  have hden : (⟨(πT i) XU, piT_mem_primeCompl fR lam0 hbot n m frel q πT i hXUmem⟩ : q.primeCompl)
      = u := Subtype.ext hpiXU
  rw [hpiXT, hden]

/-- If `algebraMap (T_K)(S_K) (fT i K xt) = 0` at some later stage `K`, then
`of i (algebraMap (T_i)(S_i) xt) = 0` in `colim S_i`. -/
lemma algMap_of_zero_of_stage (hqS : IsLocalization q.primeCompl S)
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (i K : Λ) (hiK : i ≤ K) (xt : Tobj fR lam0 hbot n m frel i)
    (hz : (algebraMap (Tobj fR lam0 hbot n m frel K)
        (Sobj' fR lam0 hbot n m frel q πT K)) (fT i K hiK xt) = 0) :
    Ring.DirectLimit.of (Sobj' fR lam0 hbot n m frel q πT)
        (fun i j h => (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h :
          Sobj' fR lam0 hbot n m frel q πT i → Sobj' fR lam0 hbot n m frel q πT j)) i
        ((algebraMap (Tobj fR lam0 hbot n m frel i)
          (Sobj' fR lam0 hbot n m frel q πT i)) xt) = 0 := by
  have hof := (Ring.DirectLimit.of_f
    (G := Sobj' fR lam0 hbot n m frel q πT)
    (f := fun i j h => (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h :
      Sobj' fR lam0 hbot n m frel q πT i → Sobj' fR lam0 hbot n m frel q πT j))
    hiK ((algebraMap (Tobj fR lam0 hbot n m frel i)
      (Sobj' fR lam0 hbot n m frel q πT i)) xt)).symm
  rw [hof]
  show Ring.DirectLimit.of (Sobj' fR lam0 hbot n m frel q πT) _ K
      (fSmap fR lam0 hbot n m frel q πT fT hπcompat i K hiK
        ((algebraMap (Tobj fR lam0 hbot n m frel i)
          (Sobj' fR lam0 hbot n m frel q πT i)) xt)) = 0
  rw [fSmap_algebraMap, hz, map_zero]

/-- `iotaS` is injective. -/
lemma iotaS_injective (hqS : IsLocalization q.primeCompl S)
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hTdir : DirectedSystem (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j)))
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (eT : Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
        (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
        ≃+* T)
    (heT : ∀ i, eT.toRingHom.comp (Ring.DirectLimit.of _ _ i) = πT i) :
    Function.Injective (iotaS fR lam0 hbot n m frel q πT hqS fT hπcompat) := by
  have : DirectedSystem (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j)) :=
    hTdir
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨i, w, rfl⟩ := Ring.DirectLimit.exists_of z
  obtain ⟨⟨xt, xu⟩, hw⟩ := IsLocalization.mk'_surjective
    (qcon fR lam0 hbot n m frel q πT i).primeCompl w
  subst hw
  rw [iotaS_of, sigmaS_mk'] at hz
  -- hz : mk' S (πT i xt) ⟨πT i xu, _⟩ = 0
  rw [IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨mm, hmm⟩ := hz
  -- hmm : ↑mm * πT i xt = 0,  mm : q.primeCompl
  obtain ⟨k, hik, Ym, hpiYm⟩ :=
    exists_piT_eq fR lam0 hbot n m frel πT fT hπcompat eT heT i (mm : T)
  have hpiXt : (πT k) (fT i k hik xt) = (πT i) xt := RingHom.congr_fun (hπcompat i k hik) xt
  have hprod : (πT k) (Ym * fT i k hik xt) = 0 := by
    rw [map_mul, hpiYm, hpiXt, hmm]
  -- of k (Ym * Xt) = 0 in colim T_i
  have hofTzero : Ring.DirectLimit.of (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
      k (Ym * fT i k hik xt) = 0 := by
    apply eT.injective
    rw [map_zero, ← piT_eq_eT fR lam0 hbot n m frel πT fT eT heT k, hprod]
  -- descend
  obtain ⟨K, hkK, hKzero⟩ := Ring.DirectLimit.of.zero_exact hofTzero
  have hYm'mem : fT k K hkK Ym ∈ (qcon fR lam0 hbot n m frel q πT K).primeCompl := by
    show (πT K) (fT k K hkK Ym) ∈ q.primeCompl
    have : (πT K) (fT k K hkK Ym) = mm := (RingHom.congr_fun (hπcompat k K hkK) Ym).trans hpiYm
    rw [this]
    exact mm.property
  -- algMap Xt' = 0 in S_K
  have hunit : IsUnit ((algebraMap (Tobj fR lam0 hbot n m frel K)
      (Sobj' fR lam0 hbot n m frel q πT K)) (fT k K hkK Ym)) :=
    IsLocalization.map_units (Sobj' fR lam0 hbot n m frel q πT K)
      (⟨fT k K hkK Ym, hYm'mem⟩ : (qcon fR lam0 hbot n m frel q πT K).primeCompl)
  have hXt'zero : (algebraMap (Tobj fR lam0 hbot n m frel K)
      (Sobj' fR lam0 hbot n m frel q πT K)) (fT k K hkK (fT i k hik xt)) = 0 := by
    apply (IsUnit.mul_right_eq_zero hunit).mp
    rw [← map_mul, ← map_mul, hKzero, map_zero]
  -- of i (algMap xt) = 0
  have hofSzero : Ring.DirectLimit.of (Sobj' fR lam0 hbot n m frel q πT)
      (fun i j h => (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h :
        Sobj' fR lam0 hbot n m frel q πT i → Sobj' fR lam0 hbot n m frel q πT j)) i
      ((algebraMap (Tobj fR lam0 hbot n m frel i)
        (Sobj' fR lam0 hbot n m frel q πT i)) xt) = 0 := by
    apply algMap_of_zero_of_stage fR lam0 hbot n m frel q πT hqS fT hπcompat i K
      (le_trans hik hkK) xt
    rwa [← hTdir.map_map hik hkK xt]
  -- finish: of i (mk' xt ⟨xu,_⟩) = of i (algMap xt) * of i (mk' 1 ⟨xu,_⟩) = 0
  show Ring.DirectLimit.of (Sobj' fR lam0 hbot n m frel q πT)
      (fun i j h => (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h :
        Sobj' fR lam0 hbot n m frel q πT i → Sobj' fR lam0 hbot n m frel q πT j)) i
      (IsLocalization.mk' (Sobj' fR lam0 hbot n m frel q πT i) xt xu) = 0
  rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, hofSzero, zero_mul]

/-- Condition (1): the colimit of the `S_i = (T_i)_{q_i}` recovers `S`, compatibly with `φ` and
`eR`. This says that localization commutes with the filtered colimit,
`S = T_q = (colim T_i)_q ≅ colim (T_i)_{q_i}`. -/
lemma colimLocalization (hφ : IsLocalHom φ) (hφalg : φ = algebraMap R S)
    (hqS : IsLocalization q.primeCompl S)
    (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
    (hTdir : DirectedSystem (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j)))
    (hπcompat : ∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i)
    (hfTR : ∀ i j (hij : i ≤ j),
      (fT i j hij).comp (RtoT fR lam0 hbot n m frel i)
        = (RtoT fR lam0 hbot n m frel j).comp (fR i j hij))
    (hπR : ∀ i, (πT i).comp (RtoT fR lam0 hbot n m frel i)
        = (algebraMap R T).comp (RtoR fR eR i))
    -- the `T`-side colimit iso (πT exhibits `T` as `colim T_i`), from `colimQuotient`.
    -- This is essential: without it `πT` need not be jointly surjective and the lemma is FALSE.
    (eT : Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
        (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
        ≃+* T)
    (heT : ∀ i, eT.toRingHom.comp (Ring.DirectLimit.of _ _ i) = πT i) :
    ∃ (eS : Ring.DirectLimit (Sobj' fR lam0 hbot n m frel q πT)
        (fun i j h => (fSmap fR lam0 hbot n m frel q πT fT hπcompat i j h :
          Sobj' fR lam0 hbot n m frel q πT i → Sobj' fR lam0 hbot n m frel q πT j)) ≃+* S),
       φ.comp eR.toRingHom = eS.toRingHom.comp
         (Ring.DirectLimit.map (fun i => psiS fR lam0 hbot n m frel q πT i)
           (fun i j hij => psiS_comm fR lam0 hbot n m frel q πT fT hπcompat hfTR i j hij)) := by
  refine ⟨RingEquiv.ofBijective (iotaS fR lam0 hbot n m frel q πT hqS fT hπcompat)
    ⟨iotaS_injective fR lam0 hbot n m frel q πT hqS fT hTdir hπcompat eT heT,
     iotaS_surjective fR lam0 hbot n m frel q πT hqS fT hπcompat eT heT⟩, ?_⟩
  apply RingHom.ext
  intro z
  obtain ⟨i, r, rfl⟩ := Ring.DirectLimit.exists_of z
  rw [RingHom.comp_apply, RingHom.comp_apply, Ring.DirectLimit.map_apply_of]
  -- RHS = eS.toRingHom (of i (psiS i r)) ; eS = ofBijective iotaS
  show φ (eR.toRingHom (Ring.DirectLimit.of Robj _ i r))
    = iotaS fR lam0 hbot n m frel q πT hqS fT hπcompat
        (Ring.DirectLimit.of _ _ i (psiS fR lam0 hbot n m frel q πT i r))
  rw [iotaS_of,
    show psiS fR lam0 hbot n m frel q πT i r
      = (algebraMap (Tobj fR lam0 hbot n m frel i)
          (Sobj' fR lam0 hbot n m frel q πT i)) (RtoT fR lam0 hbot n m frel i r) from rfl,
    sigmaS_algebraMap,
    show (πT i) (RtoT fR lam0 hbot n m frel i r)
      = (algebraMap R T) (RtoR fR eR i r) from DFunLike.congr_fun (hπR i) r,
    ← IsScalarTower.algebraMap_apply R T S, hφalg]
  rfl

/-- Linchpin: `Irel j = Ideal.map (map (fR i j)) (Irel i)`. -/
lemma Irel_map_eq
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j) :
    Irel fR lam0 hbot n m frel j
      = Ideal.map (MvPolynomial.map (fR i j hij)) (Irel fR lam0 hbot n m frel i) := by
  rw [Irel, Irel, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  exact congrArg _ (funext fun k => (frelAt_transport fR lam0 hbot n m frel hRdir i j hij k).symm)

-- `Tobj` is only defeq to the quotient it names, so relax type-transparency for `rw`.
set_option backward.isDefEq.respectTransparency.types false in
/-- For `i ≤ j`, the canonical base-change isomorphism `T_i ⊗_{R_i} R_j ≃ₐ[R_i] T_j`, where the
`R_i`-algebra structure on `R_j` is supplied by the instance binder `[Algebra (Robj i) (Robj j)]`
together with the hypothesis `halg` pinning its `algebraMap` to the transition map `fR i j hij`.

This is the statement that base change commutes with `R_i[x]/(finitely generated ideal)`, and it
is where finite presentation is essential; the generators of `Irel i` map to those of `Irel j` by
`frelAt_transport`. -/
lemma baseChangeQuotient
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j)
    [Algebra (Robj i) (Robj j)]
    (halg : (algebraMap (Robj i) (Robj j) : Robj i →+* Robj j) = fR i j hij) :
    letI : Algebra (Robj i) (Tobj fR lam0 hbot n m frel i) :=
      (RtoT fR lam0 hbot n m frel i).toAlgebra
    letI : Algebra (Robj i) (Tobj fR lam0 hbot n m frel j) :=
      ((RtoT fR lam0 hbot n m frel j).comp (fR i j hij)).toAlgebra
    ∃ e : Tobj fR lam0 hbot n m frel i ⊗[Robj i] Robj j
        ≃ₐ[Robj i] Tobj fR lam0 hbot n m frel j,
      (∀ t : Tobj fR lam0 hbot n m frel i,
        e (t ⊗ₜ[Robj i] (1 : Robj j))
          = fTmap fR lam0 hbot n m frel hRdir i j hij t) ∧
      (∀ r : Robj j,
        e ((1 : Tobj fR lam0 hbot n m frel i) ⊗ₜ[Robj i] r)
          = RtoT fR lam0 hbot n m frel j r) := by
  let instTi : Algebra (Robj i) (Tobj fR lam0 hbot n m frel i) :=
    (RtoT fR lam0 hbot n m frel i).toAlgebra
  let instTj : Algebra (Robj i) (Tobj fR lam0 hbot n m frel j) :=
    ((RtoT fR lam0 hbot n m frel j).comp (fR i j hij)).toAlgebra
  -- bridge: the `letI` algebra structure on `Tobj i` agrees with the canonical
  -- `Ideal.Quotient` structure on the (defeq) quotient type.
  let bi : Tobj fR lam0 hbot n m frel i
      ≃ₐ[Robj i] (MvPolynomial (Fin n) (Robj i) ⧸ Irel fR lam0 hbot n m frel i) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.refl (Tobj fR lam0 hbot n m frel i)) (fun _ => rfl)
  let bj : (MvPolynomial (Fin n) (Robj j) ⧸ Irel fR lam0 hbot n m frel j)
      ≃ₐ[Robj i] Tobj fR lam0 hbot n m frel j :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.refl (MvPolynomial (Fin n) (Robj j) ⧸ Irel fR lam0 hbot n m frel j))
      (fun r => by
      show (algebraMap (Robj i) (MvPolynomial (Fin n) (Robj j) ⧸ Irel fR lam0 hbot n m frel j)) r
          = (algebraMap (Robj i) (Tobj fR lam0 hbot n m frel j)) r
      show (Ideal.Quotient.mk (Irel fR lam0 hbot n m frel j))
          (MvPolynomial.C ((algebraMap (Robj i) (Robj j)) r)) = _
      rw [halg]; rfl)
  -- Step 2: quotient base change
  let e2 := Algebra.TensorProduct.quotientTensorEquiv (R := Robj i) (Robj i) (Robj j)
    (MvPolynomial (Fin n) (Robj i)) (Irel fR lam0 hbot n m frel i)
  -- algebra iso `g : R_i[x] ⊗[R_i] R_j ≃ₐ[R_i] R_j[x]`
  let g : (MvPolynomial (Fin n) (Robj i)) ⊗[Robj i] (Robj j)
      ≃ₐ[Robj i] MvPolynomial (Fin n) (Robj j) :=
    (Algebra.TensorProduct.comm (Robj i) (MvPolynomial (Fin n) (Robj i)) (Robj j)).trans
      ((MvPolynomial.algebraTensorAlgEquiv (Robj i) (Robj j)).restrictScalars (Robj i))
  -- key: the composite ring hom equals `MvPolynomial.map (fR i j)`
  have hcomp : (g.toRingHom).comp
      (algebraMap (MvPolynomial (Fin n) (Robj i))
        ((MvPolynomial (Fin n) (Robj i)) ⊗[Robj i] (Robj j)))
      = MvPolynomial.map (fR i j hij) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, MvPolynomial.map_C]
      show g (algebraMap (MvPolynomial (Fin n) (Robj i)) _ (MvPolynomial.C r)) = _
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp only [g, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
        AlgEquiv.restrictScalars_apply, MvPolynomial.algebraTensorAlgEquiv]
      simp [halg]
    · intro s
      rw [RingHom.comp_apply, MvPolynomial.map_X]
      show g (algebraMap (MvPolynomial (Fin n) (Robj i)) _ (MvPolynomial.X s)) = _
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp only [g, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
        AlgEquiv.restrictScalars_apply, MvPolynomial.algebraTensorAlgEquiv]
      simp only [Algebra.algebraMap_self, RingHom.id_apply,
        AddMonoidAlgebra.scalarTensorEquiv_tmul, one_smul]
      show AddMonoidAlgebra.mapAlgHom (Fin n →₀ ℕ) (Algebra.ofId (Robj i) (Robj j))
          (AddMonoidAlgebra.single (Finsupp.single s 1) 1)
        = AddMonoidAlgebra.single (Finsupp.single s 1) (1 : Robj j)
      rw [AddMonoidAlgebra.mapAlgHom_single, map_one]
  -- the mapped ideal equals `Irel j`
  have hJ : Irel fR lam0 hbot n m frel j
      = Ideal.map (g.toRingHom)
        (Ideal.map (algebraMap (MvPolynomial (Fin n) (Robj i))
          ((MvPolynomial (Fin n) (Robj i)) ⊗[Robj i] (Robj j)))
          (Irel fR lam0 hbot n m frel i)) := by
    rw [Ideal.map_map, hcomp, ← Irel_map_eq fR lam0 hbot n m frel hRdir i j hij]
  let e3 := Ideal.quotientEquivAlg
    (Ideal.map (algebraMap (MvPolynomial (Fin n) (Robj i))
      ((MvPolynomial (Fin n) (Robj i)) ⊗[Robj i] (Robj j)))
      (Irel fR lam0 hbot n m frel i))
    (Irel fR lam0 hbot n m frel j) g hJ
  let E := (((Algebra.TensorProduct.congr bi (AlgEquiv.refl)).trans e2).trans e3).trans bj
  have hE : ∀ (p : MvPolynomial (Fin n) (Robj i)) (r : Robj j),
      E ((Ideal.Quotient.mk (Irel fR lam0 hbot n m frel i) p) ⊗ₜ[Robj i] r)
        = Ideal.Quotient.mk (Irel fR lam0 hbot n m frel j) (g (p ⊗ₜ[Robj i] r)) := by
    intro p r
    simp only [E, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    show bj (e3 (Algebra.TensorProduct.quotientTensorEquiv (R := Robj i) (Robj i) (Robj j)
        (MvPolynomial (Fin n) (Robj i)) (Irel fR lam0 hbot n m frel i)
        ((Ideal.Quotient.mk (Irel fR lam0 hbot n m frel i) p) ⊗ₜ[Robj i] r))) = _
    rw [Algebra.TensorProduct.quotientTensorEquiv_apply_tmul]
    show bj (Ideal.quotientEquivAlg
        (Ideal.map (algebraMap (MvPolynomial (Fin n) (Robj i))
          ((MvPolynomial (Fin n) (Robj i)) ⊗[Robj i] (Robj j)))
          (Irel fR lam0 hbot n m frel i))
        (Irel fR lam0 hbot n m frel j) g hJ
        (Ideal.Quotient.mk _ (p ⊗ₜ[Robj i] r))) = _
    rw [Ideal.quotientEquivAlg_mk]
    rfl
  refine ⟨E, ?_, ?_⟩
  · intro t
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
    show E ((Ideal.Quotient.mk (Irel fR lam0 hbot n m frel i) p) ⊗ₜ[Robj i] (1 : Robj j))
        = fTmap fR lam0 hbot n m frel hRdir i j hij (Ideal.Quotient.mk _ p)
    rw [fTmap_mk, hE]
    congr 1
    have hpe : (p ⊗ₜ[Robj i] (1 : Robj j))
        = algebraMap (MvPolynomial (Fin n) (Robj i))
            ((MvPolynomial (Fin n) (Robj i)) ⊗[Robj i] (Robj j)) p := by
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp
    rw [hpe]
    have hg : g (algebraMap (MvPolynomial (Fin n) (Robj i))
            ((MvPolynomial (Fin n) (Robj i)) ⊗[Robj i] (Robj j)) p)
        = MvPolynomial.map (fR i j hij) p := by
      have := RingHom.congr_fun hcomp p
      simpa [RingHom.comp_apply] using this
    exact hg
  · intro r
    refine (hE 1 r).trans ?_
    have hgr : g ((1 : MvPolynomial (Fin n) (Robj i)) ⊗ₜ[Robj i] r)
        = MvPolynomial.C r := by
      simp only [g, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
        AlgEquiv.restrictScalars_apply, MvPolynomial.algebraTensorAlgEquiv]
      simp only [AddMonoidAlgebra.scalarTensorEquiv_tmul, map_one]
      rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_one]
    rw [hgr]
    rfl

end

end Descent

end

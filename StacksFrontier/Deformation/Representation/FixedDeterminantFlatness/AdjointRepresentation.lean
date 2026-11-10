module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteCochains
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.Descent
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.Universal

/-!
# The adjoint representation on trace-zero matrices, and test rings in other universes

Let `ρ₀ : π → GLₙ(F)` be a representation over a field. The trace-zero matrices `ad⁰ ρ₀` carry
the adjoint action `g • X = ρ₀(g) X ρ₀(g)⁻¹`; they are the coefficients of the tangent and
obstruction spaces of deformations of `ρ₀` with fixed determinant.

The universal property `Deformation.IsUniversalFixedDeterminantDeformation` quantifies over test
rings in the universe of the deformation ring. The rings one wants to test against in the
deformation theory of `ρ₀` (dual numbers over `𝐅_ℓ`, quotients of power series rings over
`ℤ_[ℓ]`) live in `Type`; the last section transports the universal property to them through
`ULift`.

## Main definitions

* `Deformation.AdZero ρ`: the trace-zero matrices with the adjoint action of `ρ`.

## Main results

* `Deformation.AdZero.hasOpenStabilizers`: `ad⁰ ρ₀` is a discrete module when `ρ₀` is
  continuous into a discrete general linear group.
* `Deformation.AdZero.eq_zero_of_forall_smul_eq`: `(ad⁰ ρ₀) ^ N = 0` when `ρ₀` is absolutely
  irreducible on `N` and `ℓ ∤ n`.
* `Deformation.IsUniversalFixedDeterminantDeformation.exists_of_small`,
  `Deformation.IsUniversalFixedDeterminantDeformation.unique_of_small`: the universal property
  for test rings in `Type`.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Deformation

/-! ### Trace-zero matrices with the adjoint action -/

variable {G : Type u} [Group G] {n : ℕ} {F : Type v} [Field F]

/-- The trace-zero `n × n` matrices over `F`, with the adjoint action of a matrix representation
`ρ : G → GLₙ(F)`: `g • X = ρ(g) X ρ(g)⁻¹`. -/
def AdZero (_ρ : G →* Matrix.GeneralLinearGroup (Fin n) F) : Type v :=
  LinearMap.ker (Matrix.traceLinearMap (Fin n) F F)

namespace AdZero

variable (ρ : G →* Matrix.GeneralLinearGroup (Fin n) F)

/-- `ad⁰ ρ` is an additive group under matrix addition. -/
instance : AddCommGroup (AdZero ρ) :=
  inferInstanceAs (AddCommGroup (LinearMap.ker (Matrix.traceLinearMap (Fin n) F F)))

/-- `ad⁰ ρ` is an `F`-vector space under scalar multiplication of matrices. -/
instance : Module F (AdZero ρ) :=
  inferInstanceAs (Module F (LinearMap.ker (Matrix.traceLinearMap (Fin n) F F)))

/-- `ad⁰ ρ` is finite when `F` is finite. -/
instance [Finite F] : Finite (AdZero ρ) :=
  inferInstanceAs (Finite (LinearMap.ker (Matrix.traceLinearMap (Fin n) F F)))

variable {ρ}

/-- The underlying matrix. -/
def val (X : AdZero ρ) : Matrix (Fin n) (Fin n) F := (X : LinearMap.ker _).1

/-- The underlying matrix of an element of `ad⁰ ρ` has trace zero. -/
lemma trace_val (X : AdZero ρ) : X.val.trace = 0 := (X : LinearMap.ker _).2

/-- A trace-zero matrix as an element of `ad⁰`. -/
def mk (X : Matrix (Fin n) (Fin n) F) (hX : X.trace = 0) : AdZero ρ :=
  (⟨X, hX⟩ : LinearMap.ker (Matrix.traceLinearMap (Fin n) F F))

/-- The underlying matrix of `mk X hX` is `X`. -/
@[simp] lemma val_mk (X : Matrix (Fin n) (Fin n) F) (hX : X.trace = 0) :
    (mk (ρ := ρ) X hX).val = X := rfl

/-- Two elements of `ad⁰ ρ` with the same underlying matrix are equal. -/
@[ext] lemma ext {X Y : AdZero ρ} (h : X.val = Y.val) : X = Y :=
  Subtype.ext h

/-- The underlying matrix of a sum is the sum of the underlying matrices. -/
@[simp] lemma val_add (X Y : AdZero ρ) : (X + Y).val = X.val + Y.val := rfl

/-- The underlying matrix of a difference is the difference of the underlying matrices. -/
@[simp] lemma val_sub (X Y : AdZero ρ) : (X - Y).val = X.val - Y.val := rfl

/-- The underlying matrix of `-X` is the negative of the underlying matrix of `X`. -/
@[simp] lemma val_neg (X : AdZero ρ) : (-X).val = -X.val := rfl

/-- The underlying matrix of `0` is the zero matrix. -/
@[simp] lemma val_zero : (0 : AdZero ρ).val = 0 := rfl

/-- The underlying matrix of `a • X` is `a` times the underlying matrix of `X`. -/
@[simp] lemma val_smul (a : F) (X : AdZero ρ) : (a • X).val = a • X.val := rfl

/-- The underlying matrix, as a linear map. -/
def valₗ : AdZero ρ →ₗ[F] Matrix (Fin n) (Fin n) F :=
  (LinearMap.ker (Matrix.traceLinearMap (Fin n) F F)).subtype

/-- `valₗ X` is the underlying matrix of `X`. -/
@[simp] lemma valₗ_apply (X : AdZero ρ) : valₗ X = X.val := rfl

/-- The underlying matrix of a finite sum is the sum of the underlying matrices. -/
@[simp] lemma val_sum {ι : Type*} (s : Finset ι) (X : ι → AdZero ρ) :
    (∑ i ∈ s, X i).val = ∑ i ∈ s, (X i).val := by
  simp only [← valₗ_apply, map_sum]

/-- Conjugation by an invertible matrix preserves the trace: `tr(A X A⁻¹) = tr X`. -/
lemma trace_conj (A : Matrix.GeneralLinearGroup (Fin n) F) (X : Matrix (Fin n) (Fin n) F) :
    ((A : Matrix (Fin n) (Fin n) F) * X * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- The adjoint action `g • X = ρ(g) X ρ(g)⁻¹` of `G` on `ad⁰ ρ`. -/
instance : DistribMulAction G (AdZero ρ) where
  smul g X := mk ((ρ g : Matrix (Fin n) (Fin n) F) * X.val * ((ρ g)⁻¹ : _))
    (by rw [trace_conj, trace_val])
  one_smul X := by
    ext1
    change ((ρ 1 : Matrix (Fin n) (Fin n) F)) * X.val * ((ρ 1)⁻¹ : _) = X.val
    simp
  mul_smul g h X := by
    ext1
    change ((ρ (g * h) : Matrix (Fin n) (Fin n) F)) * X.val * ((ρ (g * h))⁻¹ : _) =
      (ρ g : Matrix (Fin n) (Fin n) F) * ((ρ h : Matrix (Fin n) (Fin n) F) * X.val *
        ((ρ h)⁻¹ : _)) * ((ρ g)⁻¹ : _)
    simp only [map_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  smul_zero g := by
    ext1
    change ((ρ g : Matrix (Fin n) (Fin n) F)) * 0 * ((ρ g)⁻¹ : _) = 0
    simp
  smul_add g X Y := by
    ext1
    change ((ρ g : Matrix (Fin n) (Fin n) F)) * (X.val + Y.val) * ((ρ g)⁻¹ : _) = _ + _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl

/-- The underlying matrix of `g • X` is `ρ(g) X ρ(g)⁻¹`. -/
lemma val_smul_group (g : G) (X : AdZero ρ) :
    (g • X).val = (ρ g : Matrix (Fin n) (Fin n) F) * X.val * ((ρ g)⁻¹ : _) := rfl

/-- The adjoint action of `G` on `ad⁰ ρ` commutes with scalar multiplication by `F`. -/
instance : SMulCommClass G F (AdZero ρ) where
  smul_comm g a X := by
    ext1
    rw [val_smul_group, val_smul, val_smul, val_smul_group, Matrix.mul_smul, Matrix.smul_mul]

/-- `ad⁰ ρ` is a discrete module when `ρ` is continuous into a discrete general linear group. -/
theorem hasOpenStabilizers [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {ρ : G →ₜ* Matrix.GeneralLinearGroup (Fin n) F} :
    Stacks.GroupCohomology.HasOpenStabilizers G (AdZero ρ.toMonoidHom) := by
  intro X
  have : {g : G | g • X = X} = ρ ⁻¹' {A | AdZero.mk (ρ := ρ.toMonoidHom)
      ((A : Matrix (Fin n) (Fin n) F) * X.val * ((A⁻¹ : Matrix.GeneralLinearGroup _ F) : _))
      (by rw [trace_conj, trace_val]) = X} := rfl
  rw [this]
  exact (isOpen_discrete _).preimage ρ.continuous

/-- **`(ad⁰ ρ₀) ^ N = 0`** when `ρ₀` is absolutely irreducible on `N` and `n` is invertible in
`F`: a matrix commuting with a spanning family is scalar, and a trace-zero scalar is zero. -/
theorem eq_zero_of_forall_smul_eq {ℓ : ℕ} [Fact ℓ.Prime]
    {ρ : G →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} (N : Subgroup G)
    (hirr : IsAbsolutelyIrreducible fun g : N => ρ g) (hn : ¬ ℓ ∣ n) (X : AdZero ρ)
    (hX : ∀ g ∈ N, g • X = X) : X = 0 := by
  have hcomm : ∀ g : N, Commute (((ρ g : Matrix (Fin n) (Fin n) (ZMod ℓ))).map
      (algebraMap (ZMod ℓ) (ZMod ℓ))) X.val := by
    intro g
    have h1 := congrArg AdZero.val (hX g g.2)
    rw [val_smul_group] at h1
    have hid : ((ρ g : Matrix (Fin n) (Fin n) (ZMod ℓ))).map (algebraMap (ZMod ℓ) (ZMod ℓ)) =
        (ρ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) := by ext; simp
    rw [hid]
    change (ρ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * X.val = X.val * ρ g
    calc (ρ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * X.val
        = (ρ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * X.val * ((ρ g)⁻¹ : _) * ρ g := by
          rw [Matrix.mul_assoc _ (((ρ g)⁻¹ : Matrix.GeneralLinearGroup _ _) :
            Matrix (Fin n) (Fin n) (ZMod ℓ)), ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.mul_one]
      _ = X.val * ρ g := by rw [h1]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_span_eq_top
    (ℓ := ℓ) (S := ZMod ℓ) (fun g : N => (ρ g : Matrix (Fin n) (Fin n) (ZMod ℓ))) hirr X.val hcomm
  have htr : (n : ZMod ℓ) * c = 0 := by
    have := trace_val X
    rw [← hc] at this
    simpa [Matrix.trace, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using this
  have hn' : (n : ZMod ℓ) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hc0 : c = 0 := (mul_eq_zero.mp htr).resolve_left hn'
  ext1
  rw [← hc, hc0, map_zero, val_zero]

end AdZero

/-! ### Continuity for adic topologies -/

/-- A ring homomorphism between local rings mapping the maximal ideal into the maximal ideal is
continuous for the maximal-adic topologies. -/
theorem continuous_adic_of_map_maximalIdeal_le {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) (hf : (maximalIdeal A).map f ≤ maximalIdeal B) :
    @Continuous A B (maximalIdeal A).adicTopology (maximalIdeal B).adicTopology f := by
  let : TopologicalSpace A := (maximalIdeal A).adicTopology
  let : TopologicalSpace B := (maximalIdeal B).adicTopology
  have : IsTopologicalRing A := (maximalIdeal A).ringFilterBasis.isTopologicalRing
  have : IsTopologicalRing B := (maximalIdeal B).ringFilterBasis.isTopologicalRing
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, ((maximalIdeal A).hasBasis_nhds_zero_adic).tendsto_iff
    ((maximalIdeal B).hasBasis_nhds_zero_adic)]
  intro k _
  refine ⟨k, trivial, fun x hx => ?_⟩
  have : (maximalIdeal A ^ k).map f ≤ maximalIdeal B ^ k := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hf k
  exact this (Ideal.mem_map_of_mem f hx)

/-! ### Test rings in another universe -/

namespace IsUniversalFixedDeterminantDeformation

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

section Small

variable (S : Type) [CommRing S] [IsLocalRing S] [Algebra ℤ_[ℓ] S]

omit [Fact ℓ.Prime] in
private lemma isLocalRing_ulift : IsLocalRing (ULift.{v} S) :=
  IsLocalRing.of_surjective' (ULift.ringEquiv (R := S)).symm.toRingHom
    (ULift.ringEquiv (R := S)).symm.surjective

private lemma map_maximalIdeal_ulift :
    letI := isLocalRing_ulift S
    (maximalIdeal (ULift.{v} S)).map ((ULift.ringEquiv (R := S)) : (ULift.{v} S) →+* S) =
      maximalIdeal S := by
  let := isLocalRing_ulift S
  exact IsLocalRing.map_ringEquiv_maximalIdeal _

private lemma map_maximalIdeal_ulift_symm :
    letI := isLocalRing_ulift S
    (maximalIdeal S).map ((ULift.ringEquiv (R := S)).symm : S →+* (ULift.{v} S)) =
      maximalIdeal (ULift.{v} S) := by
  let := isLocalRing_ulift S
  exact IsLocalRing.map_ringEquiv_maximalIdeal _

/-- The universal property of `h` for the test ring `S : Type`, transported through `ULift`. -/
private theorem existsUnique_of_small
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    [tS : TopologicalSpace S] (htS : tS = (maximalIdeal S).adicTopology)
    (hcS : IsAdicComplete (maximalIdeal S) S) (red : S →+* ZMod ℓ)
    (hred : Function.Surjective red) (hredc : Continuous red)
    (hredalg : ∀ a : ℤ_[ℓ], red (algebraMap ℤ_[ℓ] S a) = PadicInt.toZMod a)
    (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) S)
    (hρ : IsConjugate (fun g => Matrix.GeneralLinearGroup.map red (ρ g)) (fun g => ρ₀ g))
    (hdet : ∀ g, Matrix.GeneralLinearGroup.det (ρ g) = Units.map (algebraMap ℤ_[ℓ] S) (δ g)) :
    ∃! ψ : R →ₐ[ℤ_[ℓ]] S, Continuous (ψ : R → S) ∧
      IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ.toRingHom (ρuniv g))
        (fun g => ρ g) := by
  let := isLocalRing_ulift S
  let tSu : TopologicalSpace (ULift.{v} S) := (maximalIdeal (ULift.{v} S)).adicTopology
  set e : (ULift.{v} S) ≃ₐ[ℤ_[ℓ]] S := ULift.algEquiv
  have he : ((e : (ULift.{v} S) →+* S)) =
      ((ULift.ringEquiv (R := S)) : (ULift.{v} S) →+* S) := rfl
  have he' : ((e.symm : S →+* (ULift.{v} S))) =
      ((ULift.ringEquiv (R := S)).symm : S →+* (ULift.{v} S)) := rfl
  have hec : Continuous (e : (ULift.{v} S) → S) := by
    rw [htS]
    exact continuous_adic_of_map_maximalIdeal_le (e : (ULift.{v} S) →+* S)
      (by rw [he, map_maximalIdeal_ulift])
  have hesc : Continuous (e.symm : S → (ULift.{v} S)) := by
    rw [htS]
    exact continuous_adic_of_map_maximalIdeal_le (e.symm : S →+* (ULift.{v} S))
      (by rw [he', map_maximalIdeal_ulift_symm])
  have hcSu : IsAdicComplete (maximalIdeal (ULift.{v} S)) (ULift.{v} S) := by
    rw [← map_maximalIdeal_ulift_symm S]
    exact (IsAdicComplete.congr_ringEquiv _ (ULift.ringEquiv (R := S)).symm).mpr hcS
  let ρ' : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ULift.{v} S) :=
    { toMonoidHom :=
        (Matrix.GeneralLinearGroup.map (e.symm : S →+* (ULift.{v} S))).comp ρ.toMonoidHom
      continuous_toFun := (Matrix.GeneralLinearGroup.continuous_map _ hesc).comp ρ.continuous }
  have hmapcomp : ∀ (f : S →+* ZMod ℓ) (A : Matrix.GeneralLinearGroup (Fin n) S),
      Matrix.GeneralLinearGroup.map (f.comp (e : (ULift.{v} S) →+* S))
        (Matrix.GeneralLinearGroup.map (e.symm : S →+* (ULift.{v} S)) A) =
        Matrix.GeneralLinearGroup.map f A := by
    intro f A
    ext i j
    simp
  have hlift : ∀ ψ : R →ₐ[ℤ_[ℓ]] S, Continuous (ψ : R → S) →
      IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ.toRingHom (ρuniv g))
        (fun g => ρ g) →
      Continuous ((e.symm.toAlgHom.comp ψ : R →ₐ[ℤ_[ℓ]] (ULift.{v} S)) : R → (ULift.{v} S)) ∧
      IsConjugate (fun g => Matrix.GeneralLinearGroup.map
        (e.symm.toAlgHom.comp ψ).toRingHom (ρuniv g)) (fun g => ρ' g) := by
    intro ψ hψc hψ
    refine ⟨hesc.comp hψc, ?_⟩
    obtain ⟨P, hP⟩ := hψ
    refine ⟨Matrix.GeneralLinearGroup.map (e.symm : S →+* (ULift.{v} S)) P, fun g => ?_⟩
    have := congrArg (Matrix.GeneralLinearGroup.map (e.symm : S →+* (ULift.{v} S))) (hP g)
    simp only [map_mul, map_inv] at this
    have k2 : Matrix.GeneralLinearGroup.map (e.symm : S →+* (ULift.{v} S))
        (Matrix.GeneralLinearGroup.map ψ.toRingHom (ρuniv g)) =
        Matrix.GeneralLinearGroup.map (e.symm.toAlgHom.comp ψ).toRingHom (ρuniv g) := by
      ext i j; rfl
    rw [k2] at this
    exact this
  obtain ⟨ψ', ⟨hψ'c, hψ'⟩, huniq⟩ := h.universal (ULift.{v} S) rfl hcSu
    (red.comp (e : (ULift.{v} S) →+* S))
    (hred.comp e.surjective) (hredc.comp hec) (fun a => by simp [hredalg]) ρ'
    (by
      obtain ⟨P, hP⟩ := hρ
      refine ⟨P, fun g => ?_⟩
      change ρ₀ g = P * Matrix.GeneralLinearGroup.map (red.comp (e : (ULift.{v} S) →+* S))
        (Matrix.GeneralLinearGroup.map (e.symm : S →+* (ULift.{v} S)) (ρ g)) * P⁻¹
      rw [hmapcomp red (ρ g)]
      exact hP g)
    (fun g => by
      refine Units.ext ?_
      have h1 := congrArg Units.val (hdet g)
      rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      change ((ρ g : Matrix (Fin n) (Fin n) S).map (e.symm : S →+* (ULift.{v} S))).det = _
      rw [show (ρ g : Matrix (Fin n) (Fin n) S).map (e.symm : S →+* (ULift.{v} S)) =
        (e.symm : S →+* (ULift.{v} S)).mapMatrix (ρ g : Matrix (Fin n) (Fin n) S) from rfl,
        ← RingHom.map_det, h1]
      simp)
  refine ⟨e.toAlgHom.comp ψ', ⟨hec.comp hψ'c, ?_⟩, fun ψ hψ => ?_⟩
  · obtain ⟨P, hP⟩ := hψ'
    refine ⟨Matrix.GeneralLinearGroup.map (e : (ULift.{v} S) →+* S) P, fun g => ?_⟩
    have := congrArg (Matrix.GeneralLinearGroup.map (e : (ULift.{v} S) →+* S)) (hP g)
    simp only [map_mul, map_inv] at this
    have k1 : Matrix.GeneralLinearGroup.map (e : (ULift.{v} S) →+* S) (ρ' g) = ρ g := by
      ext i j
      exact e.apply_symm_apply _
    have k2 : Matrix.GeneralLinearGroup.map (e : (ULift.{v} S) →+* S)
        (Matrix.GeneralLinearGroup.map ψ'.toRingHom (ρuniv g)) =
        Matrix.GeneralLinearGroup.map (e.toAlgHom.comp ψ').toRingHom (ρuniv g) := by
      ext i j; rfl
    rw [k1, k2] at this
    exact this
  · rw [← huniq _ (hlift ψ hψ.1 hψ.2)]
    ext x
    simp

/-- **Existence in the universal property for a test ring in `Type`.** -/
theorem exists_of_small (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    [tS : TopologicalSpace S] (htS : tS = (maximalIdeal S).adicTopology)
    (hcS : IsAdicComplete (maximalIdeal S) S) (red : S →+* ZMod ℓ)
    (hred : Function.Surjective red) (hredc : Continuous red)
    (hredalg : ∀ a : ℤ_[ℓ], red (algebraMap ℤ_[ℓ] S a) = PadicInt.toZMod a)
    (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) S)
    (hρ : IsConjugate (fun g => Matrix.GeneralLinearGroup.map red (ρ g)) (fun g => ρ₀ g))
    (hdet : ∀ g, Matrix.GeneralLinearGroup.det (ρ g) = Units.map (algebraMap ℤ_[ℓ] S) (δ g)) :
    ∃ ψ : R →ₐ[ℤ_[ℓ]] S, Continuous (ψ : R → S) ∧
      IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ.toRingHom (ρuniv g))
        (fun g => ρ g) :=
  (existsUnique_of_small S h htS hcS red hred hredc hredalg ρ hρ hdet).exists

/-- **Uniqueness in the universal property for a test ring in `Type`.** -/
theorem unique_of_small (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    [tS : TopologicalSpace S] (htS : tS = (maximalIdeal S).adicTopology)
    (hcS : IsAdicComplete (maximalIdeal S) S) (red : S →+* ZMod ℓ)
    (hred : Function.Surjective red) (hredc : Continuous red)
    (hredalg : ∀ a : ℤ_[ℓ], red (algebraMap ℤ_[ℓ] S a) = PadicInt.toZMod a)
    (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) S)
    (hρ : IsConjugate (fun g => Matrix.GeneralLinearGroup.map red (ρ g)) (fun g => ρ₀ g))
    (hdet : ∀ g, Matrix.GeneralLinearGroup.det (ρ g) = Units.map (algebraMap ℤ_[ℓ] S) (δ g))
    (ψ₁ ψ₂ : R →ₐ[ℤ_[ℓ]] S) (hψ₁c : Continuous (ψ₁ : R → S))
    (hψ₁ : IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ₁.toRingHom (ρuniv g))
      (fun g => ρ g))
    (hψ₂c : Continuous (ψ₂ : R → S))
    (hψ₂ : IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ₂.toRingHom (ρuniv g))
      (fun g => ρ g)) : ψ₁ = ψ₂ :=
  (existsUnique_of_small S h htS hcS red hred hredc hredalg ρ hρ hdet).unique
    ⟨hψ₁c, hψ₁⟩ ⟨hψ₂c, hψ₂⟩

end Small

end IsUniversalFixedDeterminantDeformation

end Deformation

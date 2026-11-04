module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Topology.Instances.Matrix
public import StacksFrontier.Deformation.Representation.FixedDeterminantUniversal
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.Descent
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology

/-!
# Primes of a universal deformation ring along which the geometric image is finite

Let `R` be the universal deformation ring of a residual representation `ρ₀ : π → GLₙ(𝐅_ℓ)` with
determinant fixed to `δ`, let `N ⊆ π` be a normal subgroup on which `ρ₀` is absolutely
irreducible, and assume that `ℓ` does not divide `n`. If `R` is Noetherian and `𝔮` is a prime of
`R` containing `ℓ` such that the pushforward of the universal representation to `R/𝔮` has finite
image on `N`, then `𝔮` is the maximal ideal.

Indeed, by `Matrix.GeneralLinearGroup.exists_conj_eq_map_of_finite_image` the pushforward is
conjugate to the constant deformation `ρ₀ ⊗ R/𝔮`, so the quotient map `R → R/𝔮` and the map
`R → 𝐅_ℓ → R/𝔮` classify the same deformation; by uniqueness in the universal property they
agree, and `R/𝔮 = 𝐅_ℓ`.

## Main results

* `Deformation.IsUniversalFixedDeterminantDeformation.eq_maximalIdeal_of_finite_image`.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Matrix.GeneralLinearGroup

/-- Pushforward along a continuous ring homomorphism is continuous on general linear groups. -/
theorem continuous_map {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R]
    [CommRing S] [TopologicalSpace R] [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) :
    Continuous (map (n := n) f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

end Matrix.GeneralLinearGroup

/-- A ring homomorphism to a discrete ring killing a power of an ideal `I` is continuous for the
`I`-adic topology. -/
theorem RingHom.continuous_adic_of_pow_le_ker {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace B] [DiscreteTopology B] (I : Ideal A) (f : A →+* B) (k : ℕ)
    (h : I ^ k ≤ RingHom.ker f) : @Continuous A B I.adicTopology _ f := by
  let : TopologicalSpace A := I.adicTopology
  have : IsTopologicalRing A := I.ringFilterBasis.isTopologicalRing
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, nhds_discrete B, Filter.tendsto_pure]
  filter_upwards [(Ideal.hasBasis_nhds_zero_adic I).mem_of_mem (i := k) trivial] with x hx
  exact h (by simpa using hx)

namespace Deformation.IsUniversalFixedDeterminantDeformation

universe u v

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

/-- The kernel of the reduction map of a universal deformation ring is its maximal ideal. -/
theorem ker_reduce (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) :
    RingHom.ker reduce = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective reduce h.reduce_surjective)

/-- A ring homomorphism `ℤ_[ℓ] → A` into a ring of characteristic `ℓ` is the reduction followed by
the structure map of `A` as a `ZMod ℓ`-algebra. -/
theorem _root_.PadicInt.ringHom_eq_comp_toZMod {A : Type*} [CommRing A] [Algebra (ZMod ℓ) A]
    (f : ℤ_[ℓ] →+* A) : f = (algebraMap (ZMod ℓ) A).comp PadicInt.toZMod := by
  have hker : RingHom.ker (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ) ≤ RingHom.ker f := by
    intro x hx
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [RingHom.mem_ker, map_mul, map_natCast]
    have : (ℓ : A) = 0 := by
      rw [← map_natCast (algebraMap (ZMod ℓ) A), ZMod.natCast_self, map_zero]
    rw [this, zero_mul]
  let g : ZMod ℓ →+* A := (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ).liftOfRightInverse ZMod.cast
    (ZMod.ringHom_rightInverse _) ⟨f, hker⟩
  have hg : g.comp PadicInt.toZMod = f :=
    RingHom.liftOfRightInverse_comp _ _ _ ⟨f, hker⟩
  rw [← hg, Subsingleton.elim g (algebraMap (ZMod ℓ) A)]

section Quotient

/-- Pushing forward along `f` and then `g` is pushing forward along any `k` equal to `g ∘ f`. -/
private theorem map_map_of_forall_eq {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (k : A →+* C) (hk : ∀ a, g (f a) = k a)
    (x : Matrix.GeneralLinearGroup (Fin n) A) :
    Matrix.GeneralLinearGroup.map g (Matrix.GeneralLinearGroup.map f x) =
      Matrix.GeneralLinearGroup.map k x :=
  Matrix.GeneralLinearGroup.ext fun i j => by simp [hk]

variable (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
  (I : Ideal R) [IsLocalRing (R ⧸ I)] [Algebra (ZMod ℓ) (R ⧸ I)]

include h in
/-- A local quotient of a universal deformation ring lies under the maximal ideal. -/
theorem le_maximalIdeal_of_isLocalRing_quotient : I ≤ maximalIdeal R :=
  IsLocalRing.le_maximalIdeal fun hI =>
    not_subsingleton (R ⧸ I) (Ideal.Quotient.subsingleton_iff.2 hI)

/-- The reduction map of a local quotient `R ⧸ I` of a universal deformation ring. -/
def quotientReduce : R ⧸ I →+* ZMod ℓ :=
  Ideal.Quotient.lift I reduce fun a ha => by
    rw [← RingHom.mem_ker, h.ker_reduce]
    exact h.le_maximalIdeal_of_isLocalRing_quotient I ha

/-- The reduction map of `R ⧸ I` sends the class of `x` to the reduction of `x`. -/
theorem quotientReduce_mk (x : R) : h.quotientReduce I (Ideal.Quotient.mk I x) = reduce x :=
  Ideal.Quotient.lift_mk _ _ _

/-- The reduction map of `R ⧸ I` is a left inverse of the structure map `ZMod ℓ → R ⧸ I`. -/
theorem quotientReduce_algebraMap (c : ZMod ℓ) :
    h.quotientReduce I (algebraMap (ZMod ℓ) (R ⧸ I) c) = c := by
  have : (h.quotientReduce I).comp (algebraMap (ZMod ℓ) (R ⧸ I)) = RingHom.id _ :=
    Subsingleton.elim _ _
  exact RingHom.congr_fun this c

/-- An element of `R ⧸ I` lies in the maximal ideal if and only if its reduction vanishes. -/
theorem mem_maximalIdeal_quotient_iff (x : R ⧸ I) :
    x ∈ maximalIdeal (R ⧸ I) ↔ h.quotientReduce I x = 0 := by
  have := RingHom.ker_isMaximal_of_surjective (h.quotientReduce I)
    (ZMod.ringHom_surjective _)
  rw [← IsLocalRing.eq_maximalIdeal this, RingHom.mem_ker]

include h in
/-- The class of `a` lies in the maximal ideal of `R ⧸ I` if and only if `a` lies in the maximal
ideal of `R`. -/
theorem mk_mem_maximalIdeal_quotient_iff (a : R) :
    Ideal.Quotient.mk I a ∈ maximalIdeal (R ⧸ I) ↔ a ∈ maximalIdeal R := by
  rw [h.mem_maximalIdeal_quotient_iff, h.quotientReduce_mk, ← RingHom.mem_ker, h.ker_reduce]

/-- Every element of `R ⧸ I` is congruent, modulo the maximal ideal, to the image of its
reduction under the structure map. -/
theorem sub_algebraMap_quotientReduce_mem (x : R ⧸ I) :
    x - algebraMap (ZMod ℓ) (R ⧸ I) (h.quotientReduce I x) ∈ maximalIdeal (R ⧸ I) := by
  rw [h.mem_maximalIdeal_quotient_iff, map_sub, h.quotientReduce_algebraMap, sub_self]

include h in
/-- The structure map `ZMod ℓ → R ⧸ I` followed by the residue map of `R ⧸ I` is surjective. -/
theorem residue_comp_algebraMap_surjective :
    Function.Surjective ((residue (R ⧸ I)).comp (algebraMap (ZMod ℓ) (R ⧸ I))) := fun y => by
  obtain ⟨x, rfl⟩ := residue_surjective y
  refine ⟨h.quotientReduce I x, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← neg_mem_iff,
    neg_sub]
  exact h.sub_algebraMap_quotientReduce_mem I x

omit [IsLocalRing R] [TopologicalSpace R] [IsLocalRing (R ⧸ I)] in
/-- The composite `ℤ_[ℓ] → R → R ⧸ I` is the reduction `ℤ_[ℓ] → ZMod ℓ` followed by the
structure map `ZMod ℓ → R ⧸ I`. -/
theorem mk_comp_algebraMap :
    (Ideal.Quotient.mk I).comp (algebraMap ℤ_[ℓ] R) =
      (algebraMap (ZMod ℓ) (R ⧸ I)).comp PadicInt.toZMod :=
  PadicInt.ringHom_eq_comp_toZMod _

/-- The pushforward of the universal representation to `R ⧸ I`, conjugated by the image of a
fixed matrix conjugating its reduction to `ρ₀`, so that its reduction is exactly `ρ₀`. -/
def normalizedPushforward : π →* Matrix.GeneralLinearGroup (Fin n) (R ⧸ I) :=
  (MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap (ZMod ℓ) (R ⧸ I))
    h.reduce_rep.choose)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp ρuniv.toMonoidHom)

omit [IsLocalRing (R ⧸ I)] in
/-- The value of `normalizedPushforward` at `g` is the image of `ρuniv g` in `R ⧸ I`, conjugated
by the image of the chosen conjugating matrix. -/
theorem normalizedPushforward_apply (g : π) :
    h.normalizedPushforward I g =
      Matrix.GeneralLinearGroup.map (algebraMap (ZMod ℓ) (R ⧸ I)) h.reduce_rep.choose *
        Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (ρuniv g) *
        (Matrix.GeneralLinearGroup.map (algebraMap (ZMod ℓ) (R ⧸ I)) h.reduce_rep.choose)⁻¹ := by
  simp [normalizedPushforward, MulAut.conj_apply]

/-- The reduction of `normalizedPushforward` along `quotientReduce` is `ρ₀`. -/
theorem map_quotientReduce_normalizedPushforward (g : π) :
    Matrix.GeneralLinearGroup.map (h.quotientReduce I) (h.normalizedPushforward I g) = ρ₀ g := by
  rw [normalizedPushforward_apply, map_mul, map_mul, map_inv]
  rw [map_map_of_forall_eq _ _ (RingHom.id _) (h.quotientReduce_algebraMap I),
    map_map_of_forall_eq _ _ _ (h.quotientReduce_mk I)]
  exact (h.reduce_rep.choose_spec g).symm

/-- Each entry of `normalizedPushforward I g` is congruent, modulo the maximal ideal of `R ⧸ I`,
to the image of the corresponding entry of `ρ₀ g`. -/
theorem normalizedPushforward_sub_mem (g : π) (i j : Fin n) :
    (h.normalizedPushforward I g : Matrix (Fin n) (Fin n) (R ⧸ I)) i j -
      algebraMap (ZMod ℓ) (R ⧸ I) (ρ₀ g i j) ∈ maximalIdeal (R ⧸ I) := by
  rw [h.mem_maximalIdeal_quotient_iff, map_sub, h.quotientReduce_algebraMap]
  have := congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ) => x i j)
    (h.map_quotientReduce_normalizedPushforward I g)
  simp only [Matrix.GeneralLinearGroup.map_apply] at this
  rw [this, sub_self]

omit [IsLocalRing (R ⧸ I)] in
/-- The determinant of `normalizedPushforward I g` is the image of the determinant of `ρ₀ g`. -/
theorem det_normalizedPushforward (g : π) :
    (h.normalizedPushforward I g : Matrix (Fin n) (Fin n) (R ⧸ I)).det =
      algebraMap (ZMod ℓ) (R ⧸ I) (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)).det := by
  rw [normalizedPushforward_apply, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.det_one, one_mul]
  have h2 := congrArg Units.val (h.det_rep g)
  have h3 := congrArg Units.val (h.delta_reduce g)
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h2 h3
  rw [show ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (ρuniv g) :
      Matrix.GeneralLinearGroup (Fin n) (R ⧸ I)) : Matrix (Fin n) (Fin n) (R ⧸ I)) =
      (Ideal.Quotient.mk I).mapMatrix (ρuniv g : Matrix (Fin n) (Fin n) R) from rfl,
    ← RingHom.map_det, h2, ← h3, ← RingHom.comp_apply (algebraMap (ZMod ℓ) (R ⧸ I)),
    ← mk_comp_algebraMap (ℓ := ℓ) I, RingHom.comp_apply]

omit [IsLocalRing (R ⧸ I)] in
/-- The normalized pushforwards are compatible with the maps between quotients. -/
theorem map_factor_normalizedPushforward {J : Ideal R} [IsLocalRing (R ⧸ J)]
    [Algebra (ZMod ℓ) (R ⧸ J)] (hIJ : I ≤ J)
    (g : π) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ) (h.normalizedPushforward I g) =
      h.normalizedPushforward J g := by
  rw [normalizedPushforward_apply, normalizedPushforward_apply, map_mul, map_mul, map_inv]
  rw [map_map_of_forall_eq _ _ _ (RingHom.congr_fun (Subsingleton.elim
      ((Ideal.Quotient.factor hIJ).comp (algebraMap (ZMod ℓ) (R ⧸ I)))
      (algebraMap (ZMod ℓ) (R ⧸ J)))),
    map_map_of_forall_eq _ _ _ (Ideal.Quotient.factor_mk hIJ)]

/-- **Rigidity of the universal deformation.** If over a complete local quotient `R ⧸ I` the
pushforward of the universal representation is conjugate to the constant deformation `ρ₀`, then
`I` contains the maximal ideal: the quotient map and the map `R → 𝐅_ℓ → R ⧸ I` classify the same
deformation, so they agree by uniqueness in the universal property. -/
theorem maximalIdeal_le_of_conj_eq (hcomp : IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I))
    (P : Matrix.GeneralLinearGroup (Fin n) (R ⧸ I))
    (hP : ∀ g, P⁻¹ * h.normalizedPushforward I g * P =
      Matrix.GeneralLinearGroup.map (algebraMap (ZMod ℓ) (R ⧸ I)) (ρ₀ g)) :
    maximalIdeal R ≤ I := by
  classical
  set A := R ⧸ I
  set alg := algebraMap (ZMod ℓ) A
  set mk : R →+* A := Ideal.Quotient.mk I
  set redA := h.quotientReduce I
  have hker := h.ker_reduce
  let tA : TopologicalSpace A := (maximalIdeal A).adicTopology
  have hmk_cont : Continuous mk := by
    rw [h.isAdicTopology]
    refine (mk.continuous_adic_iff _ _).2 ⟨1, le_rfl, fun x hx => ?_⟩
    rw [pow_one] at hx
    exact (h.mk_mem_maximalIdeal_quotient_iff I x).2 hx
  have hredA_cont : Continuous redA :=
    RingHom.continuous_adic_of_pow_le_ker _ redA 1 fun x hx =>
      (h.mem_maximalIdeal_quotient_iff I x).1 (by rwa [pow_one] at hx)
  let ρA : π →ₜ* Matrix.GeneralLinearGroup (Fin n) A :=
    { toMonoidHom := (Matrix.GeneralLinearGroup.map mk).comp ρuniv.toMonoidHom
      continuous_toFun := (Matrix.GeneralLinearGroup.continuous_map mk hmk_cont).comp
        ρuniv.continuous_toFun }
  have hρA : ∀ g, ρA g = Matrix.GeneralLinearGroup.map mk (ρuniv g) := fun _ => rfl
  have hmapcomp : ∀ g, Matrix.GeneralLinearGroup.map redA (ρA g) =
      Matrix.GeneralLinearGroup.map reduce (ρuniv g) := fun g =>
    map_map_of_forall_eq _ _ _ (h.quotientReduce_mk I) _
  have hdetA : ∀ g, Matrix.GeneralLinearGroup.det (ρA g) =
      Units.map (algebraMap ℤ_[ℓ] A) (δ g) := fun g => by
    rw [hρA, Matrix.GeneralLinearGroup.map_det, h.det_rep]
    ext
    rfl
  set Q := h.reduce_rep.choose
  have hQ := h.reduce_rep.choose_spec
  set Qa : Matrix.GeneralLinearGroup (Fin n) A := Matrix.GeneralLinearGroup.map alg Q
  let ψ₂ : R →ₐ[ℤ_[ℓ]] A :=
    { toRingHom := alg.comp reduce
      commutes' := fun a => by
        have := congrArg (fun f : ℤ_[ℓ] →+* A => f a) (mk_comp_algebraMap (ℓ := ℓ) I)
        simp only [RingHom.comp_apply] at this
        simp only [RingHom.toMonoidHom_eq_coe, RingHom.coe_comp, Function.comp_apply,
          h.reduce_algebraMap, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
        rw [← this]
        rfl }
  have hψ₂ : ∀ x, ψ₂ x = alg (reduce x) := fun _ => rfl
  have hψ₂cont : Continuous ψ₂ := by
    have : Continuous reduce := h.reduce_continuous
    show Continuous fun x => alg (reduce x)
    exact (continuous_of_discreteTopology (f := alg)).comp this
  have hψ₂conj : IsConjugate
      (fun g => Matrix.GeneralLinearGroup.map ψ₂.toRingHom (ρuniv g)) (fun g => ρA g) := by
    refine ⟨Qa⁻¹ * P * Qa, fun g => ?_⟩
    have e1 := hP g
    have e2 : Matrix.GeneralLinearGroup.map ψ₂.toRingHom (ρuniv g) =
        Matrix.GeneralLinearGroup.map alg (Matrix.GeneralLinearGroup.map reduce (ρuniv g)) :=
      (map_map_of_forall_eq _ _ _ (fun _ => rfl) _).symm
    have e3 := congrArg (Matrix.GeneralLinearGroup.map alg) (hQ g)
    simp only [map_mul, map_inv] at e3
    change Matrix.GeneralLinearGroup.map alg (ρ₀ g) =
      Qa * Matrix.GeneralLinearGroup.map alg (Matrix.GeneralLinearGroup.map reduce (ρuniv g)) *
        Qa⁻¹ at e3
    have hs : h.normalizedPushforward I g = P * Matrix.GeneralLinearGroup.map alg (ρ₀ g) * P⁻¹ :=
      by rw [← e1]; group
    have e4 : ρA g = Qa⁻¹ * h.normalizedPushforward I g * Qa := by
      rw [normalizedPushforward_apply]
      show ρA g = Qa⁻¹ * (Qa * ρA g * Qa⁻¹) * Qa
      group
    show ρA g = (Qa⁻¹ * P * Qa) * Matrix.GeneralLinearGroup.map ψ₂.toRingHom (ρuniv g) *
      (Qa⁻¹ * P * Qa)⁻¹
    rw [e2, e4, hs, e3]
    group
  have hψ₁conj : IsConjugate
      (fun g => Matrix.GeneralLinearGroup.map (Ideal.Quotient.mkₐ ℤ_[ℓ] I).toRingHom (ρuniv g))
      (fun g => ρA g) := ⟨1, fun g => by simp [hρA]; rfl⟩
  obtain ⟨ψ, -, huniq⟩ := h.universal A rfl hcomp redA (ZMod.ringHom_surjective _) hredA_cont
    (fun a => by
      rw [show algebraMap ℤ_[ℓ] A a = mk (algebraMap ℤ_[ℓ] R a) from rfl, h.quotientReduce_mk,
        h.reduce_algebraMap])
    ρA (by
      obtain ⟨Q', hQ'⟩ := h.reduce_rep
      exact ⟨Q', fun g => by
        show ρ₀ g = Q' * Matrix.GeneralLinearGroup.map redA (ρA g) * Q'⁻¹
        rw [hmapcomp]; exact hQ' g⟩)
    hdetA
  have e1 := huniq (Ideal.Quotient.mkₐ ℤ_[ℓ] I) ⟨hmk_cont, hψ₁conj⟩
  have e2 := huniq ψ₂ ⟨hψ₂cont, hψ₂conj⟩
  intro x hx
  have : (Ideal.Quotient.mkₐ ℤ_[ℓ] I) x = ψ₂ x := by rw [e1, e2]
  have hx0 : reduce x = 0 := by rw [← RingHom.mem_ker, hker]; exact hx
  rw [Ideal.Quotient.mkₐ_eq_mk, hψ₂, hx0, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end Quotient

/-- **Primes with finite geometric image.** Let `R` be a Noetherian universal deformation ring
of `ρ₀` with determinant fixed to `δ`, let `N` be a normal subgroup of `π` on which `ρ₀` is
absolutely irreducible, and assume `ℓ ∤ n`. A prime `𝔮` of `R` containing `ℓ` such that the
pushforward of `ρuniv` to `R/𝔮` has finite image on `N` is the maximal ideal of `R`. -/
theorem eq_maximalIdeal_of_finite_image
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    [IsNoetherianRing R] (N : Subgroup π) [N.Normal]
    (hirr : IsAbsolutelyIrreducible fun g : N => ρ₀ g) (hn : ¬ ℓ ∣ n)
    (𝔮 : Ideal R) [h𝔮 : 𝔮.IsPrime] (hℓ : algebraMap ℤ_[ℓ] R ℓ ∈ 𝔮)
    (hfin : ((fun g => Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk 𝔮) (ρuniv g)) ''
      (N : Set π)).Finite) :
    𝔮 = maximalIdeal R := by
  classical
  set A := R ⧸ 𝔮
  have : IsLocalRing A := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hℓA : ((ℓ : ℕ) : A) = 0 := by
    rwa [← map_natCast (algebraMap ℤ_[ℓ] A), ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
  have : CharP A ℓ := (CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)).2 hℓA
  let : Algebra (ZMod ℓ) A := ZMod.algebra A ℓ
  have hcompA : IsAdicComplete (maximalIdeal A) A :=
    (quotient_isNoetherianCompleteLocalRing ⟨inferInstance, inferInstance, h.isAdicComplete⟩ 𝔮
      h𝔮.ne_top).isComplete
  set σ := h.normalizedPushforward 𝔮
  have hσfin : (σ '' (N : Set π)).Finite := by
    have : σ '' (N : Set π) = (MulAut.conj (Matrix.GeneralLinearGroup.map
        (algebraMap (ZMod ℓ) A) h.reduce_rep.choose)) '' ((fun g =>
        Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk 𝔮) (ρuniv g)) '' (N : Set π)) := by
      rw [Set.image_image]
      exact Set.image_congr fun g _ => by
        rw [normalizedPushforward_apply]
        rfl
    rw [this]
    exact hfin.image _
  have hnA : IsUnit (Fintype.card (Fin n) : A) := by
    rw [Fintype.card_fin, ← map_natCast (algebraMap (ZMod ℓ) A)]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  obtain ⟨P, -, hP⟩ := Matrix.GeneralLinearGroup.exists_conj_eq_map_of_finite_image (S := A) N
    ρ₀.toMonoidHom hirr (h.residue_comp_algebraMap_surjective 𝔮) hnA σ
    (h.normalizedPushforward_sub_mem 𝔮) (h.det_normalizedPushforward 𝔮) hσfin
  exact le_antisymm (h.le_maximalIdeal_of_isLocalRing_quotient 𝔮)
    (h.maximalIdeal_le_of_conj_eq 𝔮 hcompA P hP)

end Deformation.IsUniversalFixedDeterminantDeformation

module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.IteratedDerivation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroDerivation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TorComputation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TorObstruction
public import StacksCore.Tactic.StacksAttribute

/-! # Gulliksen's obstruction to finite Tor dimension

This is the engine of Stacks Tag 09PU. Let `T` be a Tate resolution of `S` over `R`, let
`q : R' → R` have square-zero principal kernel `(f)` with annihilator image `I`, and suppose the
graded algebra of `T` admits a square-zero lift carrying divided powers compatibly. The lift
produces a degree `-2` derivation `θ` on `T.A / I·T.A` (Tag 09PS). Given a degree-two class `ξ`
which is a cycle modulo `I·T.A` and on which `θ` takes a value `y` whose image in `S/IS` is not
nilpotent — which is what Tag 09PT supplies — the conclusion is that `S` does **not** have finite
Tor dimension over `R`.

The mechanism is the one computation: `θ^[n]` sends the `n`-th divided power of `ξ` to `yⁿ`
(`iterate_derivation_dpow_quotient`). Since `T` is a projective resolution of `S`
(`Resolution.projectiveResolution`), `Tor_i(S, R/I)` is the `i`-th homology of `T.complex`
tensored with `R/I`, which `Resolution.tensorQuotEquiv` presents as `T.grade i / I·T.grade i`. If
`Tor_{2n}` vanished, the class of `γ_n(ξ)` in degree `2n` would be a boundary; applying `θ` `n`
times would then exhibit `yⁿ` as a boundary too
(`iterate_derivation_differential_quotient`), and the augmentation kills boundaries — so `yⁿ`
would die in `S/IS`, contradicting non-nilpotency. As only the even degrees `2n` are used,
`not_exists_tor_vanishing_bound_of_even_ne_zero` is enough to contradict finite Tor dimension.

## Statement form

The lift is taken as an `IsDividedPowerSquareZeroLift`, whose `map_dpow` and `D_dpow` fields say
that `π` commutes with divided powers and that `D` obeys the divided-power Leibniz rule. Both are
essential: without them there is no `δ.dpow m b` to differentiate and the argument has nothing to
run on. They are exactly the two clauses of Tag 09PS's construction that concern `δ`.

The conclusion is prefixed by `letI`s installing the resolution's `Ring`, `Algebra`,
`GradedAlgebra`, `IsStrictlyGradedComm` and `IsDifferentialGradedAlgebra` instances. These are
*fields* of `Resolution` rather than instances, so without them `IsSquareZeroLift` cannot even be
written down on `T.A`.

## Main results

* `not_exists_tor_vanishing_bound_of_derivation_class` — Gulliksen's obstruction.

## References

* [Stacks Project, Tag 09PU](https://stacks.math.columbia.edu/tag/09PU)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open CategoryTheory Limits CategoryTheory.MonoidalCategory

universe u

/-- The derivation of a square-zero lift sends boundaries to boundaries. -/
private theorem IsSquareZeroLift.exists_derivation_mk_differential
    {R' R A B : Type u} [CommRing R'] [CommRing R] [Ring A] [Algebra R A] [Ring B]
    [Algebra R' B] {q : R' →+* R} {f : R'} {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
    {d : A →ₗ[R] A} [IsDifferentialGradedAlgebra 𝒜 d] {ℬ : ℕ → Submodule R' B} [GradedAlgebra ℬ]
    {π : B →+* A} {D : B →ₗ[R'] B} {κ : RingHom.ker π →+ (A ⧸ squareZeroAnnihilatorSMul q f A)}
    (h : IsSquareZeroLift q f 𝒜 d ℬ π D κ) (z : A) :
    ∃ w : A, h.derivation (Submodule.Quotient.mk (d z)) = Submodule.Quotient.mk (d w) := by
  obtain ⟨b, rfl⟩ := h.surjective z
  obtain ⟨c, hc⟩ := (h.mem_ker_iff (D (D b))).mp (h.map_D_comp_D b)
  refine ⟨π c, ?_⟩
  rw [← h.map_D b, h.derivation_mk_map_eq (β := D c), h.map_D]
  rw [hc]
  simpa [Algebra.smul_def] using _root_.map_smul D f c

/-- The derivation of a divided-power square-zero lift on the divided powers of a degree-two
class: if `θ ξ = y`, then `θ (γ_m ξ) = y · γ_{m-1} ξ`. -/
private theorem IsDividedPowerSquareZeroLift.derivation_mk_dpow
    {R' R A B : Type u} [CommRing R'] [CommRing R] [Ring A] [Algebra R A] [Ring B]
    [Algebra R' B] {q : R' →+* R} {f : R'} {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
    {d : A →ₗ[R] A} [IsDifferentialGradedAlgebra 𝒜 d] {ℬ : ℕ → Submodule R' B} [GradedAlgebra ℬ]
    {π : B →+* A} {D : B →ₗ[R'] B} {κ : RingHom.ker π →+ (A ⧸ squareZeroAnnihilatorSMul q f A)}
    [IsStrictlyGradedComm 𝒜]
    {γ : DividedPowerStructure 𝒜} [IsStrictlyGradedComm ℬ] {δ : DividedPowerStructure ℬ}
    (h : IsDividedPowerSquareZeroLift q f 𝒜 γ d ℬ δ π D κ) {ξ y : A} (hξ : ξ ∈ 𝒜 2)
    (hθξ : h.derivation (Submodule.Quotient.mk ξ) = Submodule.Quotient.mk y)
    {m : ℕ} (hm : m ≠ 0) :
    h.derivation (Submodule.Quotient.mk (γ.dpow m ξ)) =
      Submodule.Quotient.mk (y * γ.dpow (m - 1) ξ) := by
  obtain ⟨b, hb, rfl⟩ :=
    exists_mem_grade_map_eq (𝒜 := ℬ) (ℬ := 𝒜) π h.surjective h.map_mem_grade hξ
  have hbpos : b ∈ positiveEvenPart ℬ := mem_positiveEvenPart_of_mem_grade _ (d := 1) one_pos hb
  obtain ⟨c, hc⟩ := (h.mem_ker_iff (D (D b))).mp (h.map_D_comp_D b)
  have hcy : Submodule.Quotient.mk (p := squareZeroAnnihilatorSMul q f A) (π c) =
      Submodule.Quotient.mk y := by
    rw [← h.derivation_mk_map_eq hc, hθξ]
  rw [← h.map_dpow m b hbpos, h.derivation_mk_map_eq (β := c * δ.dpow (m - 1) b), map_mul,
    h.map_dpow (m - 1) b hbpos]
  · refine (Submodule.Quotient.eq _).2 ?_
    rw [← sub_mul]
    exact mul_mem_smul_top_right _ ((Submodule.Quotient.eq _).1 hcy)
  · rw [differential_sq_dpow_of_rules ℬ δ D
      (fun {i} {x} hx => h.D_mem_grade i x hx)
      (fun {i j} {x y} hx hy => h.D_leibniz i j x y hx hy)
      (fun {n} {x} hn hx => h.D_dpow n x hn hx) hb m hm, hc, mul_assoc]

/-- The differential of `T.complex ⊗ R/I` is `d ⊗ id`. -/
private theorem Resolution.tensorComplex_d_apply
    {R S σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ) (I : Ideal R) (i : ℕ)
    (v : TensorProduct R (T.grade (i + 1)) (R ⧸ I)) :
    ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj T.complex).d (i + 1) i v =
      LinearMap.rTensor (R ⧸ I) (T.differentialAt i) v := by
  change ((T.complex.d (i + 1) i ▷ ModuleCat.of R (R ⧸ I)).hom) v = _
  rw [ModuleCat.hom_whiskerRight]
  simp only [Resolution.complex, ChainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- `tensorQuotEquiv` carries `d ⊗ id` to the map induced by `d` on `T.grade i / I • ⊤`. -/
private theorem Resolution.tensorQuotEquiv_rTensor_differentialAt
    {R S σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ) (I : Ideal R) (i : ℕ)
    (w : TensorProduct R (T.grade (i + 1)) (R ⧸ I)) :
    letI : Ring T.A := T.ring
    letI : Algebra R T.A := T.algebra
    T.tensorQuotEquiv I i (LinearMap.rTensor (R ⧸ I) (T.differentialAt i) w) =
      (I • (⊤ : Submodule R (T.grade (i + 1)))).mapQ (I • (⊤ : Submodule R (T.grade i)))
        (T.differentialAt i) (Submodule.smul_top_le_comap_smul_top I (T.differentialAt i))
        (T.tensorQuotEquiv I (i + 1) w) := by
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  refine TensorProduct.inductionOn w ?_ ?_
  · intro a b
    obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp [Resolution.tensorQuotEquiv, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
      Submodule.mapQ_apply, map_smul]
  · intro x z hx hz
    simp [hx, hz]

/-- If `Tor_{n+1}(S, R/I)` vanishes, every element of degree `n + 1` whose differential lies in
`I • T.A` is a boundary modulo `I • T.A`. -/
private theorem Resolution.exists_differential_mk_eq_of_isZero_tor
    {R S σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ) (hφ : Function.Surjective φ)
    (I : Ideal R) {n : ℕ} (hTor : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj
      (ModuleCat.of R S)).obj (ModuleCat.of R (R ⧸ I)))) :
    letI : Ring T.A := T.ring
    letI : Algebra R T.A := T.algebra
    ∀ x ∈ T.grade (n + 1), T.differential x ∈ I • (⊤ : Submodule R T.A) →
      ∃ w : T.A, Submodule.Quotient.mk (p := I • (⊤ : Submodule R T.A)) (T.differential w) =
        Submodule.Quotient.mk x := by
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  let : GradedAlgebra T.grade := T.graded
  let : IsStrictlyGradedComm T.grade := T.strict
  let : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  intro x hx hdx
  let K := (((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj T.complex
  let xs : T.grade (n + 1) := ⟨x, hx⟩
  let z : TensorProduct R (T.grade (n + 1)) (R ⧸ I) := xs ⊗ₜ[R] Ideal.Quotient.mk I 1
  have hevalz : T.tensorQuotEquiv I (n + 1) z = Submodule.Quotient.mk xs := by
    dsimp [Resolution.tensorQuotEquiv, z]
    simpa using TensorProduct.tensorQuotEquivQuotSMul_tmul_mk I xs (1 : R)
  have hmem : T.differentialAt n xs ∈ I • (⊤ : Submodule R (T.grade n)) := by
    let p : T.A →ₗ[R] T.grade n := (GradedAlgebra.proj T.grade n).codRestrict (T.grade n)
      fun a => by
        rw [GradedAlgebra.proj_apply]
        exact (DirectSum.decompose T.grade a n).property
    have hp : p (T.differential x) = T.differentialAt n xs := by
      apply Subtype.ext
      change GradedAlgebra.proj T.grade n (T.differential x) = T.differential x
      simp [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem T.grade
        (IsDifferentialGradedAlgebra.d_mem (𝒜 := T.grade) (d := T.differential) hx)]
    rw [← hp]
    exact Submodule.smul_top_le_comap_smul_top I p hdx
  have hz0 : LinearMap.rTensor (R ⧸ I) (T.differentialAt n) z = 0 := by
    apply (T.tensorQuotEquiv I n).injective
    rw [T.tensorQuotEquiv_rTensor_differentialAt, hevalz, Submodule.mapQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero]
  have hzcycle : K.d (n + 1) n z = 0 := (T.tensorComplex_d_apply I n z).trans hz0
  have hK : IsZero (K.homology (n + 1)) := by
    simpa [K] using (T.torIsoHomology hφ (ModuleCat.of R (R ⧸ I)) (n + 1)).isZero_iff.mp hTor
  have hnext : (ComplexShape.down ℕ).next (n + 1) = n := by simp
  let zc := K.cyclesMk z n hnext hzcycle
  have hπz : K.homologyπ (n + 1) zc = 0 :=
    congrArg (fun fh => fh zc) (hK.eq_of_tgt (K.homologyπ (n + 1)) 0)
  have hinc : (ConcreteCategory.hom (K.iCycles (n + 1))) zc = z := by
    simpa [zc] using HomologicalComplex.i_cyclesMk K z n hnext hzcycle
  obtain ⟨w, hw⟩ := (homologyπ_eq_zero_iff_exists_boundary K (n + 1) zc).mp hπz
  rw [hinc] at hw
  obtain ⟨wrep, hwrep⟩ := Submodule.Quotient.mk_surjective _ (T.tensorQuotEquiv I (n + 1 + 1) w)
  have hclass := T.tensorQuotEquiv_rTensor_differentialAt I (n + 1) w
  rw [(T.tensorComplex_d_apply I (n + 1) w).symm.trans hw, hevalz, ← hwrep,
    Submodule.mapQ_apply] at hclass
  refine ⟨wrep.1, (Submodule.Quotient.eq _).2 ?_⟩
  exact Submodule.smul_top_le_comap_smul_top I (T.grade (n + 1)).subtype
    ((Submodule.Quotient.eq _).1 hclass.symm)

/-- The augmentation maps `I • T.A` into `I S`. -/
private theorem Resolution.augmentation_mem_map_of_mem_smul_top
    {R S σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ) (I : Ideal R) :
    letI : Ring T.A := T.ring
    letI : Algebra R T.A := T.algebra
    ∀ {x : T.A}, x ∈ I • (⊤ : Submodule R T.A) → T.augmentation x ∈ I.map (algebraMap R S) := by
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr a _
    change T.augmentation.toLinearMap (r • a) ∈ I.map (algebraMap R S)
    rw [map_smul]
    change r • T.augmentation a ∈ I.map (algebraMap R S)
    simpa only [← Algebra.smul_def] using
      Ideal.mul_mem_right (T.augmentation a) _ (Ideal.mem_map_of_mem (algebraMap R S) hr)
  · intro x₁ x₂ hx₁ hx₂
    rw [map_add]
    exact add_mem hx₁ hx₂

/-- **Gulliksen's obstruction, the engine of Stacks 09PU.** A Tate resolution of `S` whose graded
algebra carries a divided-power square-zero lift across `q`, together with a degree-two class `ξ`
that is a cycle modulo `I·T.A` and whose derivation value `y` is non-nilpotent in `S/IS`, forces
`S` to have infinite Tor dimension over `R`. -/
public theorem not_exists_tor_vanishing_bound_of_derivation_class
    {R S σ R' : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing R']
    {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ)
    (hφ : Function.Surjective φ) (q : R' →+* R) (f : R') :
    letI : Ring T.A := T.ring
    letI : Algebra R T.A := T.algebra
    letI : GradedAlgebra T.grade := T.graded
    letI : IsStrictlyGradedComm T.grade := T.strict
    letI : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
    letI : IsCompatibleWithDifferential T.gamma T.differential := T.compatible
    ∀ {B : Type u} [Ring B] [Algebra R' B]
      (𝒝 : ℕ → Submodule R' B) [GradedAlgebra 𝒝] [IsStrictlyGradedComm 𝒝]
      (δ : DividedPowerStructure 𝒝)
      (π : B →+* T.A) (D : B →ₗ[R'] B)
      (κ : RingHom.ker π →+ (T.A ⧸ squareZeroAnnihilatorSMul q f T.A))
      (h : IsDividedPowerSquareZeroLift q f T.grade T.gamma T.differential 𝒝 δ π D κ),
      ∀ (ξ y : T.A), ξ ∈ T.grade 2 →
        T.differential ξ ∈ squareZeroAnnihilatorSMul q f T.A →
        y ∈ T.grade 0 →
        h.derivation (Submodule.Quotient.mk ξ) = Submodule.Quotient.mk y →
        ¬ IsNilpotent (Ideal.Quotient.mk
            (Ideal.map (algebraMap R S) (squareZeroAnnihilator q f))
            (T.augmentation y)) →
      ¬ ∃ bd : ℕ, ∀ (M : ModuleCat.{u} R) (i : ℕ), bd < i →
        IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R S)).obj M) := by
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  let : GradedAlgebra T.grade := T.graded
  let : IsStrictlyGradedComm T.grade := T.strict
  let : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  let : IsCompatibleWithDifferential T.gamma T.differential := T.compatible
  intro B _ _ 𝒝 _ _ δ π D κ h ξ y hξ hdξ hy hθξ hnil
  set I : Ideal R := squareZeroAnnihilator q f
  have hξpos : ξ ∈ positiveEvenPart T.grade :=
    mem_positiveEvenPart_of_mem_grade _ (d := 1) one_pos hξ
  apply not_exists_tor_vanishing_bound_of_even_ne_zero (S := S) (M := R ⧸ I)
  intro k hk hTor
  have hk' : 2 * k - 1 + 1 = 2 * k := by omega
  have hdp : T.gamma.dpow k ξ ∈ T.grade (2 * k - 1 + 1) := by
    rw [hk']
    simpa using T.gamma.dpow_mem_grade (d := 1) (Nat.ne_of_gt hk) hξpos hξ
  have hddp : T.differential (T.gamma.dpow k ξ) ∈ I • (⊤ : Submodule R T.A) := by
    rw [IsCompatibleWithDifferential.d_dpow (γ := T.gamma) (d := T.differential)
      (Nat.ne_of_gt hk) hξpos]
    exact mul_mem_smul_top_right I hdξ
  obtain ⟨w, hw⟩ :=
    T.exists_differential_mk_eq_of_isZero_tor hφ I (by rwa [hk']) _ hdp hddp
  -- The derivation sends boundaries to boundaries, and divided powers to the engine's form.
  obtain ⟨v, hv⟩ := iterate_derivation_differential_quotient (I • (⊤ : Submodule R T.A))
    h.derivation T.differential h.exists_derivation_mk_differential k w
  have hiter := iterate_derivation_dpow_quotient (R := R) (A := T.A) T.grade T.gamma
    (I • (⊤ : Submodule R T.A)) h.derivation h.derivation_leibniz
    (fun hx => mul_mem_smul_top_right I hx) (fun hx => mul_mem_smul_top_left I hx)
    (h.derivation_eq_zero_of_mem_grade_zero y hy) hξpos (h.derivation_mk_dpow hξ hθξ) k
  have hAug := T.augmentation_mem_map_of_mem_smul_top I
    ((Submodule.Quotient.eq _).1 (hv.symm.trans ((congrArg (h.derivation^[k]) hw).trans hiter)))
  rw [map_sub, T.augmentation_differential, zero_sub, neg_mem_iff] at hAug
  refine pow_ne_zero_of_not_isNilpotent hnil k ?_
  rwa [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]

end DividedPowers.TateResolution

end

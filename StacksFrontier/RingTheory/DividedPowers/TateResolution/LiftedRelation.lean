module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.PolynomialLift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroDerivation
public import StacksCore.Tactic.StacksAttribute

/-! # The derivation of a lifted relation

Let `q : R' → R` be a surjection with square-zero principal kernel `(f)`, let `(A, 𝒜, d)` be a
graded algebra with differential admitting a square-zero lift `(B, ℬ, π, D, κ)`, and let
`θ = h.derivation` be the degree `-2` derivation on `A / IA` that the lift produces, where `I`
is the image of the annihilator of `f` (Stacks Tag 09PS).

Suppose `ε : A → S` presents `S` as `H₀(A)` with `H₁(A) = 0`, and that `S` is presented as
`R[x₁,…,x_n]/(F₁,…,F_m)`. Given a relation `∑ rⱼ Fⱼ = 0` whose coefficients all lie in `I`, and
lifts `r'ⱼ, F'ⱼ` over `R'` with `∑ r'ⱼ F'ⱼ = g f`, this file produces a degree-two class `ξ`
with `θ ξ = g` in `S / IS`. That is Stacks Tag 09PT.

The construction follows the source. Lift the presentation to `ψ : R[x] → 𝒜 0` using
surjectivity of `ε` in degree zero; since `ε (ψ Fⱼ) = φ Fⱼ = 0`, exactness in degree zero gives
`uⱼ ∈ 𝒜 1` with `d uⱼ = ψ Fⱼ`; then `z = ∑ ψ(rⱼ) uⱼ` is a cycle in degree one because
`∑ rⱼ Fⱼ = 0`, and `H₁(A) = 0` gives `ξ ∈ 𝒜 2` with `d ξ = z`. Because the coefficients of `rⱼ`
lie in `I`, `z` lies in `I·A`, so `ξ` is a cycle modulo `I·A`.

To compute `θ ξ`, everything is lifted to `B`. The subtle step is the coefficients: the `rⱼ` are
lifted not to the given `r'ⱼ` but to polynomials `rAⱼ` whose coefficients *annihilate* `f`
(`exists_map_eq_and_coeff_mem_annihilator`), which is what kills the error term `∑ f ψ(rⱼ) aⱼ` of
the source. The two lifts differ by a multiple of `f` (`exists_eq_C_mul_of_map_eq_zero`), which
replaces `g` by `gA = g - ∑ bⱼ F'ⱼ` — a change invisible in `S`. Then `D² w = f · (ψB gA + D c₀)`
for any lift `w` of `ξ`, and `θ ξ` is the class of `π (ψB gA + D c₀)`, whose image under `ε` is
`φ (map q g)` since `ε ∘ d = 0`.

## Statement form

The source states this for the derivation of Tag 09PS, which is built from a
`GradedDividedPowerPolynomial` and whose construction asserts the existence of a lift. Here it is
stated for an arbitrary lift instead. That is a generalization — instantiating at the canonical
lift returns the source's form, since that derivation is by definition the one of its lift — and it
makes this result independent of the existence of a lift, which is a separate and much harder
statement. The only facts needed about the divided-power polynomial structure are that `𝒜 0` is
the image of the coefficient map and that `ι'` lands in `ℬ 0`; both are hypotheses here and both
are fields of the structure.

## Main results

* `exists_mem_grade_two_derivation_eq_lift` — the degree-two class and the value of `θ` on it.

## References

* [Stacks Project, Tag 09PT](https://stacks.math.columbia.edu/tag/09PT)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w x z t

/-- In a strictly graded-commutative algebra, any family in degree zero is the image of the
variables under an algebra map from a polynomial ring landing in degree zero. -/
private theorem exists_algHom_mvPolynomial_gradeZero
    {R : Type u} {A : Type w} {ι : Type z} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (a : ι → A) (ha : ∀ i, a i ∈ 𝒜 0) :
    ∃ ψ : MvPolynomial ι R →ₐ[R] A, (∀ p, ψ p ∈ 𝒜 0) ∧ ∀ i, ψ (MvPolynomial.X i) = a i := by
  let A₀ : Subalgebra R A :=
    { carrier := 𝒜 0
      zero_mem' := (𝒜 0).zero_mem
      one_mem' := SetLike.one_mem_graded 𝒜
      add_mem' := (𝒜 0).add_mem
      mul_mem' := fun hx hy => by simpa using SetLike.mul_mem_graded hx hy
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact (𝒜 0).smul_mem r (SetLike.one_mem_graded 𝒜) }
  let _ : CommRing A₀ :=
    { (inferInstance : Ring A₀) with
      mul_comm := fun x y => Subtype.ext <| by
        simpa using IsStrictlyGradedComm.graded_comm
          (𝒜 := 𝒜) (i := 0) (j := 0) x.property y.property }
  let ψ₀ : MvPolynomial ι R →ₐ[R] A₀ := MvPolynomial.aeval fun i => (⟨a i, ha i⟩ : A₀)
  exact ⟨A₀.val.comp ψ₀, fun p => (ψ₀ p).property, fun i => by simp [ψ₀]⟩

/-- An algebra map sends `I • ⊤` into the extension of `I`. -/
private theorem algHom_mem_map_of_mem_smul_top
    {R : Type u} {A : Type w} {S : Type t} [CommRing R] [Ring A] [Algebra R A]
    [CommRing S] [Algebra R S] (ε : A →ₐ[R] S) (I : Ideal R) {x : A}
    (hx : x ∈ I • (⊤ : Submodule R A)) : ε x ∈ I.map (algebraMap R S) := by
  have hle : I • (⊤ : Submodule R A) ≤
      Submodule.comap ε.toLinearMap ((I.map (algebraMap R S)).restrictScalars R) := by
    refine Submodule.smul_le.mpr fun r hr a _ => ?_
    show ε (r • a) ∈ I.map (algebraMap R S)
    rw [Algebra.smul_def, map_mul, ε.commutes]
    exact Ideal.mul_mem_right (ε a) _ (Ideal.mem_map_of_mem (algebraMap R S) hr)
  exact hle hx

/-- If `d uⱼ = ψ Fⱼ` and `∑ rⱼ Fⱼ = 0`, then `∑ ψ(rⱼ) uⱼ` is a cycle. -/
private theorem differential_sum_mul_eq_zero
    {R : Type u} {A : Type w} {ν : Type z} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} [IsDifferentialGradedAlgebra 𝒜 d]
    (ψ : MvPolynomial ν R →ₐ[R] A) (hψ : ∀ p, ψ p ∈ 𝒜 0) {m : ℕ}
    (r F : Fin m → MvPolynomial ν R) (hrel : ∑ j, r j * F j = 0)
    (u : Fin m → A) (hu : ∀ j, u j ∈ 𝒜 1) (hdu : ∀ j, d (u j) = ψ (F j)) :
    d (∑ j, ψ (r j) * u j) = 0 := by
  rw [map_sum]
  simp_rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) (hψ (r _)) (hu _),
    IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) (hψ _), hdu]
  simp only [zero_mul, zero_add, pow_zero, one_smul]
  calc
    (∑ j, ψ (r j) * ψ (F j)) = ψ (∑ j, r j * F j) := by simp
    _ = 0 := by simp [hrel]

/-- If `ψ` agrees with `π ∘ ι'` on lifts `p'ᵢ` of the variables, then `π ∘ ι' ∘ aeval p'` lifts
`ψ`. -/
private theorem map_aeval_eq_of_map_eq
    {R' : Type u} {R : Type v} {A : Type w} {B : Type x} {σ : Type z} {ν : Type t}
    [CommRing R'] [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R' B]
    {q : R' →+* R} (π : B →+* A) (ι : MvPolynomial σ R →ₐ[R] A)
    (ι' : MvPolynomial σ R' →ₐ[R'] B) (hπι : ∀ p, π (ι' p) = ι (MvPolynomial.map q p))
    (ψ : MvPolynomial ν R →ₐ[R] A) (p' : ν → MvPolynomial σ R')
    (hp' : ∀ i, ι (MvPolynomial.map q (p' i)) = ψ (MvPolynomial.X i))
    (p₀ : MvPolynomial ν R') :
    π (ι' (MvPolynomial.aeval p' p₀)) = ψ (MvPolynomial.map q p₀) := by
  have hFG : ι.toRingHom.comp ((MvPolynomial.map q).comp (MvPolynomial.aeval p').toRingHom) =
      ψ.toRingHom.comp (MvPolynomial.map q) :=
    MvPolynomial.ringHom_ext (fun _ => by simp) fun i => by simpa using hp' i
  exact (hπι _).trans (RingHom.congr_fun hFG p₀)

/-- Changing the coefficients of a relation `∑ r'ⱼ Fⱼ = g c` by multiples `c bⱼ` changes `g` by
`∑ bⱼ Fⱼ`. -/
private theorem sum_mul_eq_sub_mul_of_sub_eq_mul {T : Type u} [CommRing T] {m : ℕ} {c g : T}
    {r r' b F : Fin m → T} (hlift : ∑ j, r' j * F j = g * c)
    (hdiff : ∀ j, r' j - r j = c * b j) :
    ∑ j, r j * F j = (g - ∑ j, b j * F j) * c := by
  rw [sub_mul, ← hlift, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_eq_iff_eq_add'.mp (hdiff j)]
  ring

/-- If the coefficients of `rⱼ` annihilate `f`, `D vⱼ = ψ F'ⱼ + f cⱼ` and `∑ rⱼ F'ⱼ = g f`, then
`D (∑ ψ(rⱼ) vⱼ) = f ψ(g)`. -/
private theorem differential_sum_mul_eq_generator_mul
    {R' : Type u} {B : Type x} {ν : Type z} [CommRing R'] [Ring B] [Algebra R' B]
    (ℬ : ℕ → Submodule R' B) [GradedAlgebra ℬ] (D : B →ₗ[R'] B)
    (hDzero : ∀ b : B, b ∈ ℬ 0 → D b = 0)
    (hDmul : ∀ (i j : ℕ) (b c : B), b ∈ ℬ i → c ∈ ℬ j →
      D (b * c) = D b * c + (-1 : R') ^ i • (b * D c))
    (ψ : MvPolynomial ν R' →ₐ[R'] B) (hψ : ∀ p, ψ p ∈ ℬ 0) {f : R'} {m : ℕ}
    (r F : Fin m → MvPolynomial ν R') (g : MvPolynomial ν R')
    (hrann : ∀ j e, (r j).coeff e ∈ (Ideal.span {f}).annihilator)
    (hrel : ∑ j, r j * F j = g * MvPolynomial.C f)
    (v c : Fin m → B) (hDv : ∀ j, D (v j) = ψ (F j) + algebraMap R' B f * c j) :
    D (∑ j, ψ (r j) * v j) = algebraMap R' B f * ψ g := by
  have hrf (j : Fin m) : MvPolynomial.C f * r j = 0 := by
    ext e
    rw [MvPolynomial.coeff_C_mul]
    simpa [smul_eq_mul, mul_comm] using (Submodule.mem_annihilator_span_singleton f
      ((r j).coeff e)).mp (hrann j e)
  have hprod (j : Fin m) : ψ (r j) * D (v j) = ψ (r j) * ψ (F j) := by
    have hscalar : algebraMap R' B f * ψ (r j) = 0 := by
      simpa [map_mul] using congrArg ψ (hrf j)
    have hzero : ψ (r j) * (algebraMap R' B f * c j) = 0 := by
      rw [IsSquareZeroLift.generator_mul_comm f (ψ (r j)) (c j), ← mul_assoc, hscalar, zero_mul]
    rw [hDv, mul_add, hzero, add_zero]
  calc
    D (∑ j, ψ (r j) * v j) = ∑ j, ψ (r j) * ψ (F j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [differential_mul_of_mem_gradeZero ℬ D hDzero hDmul (hψ (r j)), hprod]
    _ = ψ (g * MvPolynomial.C f) := by
      rw [← hrel, map_sum]
      simp [map_mul]
    _ = algebraMap R' B f * ψ g := by
      rw [map_mul]
      simpa using (Algebra.commutes f (ψ g)).symm

/-- **Stacks 09PT.** A relation `∑ rⱼ Fⱼ = 0` with all coefficients in `I`, lifting to
`∑ r'ⱼ F'ⱼ = g f`, yields a class `ξ ∈ 𝒜 2` which is a cycle modulo `I·A` and on which the
derivation of the square-zero lift takes the value `g`, read in `S / IS`. -/
@[stacks 09PT]
public theorem exists_mem_grade_two_derivation_eq_lift
    {R' : Type u} {R : Type v} {A : Type w} {B : Type x} {σ : Type z} {S : Type t}
    [CommRing R'] [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R' B]
    [CommRing S] [Algebra R S]
    {q : R' →+* R} {f : R'}
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    {d : A →ₗ[R] A} [IsDifferentialGradedAlgebra 𝒜 d]
    {ℬ : ℕ → Submodule R' B} [GradedAlgebra ℬ]
    {π : B →+* A} {D : B →ₗ[R'] B}
    {κ : RingHom.ker π →+ (A ⧸ squareZeroAnnihilatorSMul q f A)}
    (h : IsSquareZeroLift q f 𝒜 d ℬ π D κ)
    (hker : RingHom.ker q = Ideal.span {f})
    (ι : MvPolynomial σ R →ₐ[R] A) (ι' : MvPolynomial σ R' →ₐ[R'] B)
    (hι₀ : ∀ a : A, a ∈ 𝒜 0 → ∃ p, ι p = a)
    (hι'mem : ∀ p : MvPolynomial σ R', ι' p ∈ ℬ 0)
    (hπι : ∀ p : MvPolynomial σ R', π (ι' p) = ι (MvPolynomial.map q p))
    (ε : A →ₐ[R] S)
    (hε₀ : ∀ s : S, ∃ a : A, a ∈ 𝒜 0 ∧ ε a = s)
    (hεd : ∀ a : A, ε (d a) = 0)
    (hH₀ : ∀ a : A, a ∈ 𝒜 0 → ε a = 0 → ∃ b : A, b ∈ 𝒜 1 ∧ d b = a)
    (hH₁ : ∀ a : A, a ∈ 𝒜 1 → d a = 0 → ∃ b : A, b ∈ 𝒜 2 ∧ d b = a)
    (n m : ℕ)
    (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (F r : Fin m → MvPolynomial (Fin n) R)
    (hkerφ : RingHom.ker φ.toRingHom = Ideal.span (Set.range F))
    (hrel : ∑ j, r j * F j = 0)
    (hcoeff : ∀ (j : Fin m) (e : Fin n →₀ ℕ),
      (r j).coeff e ∈ squareZeroAnnihilator q f)
    (F' r' : Fin m → MvPolynomial (Fin n) R')
    (g : MvPolynomial (Fin n) R')
    (hF : ∀ j, MvPolynomial.map q (F' j) = F j)
    (hr : ∀ j, MvPolynomial.map q (r' j) = r j)
    (hlift : ∑ j, r' j * F' j = g * MvPolynomial.C f) :
    ∃ ξ y : A,
      ξ ∈ 𝒜 2 ∧ d ξ ∈ squareZeroAnnihilatorSMul q f A ∧ y ∈ 𝒜 0 ∧
      h.derivation (Submodule.Quotient.mk ξ) = Submodule.Quotient.mk y ∧
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) (squareZeroAnnihilator q f)) (ε y) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R S) (squareZeroAnnihilator q f))
          (φ (MvPolynomial.map q g)) := by
  classical
  set I : Ideal R := squareZeroAnnihilator q f
  set J : Submodule R A := squareZeroAnnihilatorSMul q f A
  have hq : Function.Surjective q := h.surjective_base
  -- The degree-zero part is a commutative subalgebra, where the presentation is lifted.
  choose a ha0 hεa using fun i => hε₀ (φ (MvPolynomial.X i))
  obtain ⟨ψ, hψgrade, hψX⟩ := exists_algHom_mvPolynomial_gradeZero (R := R) (𝒜 := 𝒜) a ha0
  have hεψ (p : MvPolynomial (Fin n) R) : ε (ψ p) = φ p := by
    have hmap : ε.comp ψ = φ := MvPolynomial.algHom_ext fun i => by simp [hψX, hεa]
    exact DFunLike.congr_fun hmap p
  have hφF (j : Fin m) : φ (F j) = 0 := by
    have hFmem : F j ∈ RingHom.ker φ.toRingHom := by
      rw [hkerφ]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact RingHom.mem_ker.mp hFmem
  -- Exactness in degree zero bounds each `ψ Fⱼ`; the relation makes `z` a cycle in degree one.
  choose u hu1 hdu using fun j => hH₀ (ψ (F j)) (hψgrade (F j)) (by simp [hεψ, hφF])
  let z : A := ∑ j, ψ (r j) * u j
  have hz1 : z ∈ 𝒜 1 :=
    Submodule.sum_mem _ fun j _ => SetLike.mul_mem_graded (hψgrade (r j)) (hu1 j)
  have hdz : d z = 0 := differential_sum_mul_eq_zero ψ hψgrade r F hrel u hu1 hdu
  obtain ⟨ξ, hξ2, hdξ⟩ := hH₁ z hz1 hdz
  obtain ⟨y, hy0, hθξ⟩ := h.derivation_mem_grade 0 ξ (by simpa using hξ2)
  -- Transport the presentation through the coefficient maps `ι`, `ι'`.
  choose p hιp using fun i => hι₀ (a i) (ha0 i)
  choose p' hmapP using fun i => MvPolynomial.map_surjective (f := q) hq (p i)
  let ψB : MvPolynomial (Fin n) R' →ₐ[R'] B := ι'.comp (MvPolynomial.aeval p')
  have hψB (p₀ : MvPolynomial (Fin n) R') : π (ψB p₀) = ψ (MvPolynomial.map q p₀) :=
    map_aeval_eq_of_map_eq π ι ι' hπι ψ p' (fun i => by rw [hmapP, hιp, hψX]) p₀
  -- Lift the coefficients so that they annihilate `f`; this is what kills the error term.
  choose rA hrA hrAann using fun j =>
    exists_map_eq_and_coeff_mem_annihilator q hq f (r j) (hcoeff j)
  choose b hdiff using fun j =>
    exists_eq_C_mul_of_map_eq_zero q f hker (r' j - rA j) (by rw [map_sub, hr j, hrA j, sub_self])
  let gA : MvPolynomial (Fin n) R' := g - ∑ j, b j * F' j
  have hliftA : ∑ j, rA j * F' j = gA * MvPolynomial.C f :=
    sum_mul_eq_sub_mul_of_sub_eq_mul hlift hdiff
  -- Lift the chain `uⱼ`, `ξ` to `B` and compute `D²`.
  choose v hπv using fun j => h.surjective (u j)
  have hDv_exists (j : Fin m) : ∃ x : B,
      D (v j) - ψB (F' j) = algebraMap R' B f * x := by
    apply (h.mem_ker_iff (D (v j) - ψB (F' j))).mp
    simp [map_sub, h.map_D, hπv, hdu, hψB, hF]
  choose c hDv_eq using hDv_exists
  let zB : B := ∑ j, ψB (rA j) * v j
  have hDzB : D zB = algebraMap R' B f * ψB gA :=
    differential_sum_mul_eq_generator_mul ℬ D h.D_eq_zero h.D_leibniz ψB (fun _ => hι'mem _)
      rA F' gA hrAann hliftA v c fun j => sub_eq_iff_eq_add'.mp (hDv_eq j)
  obtain ⟨w, hπw⟩ := h.surjective ξ
  have hπzB : π zB = z := by
    dsimp [zB, z]
    simp [map_sum, map_mul, hψB, hrA, hπv]
  obtain ⟨c₀, hDw_eq⟩ : ∃ x : B, D w - zB = algebraMap R' B f * x := by
    apply (h.mem_ker_iff (D w - zB)).mp
    rw [map_sub, h.map_D, hπw, hdξ, hπzB]
    simp
  let e₀ : B := ψB gA + D c₀
  have hDsqw : D (D w) = algebraMap R' B f * e₀ := by
    have hDscalar (x : B) : D (algebraMap R' B f * x) = algebraMap R' B f * D x := by
      rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
    dsimp only [e₀]
    rw [sub_eq_iff_eq_add'.mp hDw_eq, map_add, hDzB, hDscalar, mul_add]
  -- `θ ξ` is the class of `π e₀`, whose image in `S/IS` is the lifted relation.
  have hθe : h.derivation (Submodule.Quotient.mk ξ) = Submodule.Quotient.mk (π e₀) := by
    rw [← hπw]
    exact h.derivation_mk_map_eq hDsqw
  have hdiffJ : y - π e₀ ∈ J :=
    (Submodule.Quotient.eq J).mp (by simpa using hθξ.symm.trans hθe)
  have hεe : ε (π e₀) = φ (MvPolynomial.map q g) := by
    dsimp only [e₀]
    rw [map_add, map_add, hψB, h.map_D, hεψ, hεd, add_zero]
    simp [gA, map_sub, map_sum, map_mul, hF, hφF]
  refine ⟨ξ, y, hξ2, ?_, hy0, hθξ, ?_⟩
  · rw [hdξ]
    exact Submodule.sum_mem _ fun j _ => eval_mul_mem_smul_top I ψ (r j) (hcoeff j) (u j)
  · exact Ideal.Quotient.eq.mpr
      (by simpa [map_sub, hεe] using algHom_mem_map_of_mem_smul_top ε I hdiffJ)

end DividedPowers.TateResolution

end

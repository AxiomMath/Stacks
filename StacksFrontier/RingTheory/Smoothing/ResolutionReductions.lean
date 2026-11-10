module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.LiftingResolutionsFromEighthPowers
public import StacksFrontier.RingTheory.Smoothing.ParameterPowerAlgebra

/-!
# Evaluating the auxiliary algebras of a resolution and reducing to a twisted base

Fix a field `k`, a finite-type `k`-algebra `A` with `H_{A/k} = (a_1, …, a_t)`, a `k`-algebra map
`A → Λ` and a prime `q ⊂ Λ`, and let `B = A[x_1, …, x_d, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} a_j)` with
`B → C` the enlargement of Stacks 07FP, carrying a `k[x_1, …, x_d]`-algebra retraction `C → B`.

Elements `π'_1, …, π'_d ∈ Λ` and `λ_{ij} ∈ Λ` satisfying `(π'_i)^{2N} = Σ_j a_j λ_{ij}` determine
an `A`-algebra map `B → Λ`, hence by the retraction a ring map `C → Λ`. On the other side,
`π_1, …, π_d` in the polynomial ring `k[y_1, …, y_m]` and `δ_1, …, δ_d ∈ Λ` determine the
*twisted base* `R = k[y_1, …, y_m, t_1, …, t_d]` with its two structure maps: `R → Λ` extending a
given `φ : k[y_1, …, y_m] → Λ` by `t_i ↦ δ_i`, and `k[x_1, …, x_d] → R` sending `x_i` to the
twisted parameter `γ_i = π_i t_i`.

The two reduction steps in this situation are: resolving `R → D → Λ ⊃ q` suffices to resolve
`k → A → Λ ⊃ q`, when `R` is smooth over `k` and the generators `a_j` of `H_{A/k}` map into
`H_{D/R}`; and resolving the quotient of a chain by `(γ_1^{8c}, …, γ_d^{8c})` suffices to resolve
the chain itself, when the `γ_i^c` are strictly standard.

## Main definitions

* `Stacks.Smoothing.parameterPowerAlgebraToTarget`: the `A`-algebra map `B → Λ` with
  `x_i ↦ π'_i` and `z_{ij} ↦ λ_{ij}`.
* `Stacks.Smoothing.improvedAlgebraToTarget`: the ring map `C → Λ` obtained from it by the
  retraction `C → B`.
* `Stacks.Smoothing.twistedParameter`: the element `γ_i = π_i t_i` of
  `R = k[y_1, …, y_m, t_1, …, t_d]`.
* `Stacks.Smoothing.twistedBaseToTarget`: the `k`-algebra map `R → Λ` given by `φ` on the `y_j`
  and by `t_i ↦ δ_i`.
* `Stacks.Smoothing.twistedBaseHom`: the `k`-algebra map `k[x_1, …, x_d] → R`, `x_i ↦ γ_i`.
* `Stacks.Smoothing.twistedParameterPowerIdeal`: the ideal `(γ_1^e, …, γ_d^e) ⊂ R`.
* `Stacks.Smoothing.twistedBasePrime`: the prime `r ⊂ R` lying under `q`.
* `Stacks.Smoothing.baseParameterPowerIdeal`: the ideal `(π_1^e, …, π_d^e) ⊂ k[y_1, …, y_m]`.

## Main results

* `Stacks.Smoothing.canBeResolved_of_canBeResolved_of_smooth_base`: the reduction of
  `k → A → Λ ⊃ q` to `R → D → Λ ⊃ q`.
* `Stacks.Smoothing.singularIdeal_le_singularIdeal_of_smooth`: `H_{T/R} ⊆ H_{T/k}` for a tower
  `k → R → T` with `R` smooth over `k`.
* `Stacks.Smoothing.canBeResolved_of_quotient_span_pow`: the reduction of `R → D → Λ ⊃ q` to its
  quotient by `(γ_1^{8c}, …, γ_d^{8c})`.
* `Stacks.Smoothing.isStrictlyStandard_tensorProduct_pow_X`: strict standardness of `γ_i^c` in
  the base change over `R`.
* `Stacks.Smoothing.twistedParameterPowerIdeal_eq_eighthPowerIdeal`: `(γ_1^e, …, γ_d^e)` with
  `e = 8c` is the ideal of eighth powers of `γ_1^c, …, γ_d^c`.
* `Stacks.Smoothing.mem_singularIdeal_algebraMap_of_smooth_away` and
  `Stacks.Smoothing.mem_singularIdeal_includeRight`: the two transfers of the singular ideal,
  along `B → C` and along the base change to `R ⊗_{k[x_1, …, x_d]} C`.
* `Stacks.Smoothing.canBeResolved_of_canBeResolved_tensorProduct`: the first reduction at the
  chain `R → R ⊗_{k[x_1, …, x_d]} C → Λ` itself, with `a_j ⊗ 1 ∈ H_{(R ⊗ C)/R}` discharged from
  `H_{A/k} ⊆ H_{B/k[x_1, …, x_d]}`.

## Implementation notes

The variables of `R` are indexed by `Fin m ⊕ Fin d`, with `y_j = X (Sum.inl j)` and
`t_i = X (Sum.inr i)`; those of `B` by `Fin d ⊕ Fin d × Fin t` as in
`Stacks.Smoothing.parameterPowerAlgebra`.

The base change `C ⊗_{k[x_1, …, x_d]} R` is handled in the shape `R ⊗_{k[x_1, …, x_d]} C`, for
which the `R`-algebra structure is Mathlib's canonical one and
`isStrictlyStandard_basechange` applies verbatim; the two are isomorphic as
`R`-algebras. In the two reduction theorems the base `R` and the middle algebra `D` are left
abstract, carrying only the structure that the earlier steps supply, so that they apply to the
polynomial ring and the base change above and also to their localizations and quotients.

## References

* [Stacks Project, Tag 07FY](https://stacks.math.columbia.edu/tag/07FY)
* [Stacks Project, Tag 07FZ](https://stacks.math.columbia.edu/tag/07FZ)
* [Stacks Project, Tag 07G0](https://stacks.math.columbia.edu/tag/07G0)
* [Stacks Project, Tag 07G1](https://stacks.math.columbia.edu/tag/07G1)
* [Stacks Project, Tag 07G2](https://stacks.math.columbia.edu/tag/07G2)
* [Stacks Project, Tag 07G3](https://stacks.math.columbia.edu/tag/07G3)
* [Stacks Project, Tag 07G5](https://stacks.math.columbia.edu/tag/07G5)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Smoothing

universe u v w

/-! ### Evaluating `B` and `C` in `Λ` -/

/-- The `A`-algebra map `B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} a_j) → Λ` sending `x_i` to
`π'_i` and `z_{ij}` to `λ_{ij}`, where `(π'_i)^{2N} = Σ_j a_j λ_{ij}` in `Λ`. -/
@[stacks 07FY]
noncomputable def parameterPowerAlgebraToTarget {A : Type v} {Λ : Type w} [CommRing A]
    [CommRing Λ] [Algebra A Λ] {d t : ℕ} (N : ℕ) (a : Fin t → A) (π' : Fin d → Λ)
    (lam : Fin d → Fin t → Λ)
    (hπ' : ∀ i, π' i ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j) :
    parameterPowerAlgebra A d N a →ₐ[A] Λ :=
  Ideal.Quotient.liftₐ _
    (MvPolynomial.aeval (Sum.elim π' fun ij : Fin d × Fin t => lam ij.1 ij.2)) <| by
      have h : parameterPowerIdeal d N a ≤
          RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := Λ)
            (Sum.elim π' fun ij : Fin d × Fin t => lam ij.1 ij.2)).toRingHom := by
        rw [parameterPowerIdeal, Ideal.span_le]
        rintro x ⟨i, rfl⟩
        simp [RingHom.mem_ker, hπ' i]
      exact fun x hx => h hx

/-- The map `Stacks.Smoothing.parameterPowerAlgebraToTarget` sends the class of `x_i` to `π'_i`. -/
@[simp]
lemma parameterPowerAlgebraToTarget_X_inl {A : Type v} {Λ : Type w} [CommRing A] [CommRing Λ]
    [Algebra A Λ] {d t : ℕ} (N : ℕ) (a : Fin t → A) (π' : Fin d → Λ)
    (lam : Fin d → Fin t → Λ)
    (hπ' : ∀ i, π' i ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j) (i : Fin d) :
    parameterPowerAlgebraToTarget N a π' lam hπ'
        (Ideal.Quotient.mk (parameterPowerIdeal d N a) (MvPolynomial.X (Sum.inl i))) = π' i := by
  change MvPolynomial.aeval (Sum.elim π' fun ij : Fin d × Fin t => lam ij.1 ij.2)
      (MvPolynomial.X (Sum.inl i)) = π' i
  simp

/-- The map `Stacks.Smoothing.parameterPowerAlgebraToTarget` sends the class of `z_{ij}` to
`λ_{ij}`. -/
@[simp]
lemma parameterPowerAlgebraToTarget_X_inr {A : Type v} {Λ : Type w} [CommRing A] [CommRing Λ]
    [Algebra A Λ] {d t : ℕ} (N : ℕ) (a : Fin t → A) (π' : Fin d → Λ)
    (lam : Fin d → Fin t → Λ)
    (hπ' : ∀ i, π' i ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j) (i : Fin d) (j : Fin t) :
    parameterPowerAlgebraToTarget N a π' lam hπ'
        (Ideal.Quotient.mk (parameterPowerIdeal d N a) (MvPolynomial.X (Sum.inr (i, j)))) =
      lam i j := by
  change MvPolynomial.aeval (Sum.elim π' fun ij : Fin d × Fin t => lam ij.1 ij.2)
      (MvPolynomial.X (Sum.inr (i, j))) = lam i j
  simp

/-- The ring map `C → Λ` obtained by composing the `k[x_1, …, x_d]`-algebra retraction `g : C → B`
of Stacks 07FP with the map `B → Λ` of `Stacks.Smoothing.parameterPowerAlgebraToTarget`. -/
@[stacks 07FY]
noncomputable def improvedAlgebraToTarget {k : Type u} {A : Type v} {Λ : Type w} {C : Type v}
    [CommRing k] [CommRing A] [CommRing Λ] [CommRing C] [Algebra k A] [Algebra A Λ] {d t : ℕ}
    [Algebra (MvPolynomial (Fin d) k) C] (N : ℕ) (a : Fin t → A) (π' : Fin d → Λ)
    (lam : Fin d → Fin t → Λ)
    (hπ' : ∀ i, π' i ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j)
    (g : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a) : C →+* Λ :=
  (parameterPowerAlgebraToTarget N a π' lam hπ').toRingHom.comp g.toRingHom

/-- The map `Stacks.Smoothing.improvedAlgebraToTarget` sends `c ∈ C` to the image of `g c` under
`Stacks.Smoothing.parameterPowerAlgebraToTarget`. -/
lemma improvedAlgebraToTarget_apply {k : Type u} {A : Type v} {Λ : Type w} {C : Type v}
    [CommRing k] [CommRing A] [CommRing Λ] [CommRing C] [Algebra k A] [Algebra A Λ] {d t : ℕ}
    [Algebra (MvPolynomial (Fin d) k) C] (N : ℕ) (a : Fin t → A) (π' : Fin d → Λ)
    (lam : Fin d → Fin t → Λ)
    (hπ' : ∀ i, π' i ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j)
    (g : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a) (c : C) :
    improvedAlgebraToTarget N a π' lam hπ' g c =
      parameterPowerAlgebraToTarget N a π' lam hπ' (g c) :=
  rfl

/-! ### The twisted base `R = k[y_1, …, y_m, t_1, …, t_d]` -/

/-- The twisted parameter `γ_i = π_i t_i` in `R = k[y_1, …, y_m, t_1, …, t_d]`, for
`π_i ∈ k[y_1, …, y_m]`. -/
noncomputable def twistedParameter {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (i : Fin d) : MvPolynomial (Fin m ⊕ Fin d) k :=
  MvPolynomial.rename Sum.inl (π i) * MvPolynomial.X (Sum.inr i)

/-- The `k`-algebra map `R = k[y_1, …, y_m, t_1, …, t_d] → Λ` which is a given
`φ : k[y_1, …, y_m] → Λ` on the variables `y_j` and sends `t_i` to `δ_i ∈ Λ`. -/
@[stacks 07FZ]
noncomputable def twistedBaseToTarget {k : Type u} {Λ : Type w} [CommRing k] [CommRing Λ]
    [Algebra k Λ] {m d : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (δ : Fin d → Λ) :
    MvPolynomial (Fin m ⊕ Fin d) k →ₐ[k] Λ :=
  MvPolynomial.aeval (Sum.elim (fun j => φ (MvPolynomial.X j)) δ)

/-- The map `Stacks.Smoothing.twistedBaseToTarget` sends `t_i` to `δ_i`. -/
@[simp]
lemma twistedBaseToTarget_X_inr {k : Type u} {Λ : Type w} [CommRing k] [CommRing Λ] [Algebra k Λ]
    {m d : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (δ : Fin d → Λ) (i : Fin d) :
    twistedBaseToTarget φ δ (MvPolynomial.X (Sum.inr i)) = δ i :=
  MvPolynomial.aeval_X _ _

/-- On the subalgebra `k[y_1, …, y_m] ⊆ R` the map of
`Stacks.Smoothing.twistedBaseToTarget` is the given `φ`. -/
lemma twistedBaseToTarget_comp_rename {k : Type u} {Λ : Type w} [CommRing k] [CommRing Λ]
    [Algebra k Λ] {m d : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (δ : Fin d → Λ) :
    (twistedBaseToTarget φ δ).comp
        (MvPolynomial.rename (σ := Fin m) (τ := Fin m ⊕ Fin d) (R := k) Sum.inl) = φ := by
  refine MvPolynomial.algHom_ext fun j => ?_
  simp [twistedBaseToTarget]

/-- The `k`-algebra map `k[x_1, …, x_d] → R = k[y_1, …, y_m, t_1, …, t_d]` sending `x_i` to the
twisted parameter `γ_i = π_i t_i`. -/
@[stacks 07FZ]
noncomputable def twistedBaseHom {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) :
    MvPolynomial (Fin d) k →ₐ[k] MvPolynomial (Fin m ⊕ Fin d) k :=
  MvPolynomial.aeval (twistedParameter π)

/-- The map `Stacks.Smoothing.twistedBaseHom` sends `x_i` to the twisted parameter `γ_i`. -/
@[simp]
lemma twistedBaseHom_X {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (i : Fin d) :
    twistedBaseHom π (MvPolynomial.X i) = twistedParameter π i :=
  MvPolynomial.aeval_X _ _

/-- The ideal `I = (γ_1^e, …, γ_d^e)` of `R = k[y_1, …, y_m, t_1, …, t_d]` generated by the `e`-th
powers of the twisted parameters. -/
@[stacks 07G1]
noncomputable def twistedParameterPowerIdeal {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (e : ℕ) : Ideal (MvPolynomial (Fin m ⊕ Fin d) k) :=
  Ideal.span (Set.range fun i => twistedParameter π i ^ e)

/-- The prime `r ⊂ R = k[y_1, …, y_m, t_1, …, t_d]` which is the inverse image of `q ⊂ Λ` under the
map of `Stacks.Smoothing.twistedBaseToTarget`. -/
@[stacks 07G3]
noncomputable def twistedBasePrime {k : Type u} {Λ : Type w} [CommRing k] [CommRing Λ]
    [Algebra k Λ] {m d : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (δ : Fin d → Λ) (q : Ideal Λ) :
    Ideal (MvPolynomial (Fin m ⊕ Fin d) k) :=
  q.comap (twistedBaseToTarget φ δ).toRingHom

/-- The ideal `Stacks.Smoothing.twistedBasePrime φ δ q` is prime when `q` is prime. -/
instance isPrime_twistedBasePrime {k : Type u} {Λ : Type w} [CommRing k] [CommRing Λ]
    [Algebra k Λ] {m d : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (δ : Fin d → Λ) (q : Ideal Λ)
    [q.IsPrime] : (twistedBasePrime φ δ q).IsPrime :=
  Ideal.comap_isPrime _ _

/-- The ideal `J = (π_1^e, …, π_d^e)` of `k[y_1, …, y_m]`. -/
@[stacks 07G5]
noncomputable def baseParameterPowerIdeal {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (e : ℕ) : Ideal (MvPolynomial (Fin m) k) :=
  Ideal.span (Set.range fun i => π i ^ e)

/-! ### Reducing to the twisted base -/

/-- In a tower `k → R → T` with `R` smooth over `k`, the singular ideal `H_{T/R}` is contained in
`H_{T/k}`: a localization of `T` smooth over `R` is smooth over `k`. -/
theorem singularIdeal_le_singularIdeal_of_smooth (k R T : Type*) [CommRing k] [CommRing R]
    [CommRing T] [Algebra k R] [Algebra R T] [Algebra k T] [IsScalarTower k R T]
    [Algebra.Smooth k R] : singularIdeal R T ≤ singularIdeal k T := by
  rw [singularIdeal, singularIdeal]
  refine PrimeSpectrum.vanishingIdeal_anti_mono ?_
  rintro p hp ⟨g, hg, hsmooth⟩
  have : Algebra.Smooth R (Localization.Away g) := hsmooth
  exact hp ⟨g, hg, Algebra.Smooth.comp k R (Localization.Away g)⟩

/-- Let `k → A → Λ ⊃ q` be a chain with `H_{A/k} = (a_1, …, a_t)`, and let `R → D → Λ` be a chain
through the same `Λ` with `R` smooth over `k`, where `A → D` is an intermediate `k`-algebra map. If
every `a_j` maps into `H_{D/R}`, then resolving `R → D → Λ ⊃ q` resolves `k → A → Λ ⊃ q`. Applied
to `D = C ⊗_{k[x_1, …, x_d]} R`, this is the reduction of step (16) of Stacks 07FJ. -/
@[stacks 07G0 "for an arbitrary R-algebra D in place of C ⊗_{k[x_1, …, x_d]} R"]
theorem canBeResolved_of_canBeResolved_of_smooth_base {k : Type u} {R : Type u} {A : Type v}
    {D : Type v} {Λ : Type w} [CommRing k] [CommRing R] [CommRing A] [CommRing D] [CommRing Λ]
    [Algebra k R] [Algebra k A] [Algebra k D] [Algebra k Λ] [Algebra A Λ] [Algebra R D]
    [Algebra R Λ] [Algebra D Λ] [Algebra A D] [IsScalarTower k A Λ] [IsScalarTower k R Λ]
    [IsScalarTower k R D] [IsScalarTower k A D] [IsScalarTower R D Λ] [IsScalarTower A D Λ]
    [Algebra.Smooth k R] {t : ℕ} (a : Fin t → A) (q : Ideal Λ)
    (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (haD : ∀ j, algebraMap A D (a j) ∈ singularIdeal R D)
    (h : CanBeResolved R D Λ q) : CanBeResolved k A Λ q := by
  obtain ⟨T, instT, instRT, instDT, instTΛ, hRDT, hDTΛ, hRTΛ, hfp, hle, hnle⟩ := h
  let : CommRing T := instT
  let : Algebra R T := instRT
  let : Algebra D T := instDT
  let : Algebra T Λ := instTΛ
  let : IsScalarTower R D T := hRDT
  let : IsScalarTower D T Λ := hDTΛ
  let : IsScalarTower R T Λ := hRTΛ
  let : Algebra.FinitePresentation R T := hfp
  let : Algebra k T := ((algebraMap R T).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A T := ((algebraMap D T).comp (algebraMap A D)).toAlgebra
  have : IsScalarTower A D T := IsScalarTower.of_algebraMap_eq' rfl
  have hkAT : IsScalarTower k A T := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply k R T, IsScalarTower.algebraMap_apply A D T,
      ← IsScalarTower.algebraMap_apply k A D, IsScalarTower.algebraMap_apply k R D,
      ← IsScalarTower.algebraMap_apply R D T]
  have hkTΛ : IsScalarTower k T Λ := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply k R T, ← IsScalarTower.algebraMap_apply R T Λ,
      ← IsScalarTower.algebraMap_apply k R Λ]
  have hATΛ : IsScalarTower A T Λ := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply A D T, ← IsScalarTower.algebraMap_apply D T Λ,
      ← IsScalarTower.algebraMap_apply A D Λ]
  have hmap : Ideal.map (algebraMap T Λ) (singularIdeal R T) ≤
      Ideal.map (algebraMap T Λ) (singularIdeal k T) :=
    Ideal.map_mono (singularIdeal_le_singularIdeal_of_smooth k R T)
  refine ⟨T, instT, inferInstance, inferInstance, instTΛ, hkAT, hATΛ, hkTΛ,
    Algebra.FinitePresentation.trans k R T, ?_, fun hq => hnle ((Ideal.radical_mono hmap).trans hq)⟩
  refine Ideal.radical_le_radical_iff.2 ?_
  rw [← ha, Ideal.map_span, Ideal.span_le]
  rintro x ⟨y, ⟨j, rfl⟩, rfl⟩
  refine (Ideal.radical_mono hmap) (hle (Ideal.le_radical ?_))
  rw [IsScalarTower.algebraMap_apply A D Λ]
  exact Ideal.mem_map_of_mem _ (haD j)

/-! ### Transferring the generators of `H_{A/k}` into `H_{(R ⊗ C)/R}` -/

/-- A smooth algebra map is a local complete intersection. -/
alias ringHom_isLocalCompleteIntersection_of_algebra_smooth :=
  ringHom_isLocalCompleteIntersection_of_smooth

/-- Let `kx → B → C` be a tower with `B` of finite presentation over `kx`, and let `b ∈ H_{B/kx}`.
If `C_b` is smooth over `B_b`, then the image of `b` lies in `H_{C/kx}`: the composite
`kx → B_b → C_b` is smooth. -/
theorem mem_singularIdeal_algebraMap_of_smooth_away {kx B C : Type*} [CommRing kx] [CommRing B]
    [CommRing C] [Algebra kx B] [Algebra B C] [Algebra kx C] [IsScalarTower kx B C]
    [Algebra.FinitePresentation kx B] {b : B} (hb : b ∈ singularIdeal kx B)
    (hsm :
      letI : Algebra (Localization.Away b) (Localization.Away (algebraMap B C b)) :=
        (Localization.awayMap (algebraMap B C) b).toAlgebra
      Algebra.Smooth (Localization.Away b) (Localization.Away (algebraMap B C b))) :
    algebraMap B C b ∈ singularIdeal kx C := by
  let : Algebra (Localization.Away b) (Localization.Away (algebraMap B C b)) :=
    (Localization.awayMap (algebraMap B C) b).toAlgebra
  have : Algebra.Smooth kx (Localization.Away b) :=
    smooth_localization_away_of_mem_singularIdeal kx B hb
  have : IsScalarTower kx (Localization.Away b) (Localization.Away (algebraMap B C b)) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change _ = Localization.awayMap (algebraMap B C) b _
    rw [IsScalarTower.algebraMap_apply kx B (Localization.Away b),
      Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
      ← IsScalarTower.algebraMap_apply kx B C,
      ← IsScalarTower.algebraMap_apply kx C (Localization.Away (algebraMap B C b))]
  exact mem_singularIdeal_of_smooth_of_isLocalizationAway kx C
    (Localization.Away (algebraMap B C b))
    (Algebra.Smooth.comp kx (Localization.Away b) _)

/-- The singular ideal grows under base change: `g ∈ H_{C/kx}` gives `1 ⊗ g ∈ H_{(R ⊗ C)/R}`,
because `(R ⊗_{kx} C)_{1 ⊗ g} ≅ R ⊗_{kx} C_g` is smooth over `R`. -/
theorem mem_singularIdeal_includeRight {kx : Type u} {R : Type u} {C : Type v} [CommRing kx]
    [CommRing R] [CommRing C] [Algebra kx R] [Algebra kx C]
    [Algebra.FinitePresentation kx C] {g : C} (hg : g ∈ singularIdeal kx C) :
    (Algebra.TensorProduct.includeRight g : R ⊗[kx] C) ∈ singularIdeal R (R ⊗[kx] C) := by
  have hsm : Algebra.Smooth kx (Localization.Away g) :=
    smooth_localization_away_of_mem_singularIdeal kx C hg
  have : Algebra.Smooth R (Localization.Away ((1 : R) ⊗ₜ[kx] g)) :=
    Algebra.Smooth.of_equiv
      (IsLocalization.Away.tensorProductEquivTMulRight kx R g (Localization.Away g))
  simpa [Algebra.TensorProduct.includeRight_apply] using
    mem_singularIdeal_of_smooth_of_isLocalizationAway R (R ⊗[kx] C)
      (f := (1 : R) ⊗ₜ[kx] g) (Localization.Away ((1 : R) ⊗ₜ[kx] g)) this

/-- A generator `a_j` of `H_{A/k}` whose image lies in `H_{B/k[x_1, …, x_d]}` has its image in
`R ⊗_{k[x_1, …, x_d]} C` lying in `H_{(R ⊗ C)/R}`, where `B` is the parameter-power algebra and
`C` is the enlargement of Stacks 07FP, whose conclusion supplies the smoothness of `C_b` over
`B_b`. -/
theorem mem_singularIdeal_includeRight_algebraMap {k : Type u} {A : Type v} {R : Type u}
    {C : Type v} [Field k] [CommRing A] [CommRing R] [CommRing C] [Algebra k A]
    [Algebra.FiniteType k A] {d t N : ℕ} {a : Fin t → A} [Algebra (MvPolynomial (Fin d) k) R]
    [Algebra (MvPolynomial (Fin d) k) C] [Algebra (parameterPowerAlgebra A d N a) C]
    [IsScalarTower (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) C] [Algebra A C]
    [IsScalarTower A (parameterPowerAlgebra A d N a) C]
    [Algebra.FinitePresentation (MvPolynomial (Fin d) k) C]
    (hB : ∀ j, algebraMap A (parameterPowerAlgebra A d N a) (a j) ∈
      singularIdeal (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a))
    (hC : ∀ b : parameterPowerAlgebra A d N a,
      RingHom.IsLocalCompleteIntersection
          (algebraMap (MvPolynomial (Fin d) k) (Localization.Away b)) →
      (letI : Algebra (Localization.Away b)
          (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)) :=
        (Localization.awayMap (algebraMap (parameterPowerAlgebra A d N a) C) b).toAlgebra
      Algebra.Smooth (Localization.Away b)
        (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)))) (j : Fin t) :
    (Algebra.TensorProduct.includeRight (algebraMap A C (a j)) :
        R ⊗[MvPolynomial (Fin d) k] C) ∈
      singularIdeal R (R ⊗[MvPolynomial (Fin d) k] C) := by
  have : Algebra.Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j))) :=
    smooth_localization_away_of_mem_singularIdeal _ _ (hB j)
  have h := mem_singularIdeal_algebraMap_of_smooth_away (hB j)
    (hC _ ringHom_isLocalCompleteIntersection_of_algebra_smooth)
  rw [← IsScalarTower.algebraMap_apply A (parameterPowerAlgebra A d N a) C] at h
  exact mem_singularIdeal_includeRight h

/-- Stacks 07G0 at the chain of step (16) itself: `R → R ⊗_{k[x_1, …, x_d]} C → Λ`, with the
membership `a_j ⊗ 1 ∈ H_{(R ⊗ C)/R}` discharged from `H_{A/k} ⊆ H_{B/k[x_1, …, x_d]}` and the
conclusion of Stacks 07FP. The tag is carried by
`Stacks.Smoothing.canBeResolved_of_canBeResolved_of_smooth_base`, of which this is an
instantiation. -/
theorem canBeResolved_of_canBeResolved_tensorProduct {k : Type u} {A : Type u} {Λ : Type w}
    {R : Type u} {C : Type u} [Field k] [CommRing A] [CommRing Λ] [CommRing R] [CommRing C]
    [Algebra k A] [Algebra A Λ] [Algebra k Λ] [IsScalarTower k A Λ] [Algebra.FiniteType k A]
    [Algebra k R] [Algebra R Λ] [IsScalarTower k R Λ] [Algebra.Smooth k R] {d t N : ℕ}
    [Algebra (MvPolynomial (Fin d) k) R] [IsScalarTower k (MvPolynomial (Fin d) k) R]
    [Algebra (MvPolynomial (Fin d) k) C] [Algebra k C]
    [IsScalarTower k (MvPolynomial (Fin d) k) C] [Algebra A C] [IsScalarTower k A C]
    {a : Fin t → A} [Algebra (parameterPowerAlgebra A d N a) C]
    [IsScalarTower (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) C]
    [IsScalarTower A (parameterPowerAlgebra A d N a) C]
    [Algebra.FinitePresentation (MvPolynomial (Fin d) k) C]
    [Algebra (R ⊗[MvPolynomial (Fin d) k] C) Λ]
    [IsScalarTower R (R ⊗[MvPolynomial (Fin d) k] C) Λ] (q : Ideal Λ)
    (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (hAΛ : ∀ x : A, algebraMap (R ⊗[MvPolynomial (Fin d) k] C) Λ
        (Algebra.TensorProduct.includeRight (algebraMap A C x)) = algebraMap A Λ x)
    (hB : ∀ j, algebraMap A (parameterPowerAlgebra A d N a) (a j) ∈
      singularIdeal (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a))
    (hC : ∀ b : parameterPowerAlgebra A d N a,
      RingHom.IsLocalCompleteIntersection
          (algebraMap (MvPolynomial (Fin d) k) (Localization.Away b)) →
      (letI : Algebra (Localization.Away b)
          (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)) :=
        (Localization.awayMap (algebraMap (parameterPowerAlgebra A d N a) C) b).toAlgebra
      Algebra.Smooth (Localization.Away b)
        (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b))))
    (h : CanBeResolved R (R ⊗[MvPolynomial (Fin d) k] C) Λ q) : CanBeResolved k A Λ q := by
  let : Algebra A (R ⊗[MvPolynomial (Fin d) k] C) :=
    ((Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin d) k) (A := R)
      (B := C)).toRingHom.comp (algebraMap A C)).toAlgebra
  have : IsScalarTower k A (R ⊗[MvPolynomial (Fin d) k] C) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change _ = Algebra.TensorProduct.includeRight (algebraMap A C (algebraMap k A x))
    rw [← IsScalarTower.algebraMap_apply k A C,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) C,
      Algebra.TensorProduct.includeRight.commutes,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k)
        (R ⊗[MvPolynomial (Fin d) k] C)]
  have : IsScalarTower A (R ⊗[MvPolynomial (Fin d) k] C) Λ :=
    IsScalarTower.of_algebraMap_eq fun x => (hAΛ x).symm
  exact canBeResolved_of_canBeResolved_of_smooth_base a q ha
    (mem_singularIdeal_includeRight_algebraMap hB hC) h

/-! ### Reducing to the quotient by the twisted parameter powers -/

/-- The `c`-th power of the image of the variable `x_i` is strictly standard in
`R ⊗_{k[x_1, …, x_d]} C` over `R` as soon as it is strictly standard in `C` over
`k[x_1, …, x_d]`. For `R = k[y_1, …, y_m, t_1, …, t_d]` with `x_i ↦ γ_i` this says that `γ_i^c` is
strictly standard in the base change over `R`. -/
theorem isStrictlyStandard_tensorProduct_pow_X {k : Type u} [CommRing k] {d : ℕ} {R : Type u}
    {C : Type v} [CommRing R] [CommRing C] [Algebra (MvPolynomial (Fin d) k) R]
    [Algebra (MvPolynomial (Fin d) k) C] (c : ℕ) (i : Fin d)
    (h : IsStrictlyStandard (R := MvPolynomial (Fin d) k) (A := C)
      (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i) ^ c)) :
    IsStrictlyStandard (R := R) (A := R ⊗[MvPolynomial (Fin d) k] C)
      (algebraMap R (R ⊗[MvPolynomial (Fin d) k] C)
        (algebraMap (MvPolynomial (Fin d) k) R (MvPolynomial.X i) ^ c)) := by
  have hb := isStrictlyStandard_basechange (R := MvPolynomial (Fin d) k) (A := C) (R' := R) _ h
  have heq : (Algebra.TensorProduct.includeRight
        (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i) ^ c) :
          R ⊗[MvPolynomial (Fin d) k] C) =
      algebraMap R (R ⊗[MvPolynomial (Fin d) k] C)
        (algebraMap (MvPolynomial (Fin d) k) R (MvPolynomial.X i) ^ c) := by
    rw [map_pow, map_pow, Algebra.TensorProduct.includeRight.commutes,
      ← IsScalarTower.algebraMap_apply]
  rwa [heq] at hb

/-- The ideal generated by the `8c`-th powers of a family is the ideal generated by the eighth
powers of its `c`-th powers. -/
private lemma span_pow_eq_eighthPowerIdeal {R : Type*} [CommRing R] {d : ℕ} (γ : Fin d → R)
    (c : ℕ) :
    Ideal.span (Set.range fun i => γ i ^ (8 * c)) = eighthPowerIdeal (fun i => γ i ^ c) := by
  rw [eighthPowerIdeal]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_ofPred_eq, ← pow_mul]
  constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, by rw [Nat.mul_comm]⟩

/-- With `e = 8c`, the ideal `I = (γ_1^e, …, γ_d^e)` is the ideal generated by the eighth powers
of `γ_1^c, …, γ_d^c`, which is the ideal that Stacks 07F8 divides by. -/
theorem twistedParameterPowerIdeal_eq_eighthPowerIdeal {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (c : ℕ) :
    twistedParameterPowerIdeal π (8 * c) =
      eighthPowerIdeal (fun i => twistedParameter π i ^ c) :=
  span_pow_eq_eighthPowerIdeal _ c

/-- Let `R → D → Λ ⊃ q` be a chain with `R` Noetherian and `D` of finite presentation over `R`, let
`γ_1, …, γ_d ∈ R` with `d ≥ 1`, and let `I = (γ_1^{8c}, …, γ_d^{8c})`. Assume each `γ_i^c` maps
into `q`, is strictly standard in `D` over `R`, and has the annihilator condition of Stacks 07FW
and 07FX in `R` and in `Λ` modulo the eighth powers of `γ_1^c, …, γ_{i-1}^c`. Then resolving
`R/I → D/ID → Λ/IΛ` resolves `R → D → Λ ⊃ q`. -/
@[stacks 07G2 "for arbitrary γ_1, …, γ_d ∈ R, d ≥ 1"]
theorem canBeResolved_of_quotient_span_pow {R : Type u} {D : Type v} {Λ : Type w} [CommRing R]
    [CommRing D] [CommRing Λ] [Algebra R D] [Algebra D Λ] [Algebra R Λ] [IsScalarTower R D Λ]
    [IsNoetherianRing R] [Algebra.FinitePresentation R D] (q : Ideal Λ) [q.IsPrime] {d : ℕ}
    (hd : 1 ≤ d) (γ : Fin d → R) (c : ℕ) (I : Ideal R)
    (hI : I = Ideal.span (Set.range fun i => γ i ^ (8 * c)))
    (hγq : ∀ i, algebraMap R Λ (γ i ^ c) ∈ q)
    (hannR : ∀ i,
      let K := eighthPowerPrefixIdeal (fun i => γ i ^ c) i
      (Submodule.span (R ⧸ K) {Ideal.Quotient.mk K (γ i ^ c)}).annihilator =
        (Submodule.span (R ⧸ K) {(Ideal.Quotient.mk K (γ i ^ c)) ^ 2}).annihilator)
    (hannΛ : ∀ i,
      let K := Ideal.map (algebraMap R Λ) (eighthPowerPrefixIdeal (fun i => γ i ^ c) i)
      (Submodule.span (Λ ⧸ K)
          {Ideal.Quotient.mk K (algebraMap R Λ (γ i ^ c))}).annihilator =
        (Submodule.span (Λ ⧸ K)
          {(Ideal.Quotient.mk K (algebraMap R Λ (γ i ^ c))) ^ 2}).annihilator)
    (hstd : ∀ i, IsStrictlyStandard (R := R) (A := D) (algebraMap R D (γ i ^ c)))
    (hresolve :
      let ID := Ideal.map (algebraMap R D) I
      let IΛ := Ideal.map (algebraMap D Λ) ID
      letI : Algebra (R ⧸ I) (Λ ⧸ IΛ) :=
        ((algebraMap (D ⧸ ID) (Λ ⧸ IΛ)).comp (algebraMap (R ⧸ I) (D ⧸ ID))).toAlgebra
      letI : IsScalarTower (R ⧸ I) (D ⧸ ID) (Λ ⧸ IΛ) :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      CanBeResolved (R ⧸ I) (D ⧸ ID) (Λ ⧸ IΛ) (Ideal.map (Ideal.Quotient.mk IΛ) q)) :
    CanBeResolved R D Λ q := by
  obtain rfl : I = eighthPowerIdeal (fun i => γ i ^ c) := by
    rw [hI, span_pow_eq_eighthPowerIdeal]
  exact canBeResolved_of_quotient_eighthPowerIdeal
    { R := R, A := D, Λ := Λ, q := q } hd (fun i => γ i ^ c) hγq hannR hannΛ hstd hresolve

end Stacks.Smoothing

end

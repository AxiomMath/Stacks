module

public import StacksFrontier.Examples.Flatness.OrdinaryCone.EllipticCocycle
public import StacksFrontier.Examples.Flatness.OrdinaryCone.Segre
public import StacksFrontier.Examples.Flatness.OrdinaryCone.SegreCocycle
public import StacksFrontier.Examples.Flatness.OrdinaryCone.SegreNontrivial
public import StacksFrontier.RingTheory.GradedCompletion.MvPowerSeries
public import StacksFrontier.RingTheory.WittVector.BhattObstruction

/-!
# Graded algebras over `k⟦X₀, X₁, X₂⟧` with no map to a finite free algebra

Let `k` be a separably closed field of characteristic `p`, `P = k[X₀, X₁, X₂]` and
`R = k⟦X₀, X₁, X₂⟧`. Let `Γ` be a graded domain which is a finite `P`-module through an algebra map
sending every variable into degree one, and `S = R ⊗_P Γ`. Suppose given an Artin–Schreier–Witt
Čech cocycle over the fraction field of `Γ` on a finite family `w` of elements of `Γ` whose radical
contains the images of the variables, whose zeroth coefficient at some index is a quotient `α / β`
of two homogeneous elements of the same degree, and is not of the form `h₀ ^ p - h₀` for any
quotient `h₀` of two homogeneous elements of the same degree of `Γ`. Then there is no `R`-algebra
map from `S` to a nontrivial finite free `R`-algebra.

Indeed, `Γ → S` is injective, so the cocycle moves to the fraction field of `S`; the persistence of
Artin–Schreier type equations under `Γ → S`
(`Stacks.GradedCompletion.exists_div_eq_pow_sub_of_fractionRing`) shows that its zeroth coefficient
is still not of the form `h ^ p - h` there, and the obstruction
`Stacks.ArtinSchreier.isEmpty_algHom_of_artinSchreierWitt_cocycle` applies to the henselian local
ring `R`, its regular sequence `X₀, X₁, X₂` and the domain `S`, finite over `R`.

## Main results

* `Stacks.GradedCompletion.includeRight_injective`: `Γ → R ⊗_P Γ`, `γ ↦ 1 ⊗ γ`, is injective.
* `Stacks.GradedCompletion.isEmpty_algHom_tensorProduct_of_cocycle`: the statement above.
* `Stacks.Examples.OrdinaryCone.algebraMap_X_mem_radical_span_segreCover`,
  `Stacks.Examples.OrdinaryCone.segreElem_ne_zero`,
  `Stacks.Examples.OrdinaryCone.segreElem_sq_mem_segreGrading`: the hypotheses on the covering and
  on the zeroth coefficient `(zs)² / (xs)²` for the Segre product of the ordinary cone with
  `k[s, t]`.
* `Stacks.Examples.OrdinaryCone.isEmpty_algHom_tensor_segre`: over a separably closed field `k` of
  characteristic two, `k⟦X₀, X₁, X₂⟧ ⊗_{k[X₀, X₁, X₂]} Γ`, for `Γ` the Segre product of the
  ordinary cone with `k[s, t]`, admits no `k⟦X₀, X₁, X₂⟧`-algebra map to a nontrivial finite free
  `k⟦X₀, X₁, X₂⟧`-algebra.
-/

@[expose] public section

open MvPolynomial TensorProduct WittVector IsLocalRing RingTheory.Sequence
open Stacks.ArtinSchreier Stacks.RingTheory.PuncturedVanishing
open scoped nonZeroDivisors

namespace Stacks.GradedCompletion

variable {k Γ : Type*} [Field k] [CommRing Γ] [Algebra k Γ] (𝒜 : ℕ → Submodule k Γ)
  [GradedAlgebra 𝒜]

section Inclusion

variable {n : ℕ} [Algebra (MvPolynomial (Fin n) k) Γ] [IsScalarTower k (MvPolynomial (Fin n) k) Γ]

/-- The map `Γ → R ⊗_P Γ`, `γ ↦ 1 ⊗ γ`, is injective: followed by the embedding of `R ⊗_P Γ` into
`Γ⟦T⟧` it is `γ ↦ ∑_d γ_d T^d`. -/
theorem includeRight_injective
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1) :
    Function.Injective (Algebra.TensorProduct.includeRight :
      Γ →ₐ[MvPolynomial (Fin n) k] MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ) := by
  intro γ γ' h
  have h' := congrArg (completionMap 𝒜 hX) h
  simp only [Algebra.TensorProduct.includeRight_apply, completionMap_tmul, map_one,
    one_mul] at h'
  exact toPowerSeries_injective 𝒜 h'

end Inclusion

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

/-- **No map to a finite free algebra.** Let `k` be a separably closed field of characteristic `p`,
`P = k[X₀, X₁, X₂]`, `R = k⟦X₀, X₁, X₂⟧`, and let `Γ` be a graded domain which is a finite
`P`-module through an algebra map sending every variable into degree one. Let `w` be a finite
family of elements of `Γ` whose radical contains the images of the variables, and let `a j`,
`b i j` be Witt vectors over the fraction field of `Γ` with coefficients in `Γ[1/w j]`, resp.
`Γ[1/(w i * w j)]`, with `b i j + b j k = b i k` and `F (b i j) - b i j = a i - a j`. If the zeroth
coefficient of `a j₀` is `α / β` with `α, β ∈ Γ_d`, and is not `h₀ ^ p - h₀` for any quotient
`h₀ = α' / β'` of elements `α', β' ∈ Γ_{d'}`, then there is no `R`-algebra map from `R ⊗_P Γ` to a
nontrivial finite free `R`-algebra. -/
theorem isEmpty_algHom_tensorProduct_of_cocycle [CharP k p] [IsSepClosed k] [IsDomain Γ]
    [Algebra (MvPolynomial (Fin 3) k) Γ] [IsScalarTower k (MvPolynomial (Fin 3) k) Γ]
    [Module.Finite (MvPolynomial (Fin 3) k) Γ]
    (hX : ∀ i, algebraMap (MvPolynomial (Fin 3) k) Γ (X i) ∈ 𝒜 1)
    {ι : Type*} [Finite ι] (w : ι → Γ)
    (hxw : ∀ i, algebraMap (MvPolynomial (Fin 3) k) Γ (X i) ∈ (Ideal.span (Set.range w)).radical)
    (a : ι → 𝕎 (FractionRing Γ)) (b : ι → ι → 𝕎 (FractionRing Γ))
    (ha : ∀ j n, (a j).coeff n ∈ awaySubring (FractionRing Γ) (w j))
    (hb : ∀ i j n, (b i j).coeff n ∈ awaySubring (FractionRing Γ) (w i * w j))
    (hcoc : ∀ i j k, b i j + b j k = b i k)
    (hab : ∀ i j, frobenius (b i j) - b i j = a i - a j) (j₀ : ι) {d : ℕ} {α β : Γ}
    (hα : α ∈ 𝒜 d) (hβ : β ∈ 𝒜 d) (hβ0 : β ≠ 0)
    (ha₀ : (a j₀).coeff 0 = algebraMap Γ (FractionRing Γ) α / algebraMap Γ (FractionRing Γ) β)
    (h₀ : ∀ (d' : ℕ) (α' β' : Γ), α' ∈ 𝒜 d' → β' ∈ 𝒜 d' → β' ≠ 0 →
      (algebraMap Γ (FractionRing Γ) α' / algebraMap Γ (FractionRing Γ) β') ^ p -
        algebraMap Γ (FractionRing Γ) α' / algebraMap Γ (FractionRing Γ) β' ≠ (a j₀).coeff 0)
    (T : Type*) [CommRing T] [Nontrivial T] [Algebra (MvPowerSeries (Fin 3) k) T]
    [Module.Free (MvPowerSeries (Fin 3) k) T] [Module.Finite (MvPowerSeries (Fin 3) k) T] :
    IsEmpty (MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k] Γ →ₐ[MvPowerSeries (Fin 3) k]
      T) := by
  set R := MvPowerSeries (Fin 3) k
  set S := R ⊗[MvPolynomial (Fin 3) k] Γ
  have : IsDomain S := isDomain_tensorProduct hX
  have : IsSepClosed (ResidueField R) := MvPowerSeries.isSepClosed_residueField k 3
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have : CharP R p := charP_of_injective_algebraMap (algebraMap k R).injective p
  have hreg :
      IsWeaklyRegular R [(MvPowerSeries.X 0 : R), MvPowerSeries.X 1, MvPowerSeries.X 2] := by
    simpa [List.ofFn_succ] using MvPowerSeries.isWeaklyRegular_ofFn_X k 3
  -- the inclusion `Γ → S` and the induced map of fraction fields
  set ι' : Γ →ₐ[MvPolynomial (Fin 3) k] S := Algebra.TensorProduct.includeRight
  have hinj : Function.Injective ι' := includeRight_injective 𝒜 hX
  let ψ : FractionRing Γ →+* FractionRing S := IsLocalization.map (FractionRing S)
    ι'.toRingHom (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have hψ : ∀ γ, ψ (algebraMap Γ (FractionRing Γ) γ) = algebraMap S (FractionRing S) (ι' γ) :=
    fun γ => IsLocalization.map_eq _ _
  have hmem : ∀ (s : Γ) (ω : FractionRing Γ), ω ∈ awaySubring (FractionRing Γ) s →
      ψ ω ∈ awaySubring (FractionRing S) (ι' s) := fun s ω h =>
    map_mem_awaySubring ι'.toRingHom ψ hψ h
  -- the images of the variables of `R` in `S` lie in the radical of the ideal of the `1 ⊗ w j`
  have hxw' : ∀ i, algebraMap R S (MvPowerSeries.X i) ∈
      (Ideal.span (Set.range (fun j => ι' (w j)))).radical := by
    intro i
    have hXi :
        algebraMap R S (MvPowerSeries.X i) = ι' (algebraMap (MvPolynomial (Fin 3) k) Γ (X i)) := by
      rw [← MvPowerSeries.algebraMap_mvPolynomial_X k 3 (A := k) i,
        ← IsScalarTower.algebraMap_apply, ← ι'.commutes]
    obtain ⟨m, hm⟩ := hxw i
    have h := Ideal.mem_map_of_mem ι'.toRingHom hm
    rw [Ideal.map_span, ← Set.range_comp, map_pow] at h
    exact ⟨m, hXi ▸ h⟩
  -- the zeroth coefficient stays outside the image of `h ↦ h ^ p - h`
  have hβS : algebraMap S (FractionRing S) (ι' β) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).2
      ((map_ne_zero_iff _ hinj).2 hβ0)
  have h₀' : ∀ h : FractionRing S, h ^ p - h ≠ (map ψ (a j₀)).coeff 0 := by
    intro h hh
    rw [map_coeff, ha₀, map_div₀, hψ, hψ] at hh
    obtain ⟨d', α', β', hα', hβ', hβ'0, heq⟩ := exists_div_eq_pow_sub_of_fractionRing hX
      hp.out.two_le hα hβ hβ0 h (by rw [hh]; exact (mul_div_cancel₀ _ hβS).symm)
    exact h₀ d' α' β' hα' hβ' hβ'0 (by rw [ha₀, heq])
  exact isEmpty_algHom_of_artinSchreierWitt_cocycle (p := p) R hreg
    (x := fun i => (MvPowerSeries.X i : R)) (fun i h => by
      simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h)
    S (fun j => ι' (w j)) hxw'
    (fun j => map ψ (a j)) (fun i j => map ψ (b i j))
    (fun j n => by rw [map_coeff]; exact hmem _ _ (ha j n))
    (fun i j n => by rw [map_coeff, ← map_mul]; exact hmem _ _ (hb i j n))
    (fun i j k => by rw [← map_add, hcoc])
    (fun i j => by rw [← map_frobenius, ← map_sub, ← map_sub, hab]) j₀ h₀' T

end Stacks.GradedCompletion

namespace Stacks.Examples.OrdinaryCone

variable (k : Type*) [CommRing k]

/-- The images of the variables of `k[X₀, X₁, X₂]` in the Segre product lie in the radical of the
ideal generated by `xs, xt, ys, yt`. -/
theorem algebraMap_X_mem_radical_span_segreCover (i : Fin 3) :
    algebraMap (MvPolynomial (Fin 3) k) (segre k) (X i) ∈
      (Ideal.span (Set.range (segreCover k))).radical :=
  Ideal.le_radical (segreBase_X_mem_span_segreCover k i)

/-- The generators `u v` of the Segre product are nonzero. -/
theorem segreElem_ne_zero [Nontrivial k] (i : Fin 3) (j : Fin 2) : segreElem k i j ≠ 0 := by
  have hu : (Ideal.Quotient.mk (Ideal.span {equation k}) (X i) : Cone k) ≠ 0 := by
    fin_cases i
    exacts [Cone.x_ne_zero k, Cone.y_ne_zero k, Cone.z_ne_zero k]
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_segreElem, ZeroMemClass.coe_zero, segreGen, C_mul_X_eq_monomial,
    monomial_eq_zero] at h'
  exact hu h'

/-- The square of a generator of the Segre product has degree two. -/
theorem segreElem_sq_mem_segreGrading (i : Fin 3) (j : Fin 2) :
    segreElem k i j ^ 2 ∈ segreGrading k 2 :=
  SetLike.pow_mem_graded 2 (segreElem_mem_segreGrading k i j)

/-- **No map to a finite free algebra, for the Segre product.** Let `k` be a separably closed
field of characteristic two, `P = k[X₀, X₁, X₂]`, `R = k⟦X₀, X₁, X₂⟧` and `Γ` the Segre product of
the ordinary cone `k[x, y, z]/(z³ + (y² + xy) z + x³)` with `k[s, t]`, a `P`-algebra through
`X₀ ↦ xs`, `X₁ ↦ yt`, `X₂ ↦ xt + ys`. Then `R ⊗_P Γ` admits no `R`-algebra map to a nontrivial
finite free `R`-algebra: the Artin–Schreier–Witt cocycle of the elliptic curve, pulled back to
`E × ℙ¹` and with zeroth coefficient `(zs)² / (xs)²`, obstructs it. -/
theorem isEmpty_algHom_tensor_segre {k : Type*} [Field k] [IsSepClosed k] [CharP k 2]
    (T : Type*) [CommRing T] [Nontrivial T] [Algebra (MvPowerSeries (Fin 3) k) T]
    [Module.Free (MvPowerSeries (Fin 3) k) T] [Module.Finite (MvPowerSeries (Fin 3) k) T] :
    IsEmpty (MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k] segre k →ₐ[MvPowerSeries (Fin 3) k]
      T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : ∀ l : k, ∃ μ : k, μ ^ 2 + μ = l := fun l => by
    obtain ⟨μ, hμ⟩ := Stacks.ArtinSchreier.exists_pow_sub_self_eq_of_isSepClosed (L := k)
      one_lt_two (CharP.cast_eq_zero k 2) l
    exact ⟨μ, by rw [← hμ, CharTwo.sub_eq_add]⟩
  obtain ⟨a, b, ha, hb, hcoc, -, hab, ha₀⟩ := exists_segre_wittVector_cocycle k hk
  exact Stacks.GradedCompletion.isEmpty_algHom_tensorProduct_of_cocycle (p := 2)
    (segreGrading k) (algebraMap_X_mem_segreGrading k) (segreCover k)
    (algebraMap_X_mem_radical_span_segreCover k) a b ha hb hcoc hab 0
    (segreElem_sq_mem_segreGrading k 2 0) (segreElem_sq_mem_segreGrading k 0 0)
    (pow_ne_zero 2 (segreElem_ne_zero k 0 0)) ha₀
    (fun d α β hα hβ hβ0 => ha₀ ▸ forall_sq_sub_self_ne_sq_zs_div_sq_xs k d α β hα hβ hβ0) T

end Stacks.Examples.OrdinaryCone

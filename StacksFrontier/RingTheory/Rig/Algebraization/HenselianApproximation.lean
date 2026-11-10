module

public import StacksFrontier.RingTheory.Rig.DeformationPrincipal
public import StacksFrontier.RingTheory.Rig.HenselizationDescent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Completion
public import StacksFrontier.RingTheory.Rig.PrincipalLiftUniform
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Approximating formal points of an algebra étale off `V(a)` by henselian points

Let `A₀` be a Noetherian ring, `a₀ ∈ A₀`, and `W` a finite type `A₀`-algebra which is étale over
`Spec A₀ ∖ V(a₀)` and whose `a₀`-adic completion is rig-smooth. Let `D` be a Noetherian ring with
an ideal `𝔡`. There are constants `n₀` and `c`, depending only on `W` and on `(D, 𝔡)`, such that
if `μ : W → D^∧` is a ring map which is `A₀`-linear modulo `𝔡ⁿ` with `n ≥ n₀`, for some
`A₀`-algebra structure on `D` with `a₀ D = 𝔡`, then `μ` agrees modulo `𝔡ⁿ⁻ᶜ` with a ring map
`W → Dʰ` into the henselization of `(D, 𝔡)`.

## Main results

* `Rig.exists_ringHom_henselization_approx`: a ring map `W → D^∧` which is `A₀`-linear modulo
  `𝔡ⁿ` agrees modulo `𝔡ⁿ⁻ᶜ` with an `A₀`-linear ring map `W → Dʰ`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace Rig

attribute [local instance] HasDerivedCategory.standard

/-- Let `W` be a finite type `A₀`-algebra, étale over `Spec A₀ ∖ V(a₀)`, whose `a₀`-adic
completion is rig-smooth, and let `𝔡 = (d₀)` be an ideal of a Noetherian ring `D`. There are
`n₀` and `c` such that for every `n ≥ n₀`, every `A₀`-algebra structure on `D` with `a₀ ↦ d₀` and
every ring map `μ : W → D^∧` which is `A₀`-linear modulo `𝔡ⁿ`, there is an `A₀`-linear ring map
`ψ : W → Dʰ` into the henselization whose image in `D^∧` agrees with `μ` modulo `𝔡ⁿ⁻ᶜ`. -/
theorem exists_ringHom_henselization_approx {A₀ : Type u} [CommRing A₀]
    [IsNoetherianRing A₀] (a₀ : A₀) (I : Ideal A₀) (hI : I = Ideal.span {a₀})
    (W : Type u) [CommRing W] [Algebra A₀ W] [Algebra.FiniteType A₀ W]
    (hEt : IsEtaleOutside I W) (hsm : IsRigSmooth (adicCompletionObj I (B := W)))
    (D : Type u) [CommRing D] [IsNoetherianRing D] (𝔡 : Ideal D) (d₀ : D)
    (hgen : 𝔡 = Ideal.span {d₀}) :
    ∃ n₀ c : ℕ, ∀ n, n₀ ≤ n → ∀ (_ : Algebra A₀ D), algebraMap A₀ D a₀ = d₀ →
      ∀ μ : W →+* AdicCompletion 𝔡 D,
        (∀ x : A₀, μ (algebraMap A₀ W x) -
            algebraMap D (AdicCompletion 𝔡 D) (algebraMap A₀ D x) ∈
          (𝔡.map (algebraMap D (AdicCompletion 𝔡 D))) ^ n) →
        ∃ ψ : W →+* henselization D 𝔡,
          (∀ x : A₀, ψ (algebraMap A₀ W x) =
            algebraMap D (henselization D 𝔡) (algebraMap A₀ D x)) ∧
          ∀ w, (henselizationToAdicCompletion D 𝔡).1 (ψ w) - μ w ∈
            (𝔡.map (algebraMap D (AdicCompletion 𝔡 D))) ^ (n - c) := by
  obtain ⟨P, c, hc⟩ := hsm
  obtain ⟨d, hd⟩ := exists_disjoint_torsionIdeal_pow_span_singleton
    (algebraMap D (AdicCompletion 𝔡 D) d₀)
  refine ⟨max (2 * c) (c + d) + 1, c, fun n hn inst hd₀ μ hμ ↦ ?_⟩
  have h𝔡 : I.map (algebraMap A₀ D) = 𝔡 := by
    rw [hgen, hI, Ideal.map_span, Set.image_singleton, hd₀]
  subst h𝔡
  have hIC : I.map (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D)) =
      (I.map (algebraMap A₀ D)).map
        (algebraMap D (AdicCompletion (I.map (algebraMap A₀ D)) D)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : IsAdicComplete (I.map (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D)))
      (AdicCompletion (I.map (algebraMap A₀ D)) D) := by
    rw [hIC]
    exact AdicCompletion.isAdicComplete_self _ (Ideal.fg_of_isNoetherianRing _)
  have he : algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D) a₀ =
      algebraMap D (AdicCompletion (I.map (algebraMap A₀ D)) D) d₀ := by
    rw [IsScalarTower.algebraMap_apply A₀ D, hd₀]
  have htor : Disjoint (torsionIdeal (AdicCompletion (I.map (algebraMap A₀ D)) D)
      (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D) a₀))
      ((I.map (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D))) ^ d) := by
    have hsp : I.map (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D)) =
        Ideal.span {algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D) a₀} := by
      rw [← Set.image_singleton, ← Ideal.map_span, ← hI]
    rwa [hsp, he]
  have ha₀ : a₀ ∈ I := hI ▸ Ideal.mem_span_singleton_self a₀
  have hμa : μ (algebraMap A₀ W a₀) ∈ (I.map (algebraMap A₀ D)).map
      (algebraMap D (AdicCompletion (I.map (algebraMap A₀ D)) D)) := by
    have h2 : algebraMap D (AdicCompletion (I.map (algebraMap A₀ D)) D) (algebraMap A₀ D a₀) ∈
        (I.map (algebraMap A₀ D)).map
          (algebraMap D (AdicCompletion (I.map (algebraMap A₀ D)) D)) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha₀)
    have h3 := Ideal.add_mem _ (Ideal.pow_le_self (by lia) (hμ a₀)) h2
    rwa [sub_add_cancel] at h3
  let μn : W →ₐ[A₀] AdicCompletion (I.map (algebraMap A₀ D)) D ⧸
      (I.map (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D))) ^ n :=
    { toRingHom := (Ideal.Quotient.mk _).comp μ
      commutes' := fun x ↦ by
        change Ideal.Quotient.mk _ (μ (algebraMap A₀ W x)) =
          Ideal.Quotient.mk _ (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D) x)
        rw [Ideal.Quotient.eq,
          IsScalarTower.algebraMap_apply A₀ D (AdicCompletion (I.map (algebraMap A₀ D)) D) x]
        convert hμ x using 2 }
  have hker : (I.map (algebraMap A₀ W)) ^ n ≤ RingHom.ker μn.toRingHom := by
    have hle : I.map (algebraMap A₀ W) ≤ ((I.map (algebraMap A₀ D)).map
        (algebraMap D (AdicCompletion (I.map (algebraMap A₀ D)) D))).comap μ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have hy' : y ∈ Ideal.span {a₀} := hI ▸ hy
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy'
      rw [Ideal.mem_comap, Ideal.mem_comap, map_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hμa
    intro x hx
    have h' : μ x ∈ ((I.map (algebraMap A₀ D)).map
        (algebraMap D (AdicCompletion (I.map (algebraMap A₀ D)) D))) ^ n :=
      Ideal.le_comap_pow μ n (Ideal.pow_right_mono hle n hx)
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    convert h' using 2
  let ψn : (adicCompletionObj I (B := W)).carrier →ₐ[A₀]
      AdicCompletion (I.map (algebraMap A₀ D)) D ⧸
        (I.map (algebraMap A₀ (AdicCompletion (I.map (algebraMap A₀ D)) D))) ^ n :=
    (Ideal.Quotient.liftₐ ((I.map (algebraMap A₀ W)) ^ n) μn hker).comp
      ((AdicCompletion.evalₐ (I.map (algebraMap A₀ W)) n).restrictScalars A₀)
  obtain ⟨φ, hφ⟩ := exists_algHom_lift_of_torsion_disjoint a₀ I hI
    (adicCompletionObj I (B := W)) P c (fun N ξ ↦ by
      rw [← map_pow]
      exact hc N ξ (a₀ ^ c) (Ideal.pow_mem_pow ha₀ c)) d htor n (by lia) ψn
  let : Algebra A₀ (henselization D (I.map (algebraMap A₀ D))) :=
    ((algebraMap D (henselization D (I.map (algebraMap A₀ D)))).comp
      (algebraMap A₀ D)).toAlgebra
  let : IsScalarTower A₀ D (henselization D (I.map (algebraMap A₀ D))) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨ψ, hψ, -⟩ := exists_unique_algHom_henselization_of_adicCompletion A₀ W D I hEt φ
  refine ⟨ψ.toRingHom, fun x ↦ ψ.commutes x, fun w ↦ ?_⟩
  have h3 : ψn (algebraMap W (AdicCompletion (I.map (algebraMap A₀ W)) W) w) =
      Ideal.Quotient.mk _ (μ w) := by
    change Ideal.Quotient.liftₐ _ μn hker (AdicCompletion.evalₐ _ n
      (AdicCompletion.of _ _ w)) = _
    rw [AdicCompletion.evalₐ_of]
    rfl
  have h2' : Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le n c))
      (ψn (algebraMap W (AdicCompletion (I.map (algebraMap A₀ W)) W) w)) =
      Ideal.Quotient.mk _ (φ (algebraMap W (AdicCompletion (I.map (algebraMap A₀ W)) W) w)) :=
    AlgHom.congr_fun hφ (algebraMap W (AdicCompletion (I.map (algebraMap A₀ W)) W) w)
  rw [h3, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h2'
  have h4 : (henselizationToAdicCompletion D (I.map (algebraMap A₀ D))).1 (ψ w) =
      φ (algebraMap W (AdicCompletion (I.map (algebraMap A₀ W)) W) w) := AlgHom.congr_fun hψ w
  change (henselizationToAdicCompletion D (I.map (algebraMap A₀ D))).1 (ψ w) - μ w ∈ _
  rw [h4, ← neg_sub, neg_mem_iff]
  convert h2' using 2
  exact hIC.symm

end Rig

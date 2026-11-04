module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartCechThickening

/-!
# Compatible split presentations of a tower of finite projective modules

Let `⋯ → R₂ → R₁ → R₀` be a tower of rings with surjective transition maps `fₙ` whose kernels
are square-zero, and let `Mₙ` be a finite projective `Rₙ`-module, with `fₙ`-semilinear
transition maps `gₙ : Mₙ₊₁ → Mₙ` which are surjective and whose kernels are
`Ker(fₙ) · Mₙ₊₁`, so that `Mₙ₊₁ ⊗ Rₙ = Mₙ`. Then there are elements `e₁, …, e_m` of
`lim Mₙ` and splittings `σₙ : Mₙ → Rₙ^m` of the presentations `Rₙ^m → Mₙ` defined by the `eᵢ`,
compatible with the transition maps.

This is the algebra behind "a compatible system of finite projective modules over a tower is the
system of reductions of one finite projective module over the limit": the `σₙ` assemble to a
splitting of `(lim Rₙ)^m → lim Mₙ`, so `lim Mₙ` is a direct summand of `(lim Rₙ)^m`, and the
reductions of `lim Mₙ` are the `Mₙ`. The consumer reads all three facts (surjectivity onto each
`Mₙ`, the kernel of the projection to `Mₙ`, and the triviality of relations) directly off the
presentation, so only the presentation is stated here.

## Main results

* `AlgebraicGeometry.C1590Private.TwoChartTower.exists_semilinear_lift`: maps out of a
  projective module lift along a surjective semilinear map.
* `AlgebraicGeometry.C1590Private.TwoChartTower.exists_compatible_splitting`: the compatible
  split presentation.
-/

@[expose] public noncomputable section

universe u v w

namespace AlgebraicGeometry.C1590Private.TwoChartTower

section SemilinearLift

variable {R R' : Type*} [CommRing R] [CommRing R'] {φ : R →+* R'}
  {P N N' : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]
  [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R' N']

/-- **Maps out of a projective module lift along a surjective semilinear map.** If `P` is a
projective `R`-module, `g : N → N'` is surjective and `φ`-semilinear, and `h : P → N'` is
`φ`-semilinear, then `h` factors through `g` by an `R`-linear map. -/
theorem exists_semilinear_lift (g : N →ₛₗ[φ] N') (hg : Function.Surjective g)
    (h : P →ₛₗ[φ] N') : ∃ l : P →ₗ[R] N, ∀ x, g (l x) = h x := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R P›
  choose n hn using fun p : P => hg (h p)
  refine ⟨Finsupp.linearCombination R n ∘ₗ s, fun x => ?_⟩
  have hx : Finsupp.linearCombination R id (s x) = x := congrArg (fun F => F x) hs
  conv_rhs => rw [← hx]
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.linearCombination_apply,
    map_finsuppSum, LinearMap.map_smulₛₗ, hn, id]

end SemilinearLift

section Tower

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
  {M : ℕ → Type v} [∀ n, AddCommGroup (M n)] [∀ n, Module (R n) (M n)]
  (g : ∀ n, M (n + 1) →ₛₗ[f n] M n)

/-- The reduction `Rₙ₊₁^m → Rₙ^m`, coordinatewise. -/
def reduceCoords (m : ℕ) (n : ℕ) : (Fin m → R (n + 1)) →ₛₗ[f n] (Fin m → R n) where
  toFun v i := f n (v i)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_mul _ _ _

/-- The `i`-th coordinate of `reduceCoords f m n v` is `f n (v i)`. -/
@[simp] theorem reduceCoords_apply (m n : ℕ) (v : Fin m → R (n + 1)) (i : Fin m) :
    reduceCoords f m n v i = f n (v i) := rfl

variable [∀ n, Module.Finite (R n) (M n)] [∀ n, Module.Projective (R n) (M n)]

/-- **A compatible split presentation of a tower of finite projective modules.** Under the
hypotheses of the module docstring there are `m`, compatible elements `e₁, …, e_m` of the `Mₙ`
and `Rₙ`-linear maps `σₙ : Mₙ → Rₙ^m` with `∑ᵢ σₙ(x)ᵢ eᵢ = x`, compatible with the transition
maps. -/
theorem exists_compatible_splitting (hf : ∀ n, Function.Surjective (f n))
    (hsq : ∀ n, RingHom.ker (f n) ^ 2 = ⊥) (hg : ∀ n, Function.Surjective (g n))
    (hker : ∀ n x, g n x = 0 → x ∈ RingHom.ker (f n) • (⊤ : Submodule (R (n + 1)) (M (n + 1)))) :
    ∃ (m : ℕ) (e : Fin m → ∀ n, M n) (σ : ∀ n, M n →ₗ[R n] (Fin m → R n)),
      (∀ i n, g n (e i (n + 1)) = e i n) ∧
      (∀ n x, ∑ i, σ n x i • e i n = x) ∧
      (∀ n x i, f n (σ (n + 1) x i) = σ n (g n x) i) := by
  classical
  -- Generators of `M₀`, lifted up the tower.
  obtain ⟨m, y, hy⟩ := Module.Finite.exists_fin (R := R 0) (M := M 0)
  let lift : ∀ n, Fin m → M n := fun n =>
    Nat.rec (motive := fun n => Fin m → M n) y (fun n e i => (hg n (e i)).choose) n
  have hlift : ∀ n i, g n (lift (n + 1) i) = lift n i := fun n i =>
    (hg n (lift n i)).choose_spec
  -- The presentations `φₙ : Rₙ^m → Mₙ`.
  let φ : ∀ n, (Fin m → R n) →ₗ[R n] M n := fun n => Fintype.linearCombination (R n) (lift n)
  have hφ : ∀ n v, φ n v = ∑ i, v i • lift n i := fun n v =>
    Fintype.linearCombination_apply _ _ _
  have hgφ : ∀ n v, g n (φ (n + 1) v) = φ n (reduceCoords f m n v) := by
    intro n v
    simp only [hφ, map_sum, LinearMap.map_smulₛₗ, hlift, reduceCoords_apply]
  have hreduce : ∀ n (v : Fin m → R n), ∃ w, reduceCoords f m n w = v := fun n v => by
    choose w hw using fun i => hf n (v i)
    exact ⟨w, funext hw⟩
  have hspan : ∀ n, Function.Surjective (φ n) := by
    intro n
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    induction n with
    | zero => exact hy
    | succ n ih =>
      refine top_le_iff.mp
        (AlgebraicGeometry.C1590Private.le_of_le_sup_smul_of_sq_eq_bot (hsq n) (fun x _ => ?_))
      have hx : g n x ∈ Submodule.span (R n) (Set.range (lift n)) := ih ▸ Submodule.mem_top
      rw [← Fintype.range_linearCombination] at hx
      obtain ⟨v, hv⟩ := hx
      obtain ⟨w, hred⟩ := hreduce n v
      have hdiff : g n (x - φ (n + 1) w) = 0 := by
        rw [map_sub, hgφ, hred]
        exact sub_eq_zero.mpr (by simpa [φ] using hv.symm)
      have hmem := hker n _ hdiff
      have hφw : φ (n + 1) w ∈ Submodule.span (R (n + 1)) (Set.range (lift (n + 1))) := by
        rw [← Fintype.range_linearCombination]; exact ⟨w, rfl⟩
      have : x = φ (n + 1) w + (x - φ (n + 1) w) := (add_sub_cancel _ _).symm
      rw [this]
      exact Submodule.add_mem_sup hφw (by simpa using hmem)
  -- The kernels `Kₙ = Ker φₙ` and the surjectivity of their reductions.
  have hredK : ∀ n (w : Fin m → R n), φ n w = 0 →
      ∃ w' : Fin m → R (n + 1), φ (n + 1) w' = 0 ∧ reduceCoords f m n w' = w := by
    intro n w hw
    obtain ⟨w₀, hred₀⟩ := hreduce n w
    have hg0 : g n (φ (n + 1) w₀) = 0 := by rw [hgφ, hred₀, hw]
    have hmem := hker n _ hg0
    -- `Ker(fₙ) • Mₙ₊₁` is the image of `Ker(fₙ) • Rₙ₊₁^m`.
    have himage : RingHom.ker (f n) • (⊤ : Submodule (R (n + 1)) (M (n + 1))) ≤
        (RingHom.ker (f n) • (⊤ : Submodule (R (n + 1)) (Fin m → R (n + 1)))).map (φ (n + 1)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hspan (n + 1))]
    obtain ⟨w₁, hw₁, hφw₁⟩ := himage hmem
    have hw₁red : reduceCoords f m n w₁ = 0 := by
      refine Submodule.smul_induction_on hw₁ (fun r hr v _ => ?_) (fun a b ha hb => ?_)
      · funext i
        simp only [reduceCoords_apply, Pi.smul_apply, smul_eq_mul, map_mul,
          RingHom.mem_ker.mp hr, zero_mul, Pi.zero_apply]
      · rw [map_add, ha, hb, add_zero]
    refine ⟨w₀ - w₁, ?_, ?_⟩
    · rw [map_sub, hφw₁, sub_self]
    · rw [map_sub, hw₁red, sub_zero, hred₀]
  -- The splittings, built up the tower.
  have hstep : ∀ n (σn : {σ : M n →ₗ[R n] (Fin m → R n) // φ n ∘ₗ σ = LinearMap.id}),
      ∃ σ' : {σ : M (n + 1) →ₗ[R (n + 1)] (Fin m → R (n + 1)) //
        φ (n + 1) ∘ₗ σ = LinearMap.id},
        ∀ x, reduceCoords f m n (σ'.1 x) = σn.1 (g n x) := by
    intro n σn
    obtain ⟨σ₀, hσ₀⟩ := Module.projective_lifting_property (φ (n + 1)) LinearMap.id
      (hspan (n + 1))
    have h1 : ∀ x, φ (n + 1) (σ₀ x) = x := fun x => congrArg (fun F => F x) hσ₀
    let K : ∀ k, Submodule (R k) (Fin m → R k) := fun k => LinearMap.ker (φ k)
    let redK : K (n + 1) →ₛₗ[f n] K n :=
      { toFun := fun w => ⟨reduceCoords f m n w.1, by
          show φ n _ = 0
          rw [← hgφ, LinearMap.mem_ker.mp w.2, map_zero]⟩
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
        map_smul' := fun _ _ => Subtype.ext (LinearMap.map_smulₛₗ _ _ _) }
    have hredK' : Function.Surjective redK := by
      intro w
      obtain ⟨w', hw', hred⟩ := hredK n w.1 w.2
      exact ⟨⟨w', hw'⟩, Subtype.ext hred⟩
    let δ : M (n + 1) →ₛₗ[f n] K n :=
      { toFun := fun x => ⟨reduceCoords f m n (σ₀ x) - σn.1 (g n x), by
          show φ n _ = 0
          rw [map_sub, ← hgφ]
          have h2 : φ n (σn.1 (g n x)) = g n x := congrArg (fun F => F (g n x)) σn.2
          rw [h1, h2, sub_self]⟩
        map_add' := fun x y => Subtype.ext (by
          simp only [map_add, Submodule.coe_add]; abel)
        map_smul' := fun r x => Subtype.ext (by
          simp only [LinearMap.map_smulₛₗ, Submodule.coe_smul, smul_sub, RingHom.id_apply]) }
    obtain ⟨ε, hε⟩ := exists_semilinear_lift redK hredK' δ
    refine ⟨⟨σ₀ - (K (n + 1)).subtype ∘ₗ ε, ?_⟩, fun x => ?_⟩
    · apply LinearMap.ext
      intro x
      have h2 : φ (n + 1) (ε x : Fin m → R (n + 1)) = 0 := (ε x).2
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub, Submodule.subtype_apply,
        h1 x, h2, sub_zero, LinearMap.id_apply]
    · have h3 : reduceCoords f m n (ε x : Fin m → R (n + 1)) =
          reduceCoords f m n (σ₀ x) - σn.1 (g n x) := congrArg Subtype.val (hε x)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_sub, h3,
        sub_sub_cancel]
  choose step hstep' using hstep
  obtain ⟨σ0, hσ0⟩ := Module.projective_lifting_property (φ 0) LinearMap.id (hspan 0)
  let σseq : ∀ n, {σ : M n →ₗ[R n] (Fin m → R n) // φ n ∘ₗ σ = LinearMap.id} := fun n =>
    Nat.rec (motive := fun n => {σ : M n →ₗ[R n] (Fin m → R n) // φ n ∘ₗ σ = LinearMap.id})
      ⟨σ0, hσ0⟩ (fun n σn => step n σn) n
  refine ⟨m, fun i n => lift n i, fun n => (σseq n).1, fun i n => hlift n i, fun n x => ?_,
    fun n x i => ?_⟩
  · have := congrArg (fun F => F x) (σseq n).2
    simpa [hφ] using this
  · exact congrFun (hstep' n (σseq n) x) i

end Tower

end AlgebraicGeometry.C1590Private.TwoChartTower

end

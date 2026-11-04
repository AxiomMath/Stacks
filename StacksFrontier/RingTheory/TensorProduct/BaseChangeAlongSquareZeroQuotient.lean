module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Changing the base ring of a base change across a pair of quotients

Let `A ⟶ A'` be a ring map, let `p : A ↠ R` and `q : A' ↠ R'` be surjections with
`q ∘ (A ⟶ A') = (R ⟶ R') ∘ p`, and let `M` and `M'` be modules over `A` and `A'` whose actions
factor through `p` and through `q` respectively.  A map `M ⟶ M'` is then both `R`-semilinear and
`A`-semilinear, and this file shows that if it exhibits `M'` as the base change of `M` along
`R ⟶ R'` then it exhibits `M'` as the base change of `M` along `A ⟶ A'` — provided
`ker q ≤ (ker p)A'`.

This is the change of base ring the chart construction of [Stacks Project, Tag 05ZT] needs.  The
quasi-coherence of the square-zero ideal `ℐ` of a square-zero extension `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0`
describes `ℐ(U)` as a base change of `ℐ(V)` along `𝒪_X(V) ⟶ 𝒪_X(U)`, whereas
`Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange` asks for a base change along `𝒜(V) ⟶ 𝒜(U)`; the
action of `𝒜` on `ℐ` factors through `𝒪_X` exactly because `ℐ` has square zero, which is the
hypothesis `hpM` below.

## Main results

* `Module.BaseChange.annihilator_map_ker_le`: **the extension of `ker p` to `A'` annihilates
  `A' ⊗[A] M`** when the action of `A` on `M` factors through `p`.
* `Module.BaseChange.bijective_liftBaseChange_of_ker_le_map_ker`: **a base change along
  `R ⟶ R'` is a base change along `A ⟶ A'`.**

## Implementation notes

The comparison is taken twice, once as an `R`-linear map and once as an `A`-linear one, together
with the identity saying that they are the same function; this is the convention of the
base-change API of this development, and here it is also what lets the hypothesis and the
conclusion speak of the two different semilinearities of one map.

The proof is an isomorphism `A' ⊗[A] M ≅ R' ⊗[R] M` under which the two comparisons correspond.
Both directions of it are a `LinearMap.liftBaseChange`, and the one going out of `R' ⊗[R] M`
needs an `R'`-action on `A' ⊗[A] M`: that is where `ker q ≤ (ker p)A'` is spent, through
`Module.BaseChange.annihilator_map_ker_le`, and it is built by
`Function.Surjective.moduleLeft` along `q` with a set-theoretic section of `q` as the action.

The hypothesis `ker q ≤ (ker p)A'` is the one part of the statement that is not formal: the
reverse inclusion is automatic from the commuting square, whereas this one holds, for the
sections of a square-zero extension over two affine charts, only because the comparison on the
ideals is already known to be surjective.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YT](https://stacks.math.columbia.edu/tag/05YT)
-/

@[expose] public section

open TensorProduct

namespace Module.BaseChange

variable {A A' R R' M M' : Type*}
    [CommRing A] [CommRing A'] [CommRing R] [CommRing R']
    [Algebra A A'] [Algebra R R']
    [AddCommGroup M] [Module A M] [Module R M]
    [AddCommGroup M'] [Module A M'] [Module A' M'] [Module R M'] [Module R' M']
    [IsScalarTower A A' M'] [IsScalarTower R R' M']

/-- **The extension of `ker p` to `A'` annihilates `A' ⊗[A] M`**, when the action of `A` on `M`
factors through the surjection `p`.

An element of the extension is a combination of elements `a • 1` with `p a = 0`, and such an
element carries `b ⊗ₜ x` to `b ⊗ₜ (a • x) = b ⊗ₜ (p a • x) = 0`. -/
theorem annihilator_map_ker_le (p : A →+* R) (hpM : ∀ (a : A) (x : M), a • x = p a • x) :
    Ideal.map (algebraMap A A') (RingHom.ker p) ≤
      Module.annihilator A' (A' ⊗[A] M) := by
  refine Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_comap.mpr ?_
  refine Module.mem_annihilator.mpr fun z => ?_
  have hax : ∀ x : M, a • x = 0 := fun x => by
    rw [hpM a x, RingHom.mem_ker.mp ha, zero_smul]
  induction z with
  | zero => exact smul_zero _
  | tmul b x =>
    rw [show algebraMap A A' a • (b ⊗ₜ[A] x) = (a • b) ⊗ₜ[A] x from by
        rw [Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul],
      TensorProduct.smul_tmul, hax x, TensorProduct.tmul_zero]
  | add z z' hz hz' => rw [smul_add, hz, hz', add_zero]

/-- **A base change along `R ⟶ R'` is a base change along `A ⟶ A'`.**

Let `p : A ↠ R` and `q : A' ↠ R'` be surjections compatible with a ring map `A ⟶ A'` and the
induced `R ⟶ R'`, let the action of `A` on `M` factor through `p` and the action of `A'` on `M'`
factor through `q`, and assume `ker q ≤ (ker p)A'`.  If a map `M ⟶ M'`, read `R`-linearly,
exhibits `M'` as the base change of `M` along `R ⟶ R'`, then the same map, read `A`-linearly,
exhibits `M'` as the base change of `M` along `A ⟶ A'`.

The hypothesis supplies an `R'`-module structure on `A' ⊗[A] M`
(`Module.BaseChange.annihilator_map_ker_le`), and `A' ⊗[A] M ≅ R' ⊗[R] M` follows: both
directions send `1 ⊗ₜ x` to `1 ⊗ₜ x`, and the two base-change comparisons correspond under it. -/
theorem bijective_liftBaseChange_of_ker_le_map_ker
    (p : A →+* R) (q : A' →+* R')
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hcomm : ∀ a : A, q (algebraMap A A' a) = algebraMap R R' (p a))
    (hpM : ∀ (a : A) (x : M), a • x = p a • x)
    (hqM : ∀ (b : A') (y : M'), b • y = q b • y)
    (hker : RingHom.ker q ≤ Ideal.map (algebraMap A A') (RingHom.ker p))
    (r : M →ₗ[R] M') (g : M →ₗ[A] M') (hrg : ∀ x, r x = g x)
    (hbc : Function.Bijective (r.liftBaseChange R')) :
    Function.Bijective (g.liftBaseChange A') := by
  classical
  -- The kernel of `q` annihilates `A' ⊗[A] M`, so elements of `A'` with the same image act alike.
  have hann : ∀ b : A', q b = 0 → ∀ z : A' ⊗[A] M, b • z = 0 := fun b hb =>
    Module.mem_annihilator.mp (annihilator_map_ker_le p hpM (hker (RingHom.mem_ker.mpr hb)))
  have hagree : ∀ b b' : A', q b = q b' → ∀ z : A' ⊗[A] M, b • z = b' • z := by
    intro b b' hbb' z
    have h0 : (b - b') • z = 0 := hann _ (by rw [map_sub, hbb', sub_self]) z
    rwa [sub_smul, sub_eq_zero] at h0
  -- An `R'`-action on `A' ⊗[A] M`, through a set-theoretic section of `q`.
  let sm : SMul R' (A' ⊗[A] M) := ⟨fun c z => Function.surjInv hq c • z⟩
  have hsm : ∀ (b : A') (z : A' ⊗[A] M), q b • z = b • z := fun b z =>
    hagree _ _ (Function.surjInv_eq hq (q b)) z
  let mR' : Module R' (A' ⊗[A] M) := Function.Surjective.moduleLeft q hq hsm
  let mR : Module R (A' ⊗[A] M) := Module.compHom _ (algebraMap R R' : R →+* R')
  have twR : IsScalarTower R R' (A' ⊗[A] M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- An `A'`-action, hence an `A`-action, on `R' ⊗[R] M`, through `q`.
  let mA' : Module A' (R' ⊗[R] M) := Module.compHom _ q
  let mA : Module A (R' ⊗[R] M) := Module.compHom _ (algebraMap A A' : A →+* A')
  have twA : IsScalarTower A A' (R' ⊗[R] M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- The two unit maps.
  have hmk : ∀ (c : R) (x : M), (1 : A') ⊗ₜ[A] (c • x) = c • ((1 : A') ⊗ₜ[A] x) := by
    intro c x
    obtain ⟨a, rfl⟩ := hp c
    rw [← hpM a x,
      show p a • ((1 : A') ⊗ₜ[A] x) = algebraMap R R' (p a) • ((1 : A') ⊗ₜ[A] x) from rfl,
      ← hcomm a, hsm,
      show algebraMap A A' a • ((1 : A') ⊗ₜ[A] x) = (a • (1 : A')) ⊗ₜ[A] x from by
        rw [Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul],
      TensorProduct.smul_tmul]
  let mk : M →ₗ[R] A' ⊗[A] M :=
    { toFun := fun x => (1 : A') ⊗ₜ[A] x
      map_add' := fun x y => TensorProduct.tmul_add _ x y
      map_smul' := fun c x => hmk c x }
  let mk' : M →ₗ[A] R' ⊗[R] M :=
    { toFun := fun x => (1 : R') ⊗ₜ[R] x
      map_add' := fun x y => TensorProduct.tmul_add _ x y
      map_smul' := fun a x => by
        show (1 : R') ⊗ₜ[R] (a • x) = a • ((1 : R') ⊗ₜ[R] x)
        rw [hpM a x,
          show a • ((1 : R') ⊗ₜ[R] x) = q (algebraMap A A' a) • ((1 : R') ⊗ₜ[R] x) from rfl,
          hcomm a, show algebraMap R R' (p a) • ((1 : R') ⊗ₜ[R] x) =
            (p a • (1 : R')) ⊗ₜ[R] x from by
              rw [Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul],
          TensorProduct.smul_tmul] }
  let θ : A' ⊗[A] M →ₗ[A'] R' ⊗[R] M := mk'.liftBaseChange A'
  let ψ : R' ⊗[R] M →ₗ[R'] A' ⊗[A] M := mk.liftBaseChange R'
  have hθ : ∀ (b : A') (x : M), θ (b ⊗ₜ[A] x) = q b ⊗ₜ[R] x := by
    intro b x
    rw [show θ (b ⊗ₜ[A] x) = b • mk' x from LinearMap.liftBaseChange_tmul _ _ _ _]
    show q b • ((1 : R') ⊗ₜ[R] x) = q b ⊗ₜ[R] x
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hψ : ∀ (c : R') (x : M), ψ (c ⊗ₜ[R] x) = Function.surjInv hq c ⊗ₜ[A] x := by
    intro c x
    rw [show ψ (c ⊗ₜ[R] x) = c • mk x from LinearMap.liftBaseChange_tmul _ _ _ _]
    show Function.surjInv hq c • ((1 : A') ⊗ₜ[A] x) = Function.surjInv hq c ⊗ₜ[A] x
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hψθ : ∀ z : A' ⊗[A] M, ψ (θ z) = z := by
    intro z
    induction z with
    | zero => rw [map_zero, map_zero]
    | tmul b x =>
      rw [hθ, hψ, show Function.surjInv hq (q b) ⊗ₜ[A] x =
          Function.surjInv hq (q b) • ((1 : A') ⊗ₜ[A] x) from by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        hagree _ _ (Function.surjInv_eq hq (q b)) ((1 : A') ⊗ₜ[A] x),
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  have hθψ : ∀ w : R' ⊗[R] M, θ (ψ w) = w := by
    intro w
    induction w with
    | zero => rw [map_zero, map_zero]
    | tmul c x => rw [hψ, hθ, Function.surjInv_eq hq c]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  -- The two comparisons correspond under that isomorphism.
  have hcomp : ∀ z : A' ⊗[A] M,
      g.liftBaseChange A' z = r.liftBaseChange R' (θ z) := by
    intro z
    induction z with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul b x =>
      rw [LinearMap.liftBaseChange_tmul, hθ, LinearMap.liftBaseChange_tmul, hrg, hqM b (g x)]
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']
  have hθbij : Function.Bijective θ :=
    ⟨fun z z' hzz' => by rw [← hψθ z, ← hψθ z', hzz'], fun w => ⟨ψ w, hθψ w⟩⟩
  have hfun : (g.liftBaseChange A' : A' ⊗[A] M → M') =
      (r.liftBaseChange R' : R' ⊗[R] M → M') ∘ (θ : A' ⊗[A] M → R' ⊗[R] M) := funext hcomp
  rw [hfun]
  exact hbc.comp hθbij

end Module.BaseChange

end

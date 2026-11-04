module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChange
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Exterior powers under scalar extension, and the Cartan remainder

The first, purely algebraic, step towards the homotopy inverse up to `a` of the base change map
of de Rham complexes (Stacks, Tag 07Q7): the identification `S ⊗_R ⋀^n W ≃ ⋀^n (S ⊗_R W)` on
pure wedges, factoring a linear map through an injective one whose range contains its image,
and the Cartan remainder `s - d h - h d` of a degreewise homotopy `h`, with the criterion that an
injective chain map admits a reverse chain map as soon as the Cartan remainder factors through
it. The remaining parts are imported by
`StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeHomotopyInverse`.
-/

@[expose] public section

open scoped TensorProduct DirectSum


universe u u' w

namespace Crystalline

open Stacks.DeRham.DifferentialDescent


section ExteriorScalarExtension

variable (R S W : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup W] [Module R W]

noncomputable def exteriorScalarInclusion (n : ℕ) :
    (⋀[R]^n W) →ₗ[R] (⋀[S]^n (S ⊗[R] W)) :=
  exteriorPower.alternatingMapLinearEquiv
    (({ toMultilinearMap := (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R
        map_eq_zero_of_eq' := fun v _i _j hv hij =>
          (exteriorPower.ιMulti S n).map_eq_zero_of_eq v hv hij } :
        (S ⊗[R] W) [⋀^Fin n]→ₗ[R] (⋀[S]^n (S ⊗[R] W))).compLinearMap
      (TensorProduct.mk R S W 1))

private theorem exteriorScalarInclusion_ιMulti (n : ℕ) (v : Fin n → W) :
    exteriorScalarInclusion R S W n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) := by
  simp [exteriorScalarInclusion]
  rfl

theorem exteriorScalarInclusion_isBaseChange (n : ℕ) :
    IsBaseChange S (exteriorScalarInclusion R S W n) :=
  DeRhamBaseChange.isBaseChange_exteriorPower (TensorProduct.isBaseChange R W S)
    _ (exteriorScalarInclusion_ιMulti R S W n)

noncomputable def exteriorScalarEquiv (n : ℕ) :
    S ⊗[R] (⋀[R]^n W) ≃ₗ[S] (⋀[S]^n (S ⊗[R] W)) :=
  (exteriorScalarInclusion_isBaseChange R S W n).equiv

theorem exteriorScalarEquiv_tmul_ιMulti (n : ℕ) (s : S) (v : Fin n → W) :
    exteriorScalarEquiv R S W n (s ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      s • exteriorPower.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) := by
  simp [exteriorScalarEquiv, exteriorScalarInclusion_ιMulti]

end ExteriorScalarExtension

/-- Factor a linear map through an injective linear map when its image is known to lie in the
range.  This is the bridge used below to turn the Cartan homotopy identity into a map with
values in the base de Rham complex. -/
private noncomputable def factorThroughRange
    {R : Type*} [Semiring R]
    {P M N : Type*} [AddCommMonoid P] [Module R P]
      [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (c : M →ₗ[R] N) (g : P →ₗ[R] N) (hc : Function.Injective c)
    (hg : ∀ x, g x ∈ LinearMap.range c) : P →ₗ[R] M :=
  (LinearEquiv.ofInjective c hc).symm.toLinearMap.comp
    (LinearMap.codRestrict (LinearMap.range c) g hg)

/-- The factor map recovers the original map after composition with the injection. -/
private theorem comp_factorThroughRange
    {R : Type*} [Semiring R]
    {P M N : Type*} [AddCommMonoid P] [Module R P]
      [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (c : M →ₗ[R] N) (g : P →ₗ[R] N) (hc : Function.Injective c)
    (hg : ∀ x, g x ∈ LinearMap.range c) :
    c.comp (factorThroughRange c g hc hg) = g := by
  ext x
  show ((LinearEquiv.ofInjective c hc)
      ((LinearEquiv.ofInjective c hc).symm ⟨g x, hg x⟩)).val = g x
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective c hc).apply_symm_apply ⟨g x, hg x⟩)

/-- Subtract the two homotopy terms from a degreewise endomorphism. -/
def cartanRemainder
    {R : Type*} [CommSemiring R]
    (Y : ℕ → Type*) [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
    (dY : ∀ n, Y n →ₗ[R] Y (n + 1))
    (h : ∀ n, Y (n + 1) →ₗ[R] Y n) (s : ∀ n, Y n →ₗ[R] Y n) :
    ∀ n, Y n →ₗ[R] Y n
  | 0 => s 0 - (h 0).comp (dY 0)
  | n + 1 => s (n + 1) - (dY n).comp (h n) - (h (n + 1)).comp (dY (n + 1))

private theorem cartanRemainder_commutes_differential
    {R : Type*} [CommSemiring R]
    (Y : ℕ → Type*) [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
    (dY : ∀ n, Y n →ₗ[R] Y (n + 1)) (h : ∀ n, Y (n + 1) →ₗ[R] Y n)
    (s : ∀ n, Y n →ₗ[R] Y n)
    (hYzero : ∀ n, (dY (n + 1)).comp (dY n) = 0)
    (hs : ∀ n x, dY n (s n x) = s (n + 1) (dY n x)) (n : ℕ) :
    (dY n).comp (cartanRemainder Y dY h s n) =
      (cartanRemainder Y dY h s (n + 1)).comp (dY n) := by
  apply LinearMap.ext
  intro y
  cases n with
  | zero =>
    have hz := LinearMap.congr_fun (hYzero 0) y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    simp [cartanRemainder, hs, hz]
  | succ n =>
    have hz₁ := LinearMap.congr_fun (hYzero n) (h n y)
    have hz₂ := LinearMap.congr_fun (hYzero (n + 1)) y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz₁ hz₂
    simp [cartanRemainder, hs, hz₁, hz₂]

/-- **The Cartan remainder commutes with an endomorphism that the data commutes with.**  The
differential need only commute with `σ` up to a term `W`, provided the homotopy anticommutes
with `W` — which for the integrating homotopy of Lemma 07Q7 and the action of a scalar of the
base is the Leibniz rule together with the anticommutativity of the wedge product. -/
private theorem cartanRemainder_comm
    {R : Type*} [CommSemiring R]
    (Y : ℕ → Type*) [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
    (dY : ∀ n, Y n →ₗ[R] Y (n + 1))
    (h : ∀ n, Y (n + 1) →ₗ[R] Y n) (s : ∀ n, Y n →ₗ[R] Y n)
    (sigma : ∀ n, Y n →ₗ[R] Y n) (W : ∀ n, Y n → Y (n + 1))
    (hs : ∀ n y, s n (sigma n y) = sigma n (s n y))
    (hd : ∀ n y, dY n (sigma n y) = sigma (n + 1) (dY n y) + W n y)
    (hh : ∀ n y, h n (sigma (n + 1) y) = sigma n (h n y))
    (hW0 : ∀ y, h 0 (W 0 y) = 0)
    (hW : ∀ n y, h (n + 1) (W (n + 1) y) + W n (h n y) = 0)
    (n : ℕ) (y : Y n) :
    cartanRemainder Y dY h s n (sigma n y) =
      sigma n (cartanRemainder Y dY h s n y) := by
  cases n with
  | zero =>
    show s 0 (sigma 0 y) - h 0 (dY 0 (sigma 0 y)) = sigma 0 (s 0 y - h 0 (dY 0 y))
    rw [hs, hd, map_add, hh, hW0, add_zero, map_sub]
  | succ n =>
    show s (n + 1) (sigma (n + 1) y) - dY n (h n (sigma (n + 1) y)) -
        h (n + 1) (dY (n + 1) (sigma (n + 1) y)) =
      sigma (n + 1) (s (n + 1) y - dY n (h n y) - h (n + 1) (dY (n + 1) y))
    have hz : h (n + 1) (W (n + 1) y) = -W n (h n y) :=
      eq_neg_of_add_eq_zero_left (hW n y)
    rw [hs, hh, hd n (h n y), hd (n + 1) y, map_add, hh (n + 1) (dY (n + 1) y), hz,
      map_sub, map_sub]
    abel

/-- An injective chain map admits a reverse chain map when the Cartan remainder factors
through it. -/
theorem reverseChainMap_of_cartanRemainder
    {R : Type*} [CommSemiring R] {I : Type*}
    (X Y : ℕ → Type*) [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
      [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
    (dX : ∀ n, X n →ₗ[R] X (n + 1)) (dY : ∀ n, Y n →ₗ[R] Y (n + 1))
    (c : ∀ n, X n →ₗ[R] Y n) (h : ∀ n, Y (n + 1) →ₗ[R] Y n)
    (s : ∀ n, Y n →ₗ[R] Y n) (t : ∀ n, X n →ₗ[R] X n)
    (sigma : I → ∀ n, Y n →ₗ[R] Y n) (tau : I → ∀ n, X n →ₗ[R] X n)
    (W : I → ∀ n, Y n → Y (n + 1))
    (hYzero : ∀ n, (dY (n + 1)).comp (dY n) = 0)
    (hs : ∀ n x, dY n (s n x) = s (n + 1) (dY n x))
    (hc : ∀ n x, dY n (c n x) = c (n + 1) (dX n x))
    (hsc : ∀ n x, s n (c n x) = c n (t n x))
    (hinj : ∀ n, Function.Injective (c n))
    (hrange : ∀ n y, cartanRemainder Y dY h s n y ∈ LinearMap.range (c n))
    (hzero : ∀ n x, h n (c (n + 1) x) = 0)
    (hsigmas : ∀ i n y, s n (sigma i n y) = sigma i n (s n y))
    (hsigmad : ∀ i n y, dY n (sigma i n y) = sigma i (n + 1) (dY n y) + W i n y)
    (hsigmah : ∀ i n y, h n (sigma i (n + 1) y) = sigma i n (h n y))
    (hsigmaW0 : ∀ i y, h 0 (W i 0 y) = 0)
    (hsigmaW : ∀ i n y, h (n + 1) (W i (n + 1) y) + W i n (h n y) = 0)
    (hct : ∀ i n x, c n (tau i n x) = sigma i n (c n x)) :
    ∃ e : ∀ n, Y n →ₗ[R] X n,
      (∀ n y, dX n (e n y) = e (n + 1) (dY n y)) ∧
      (∀ n y, c n (e n y) = cartanRemainder Y dY h s n y) ∧
      (∀ n x, e n (c n x) = t n x) ∧
      (∀ i n y, e n (sigma i n y) = tau i n (e n y)) := by
  let e : ∀ n, Y n →ₗ[R] X n := fun n =>
    factorThroughRange (c n) (cartanRemainder Y dY h s n) (hinj n) (hrange n)
  have he : ∀ n y, c n (e n y) = cartanRemainder Y dY h s n y := fun n y =>
    LinearMap.congr_fun
      (comp_factorThroughRange (c n) (cartanRemainder Y dY h s n) (hinj n) (hrange n)) y
  refine ⟨e, ?_, he, ?_, ?_⟩
  · intro n y
    apply hinj (n + 1)
    rw [← hc, he, he]
    exact LinearMap.congr_fun (cartanRemainder_commutes_differential Y dY h s hYzero hs n) y
  · intro n x
    apply hinj n
    rw [he]
    cases n <;> simp [cartanRemainder, hc, hzero, hsc]
  · intro i n y
    apply hinj n
    rw [he n (sigma i n y), hct i n (e n y), he n y]
    exact cartanRemainder_comm Y dY h s (sigma i) (W i) (hsigmas i) (hsigmad i)
      (hsigmah i) (hsigmaW0 i) (hsigmaW i) n y

end Crystalline

end

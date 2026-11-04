module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Homotopy equivalent two term complexes have stably isomorphic terms

Fix a ring `R`. All modules below are `R`-modules and all maps are `R`-module
homomorphisms.

Stacks Tag 00S3 (Lemma 10.134.14): given two two-term complexes of `R`-modules that are
homotopy equivalent, i.e. between which there are mutually homotopy-inverse morphisms,
the modules `A_1 ⊕ B_0` and `B_1 ⊕ A_0` are isomorphic as `R`-modules.

## Main definitions

* `TwoComplex R`: a *two term complex* is a pair of `R`-modules `A_1`, `A_0` together with
  an `R`-module homomorphism `d_A : A_1 → A_0`. Here `A_1` sits in degree `1` and `A_0` in
  degree `0`.
* `ComplexHom`: a *morphism of complexes* `φ : A_• → B_•` is a pair of `R`-module
  homomorphisms `φ_1 : A_1 → B_1`, `φ_0 : A_0 → B_0` such that `d_B ∘ φ_1 = φ_0 ∘ d_A`.
  Composition is componentwise and the identity is `(id, id)`.
* `Homotopic`: two morphisms `f, g : A_• → B_•` are *homotopic* if there is an `R`-module
  homomorphism `h : A_0 → B_1` with `f_1 - g_1 = h ∘ d_A` and `f_0 - g_0 = d_B ∘ h`.

## Main results

* `main_theorem_00s3`: if there exist morphisms `φ : A_• → B_•` and `ψ : B_• → A_•` such
  that `φ ∘ ψ` is homotopic to `id_{B_•}` and `ψ ∘ φ` is homotopic to `id_{A_•}`, then
  there is an isomorphism of `R`-modules `A_1 ⊕ B_0 ≅ B_1 ⊕ A_0`.

## Proof outline

Writing maps as `2×2` matrices, one verifies an upper-triangular factorization with
identity diagonal, exhibiting `Φ = (φ_1, -h'; d_A, ψ_0) : A_1 ⊕ B_0 → B_1 ⊕ A_0` and
`Ψ = (ψ_1, h; -d_B, φ_0) : B_1 ⊕ A_0 → A_1 ⊕ B_0` as mutually inverse isomorphisms.

## Implementation notes

* The conclusion is an isomorphism of `R`-modules only; the direct sums are not equipped
  with any complex structure.
* The direct sum `A_1 ⊕ B_0` is modelled by the product type `A_1 × B_0`, which carries
  the canonical `R`-module structure on a product of modules.
* "There is an isomorphism" is rendered as `Nonempty` of the type of `R`-linear
  equivalences `(A_1 × B_0) ≃ₗ[R] (B_1 × A_0)`.
-/

@[expose] public section

universe u

/-- A *two term complex* `A_1 →[d_A] A_0` of `R`-modules: a pair of `R`-modules
with an `R`-module homomorphism between them. `A_1` sits in degree `1`, `A_0` in
degree `0`. -/
structure TwoComplex (R : Type u) [Ring R] where
  /-- The module in degree `1`. -/
  A1 : Type u
  /-- The module in degree `0`. -/
  A0 : Type u
  [acg1 : AddCommGroup A1]
  [acg0 : AddCommGroup A0]
  [mod1 : Module R A1]
  [mod0 : Module R A0]
  /-- The differential `d_A : A_1 → A_0`. -/
  d : A1 →ₗ[R] A0

attribute [instance] TwoComplex.acg1 TwoComplex.acg0 TwoComplex.mod1 TwoComplex.mod0

variable {R : Type u} [Ring R]

/-- A *morphism of two term complexes* `φ : A_• → B_•`: a pair of `R`-module
homomorphisms `φ_1 : A_1 → B_1`, `φ_0 : A_0 → B_0` making the square commute, i.e.
`d_B ∘ φ_1 = φ_0 ∘ d_A`. -/
structure ComplexHom (A B : TwoComplex R) where
  /-- The degree `1` component `φ_1 : A_1 → B_1`. -/
  φ1 : A.A1 →ₗ[R] B.A1
  /-- The degree `0` component `φ_0 : A_0 → B_0`. -/
  φ0 : A.A0 →ₗ[R] B.A0
  /-- The square commutes: `d_B ∘ φ_1 = φ_0 ∘ d_A`. -/
  comm : B.d ∘ₗ φ1 = φ0 ∘ₗ A.d

/-- Composition of morphisms of complexes, performed componentwise:
`(ψ ∘ φ)_i = ψ_i ∘ φ_i`. -/
def ComplexHom.comp {A B C : TwoComplex R} (ψ : ComplexHom B C) (φ : ComplexHom A B) :
    ComplexHom A C where
  φ1 := ψ.φ1 ∘ₗ φ.φ1
  φ0 := ψ.φ0 ∘ₗ φ.φ0
  comm := by
    rw [← LinearMap.comp_assoc, ψ.comm, LinearMap.comp_assoc, φ.comm, ← LinearMap.comp_assoc]

/-- The identity morphism `id_{A_•} = (id_{A_1}, id_{A_0})`. -/
def ComplexHom.id (A : TwoComplex R) : ComplexHom A A where
  φ1 := LinearMap.id
  φ0 := LinearMap.id
  comm := by simp

/-- Two morphisms `f, g : A_• → B_•` are *homotopic* if there is an `R`-module
homomorphism `h : A_0 → B_1` (a *homotopy*) with `f_1 - g_1 = h ∘ d_A` and
`f_0 - g_0 = d_B ∘ h`. -/
def Homotopic {A B : TwoComplex R} (f g : ComplexHom A B) : Prop :=
  ∃ h : A.A0 →ₗ[R] B.A1,
    f.φ1 - g.φ1 = h ∘ₗ A.d ∧ f.φ0 - g.φ0 = B.d ∘ₗ h

/-- The shear `(m, n) ↦ (m + X n, n)`, a linear automorphism of `M × N`. -/
private def shearEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (X : N →ₗ[R] M) : (M × N) ≃ₗ[R] (M × N) :=
  { toFun := fun p => (p.fst + X p.snd, p.snd)
    invFun := fun p => (p.fst - X p.snd, p.snd)
    map_add' := by intro p q; simp [Prod.ext_iff]; abel
    map_smul' := by intro c p; simp []
    left_inv := by intro p; simp
    right_inv := by intro p; simp }

/-- **Stacks Tag 00S3 (Lemma 10.134.14).** Let `R` be a ring and let
`A_• : A_1 →[d_A] A_0` and `B_• : B_1 →[d_B] B_0` be two term complexes of
`R`-modules. Suppose there are morphisms of complexes `φ : A_• → B_•` and
`ψ : B_• → A_•` such that `φ ∘ ψ` is homotopic to `id_{B_•}` and `ψ ∘ φ` is
homotopic to `id_{A_•}`. Then there is an isomorphism of `R`-modules
`A_1 ⊕ B_0 ≅ B_1 ⊕ A_0`. -/
@[stacks 00S3]
theorem main_theorem_00s3 (A B : TwoComplex R)
    (φ : ComplexHom A B) (ψ : ComplexHom B A)
    (hB : Homotopic (φ.comp ψ) (ComplexHom.id B))
    (hA : Homotopic (ψ.comp φ) (ComplexHom.id A)) :
    Nonempty ((A.A1 × B.A0) ≃ₗ[R] (B.A1 × A.A0)) := by
  -- Extract homotopy data.
  obtain ⟨h, hB1, hB0⟩ := hB
  obtain ⟨h', hA1, hA0⟩ := hA
  -- Pointwise versions of the homotopy identities and of commutativity.
  have eB1 : ∀ x : B.A1, φ.φ1 (ψ.φ1 x) = x + h (B.d x) := fun x =>
    sub_eq_iff_eq_add'.1 (LinearMap.congr_fun hB1 x)
  have eB0 : ∀ y : B.A0, φ.φ0 (ψ.φ0 y) = y + B.d (h y) := fun y =>
    sub_eq_iff_eq_add'.1 (LinearMap.congr_fun hB0 y)
  have eA1 : ∀ x : A.A1, ψ.φ1 (φ.φ1 x) = x + h' (A.d x) := fun x =>
    sub_eq_iff_eq_add'.1 (LinearMap.congr_fun hA1 x)
  have eA0 : ∀ y : A.A0, ψ.φ0 (φ.φ0 y) = y + A.d (h' y) := fun y =>
    sub_eq_iff_eq_add'.1 (LinearMap.congr_fun hA0 y)
  have cφ : ∀ a : A.A1, B.d (φ.φ1 a) = φ.φ0 (A.d a) := LinearMap.congr_fun φ.comm
  have cψ : ∀ b : B.A1, A.d (ψ.φ1 b) = ψ.φ0 (B.d b) := LinearMap.congr_fun ψ.comm
  -- The two block maps Φ and Ψ.
  set Φ : (A.A1 × B.A0) →ₗ[R] (B.A1 × A.A0) :=
    LinearMap.prod
      (LinearMap.coprod φ.φ1 (-h))
      (LinearMap.coprod (-A.d) ψ.φ0) with hΦ
  set Ψ : (B.A1 × A.A0) →ₗ[R] (A.A1 × B.A0) :=
    LinearMap.prod
      (LinearMap.coprod ψ.φ1 h')
      (LinearMap.coprod B.d φ.φ0) with hΨ
  -- The "cross" maps.
  set X : B.A0 →ₗ[R] A.A1 := h' ∘ₗ ψ.φ0 - ψ.φ1 ∘ₗ h with hX
  set Y : A.A0 →ₗ[R] B.A1 := φ.φ1 ∘ₗ h' - h ∘ₗ φ.φ0 with hY
  -- Pointwise descriptions of Φ and Ψ.
  have Φapp : ∀ p : A.A1 × B.A0,
      Φ p = (φ.φ1 p.fst - h p.snd, -A.d p.fst + ψ.φ0 p.snd) := by
    intro p
    simp [hΦ, LinearMap.prod_apply, LinearMap.coprod_apply, sub_eq_add_neg]
  have Ψapp : ∀ p : B.A1 × A.A0,
      Ψ p = (ψ.φ1 p.fst + h' p.snd, B.d p.fst + φ.φ0 p.snd) := by
    intro p
    simp [hΨ, LinearMap.prod_apply, LinearMap.coprod_apply]
  -- Ψ ∘ Φ and Φ ∘ Ψ are the shears by X and Y.
  have hUeq : Ψ ∘ₗ Φ = (shearEquiv X : (A.A1 × B.A0) →ₗ[R] (A.A1 × B.A0)) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_
    · show (Ψ (Φ p)).fst = p.fst + X p.snd
      rw [Φapp, Ψapp]
      simp only [hX, LinearMap.sub_apply, LinearMap.comp_apply, map_add, map_sub, map_neg]
      rw [eA1]; abel
    · show (Ψ (Φ p)).snd = p.snd
      rw [Φapp, Ψapp]
      simp only [map_add, map_sub, map_neg]
      rw [cφ, eB0]; abel
  have hVeq : Φ ∘ₗ Ψ = (shearEquiv Y : (B.A1 × A.A0) →ₗ[R] (B.A1 × A.A0)) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_
    · show (Φ (Ψ p)).fst = p.fst + Y p.snd
      rw [Ψapp, Φapp]
      simp only [hY, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
      rw [eB1]; abel
    · show (Φ (Ψ p)).snd = p.snd
      rw [Ψapp, Φapp]
      simp only [map_add]
      rw [cψ, eA0]; abel
  -- Φ is bijective, having a left and a right inverse up to shears.
  have hinj : Function.Injective Φ := Function.Injective.of_comp (f := Ψ)
    (by rw [← LinearMap.coe_comp, hUeq]; exact (shearEquiv X).injective)
  have hsurj : Function.Surjective Φ := Function.Surjective.of_comp (g := Ψ)
    (by rw [← LinearMap.coe_comp, hVeq]; exact (shearEquiv Y).surjective)
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩

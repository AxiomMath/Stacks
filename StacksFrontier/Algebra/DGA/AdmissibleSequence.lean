module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.GradedAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace DifferentialGradedModule.AdmissibleSquare

/-
# Problem Description

This is Stacks project Tag 09JV (Lemma 22.7.3) from the chapter on Differential
Graded Algebra.

Fix a (commutative) ring `R` and a differential graded algebra `(A, d_A)` over
`R`: a `ℤ`-graded `R`-algebra `A = ⨁ A^n` together with an `R`-linear
differential `d_A` of degree `+1` satisfying `d_A ∘ d_A = 0` and the Leibniz rule
`d_A (a b) = d_A(a) b + (-1)^n a d_A(b)` for `a ∈ A^n`, `b ∈ A`.

We work with *right* modules (the Stacks project default for this chapter).

## Main Definitions

* A (right) differential graded `A`-module `M`: a right `A`-module with a
  `ℤ`-grading and an `R`-linear differential `d_M` of degree `+1` with
  `d_M ∘ d_M = 0`, satisfying the degree condition `M^n · A^m ⊆ M^{n+m}` and the
  Leibniz rule `d_M (m a) = d_M(m) a + (-1)^n m d_A(a)` for `m ∈ M^n`.
* A homomorphism of differential graded `A`-modules: a degree-`0`, right
  `A`-linear map commuting with the differentials.
* A graded `A`-module map: a right `A`-linear map compatible with the gradings
  only (not necessarily with the differentials). We carry a degree shift `k`.
* Homotopy between homomorphisms `f, g : M → N`: a degree `-1` graded `A`-module
  map `h : M → N` with `f - g = d_N ∘ h + h ∘ d_M`.
* Admissible monomorphism / admissible epimorphism: a homomorphism admitting a
  graded `A`-module left (resp. right) inverse.

## Main Statements

Given a square that commutes up to homotopy
```
K --f--> L
|a       |b
v        v
M --g--> N
```
i.e. `b ∘ f` and `g ∘ a` are homotopic:

* Statement 1: if `f` is an admissible monomorphism, then `b` is homotopic to a
  homomorphism `b' : L → N` with `b' ∘ f = g ∘ a`.
* Statement 2: if `g` is an admissible epimorphism, then `a` is homotopic to a
  homomorphism `a' : K → M` with `g ∘ a' = b ∘ f`.

The conclusion only asserts *existence* of `b'` (resp. `a'`).
-/

-- Note on encoding:
-- * The grading `A = ⨁ A^n` (resp. `M = ⨁ M^n`) is encoded as a family of
--   `R`-submodules together with a `DirectSum.Decomposition` instance, which
--   precisely asserts that the family realizes `A` (resp. `M`) as the internal
--   direct sum `⨁_n A^n` (resp. `⨁_n M^n`).  For the algebra this is bundled
--   into `GradedAlgebra grading`, which is definitionally `GradedRing grading`
--   and hence carries both a `SetLike.GradedMonoid` and a
--   `DirectSum.Decomposition`.
-- * The sign `(-1)^n` for `n : ℤ` is encoded via `Int.negOnePow : ℤ → ℤˣ`,
--   acting by `zsmul`.  This only depends on the parity of `n`, as required.
-- * Right `A`-modules are encoded as left modules over the opposite ring
--   `Aᵐᵒᵖ`; the right action `m · a` is `MulOpposite.op a • m`.

variable (R : Type*) [CommRing R]

/-- A **differential graded algebra** over `R`: a `ℤ`-graded `R`-algebra (the
grading being an honest internal direct-sum decomposition `A = ⨁ A^n`, encoded by
`GradedAlgebra grading`) with an `R`-linear differential of degree `+1` squaring
to zero and satisfying the (signed) Leibniz rule. -/
structure DGA where
  /-- the underlying type `A` of the algebra. -/
  carrier : Type*
  [ring : Ring carrier]
  [algebra : Algebra R carrier]
  /-- the `ℤ`-grading `A = ⨁ A^n`, given as a family of `R`-submodules. -/
  grading : ℤ → Submodule R carrier
  /-- the grading is a graded-algebra structure: it is compatible with the
  multiplication and realizes `A` as the internal direct sum `⨁_n A^n`
  (`GradedAlgebra` is `GradedRing`, which bundles `SetLike.GradedMonoid` together
  with `DirectSum.Decomposition`). -/
  [graded : GradedAlgebra grading]
  /-- the differential `d_A`, an `R`-linear map. -/
  d : carrier →ₗ[R] carrier
  /-- `d_A ∘ d_A = 0`. -/
  d_comp_d : d ∘ₗ d = 0
  /-- `d_A` has degree `+1`. -/
  d_degree : ∀ n, ∀ a ∈ grading n, d a ∈ grading (n + 1)
  /-- the Leibniz rule `d(a b) = d(a) b + (-1)^n a d(b)` for `a ∈ A^n`. -/
  leibniz : ∀ n, ∀ a ∈ grading n, ∀ b,
    d (a * b) = d a * b + (Int.negOnePow n : ℤ) • (a * d b)

attribute [instance] DGA.ring DGA.algebra DGA.graded

variable {R}

/-- A **(right) differential graded `A`-module** `M`: a right `A`-module (encoded
as a left `Aᵐᵒᵖ`-module) with a `ℤ`-grading and an `R`-linear differential `d_M`
of degree `+1` squaring to zero, compatible with the right action by degree
`M^n · A^m ⊆ M^{n+m}` and satisfying the signed Leibniz rule.  The grading is an
honest internal direct-sum decomposition `M = ⨁ M^n`, recorded by the
`DirectSum.Decomposition` field. -/
structure DGModule (𝒜 : DGA R) where
  /-- the underlying type `M` of the module. -/
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]
  /-- the right action of `𝒜` via the opposite ring. -/
  [rmodule : Module 𝒜.carrierᵐᵒᵖ carrier]
  [tower : IsScalarTower R 𝒜.carrierᵐᵒᵖ carrier]
  /-- the `ℤ`-grading `M = ⨁ M^n`. -/
  grading : ℤ → Submodule R carrier
  /-- the grading realizes `M` as the internal direct sum `⨁_n M^n`. -/
  [decomposition : DirectSum.Decomposition grading]
  /-- the differential `d_M`, an `R`-linear map. -/
  d : carrier →ₗ[R] carrier
  /-- `d_M ∘ d_M = 0`. -/
  d_comp_d : d ∘ₗ d = 0
  /-- `d_M` has degree `+1`. -/
  d_degree : ∀ n, ∀ x ∈ grading n, d x ∈ grading (n + 1)
  /-- `M^n · A^m ⊆ M^{n+m}`. -/
  smul_mem : ∀ n m, ∀ x ∈ grading n, ∀ a ∈ 𝒜.grading m,
    (MulOpposite.op a • x : carrier) ∈ grading (n + m)
  /-- the Leibniz rule `d(m a) = d(m) a + (-1)^n m d_A(a)` for `m ∈ M^n`. -/
  leibniz : ∀ n, ∀ x ∈ grading n, ∀ a,
    d (MulOpposite.op a • x)
      = MulOpposite.op a • d x + (Int.negOnePow n : ℤ) • (MulOpposite.op (𝒜.d a) • x)

attribute [instance]
  DGModule.addCommGroup DGModule.module DGModule.rmodule DGModule.tower
  DGModule.decomposition

variable {𝒜 : DGA R}

/-- A **graded `𝒜`-module map of degree `k`**: a right `𝒜`-linear map shifting the
grading by `k` (`f(M^n) ⊆ N^{n+k}`).  It need *not* be compatible with the
differentials.  Graded module maps in the usual sense have degree `k = 0`;
homotopies are graded module maps of degree `-1`. -/
@[ega "II 2.1.2" "more general"]
structure GradedHom (M N : DGModule 𝒜) (k : ℤ) where
  /-- the underlying right `𝒜`-linear map. -/
  toLinearMap : M.carrier →ₗ[𝒜.carrierᵐᵒᵖ] N.carrier
  /-- the degree-shift condition `f(M^n) ⊆ N^{n+k}`. -/
  degree : ∀ n, ∀ x ∈ M.grading n, toLinearMap x ∈ N.grading (n + k)

/-- A **homomorphism of differential graded `𝒜`-modules**: a degree-`0` graded
`𝒜`-module map commuting with the differentials. -/
structure Hom (M N : DGModule 𝒜) extends GradedHom M N 0 where
  /-- compatibility with the differentials: `f ∘ d_M = d_N ∘ f`. -/
  commute : ∀ x, toLinearMap (M.d x) = N.d (toLinearMap x)

/-- Two homomorphisms `f, g : M → N` of differential graded `𝒜`-modules are
**homotopic** if there is a degree `-1` graded `𝒜`-module map `h : M → N` with
`f(x) - g(x) = d_N(h(x)) + h(d_M(x))` for all `x`. -/
def Homotopic {M N : DGModule 𝒜} (f g : Hom M N) : Prop :=
  ∃ h : GradedHom M N (-1), ∀ x,
    f.toLinearMap x - g.toLinearMap x = N.d (h.toLinearMap x) + h.toLinearMap (M.d x)

/-- Composition of homomorphisms of differential graded `𝒜`-modules. -/
def Hom.comp {M N P : DGModule 𝒜} (g : Hom N P) (f : Hom M N) : Hom M P where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  degree := by
    intro n x hx
    simpa using g.degree n _ (by simpa using f.degree n x hx)
  commute := by
    intro x
    simp only [LinearMap.comp_apply]
    rw [f.commute, g.commute]

/-- A homomorphism `f : K → L` is an **admissible monomorphism** if it admits a
graded `𝒜`-module map `π : L → K` of degree `0` that is a left inverse:
`π ∘ f = id`. -/
def IsAdmissibleMono {K L : DGModule 𝒜} (f : Hom K L) : Prop :=
  ∃ π : GradedHom L K 0, ∀ x, π.toLinearMap (f.toLinearMap x) = x

/-- A homomorphism `g : M → N` is an **admissible epimorphism** if it admits a
graded `𝒜`-module map `s : N → M` of degree `0` that is a right inverse:
`g ∘ s = id`. -/
def IsAdmissibleEpi {M N : DGModule 𝒜} (g : Hom M N) : Prop :=
  ∃ s : GradedHom N M 0, ∀ x, g.toLinearMap (s.toLinearMap x) = x

/-- Core homogeneous computation: for a degree `-1` graded `𝒜`-module map `H`,
with `x ∈ L.grading n` homogeneous and `a ∈ 𝒜.grading m` homogeneous, the
operator `x ↦ N.d (H x) + H (L.d x)` commutes with the right action `op a • -`. -/
lemma graded_diff_smul_hom {L N : DGModule 𝒜} (H : GradedHom L N (-1))
    (n : ℤ) (x : L.carrier) (hx : x ∈ L.grading n)
    (a : 𝒜.carrier) :
    N.d (H.toLinearMap (MulOpposite.op a • x))
        + H.toLinearMap (L.d (MulOpposite.op a • x))
      = MulOpposite.op a • (N.d (H.toLinearMap x) + H.toLinearMap (L.d x)) := by
  have hHx : H.toLinearMap x ∈ N.grading (n - 1) := by
    rw [sub_eq_add_neg]
    exact H.degree n x hx
  have hsign : (Int.negOnePow (n - 1) : ℤ) = - (Int.negOnePow n : ℤ) := by
    have : Int.negOnePow (n - 1) = - Int.negOnePow n := by
      rw [show n - 1 = n + (-1) by ring, Int.negOnePow_add]
      simp
    rw [this]
    push_cast
    ring
  rw [map_smul H.toLinearMap (MulOpposite.op a) x, N.leibniz (n - 1) _ hHx a,
    L.leibniz n x hx a, map_add, map_zsmul, map_smul H.toLinearMap (MulOpposite.op (𝒜.d a)) x,
    map_smul, smul_add, hsign]
  simp only [neg_smul]
  abel

/-- The operator `x ↦ N.d (H x) + H (L.d x)` commutes with the right action of an
arbitrary algebra element `a`.  Proven by reducing both `x` and `a` to
homogeneous pieces. -/
lemma graded_diff_smul {L N : DGModule 𝒜} (H : GradedHom L N (-1))
    (a : 𝒜.carrier) (x : L.carrier) :
    N.d (H.toLinearMap (MulOpposite.op a • x))
        + H.toLinearMap (L.d (MulOpposite.op a • x))
      = MulOpposite.op a • (N.d (H.toLinearMap x) + H.toLinearMap (L.d x)) := by
  classical
  -- abbreviation for the operator value
  set D : L.carrier → N.carrier := fun y => N.d (H.toLinearMap y) + H.toLinearMap (L.d y)
    with hD
  -- D is additive and preserves 0
  have hD0 : D 0 = 0 := by simp [hD]
  have hDadd : ∀ y z, D (y + z) = D y + D z := by
    intro y z
    simp only [hD, map_add]
    abel
  -- main: ∀ x a, D (op a • x) = op a • D x, by induction on x then a
  suffices H2 : ∀ (x : L.carrier), D (MulOpposite.op a • x) = MulOpposite.op a • D x by
    simpa [hD] using H2 x
  intro x
  induction x using DirectSum.Decomposition.inductionOn L.grading with
  | zero => simp [hD0]
  | @homogeneous n y =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜.grading with
    | zero => simp [hD0]
    | homogeneous c => simpa [hD] using graded_diff_smul_hom H n y y.2 c
    | add a₁ a₂ ih₁ ih₂ => rw [MulOpposite.op_add, add_smul, add_smul, hDadd, ih₁, ih₂]
  | add y z ihy ihz =>
    have key : D (MulOpposite.op a • y + MulOpposite.op a • z)
        = MulOpposite.op a • D y + MulOpposite.op a • D z := by
      rw [hDadd, ihy, ihz]
    rw [smul_add (MulOpposite.op a) y z, key]
    simp only [hD, smul_add, map_add]
    abel

/-- Given a homomorphism `b : L → N` and a degree `-1` graded `𝒜`-module map
`H`, the map `b' x = b x - (N.d (H x) + H (L.d x))` is again a homomorphism of
differential graded `𝒜`-modules, and it is homotopic to `b` via `H`. -/
lemma exists_homotopic_sub {L N : DGModule 𝒜} (b : Hom L N) (H : GradedHom L N (-1)) :
    ∃ b' : Hom L N, Homotopic b b' ∧
      ∀ x, b'.toLinearMap x
        = b.toLinearMap x - (N.d (H.toLinearMap x) + H.toLinearMap (L.d x)) := by
  let D : L.carrier →ₗ[𝒜.carrierᵐᵒᵖ] N.carrier :=
    { toFun := fun y => N.d (H.toLinearMap y) + H.toLinearMap (L.d y)
      map_add' := fun y z => by
        simp only [map_add]
        abel
      map_smul' := fun c y => graded_diff_smul H c.unop y }
  refine ⟨{ toLinearMap := b.toLinearMap - D
            degree := fun n x hx => ?_
            commute := fun x => ?_ }, ⟨H, fun x => ?_⟩, fun x => rfl⟩
  · have h₁ := N.d_degree _ _ (H.degree n x hx)
    have h₂ := H.degree _ _ (L.d_degree n x hx)
    rw [neg_add_cancel_right] at h₁
    rw [add_neg_cancel_right] at h₂
    simpa [D] using Submodule.sub_mem _ (by simpa using b.degree n x hx) (Submodule.add_mem _ h₁ h₂)
  · have hL : L.d (L.d x) = 0 := by simpa using LinearMap.congr_fun L.d_comp_d x
    have hN : N.d (N.d (H.toLinearMap x)) = 0 := by
      simpa using LinearMap.congr_fun N.d_comp_d (H.toLinearMap x)
    simp [D, b.commute, hL, hN]
  · simp [D]

-- Main Statement(s)


/-- **Statement 1** (Stacks Tag 09JV).  Consider a square of homomorphisms of
differential graded `𝒜`-modules
```
K --f--> L
|a       |b
v        v
M --g--> N
```
that commutes up to homotopy, i.e. `b ∘ f` is homotopic to `g ∘ a`.  If `f` is an
admissible monomorphism, then `b` is homotopic to a homomorphism `b' : L → N`
that makes the diagram commute strictly: `b' ∘ f = g ∘ a`. -/
@[stacks 09JV "(1)"]
theorem statement1 {K L M N : DGModule 𝒜}
    (f : Hom K L) (a : Hom K M) (b : Hom L N) (g : Hom M N)
    (hf : IsAdmissibleMono f)
    (hcomm : Homotopic (b.comp f) (g.comp a)) :
    ∃ b' : Hom L N, Homotopic b b' ∧
      ∀ x, b'.toLinearMap (f.toLinearMap x) = g.toLinearMap (a.toLinearMap x) := by
  obtain ⟨h₀, hh₀⟩ := hcomm
  obtain ⟨π, hπ⟩ := hf
  -- the homotopy H := h₀ ∘ π : L → N of degree -1
  let H : GradedHom L N (-1) :=
    { toLinearMap := h₀.toLinearMap ∘ₗ π.toLinearMap
      degree n x hx := by
        simpa using h₀.degree n (π.toLinearMap x) (by simpa using π.degree n x hx) }
  obtain ⟨b', hbb', hformula⟩ := exists_homotopic_sub b H
  have hHf : ∀ y, H.toLinearMap (f.toLinearMap y) = h₀.toLinearMap y := fun y =>
    congrArg h₀.toLinearMap (hπ y)
  refine ⟨b', hbb', fun x => ?_⟩
  have hrel : b.toLinearMap (f.toLinearMap x) - g.toLinearMap (a.toLinearMap x)
      = N.d (h₀.toLinearMap x) + h₀.toLinearMap (K.d x) :=
    hh₀ x
  rw [hformula, ← f.commute, hHf, hHf, ← hrel]
  abel

/-- **Statement 2** (Stacks Tag 09JV).  With the same setup as Statement 1, if
`g` is an admissible epimorphism, then `a` is homotopic to a homomorphism
`a' : K → M` that makes the diagram commute strictly: `g ∘ a' = b ∘ f`. -/
@[stacks 09JV "(2)"]
theorem statement2 {K L M N : DGModule 𝒜}
    (f : Hom K L) (a : Hom K M) (b : Hom L N) (g : Hom M N)
    (hg : IsAdmissibleEpi g)
    (hcomm : Homotopic (b.comp f) (g.comp a)) :
    ∃ a' : Hom K M, Homotopic a a' ∧
      ∀ x, g.toLinearMap (a'.toLinearMap x) = b.toLinearMap (f.toLinearMap x) := by
  obtain ⟨h₀, hh₀⟩ := hcomm
  obtain ⟨s, hs⟩ := hg
  -- H := -(s ∘ h₀) : K → M of degree -1
  let H : GradedHom K M (-1) :=
    { toLinearMap := -(s.toLinearMap ∘ₗ h₀.toLinearMap)
      degree n x hx := by
        simpa using Submodule.neg_mem _ (s.degree _ _ (h₀.degree n x hx)) }
  obtain ⟨a', haa', hformula⟩ := exists_homotopic_sub a H
  have hgH : ∀ y, g.toLinearMap (H.toLinearMap y) = -h₀.toLinearMap y := fun y => by
    change g.toLinearMap (-s.toLinearMap (h₀.toLinearMap y)) = _
    rw [map_neg, hs]
  refine ⟨a', haa', fun x => ?_⟩
  have hrel : b.toLinearMap (f.toLinearMap x) - g.toLinearMap (a.toLinearMap x)
      = N.d (h₀.toLinearMap x) + h₀.toLinearMap (K.d x) :=
    hh₀ x
  rw [hformula, map_sub, map_add, g.commute, hgH, hgH, map_neg, ← neg_add,
    sub_neg_eq_add, ← hrel]
  abel

end DifferentialGradedModule.AdmissibleSquare

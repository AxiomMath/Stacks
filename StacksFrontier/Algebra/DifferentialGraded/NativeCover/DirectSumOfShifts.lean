module

public import StacksFrontier.Algebra.DifferentialGraded.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Differential graded modules and direct sums of shifts of the algebra

Let `R` be a commutative ring and let `(A, d)` be a differential graded `R`-algebra. This file
sets up the presentation of differential graded algebras and modules used for the cover of a
differential graded module by direct sums of shifts `A[k]` of the algebra (Tag 09KN), and
constructs the generic direct sum of shifts of `A` as a differential graded module.

## Main definitions

* `DifferentialGraded.NativeCover.DGAlgebra`, `DifferentialGraded.NativeCover.DGModule`:
  differential graded algebras and modules presented with the carrier, the grading and the
  differential as explicit parameters.
* `DifferentialGraded.NativeCover.DGModule.Hom`,
  `DifferentialGraded.NativeCover.DGModule.cocycles`,
  `DifferentialGraded.NativeCover.DGModule.gradedCocycles`: homomorphisms and the cocycles they
  act on.
* `DifferentialGraded.NativeCover.DGModule.shift`: the shift `M[k]`.
* `DifferentialGraded.NativeCover.AdmissibleMono`, `DifferentialGraded.NativeCover.AdmissibleSES`:
  maps and short exact sequences which split after forgetting the differentials.
* `DifferentialGraded.NativeCover.IsDirectSumOfShifts`: the property of being isomorphic to a
  direct sum of shifts of the algebra, together with
  `DifferentialGraded.NativeCover.ShiftSum.shiftDG`, the construction of such a direct sum.

## Main results

* `DifferentialGraded.NativeCover.shiftDG_isDirectSumOfShifts`: the generic direct sum of shifts
  is a direct sum of shifts of `A`.

## Implementation notes

The presentation developed here takes the carrier, the grading and the differential as
parameters, which keeps the universes of the scalar ring, of the algebra and of the module
independent and makes the carrier universe of every construction visibly `max v w`.

The sign `(-1)^n` of the graded Leibniz rule is encoded through `n.natAbs`, which has the
same parity as `n`.

## References

* [The Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace DifferentialGraded.NativeCover

universe u v w w' w₁ w₂ w₃ t

/-! ## Differential graded algebras and modules -/

/-- A differential graded algebra.

A differential graded algebra over `R` is an associative, unital `R`-algebra `A`
with an internal `Z`-grading `𝒜 : ℤ → Submodule R A`.  We require:
* `[GradedAlgebra 𝒜]`, which encodes `A^n A^m ⊆ A^{n+m}`, `1 ∈ A^0`, and the
  `R → A` structure map landing in `A^0`; and
* `DirectSum.IsInternal 𝒜`, encoding the actual direct sum decomposition
  `A = ⨁_{n} A^n`.
together with an `R`-linear differential `d` of degree `+1` squaring to zero and
satisfying the graded Leibniz rule.

The sign `(-1)^n` is encoded via `n.natAbs`, which has the same parity as `n`. -/
structure DGAlgebra (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] where
  /-- The grading is internal: `A` is the (internal) direct sum of the pieces. -/
  isInternal : DirectSum.IsInternal 𝒜
  /-- The differential. -/
  d : A →ₗ[R] A
  /-- The differential raises degree by one: `d (A^n) ⊆ A^{n+1}`. -/
  d_grade : ∀ (n : ℤ) (a : A), a ∈ 𝒜 n → d a ∈ 𝒜 (n + 1)
  /-- `d ∘ d = 0`. -/
  d_comp_d : ∀ a, d (d a) = 0
  /-- Graded Leibniz rule: for `a ∈ A^n` and `b ∈ A`,
  `d (a b) = d(a) b + (-1)^n a d(b)`. -/
  leibniz : ∀ (n : ℤ) (a : A), a ∈ 𝒜 n → ∀ b : A,
    d (a * b) = d a * b + ((-1 : R) ^ n.natAbs) • (a * d b)

/-- A right differential graded module over a differential graded algebra.

A (right) differential graded `A`-module `M` is a right `A`-module with an
internal `Z`-grading `ℳ : ℤ → Submodule R M` compatible with the algebra grading
(`M^n A^m ⊆ M^{n+m}`), together with an `R`-linear differential `d_M` of degree
`+1` squaring to zero and satisfying the graded Leibniz rule
`d_M (m a) = d_M(m) a + (-1)^n m d(a)` for `m ∈ M^n`.

We model the right `A`-action as a bilinear `smul` map `M → A → M`, with the
usual module axioms, since `A` is noncommutative. -/
structure DGModule (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    (M : Type w) [AddCommGroup M] [Module R M] where
  /-- The right `A`-action. -/
  smul : M →ₗ[R] A →ₗ[R] M
  /-- The grading on `M` as `R`-submodules. -/
  grading : ℤ → Submodule R M
  /-- The grading is internal: `M` is the (internal) direct sum of the pieces. -/
  isInternal : DirectSum.IsInternal grading
  /-- The right action is unital: `m • 1 = m`. -/
  smul_one : ∀ m : M, smul m 1 = m
  /-- The right action is associative: `(m • a) • b = m • (a b)`. -/
  smul_smul : ∀ (m : M) (a b : A), smul (smul m a) b = smul m (a * b)
  /-- Graded compatibility of action: `M^n A^m ⊆ M^{n+m}`. -/
  smul_grade : ∀ (n m : ℤ) (x : M) (a : A), x ∈ grading n → a ∈ 𝒜 m →
    smul x a ∈ grading (n + m)
  /-- The differential of `M`. -/
  d : M →ₗ[R] M
  /-- The differential raises degree by one. -/
  d_grade : ∀ (n : ℤ) (x : M), x ∈ grading n → d x ∈ grading (n + 1)
  /-- `d_M ∘ d_M = 0`. -/
  d_comp_d : ∀ x, d (d x) = 0
  /-- Graded Leibniz rule: for `m ∈ M^n` and `a ∈ A`,
  `d_M (m a) = d_M(m) a + (-1)^n m d(a)`. -/
  leibniz : ∀ (n : ℤ) (x : M), x ∈ grading n → ∀ a : A,
    d (smul x a) = smul (d x) a + ((-1 : R) ^ n.natAbs) • smul x (dA.d a)

namespace DGModule

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}

/-- A homomorphism of differential graded modules.

A homomorphism of differential graded `A`-modules `f : M → N` is an `A`-module
map compatible with gradings (`f (M^n) ⊆ N^n`) and differentials
(`f ∘ d_M = d_N ∘ f`). -/
structure Hom {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type w'} [AddCommGroup N] [Module R N]
    (P : DGModule R A 𝒜 dA M) (Q : DGModule R A 𝒜 dA N) where
  /-- The underlying `R`-linear map. -/
  toFun : M →ₗ[R] N
  /-- Compatibility with the right `A`-action. -/
  map_smul' : ∀ (m : M) (a : A), toFun (P.smul m a) = Q.smul (toFun m) a
  /-- Compatibility with gradings: `f (M^n) ⊆ N^n`. -/
  map_grade : ∀ (n : ℤ) (m : M), m ∈ P.grading n → toFun m ∈ Q.grading n
  /-- Compatibility with differentials: `f ∘ d_M = d_N ∘ f`. -/
  map_d : ∀ m, toFun (P.d m) = Q.d (toFun m)

/-- The cocycles of a differential graded module.

`Ker(d_M)` is the kernel of the differential, a graded `R`-submodule of `M`
(the submodule of cocycles). -/
def cocycles {M : Type w} [AddCommGroup M] [Module R M]
    (P : DGModule R A 𝒜 dA M) : Submodule R M :=
  LinearMap.ker P.d

/-- The homogeneous cocycles of a differential graded module.

The degree-`n` cocycles `Ker(d_M : M^n → M^{n+1})`, a graded `R`-submodule of
`M^n`.  This exhibits `Ker(d_M)` as the graded family
`⨁_n Ker(d_M : M^n → M^{n+1})`. -/
def gradedCocycles {M : Type w} [AddCommGroup M] [Module R M]
    (P : DGModule R A 𝒜 dA M) (n : ℤ) : Submodule R M :=
  P.cocycles ⊓ P.grading n

/-- The induced `R`-linear map on cocycles `Ker(d_P) → Ker(d_M)`:
a homomorphism of DG modules restricts to cocycles since it commutes with the
differentials.  This is `R`-linear (and graded), but not in general `A`-linear.
We package it as an honest `R`-linear map between the cocycle submodules. -/
def Hom.onCocycles {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type w'} [AddCommGroup N] [Module R N]
    {P : DGModule R A 𝒜 dA M} {Q : DGModule R A 𝒜 dA N}
    (f : Hom P Q) : P.cocycles →ₗ[R] Q.cocycles where
  toFun x := ⟨f.toFun x, by
    have hx : P.d x = 0 := x.2
    simp only [cocycles, LinearMap.mem_ker, ← f.map_d, hx, map_zero]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- A homomorphism is surjective if the underlying map is surjective. -/
def Hom.Surjective {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type w'} [AddCommGroup N] [Module R N]
    {P : DGModule R A 𝒜 dA M} {Q : DGModule R A 𝒜 dA N}
    (f : Hom P Q) : Prop :=
  Function.Surjective f.toFun

/-- **Degreewise (graded) surjectivity on cocycles.**

The induced map on cocycles `Ker(d_P) → Ker(d_M)` is *graded* surjective: for
every degree `n` and every cocycle `m` of `M` of degree `n` (i.e. `m` lies in
both `Ker(d_M)` and `M^n`), there is a cocycle `x` of `P` of degree `n` (i.e.
`x` lies in both `Ker(d_P)` and `P^n`) with `f x = m`. -/
def Hom.GradedSurjectiveOnCocycles {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type w'} [AddCommGroup N] [Module R N]
    {P : DGModule R A 𝒜 dA M} {Q : DGModule R A 𝒜 dA N}
    (f : Hom P Q) : Prop :=
  ∀ (n : ℤ) (m : N), m ∈ Q.gradedCocycles n →
    ∃ x : M, x ∈ P.gradedCocycles n ∧ f.toFun x = m

end DGModule

/-! ### The shift `M[k]` of a differential graded module -/

/-- Reindexing an internal grading by an `Equiv` of the index set preserves
internality. -/
theorem isInternal_comp_equiv {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (g : ℤ → Submodule R M) (h : DirectSum.IsInternal g) (e : ℤ ≃ ℤ) :
    DirectSum.IsInternal (g ∘ e) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  obtain ⟨hind, hsup⟩ := h
  refine ⟨hind.comp e.injective, ?_⟩
  rw [← hsup]
  exact e.iSup_comp (g := g)

/-- The shift `M[k]` of a differential graded module.

Let `(A, d)` be a differential graded algebra and `M` a differential graded
`A`-module with data `P : DGModule R A 𝒜 dA M`.  For `k ∈ Z`, the `k`-shifted
module `M[k]` is the differential graded `A`-module on the *same* underlying
`R`-module `M` and *same* right `A`-action, but with:
* grading `M[k]^n = M^{n+k}`, and
* differential `d_{M[k]} = (-1)^k d_M`.

We construct it explicitly as another `DGModule` structure on the carrier `M`. -/
def DGModule.shift {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
    {M : Type w} [AddCommGroup M] [Module R M] (P : DGModule R A 𝒜 dA M) (k : ℤ) :
    DGModule R A 𝒜 dA M where
  smul := P.smul
  grading n := P.grading (n + k)
  isInternal := by
    -- `n ↦ grading (n + k)` reindexes the same internal grading by the
    -- bijection `n ↦ n + k`, hence is still internal.
    have heq : (fun n => P.grading (n + k)) = P.grading ∘ (Equiv.addRight k) := by
      funext n; rfl
    rw [heq]
    exact isInternal_comp_equiv P.grading P.isInternal (Equiv.addRight k)
  smul_one := P.smul_one
  smul_smul := P.smul_smul
  smul_grade n m x a hx ha := by
    have := P.smul_grade (n + k) m x a hx ha
    simpa [add_right_comm] using this
  d := ((-1 : R) ^ k.natAbs) • P.d
  d_grade n x hx := by
    have hgr : x ∈ P.grading (n + k) := hx
    have hd : P.d x ∈ P.grading (n + k + 1) := P.d_grade (n + k) x hgr
    have hmem : (((-1 : R) ^ k.natAbs) • P.d) x ∈ P.grading (n + k + 1) := by
      simp only [LinearMap.smul_apply]
      exact (P.grading (n + k + 1)).smul_mem _ hd
    simpa [add_right_comm] using hmem
  d_comp_d x := by
    simp only [LinearMap.smul_apply, map_smul, P.d_comp_d, smul_zero]
  leibniz n x hx a := by
    have hgr : x ∈ P.grading (n + k) := hx
    have hL := P.leibniz (n + k) x hgr a
    -- `d_{M[k]} = (-1)^|k| P.d`.  Apply Leibniz of `P` at degree `n+k` and
    -- recombine signs: the factor `(-1)^|n+k|` from `P`'s Leibniz combines
    -- with the `(-1)^|k|` prefactor to give `(-1)^|n|`, since `|k| + |n+k|`
    -- and `|n|` have the same parity.
    simp only [LinearMap.smul_apply]
    rw [hL, smul_add]
    rw [map_smul, LinearMap.smul_apply]
    congr 1
    rw [_root_.smul_smul, ← pow_add]
    have hpar : (k.natAbs + (n + k).natAbs) % 2 = n.natAbs % 2 := by omega
    rcases Nat.even_or_odd (k.natAbs + (n + k).natAbs) with he | ho
    · have hn : Even n.natAbs := by rw [Nat.even_iff] at he ⊢; omega
      rw [Even.neg_one_pow he, Even.neg_one_pow hn]
    · have hn : Odd n.natAbs := by rw [Nat.odd_iff] at ho ⊢; omega
      rw [Odd.neg_one_pow ho, Odd.neg_one_pow hn]

/-! ### Admissible monomorphisms and admissible short exact sequences -/

/-- An admissible monomorphism of differential graded modules.

A homomorphism `i : K → L` of differential graded `A`-modules is an *admissible
monomorphism* if there exists a *graded* `A`-module map `r : L → K` (not required
to commute with the differentials) that is a left inverse of `i`. -/
def AdmissibleMono {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
    {K : Type w₁} [AddCommGroup K] [Module R K]
    {L : Type w₂} [AddCommGroup L] [Module R L]
    {PK : DGModule R A 𝒜 dA K} {PL : DGModule R A 𝒜 dA L}
    (i : DGModule.Hom PK PL) : Prop :=
  ∃ r : L →ₗ[R] K,
    -- `r` respects the right `A`-action
    (∀ (l : L) (a : A), r (PL.smul l a) = PK.smul (r l) a) ∧
    -- `r` respects the grading
    (∀ (n : ℤ) (l : L), l ∈ PL.grading n → r l ∈ PK.grading n) ∧
    -- `r` is a left inverse of `i`
    (∀ k, r (i.toFun k) = k)

/-- An admissible short exact sequence of differential graded modules.

A short exact sequence `0 → K → L → N → 0` of differential graded `A`-modules is
*admissible* if it is split as a sequence of *graded* `A`-modules: there is a
graded `A`-module isomorphism `L ≅ K ⊕ N` (degreewise, ignoring differentials)
compatible with the maps `i : K → L` and `p : L → N`.

Concretely, alongside the DG-module homomorphisms `i` and `p`
(which DO commute with the differentials), we record an explicit `R`-linear
isomorphism `e : L ≃ K × N` such that
* `e` respects the right `A`-action (it is `A`-linear);
* `e` respects the gradings in both directions (it is graded, i.e. it restricts
  to isomorphisms `L^n ≅ K^n ⊕ N^n` for each `n`);
* `e` is compatible with the maps of the sequence:
  - the inclusion `i : K → L` corresponds to `k ↦ (k, 0)`, i.e.
    `e (i k) = (k, 0)`; and
  - the surjection `p : L → N` corresponds to the second projection, i.e.
    `(e l).2 = p l`.

The isomorphism `e` is NOT required to commute with the differentials, exactly
matching "split as a sequence of graded `A`-modules". -/
structure AdmissibleSES {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
    {K : Type w₁} [AddCommGroup K] [Module R K]
    {L : Type w₂} [AddCommGroup L] [Module R L]
    {N : Type w'} [AddCommGroup N] [Module R N]
    (PK : DGModule R A 𝒜 dA K) (PL : DGModule R A 𝒜 dA L)
    (PN : DGModule R A 𝒜 dA N) where
  /-- The DG-module monomorphism `i : K → L`. -/
  i : DGModule.Hom PK PL
  /-- The DG-module surjection `p : L → N`. -/
  p : DGModule.Hom PL PN
  /-- `i` is injective. -/
  i_inj : Function.Injective i.toFun
  /-- `p` is surjective. -/
  p_surj : Function.Surjective p.toFun
  /-- Exactness in the middle: `range i = ker p`. -/
  exact : LinearMap.range i.toFun = LinearMap.ker p.toFun
  /-- The graded `A`-module splitting isomorphism `L ≅ K ⊕ N` (ignoring the
  differentials).  We use the underlying `R`-linear equivalence and record the
  `A`-linearity and gradedness separately. -/
  splitEquiv : L ≃ₗ[R] K × N
  /-- The splitting isomorphism respects the right `A`-action. -/
  splitEquiv_smul : ∀ (l : L) (a : A),
    splitEquiv (PL.smul l a)
      = ((PK.smul (splitEquiv l).1 a), (PN.smul (splitEquiv l).2 a))
  /-- The splitting isomorphism is graded in the forward direction:
  if `l ∈ L^n` then both components of `e l` lie in degree `n`. -/
  splitEquiv_grade : ∀ (n : ℤ) (l : L), l ∈ PL.grading n →
    (splitEquiv l).1 ∈ PK.grading n ∧ (splitEquiv l).2 ∈ PN.grading n
  /-- The splitting isomorphism is graded in the backward direction:
  if `k ∈ K^n` and `x ∈ N^n` then `e⁻¹ (k, x) ∈ L^n`. -/
  splitEquiv_symm_grade : ∀ (n : ℤ) (k : K) (x : N),
    k ∈ PK.grading n → x ∈ PN.grading n → splitEquiv.symm (k, x) ∈ PL.grading n
  /-- Compatibility with `i`: the inclusion corresponds to the first factor. -/
  splitEquiv_i : ∀ k, splitEquiv (i.toFun k) = (k, 0)
  /-- Compatibility with `p`: the surjection corresponds to the second
  projection. -/
  splitEquiv_p : ∀ l, (splitEquiv l).2 = p.toFun l

/-! ### Direct sums of shifts of `A` -/

/-- A differential graded `A`-module `(M, P)` is *a direct sum of shifts of `A`*
if there is an index type `ι`, an integer `k_i` for each `i : ι`, and a DG-module
isomorphism between `M` and the direct sum of the shifts `A[k_i]`.

We encode the direct sum of shifts abstractly: the carrier is
`DirectSum ι (fun _ => A)`, with the right `A`-action acting componentwise, the
grading where the `i`-th summand sits in degrees shifted by `k i` (so that the
homogeneous part of degree `n` consists of tuples whose `i`-th component lies in
`A^{n + k i}`), and the differential acting on the `i`-th component by
`(-1)^{k i} d`.  We state the predicate as the existence of such a description
together with a graded, `A`-linear, differential-compatible isomorphism.

The index type `ι` lives in `Type t`, independently of the input carrier; the
model direct sum has carrier universe `max v t`, independent of the scalar ring. -/
def IsDirectSumOfShifts {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
    {M : Type w} [AddCommGroup M] [Module R M] (P : DGModule R A 𝒜 dA M) : Prop :=
  ∃ (ι : Type t) (k : ι → ℤ)
    (S : Type (max v t)) (_ : AddCommGroup S) (_ : Module R S) (PS : DGModule R A 𝒜 dA S),
    -- `S` is the direct sum of shifts `A[k i]`:
    (∃ (e : S ≃ₗ[R] DirectSum ι (fun _ : ι => A)),
      -- the action is componentwise:
      (∀ (s : S) (a : A) (j : ι), (e (PS.smul s a)) j = (e s j) * a) ∧
      -- the `i`-summand of the grading is shifted by `k i`:
      (∀ (n : ℤ) (s : S), s ∈ PS.grading n ↔ ∀ j : ι, (e s j) ∈ 𝒜 (n + k j)) ∧
      -- the differential acts on the `j`-summand by `(-1)^{k j} d`:
      (∀ (s : S) (j : ι), (e (PS.d s)) j = ((-1 : R) ^ (k j).natAbs) • dA.d (e s j))) ∧
    -- `M` is isomorphic, as a DG `A`-module, to this direct sum of shifts:
    (∃ (f : DGModule.Hom P PS) (g : DGModule.Hom PS P),
      (∀ m, g.toFun (f.toFun m) = m) ∧ (∀ s, f.toFun (g.toFun s) = s))

/-! ### Construction: the generic "direct sum of shifts of `A`" as a DG module. -/

namespace ShiftSum

open scoped Classical in
/-- The right `A`-action on `⨁_ι A`, acting componentwise on the right. -/
noncomputable def rsmul (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (ι : Type t) :
    DirectSum ι (fun _ : ι => A) →ₗ[R] A →ₗ[R] DirectSum ι (fun _ : ι => A) :=
  DirectSum.toModule R ι (A →ₗ[R] DirectSum ι (fun _ : ι => A))
    (fun j => (LinearMap.mul R A).compr₂ (DirectSum.lof R ι (fun _ : ι => A) j))

open scoped Classical in
/-- The action on a single summand: `(1_j c) • a = 1_j (c * a)`. -/
theorem rsmul_lof (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A] (ι : Type t)
    (j : ι) (c a : A) :
    rsmul R A ι (DirectSum.lof R ι (fun _ : ι => A) j c) a
      = DirectSum.lof R ι (fun _ : ι => A) j (c * a) := by
  unfold rsmul
  rw [DirectSum.toModule_lof]
  rfl

/-- To compute the `j`-component of `f s` for a linear map `f`, it suffices to do so on
the summands `lof i x`. -/
private theorem component_apply_of_lof {R : Type u} {A : Type v} [CommRing R] [Ring A]
    [Algebra R A] {ι : Type t} [DecidableEq ι]
    (f : DirectSum ι (fun _ : ι => A) →ₗ[R] DirectSum ι (fun _ : ι => A)) (g : A →ₗ[R] A)
    (j : ι) (h : ∀ (i : ι) (x : A),
      f (DirectSum.lof R ι (fun _ : ι => A) i x) j = g (DirectSum.lof R ι (fun _ : ι => A) i x j))
    (s : DirectSum ι (fun _ : ι => A)) : f s j = g (s j) :=
  LinearMap.congr_fun (DirectSum.linearMap_ext R fun i => LinearMap.ext (h i)
    : DirectSum.component R ι (fun _ : ι => A) j ∘ₗ f = g ∘ₗ DirectSum.component R ι _ j) s

open scoped Classical in
/-- Componentwise description of the action: the `j`-component of `s • a` is
`s_j * a`. -/
theorem rsmul_apply (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A] (ι : Type t)
    (s : DirectSum ι (fun _ : ι => A)) (a : A) (j : ι) :
    (rsmul R A ι s a) j = (s j) * a :=
  component_apply_of_lof ((rsmul R A ι).flip a) (LinearMap.mulRight R a) j
    (fun i x => by
      rw [LinearMap.flip_apply, rsmul_lof]
      by_cases h : i = j <;> simp [DirectSum.lof_eq_of, DirectSum.of_apply, h]) s

open scoped Classical in
/-- The diagonal differential on `⨁_ι A[k_j]`: on the `j`-summand it is
`(-1)^{|k_j|} d_A`. -/
noncomputable def diffDiag (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    (ι : Type t) (k : ι → ℤ) :
    DirectSum ι (fun _ : ι => A) →ₗ[R] DirectSum ι (fun _ : ι => A) :=
  DirectSum.toModule R ι (DirectSum ι (fun _ : ι => A))
    (fun j => (((-1 : R) ^ (k j).natAbs) • DirectSum.lof R ι (fun _ : ι => A) j) ∘ₗ dA.d)

open scoped Classical in
/-- Componentwise description of the diagonal differential: its `j`-component is
`(-1)^{|k_j|} d_A` applied to the `j`-component. -/
theorem diffDiag_apply (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    (ι : Type t) (k : ι → ℤ) (s : DirectSum ι (fun _ : ι => A)) (j : ι) :
    (diffDiag R A dA ι k s) j = ((-1 : R) ^ (k j).natAbs) • dA.d (s j) :=
  component_apply_of_lof (diffDiag R A dA ι k) (((-1 : R) ^ (k j).natAbs) • dA.d) j
    (fun i x => by
      rw [diffDiag, DirectSum.toModule_lof]
      by_cases h : i = j <;>
        simp [DirectSum.lof_eq_of, DirectSum.smul_apply, DirectSum.of_apply, h]) s

open scoped Classical in
/-- The grading submodule of `⨁_ι A[k_j]` in degree `n`: tuples whose `j`-th
component lies in `𝒜 (n + k j)`. -/
def gradingSub (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) (ι : Type t) (k : ι → ℤ) (n : ℤ) :
    Submodule R (DirectSum ι (fun _ : ι => A)) where
  carrier := {s | ∀ j, s j ∈ 𝒜 (n + k j)}
  add_mem' {s t} hs ht := by
    intro j; rw [DirectSum.add_apply]; exact (𝒜 (n + k j)).add_mem (hs j) (ht j)
  zero_mem' := by intro j; simp
  smul_mem' c s hs := by
    intro j; rw [DirectSum.smul_apply]; exact (𝒜 (n + k j)).smul_mem c (hs j)

open scoped Classical in
/-- Membership in the degree-`n` piece of `⨁_ι A[k_j]`: every component `s_j` lies in
`𝒜 (n + k_j)`. -/
theorem mem_gradingSub (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) (ι : Type t) (k : ι → ℤ) (n : ℤ)
    (s : DirectSum ι (fun _ : ι => A)) :
    s ∈ gradingSub R A 𝒜 ι k n ↔ ∀ j, s j ∈ 𝒜 (n + k j) := Iff.rfl

open scoped Classical in
/-- Internality of the shift-sum grading. -/
theorem isInternal_gradingSub (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    (ι : Type t) (k : ι → ℤ) :
    DirectSum.IsInternal (gradingSub R A 𝒜 ι k) := by
  -- The grading on `⨁_ι A[k_j]` is the product of the internal gradings `𝒜 (· + k j)` on the
  -- summands, so independence and `iSup = ⊤` follow componentwise from `dA.isInternal`.
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hI := dA.isInternal
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hI
  obtain ⟨hind, hsup_top⟩ := hI
  refine ⟨?_, ?_⟩
  · -- independence: reduce componentwise to independence of `𝒜`.
    rw [iSupIndep_def]
    intro n
    rw [disjoint_iff, eq_bot_iff]
    intro s hs
    obtain ⟨hsn, hsrest⟩ := hs
    rw [Submodule.mem_bot]
    ext j
    rw [DirectSum.zero_apply]
    have h1 : s j ∈ 𝒜 (n + k j) := hsn j
    have h2 : s j ∈ ⨆ m, ⨆ (_ : m ≠ n), 𝒜 (m + k j) := by
      have hle : (⨆ m, ⨆ (_ : m ≠ n), gradingSub R A 𝒜 ι k m)
          ≤ (⨆ m, ⨆ (_ : m ≠ n), 𝒜 (m + k j)).comap
              (DirectSum.component R ι (fun _ : ι => A) j) := by
        apply iSup_le
        intro m
        apply iSup_le
        intro hm t ht
        have htj : t j ∈ 𝒜 (m + k j) := ht j
        refine Submodule.mem_comap.mpr ?_
        apply Submodule.mem_iSup_of_mem m
        exact Submodule.mem_iSup_of_mem hm htj
      exact Submodule.mem_comap.mp (hle hsrest)
    have hdisj : Disjoint (𝒜 (n + k j)) (⨆ m, ⨆ (_ : m ≠ n), 𝒜 (m + k j)) := by
      have hinj : Function.Injective (fun m : ℤ => m + k j) :=
        fun a b h => by simpa using h
      have hcomp := hind.comp hinj
      rw [iSupIndep_def] at hcomp
      exact hcomp n
    have hmem : s j ∈ (𝒜 (n + k j)) ⊓ (⨆ m, ⨆ (_ : m ≠ n), 𝒜 (m + k j)) := ⟨h1, h2⟩
    rw [hdisj.eq_bot] at hmem
    rwa [Submodule.mem_bot] at hmem
  · -- supremum: every element is a sum of homogeneous pieces.
    rw [eq_top_iff]
    intro s _
    have of_mem : ∀ (j : ι) (p : ℤ) (a : A), a ∈ 𝒜 p →
        DirectSum.of (fun _ : ι => A) j a ∈ gradingSub R A 𝒜 ι k (p - k j) := by
      intro j p a ha i
      rw [DirectSum.of_apply]
      by_cases h : j = i
      · subst h
        simp only []
        have hpk : p - k j + k j = p := by ring
        rw [hpk]
        exact ha
      · rw [dite_eq_right h]
        exact (𝒜 _).zero_mem
    have key : ∀ t : DirectSum ι (fun _ : ι => A),
        t ∈ ⨆ n, gradingSub R A 𝒜 ι k n := by
      intro t
      induction t using DirectSum.induction_on with
      | zero => exact Submodule.zero_mem _
      | of i a =>
          rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
          apply Submodule.sum_mem
          intro p _
          apply Submodule.mem_iSup_of_mem (p - k i)
          exact of_mem i p _ (DirectSum.decompose 𝒜 a p).2
      | add x y hx hy => exact Submodule.add_mem _ hx hy
    exact key s

open scoped Classical in
/-- The generic direct sum of shifts of `A` as a differential graded module. -/
noncomputable def shiftDG (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    (ι : Type t) (k : ι → ℤ) :
    DGModule R A 𝒜 dA (DirectSum ι (fun _ : ι => A)) where
  smul := rsmul R A ι
  grading := gradingSub R A 𝒜 ι k
  isInternal := isInternal_gradingSub R A 𝒜 dA ι k
  smul_one s := by
    refine DirectSum.ext (fun j => ?_)
    rw [rsmul_apply]; simp
  smul_smul s a b := by
    refine DirectSum.ext (fun j => ?_)
    rw [rsmul_apply, rsmul_apply, rsmul_apply, mul_assoc]
  smul_grade n m x a hx ha := by
    rw [mem_gradingSub] at hx ⊢
    intro j
    rw [rsmul_apply]
    have hmul : (x j) * a ∈ 𝒜 ((n + k j) + m) :=
      SetLike.mul_mem_graded (hx j) ha
    rw [show n + m + k j = (n + k j) + m by ring]
    exact hmul
  d := diffDiag R A dA ι k
  d_grade n x hx := by
    rw [mem_gradingSub] at hx ⊢
    intro j
    rw [diffDiag_apply]
    have hd : dA.d (x j) ∈ 𝒜 ((n + k j) + 1) := dA.d_grade (n + k j) (x j) (hx j)
    rw [show n + 1 + k j = (n + k j) + 1 by ring]
    exact (𝒜 _).smul_mem _ hd
  d_comp_d x := by
    refine DirectSum.ext (fun j => ?_)
    rw [diffDiag_apply, diffDiag_apply]
    rw [map_smul, dA.d_comp_d, smul_zero, smul_zero]
    simp
  leibniz n x hx a := by
    rw [mem_gradingSub] at hx
    refine DirectSum.ext (fun j => ?_)
    rw [diffDiag_apply, rsmul_apply, DirectSum.add_apply, rsmul_apply,
        diffDiag_apply, DirectSum.smul_apply, rsmul_apply]
    have hxj : x j ∈ 𝒜 (n + k j) := hx j
    have hL := dA.leibniz (n + k j) (x j) hxj a
    rw [hL, smul_add]
    rw [show ((-1 : R) ^ (k j).natAbs) • (dA.d (x j) * a)
          = (((-1 : R) ^ (k j).natAbs) • dA.d (x j)) * a by
        rw [smul_mul_assoc]]
    congr 1
    rw [smul_smul, ← pow_add]
    have hpar : ((k j).natAbs + (n + k j).natAbs) % 2 = ((n).natAbs) % 2 := by
      omega
    rcases Nat.even_or_odd ((k j).natAbs + (n + k j).natAbs) with he | ho
    · have hn : Even (n.natAbs) := by rw [Nat.even_iff] at he ⊢; omega
      rw [Even.neg_one_pow he, Even.neg_one_pow hn]
    · have hn : Odd (n.natAbs) := by rw [Nat.odd_iff] at ho ⊢; omega
      rw [Odd.neg_one_pow ho, Odd.neg_one_pow hn]

end ShiftSum

/-! ### Decomposition lemmas for the cover.

The construction proceeds as follows.

* For each homogeneous element `m ∈ M^k` we use the free DG `A`-module `P_k` on
  two generators `x` (degree `k`) and `y` (degree `k+1`) with `d x = y`,
  `d y = 0`.  As a *graded* `A`-module `P_k ≅ A[-k] ⊕ A[-k-1]`, and it sits in
  the admissible SES `0 → A[-k-1] → P_k → A[-k] → 0`.  The DG-map `P_k → M`
  sending `x ↦ m`, `y ↦ d_M m` exists (it commutes with `d` by the very
  definition `d x = y`).  Summing over ALL homogeneous `m` gives a surjection
  `φ₁ : P₁ ↠ M` and (taking `P'` = the `y`-summands `⨁ A[-k-1]`, `P''` = the
  `x`-summands `⨁ A[-k]`) an admissible SES `0 → P' → P₁ → P'' → 0` with both
  ends direct sums of shifts of `A`.
* For each cocycle `c ∈ Ker(d_M)^k` the shift `A[-k]` admits a DG-map
  `A[-k] → M` sending the degree-`k` generator `1` to `c`; this is a chain map
  *because* `d_M c = 0`, so the generator is a cocycle of `A[-k]` mapping to
  `c`.  Summing over all cocycles gives `φ₂ : P₂ → M` from a direct sum of
  shifts `P₂` whose induced map on cocycles is graded surjective.
* Forming `P = P₁ ⊕ P₂`, `φ = φ₁ ⊕ φ₂` keeps `φ` surjective (via `φ₁`), makes it
  graded surjective on cocycles (via `φ₂`), and gives the admissible SES
  `0 → P' → P → (P'' ⊕ P₂) → 0` whose ends `P'` and `P'' ⊕ P₂` are still direct
  sums of shifts of `A`.  This is the assembly lemma `cover_combine` below.

The four steps are `shiftDG_isDirectSumOfShifts`, `exists_surjective_cover`,
`exists_cocycle_cover` and `cover_combine`. -/

/-- The generic direct sum of shifts `ShiftSum.shiftDG R A 𝒜 dA ι k`
is a direct sum of shifts of `A` (`IsDirectSumOfShifts`): the witness is the direct sum itself,
with the identity as the isomorphism. -/
theorem shiftDG_isDirectSumOfShifts
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    (ι : Type t) (k : ι → ℤ) :
    IsDirectSumOfShifts.{u, v, _, t} (ShiftSum.shiftDG R A 𝒜 dA ι k) := by
  refine ⟨ι, k, DirectSum ι (fun _ : ι => A), _, _,
    ShiftSum.shiftDG R A 𝒜 dA ι k, ?_, ?_⟩
  · refine ⟨LinearEquiv.refl R (DirectSum ι (fun _ : ι => A)), ?_, ?_, ?_⟩
    · intro s a j
      simpa [ShiftSum.shiftDG] using ShiftSum.rsmul_apply R A ι s a j
    · intro n s
      simpa [ShiftSum.shiftDG] using ShiftSum.mem_gradingSub R A 𝒜 ι k n s
    · intro s j
      simpa [ShiftSum.shiftDG] using ShiftSum.diffDiag_apply R A dA ι k s j
  · refine ⟨{ toFun := LinearMap.id, map_smul' := ?_, map_grade := ?_, map_d := ?_ },
           { toFun := LinearMap.id, map_smul' := ?_, map_grade := ?_, map_d := ?_ },
           ?_, ?_⟩
    all_goals first | intros; rfl | exact fun _ _ hm => hm

end DifferentialGraded.NativeCover

end

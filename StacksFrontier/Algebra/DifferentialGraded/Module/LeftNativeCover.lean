module

public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyI
public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDual
public import StacksFrontier.Algebra.DirectSum.ParityOperator
public import StacksCore.Tactic.StacksAttribute

/-! # The native cover of a left differential graded module

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. Stacks 09KN produces,
for a differential graded `A`-module `M`, a surjection `P ⟶ M` from a module `P` which is an
extension of a direct sum of shifts of `A` by a direct sum of shifts of `A` along an *admissible*
short exact sequence. The proof of Stacks 09KT needs the same statement for *left* differential
graded modules, where it is applied to the graded dual `M∨`, and that is what this file proves.

The cover is built from the two-cell modules of the Stacks proof. For `k ∈ ℤ` let `Q_k` be the
free left `A`-module on generators `x` in degree `k` and `y` in degree `k + 1`, with
`d x = y` and `d y = 0`. A homogeneous element `m ∈ N^k` is hit by the homomorphism
`Q_k ⟶ N` sending `x` to `m` and `y` to `d m`, so the sum of one copy of `Q_k` for every
homogeneous element of `N` surjects onto `N`; and `Q_k` itself is an extension of `A[-k]` by
`A[-k-1]`, admissibly, since the inclusion of the `y`-summand and the projection to the
`x`-summand are split by maps of graded modules.

Part (2) of the source lemma — that `Ker(d_P) → Ker(d_N)` is surjective — is obtained as the
source obtains it, by adding bare shifts `A[k]` to the cover: a homogeneous cocycle `m ∈ N^k` is
the image of the generator `1` of a copy of `A[-k]`, and that generator is a cocycle. The
construction below carries both kinds of cell at once, flagged by `b : ι → Bool`; at a bare
index the pair of summands `A xᵢ ⊕ A yᵢ` is the split sum of two shifts of `A` rather than the
two-cell module, which leaves part (3) untouched.

## Main definitions

* `DifferentialGraded.LeftModule.GradedHom`: a degree-zero map of graded left `A`-modules, with
  no compatibility with the differentials, and
  `DifferentialGraded.LeftModule.IsAdmissibleMono`,
  `DifferentialGraded.LeftModule.IsAdmissibleEpi`,
  `DifferentialGraded.LeftModule.IsAdmissibleShortExact`: the admissibility notions of
  Stacks 09JT for left modules.
* `DifferentialGraded.LeftModule.cellParity`: the coefficient of `yᵢ` in `d (a xᵢ)`, which
  distinguishes a two-cell index from a bare one.
* `DifferentialGraded.LeftModule.twoCellSum`: the direct sum `⨁ᵢ Q_{kᵢ}` of cells, as a
  left differential graded `A`-module.
* `DifferentialGraded.LeftModule.twoCellIncl` and
  `DifferentialGraded.LeftModule.twoCellProj`: the two maps exhibiting `⨁ᵢ Q_{kᵢ}` as an
  extension of `⨁ᵢ A[-kᵢ]` by `⨁ᵢ A[-kᵢ-1]`.
* `DifferentialGraded.LeftModule.freeCover`: the homomorphism `⨁ᵢ Q_{kᵢ} ⟶ N` attached to a
  family of homogeneous elements of `N`.

## Main results

* `DifferentialGraded.LeftModule.twoCellSum_isAdmissibleShortExact`: the sequence
  `0 → ⨁ᵢ A[-kᵢ-1] → ⨁ᵢ Q_{kᵢ} → ⨁ᵢ A[-kᵢ] → 0` is admissible short exact.
* `DifferentialGraded.LeftModule.induction_cocycle`: a cocycle is the finite sum of its
  homogeneous components, which are themselves cocycles.
* `DifferentialGraded.LeftModule.exists_cover`: Stacks 09KN for left differential graded
  modules.

## Implementation notes

*The grading of `⨁ᵢ Q_{kᵢ}` is borrowed, the differential is not.* The underlying graded left
module of `⨁ᵢ Q_{kᵢ}` is `⨁_{ι ⊕ ι} A` with the `inl i` summand in degrees shifted by `-kᵢ`
and the `inr i` summand by `-kᵢ-1`; that is exactly the grading of
`DifferentialGraded.LeftModule.directSumShifts A (twoCellShift k)`, so the grading and its
`DirectSum.Decomposition` instance are taken from there rather than reproved. The differential
is *not* the componentwise one: it carries the off-diagonal term `d(a xᵢ) = d(a) xᵢ ± a yᵢ`,
whose sign is `(-1)^{deg a}`. That sign is supplied by `DirectSum.parity A.grading`, which lets
the differential be written as one globally defined linear map; the only facts used about it are
`DirectSum.parity_apply_of_mem` and the anticommutation `parity ∘ d + d ∘ parity = 0`
(`parity_d_add_d_parity`).

*Everything is proved through component lemmas.* Maps into and out of `⨁_{ι ⊕ ι} A` are built
from the two index-relabelling primitives `inclIdx` (along an index map, by `DirectSum.toModule`)
and `projIdx` (along an injective index map, by `DFinsupp.comapDomain`), whose components are
described by `inclIdx_apply_eq`, `inclIdx_apply_of_ne` and `projIdx_apply`. The differential of
`twoCellSum` is only ever used through `twoCellSum`'s own `twoCellDiff_apply_inl` and
`twoCellDiff_apply_inr`, and through its values on the generators `DirectSum.lof` in
`twoCellDiff_lof_inl` and `twoCellDiff_lof_inr`.

*The grading does not see the cell kinds.* The flag `b` enters only through `cellParity`, which
is the coefficient of `yᵢ` in `d (a xᵢ)`; the grading, the two end terms of the admissible
sequence and the splittings are the same whatever `b` is. That is what keeps part (3)
independent of part (2): a bare index contributes `A[-kᵢ]` to the quotient and `A[-kᵢ-1]` to the
sub, exactly as a two-cell index does, the only difference being that there the extension is
split as a sequence of differential graded modules and not merely as a graded one.

*What is proved about `cellParity`.* Four facts, and the construction uses nothing else:
`cellParity_mem` (it preserves each graded piece, needed for `d_mem`),
`cellParity_d_add_d_cellParity` (it anticommutes with `d_A`, needed for `d ∘ d = 0`),
`cellParity_mul` (the Leibniz sign rule, needed for `leibniz`) and `cellParity_smul_d` (at a
bare index it has the same effect as the parity operator on `d (v i)`, because `v i` is then a
cocycle — needed for the cover map to be a chain map).

## References

* [Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN)
* [Stacks Project, Tag 09KT](https://stacks.math.columbia.edu/tag/09KT)
* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
-/

@[expose] public noncomputable section

open scoped DirectSum

universe u v

namespace DirectSum

/-- A degree-`+1` endomorphism of a graded module commutes with the graded projections, up to
the shift: the degree-`(n+1)` component of `d x` is `d` of the degree-`n` component of `x`. Both
sides are linear and agree on a homogeneous element of degree `m`, being `d` of it when `m = n`
and `0` otherwise. -/
theorem gradedProjection_comp_of_degree_one {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (g : ℤ → Submodule R M) [DirectSum.Decomposition g]
    (d : M →ₗ[R] M) (hd : ∀ (n : ℤ) (x : M), x ∈ g n → d x ∈ g (n + 1)) (n : ℤ) :
    DirectSum.gradedProjection g (n + 1) ∘ₗ d = d ∘ₗ DirectSum.gradedProjection g n := by
  refine DirectSum.linearMap_ext_of_mem g fun m y hy => ?_
  simp only [LinearMap.comp_apply]
  by_cases hmn : m = n
  · subst hmn
    rw [DirectSum.gradedProjection_of_mem_same g (hd m y hy),
      DirectSum.gradedProjection_of_mem_same g hy]
  · rw [DirectSum.gradedProjection_of_mem_ne g (hd m y hy) (by omega),
      DirectSum.gradedProjection_of_mem_ne g hy hmn, map_zero]

end DirectSum

-- Private: the public `DifferentialGradedAlgebra.d_one` lives in the Endomorphism tree, whose
-- import this module avoids.
/-- The differential of a differential graded algebra kills the unit: the Leibniz rule for
`1 = 1 · 1` reads `d 1 = 2 d 1`, since `1` has degree `0`. -/
private theorem algebraDifferential_one {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) : A.d 1 = 0 := by
  have h1 : (1 : A.A) ∈ A.grading 0 := SetLike.one_mem_graded A.grading
  simpa using A.leibniz 0 0 1 1 h1 h1

namespace DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- The homogeneous components of a cocycle are cocycles: the degree-`(n+1)` component of
`d x` is `d` of the degree-`n` component of `x`. -/
theorem d_gradedProjection (N : LeftModule A) (n : ℤ) (x : N.M) :
    N.d (DirectSum.gradedProjection N.grading n x)
      = DirectSum.gradedProjection N.grading (n + 1) (N.d x) :=
  (LinearMap.congr_fun
    (DirectSum.gradedProjection_comp_of_degree_one N.grading N.d N.d_mem n) x).symm

/-- A property that holds for every homogeneous cocycle and is closed under zero and addition
holds for every cocycle: a cocycle is the finite sum of its homogeneous components, and each of
those is a cocycle by `d_gradedProjection`. -/
theorem induction_cocycle {N : LeftModule A} {p : N.M → Prop} (x : N.M) (hx : N.d x = 0)
    (hhom : ∀ (n : ℤ) (y : N.M), y ∈ N.grading n → N.d y = 0 → p y) (hzero : p 0)
    (hadd : ∀ y z, p y → p z → p (y + z)) : p x := by
  classical
  have hcomp : ∀ n : ℤ, N.d ((DirectSum.decompose N.grading x n : N.M)) = 0 := by
    intro n
    have h := d_gradedProjection N n x
    rwa [hx, map_zero] at h
  have hsum : (∑ n ∈ DFinsupp.support (DirectSum.decompose N.grading x),
      ((DirectSum.decompose N.grading x) n : N.M)) = x :=
    DirectSum.sum_support_decompose N.grading x
  rw [← hsum]
  exact Finset.sum_induction _ p hadd hzero fun n _ =>
    hhom n _ (DirectSum.decompose N.grading x n).2 (hcomp n)

/-- A degree-zero map of graded left `A`-modules, not required to commute with the
differentials. -/
structure GradedHom (M N : LeftModule A) where
  /-- The underlying `R`-linear map. -/
  toFun : M.M →ₗ[R] N.M
  /-- Compatibility with the left `A`-action. -/
  map_smul : ∀ (a : A.A) (x : M.M), toFun (a • x) = a • toFun x
  /-- Compatibility with the gradings. -/
  map_grading : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → toFun x ∈ N.grading n

/-- Forget compatibility with the differential. -/
def Hom.toGradedHom {M N : LeftModule A} (f : Hom M N) : GradedHom M N where
  toFun := f.toFun
  map_smul := f.map_smul
  map_grading := f.map_grading

/-- A homomorphism of left differential graded modules is an admissible monomorphism if it has a
retraction by a map of graded left modules. -/
@[stacks 09JT "part (1)"]
abbrev IsAdmissibleMono {K L : LeftModule A} (f : Hom K L) : Prop :=
  ∃ π : GradedHom L K, ∀ x : K.M, π.toFun (f.toFun x) = x

/-- An admissible monomorphism is injective on the underlying module. -/
theorem IsAdmissibleMono.injective {K L : LeftModule A} {f : Hom K L}
    (hf : IsAdmissibleMono f) : Function.Injective f.toFun :=
  Function.LeftInverse.injective hf.choose_spec

/-- A homomorphism of left differential graded modules is an admissible epimorphism if it has a
section by a map of graded left modules. -/
@[stacks 09JT "part (2)"]
abbrev IsAdmissibleEpi {L M : LeftModule A} (g : Hom L M) : Prop :=
  ∃ s : GradedHom M L, ∀ x : M.M, g.toFun (s.toFun x) = x

/-- An admissible epimorphism is surjective on the underlying module. -/
theorem IsAdmissibleEpi.surjective {L M : LeftModule A} {g : Hom L M}
    (hg : IsAdmissibleEpi g) : Function.Surjective g.toFun :=
  Function.RightInverse.surjective hg.choose_spec

/-- A short exact sequence of left differential graded modules that splits as a sequence of
graded modules. -/
@[stacks 09JT "part (3)"]
structure IsAdmissibleShortExact {K L M : LeftModule A} (f : Hom K L) (g : Hom L M) : Prop where
  /-- The first map is injective. -/
  injective : Function.Injective f.toFun
  /-- The second map is surjective. -/
  surjective : Function.Surjective g.toFun
  /-- Exactness in the middle. -/
  exact : LinearMap.range f.toFun = LinearMap.ker g.toFun
  /-- The first map is split by a map of graded modules. -/
  admissibleMono : IsAdmissibleMono f
  /-- The second map is split by a map of graded modules. -/
  admissibleEpi : IsAdmissibleEpi g

/-! ### Relabelling the index of a direct sum -/

/-- Relabelling along an injective index map `f`, as a map of direct sums *out of* the larger
sum: the `i`-th component of the image is the `f i`-th component of the argument. -/
def projIdx {ι κ : Type u} [DecidableEq ι] (A : DifferentialGradedAlgebra R)
    (f : ι → κ) (hf : Function.Injective f) :
    (⨁ _ : κ, A.A) →ₗ[R] (⨁ _ : ι, A.A) where
  toFun x := DFinsupp.comapDomain f hf x
  map_add' x y := DirectSum.ext fun i => by
    simp [DFinsupp.comapDomain_apply]
  map_smul' c x := DirectSum.ext fun i => by
    simp [DFinsupp.comapDomain_apply, DirectSum.smul_apply]

/-- Components of a relabelling projection. -/
@[simp] theorem projIdx_apply {ι κ : Type u} [DecidableEq ι] (A : DifferentialGradedAlgebra R)
    (f : ι → κ) (hf : Function.Injective f) (x : ⨁ _ : κ, A.A) (i : ι) :
    projIdx A f hf x i = x (f i) := rfl

/-- Relabelling along an index map `f`, as a map of direct sums *into* the larger sum: the
`i`-th component of the argument is placed in the `f i`-th component. -/
def inclIdx {ι κ : Type u} [DecidableEq ι] [DecidableEq κ] (A : DifferentialGradedAlgebra R)
    (f : ι → κ) : (⨁ _ : ι, A.A) →ₗ[R] (⨁ _ : κ, A.A) :=
  DirectSum.toModule R ι _ (fun i => DirectSum.lof R κ (fun _ : κ => A.A) (f i))

/-- The components of a single summand: `b` at its own index and `0` elsewhere. -/
private theorem lof_apply_eq_ite {κ : Type u} [DecidableEq κ] (A : DifferentialGradedAlgebra R)
    (c c' : κ) (b : A.A) :
    DirectSum.lof R κ (fun _ : κ => A.A) c b c' = if c = c' then b else 0 := by
  by_cases h : c = c'
  · subst h; simp
  · simp only [h, ite_false]
    exact DirectSum.of_eq_of_ne (β := fun _ : κ => A.A) c c' b (Ne.symm h)

/-- A relabelling inclusion sends a single summand to the single summand at the relabelled
index. -/
private theorem inclIdx_lof {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    (A : DifferentialGradedAlgebra R) (f : ι → κ) (j : ι) (a : A.A) :
    inclIdx A f (DirectSum.lof R ι (fun _ : ι => A.A) j a)
      = DirectSum.lof R κ (fun _ : κ => A.A) (f j) a := by
  rw [inclIdx, DirectSum.toModule_lof]

/-- A relabelling inclusion reproduces the argument's components in the image of the index
map. -/
theorem inclIdx_apply_eq {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    (A : DifferentialGradedAlgebra R) {f : ι → κ} (hf : Function.Injective f)
    (x : ⨁ _ : ι, A.A) (i : ι) : inclIdx A f x (f i) = x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j a => simp [← DirectSum.lof_eq_of R, inclIdx_lof, lof_apply_eq_ite, hf.eq_iff]
  | add x y hx hy => simp [hx, hy]

/-- A relabelling inclusion vanishes outside the image of the index map. -/
theorem inclIdx_apply_of_ne {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    (A : DifferentialGradedAlgebra R) (f : ι → κ) (x : ⨁ _ : ι, A.A) {c : κ}
    (hc : ∀ i, f i ≠ c) : inclIdx A f x c = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j a => simp [← DirectSum.lof_eq_of R, inclIdx_lof, lof_apply_eq_ite, hc j]
  | add x y hx hy => simp [hx, hy]

/-- A componentwise family of maps of a direct sum of copies of one module acts
componentwise. -/
theorem mapRange_linearMap_apply {ι : Type u} (g : ι → (A.A →ₗ[R] A.A)) (x : ⨁ _ : ι, A.A)
    (i : ι) : (DFinsupp.mapRange.linearMap g x) i = g i (x i) :=
  DFinsupp.mapRange_apply _ (fun i => map_zero (g i)) x i

/-- The parity operator of a differential graded algebra anticommutes with the differential:
`parity (d a) + d (parity a) = 0`, since `d` shifts the degree by one. -/
theorem parity_d_add_d_parity (A : DifferentialGradedAlgebra R) (a : A.A) :
    DirectSum.parity A.grading (A.d a) + A.d (DirectSum.parity A.grading a) = 0 := by
  have h : (DirectSum.parity A.grading ∘ₗ A.d) + (A.d ∘ₗ DirectSum.parity A.grading)
      = (0 : A.A →ₗ[R] A.A) :=
    DirectSum.linearMap_ext_of_mem A.grading fun p y hy => by
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
        DirectSum.parity_apply_of_mem A.grading (A.d_mem p y hy),
        DirectSum.parity_apply_of_mem A.grading hy, map_zsmul, ← add_smul]
      simp [Int.negOnePow_succ]
  simpa using LinearMap.congr_fun h a

/-! ### Two-cell cover -/

/-- The algebra acts componentwise on a direct sum of copies of itself. -/
theorem directSum_smul_apply {ι : Type u} (a : A.A) (x : ⨁ _ : ι, A.A) (i : ι) :
    (a • x) i = a * x i := DirectSum.smul_apply a x i

/-- Integer scalars act componentwise on a direct sum of copies of the algebra. -/
theorem directSum_zsmul_apply {ι : Type u} (c : ℤ) (x : ⨁ _ : ι, A.A) (i : ι) :
    (c • x) i = c • x i :=
  map_zsmul (DFinsupp.evalAddMonoidHom i) c x

/-- The degree shifts of the summands of `⨁ᵢ Q_{kᵢ}`: the generator `xᵢ` of the `inl i` summand
sits in degree `kᵢ`, so that summand is `A[-kᵢ]`, and the generator `yᵢ` of the `inr i`
summand sits in degree `kᵢ + 1`, so that summand is `A[-kᵢ-1]`. -/
def twoCellShift {ι : Type u} (k : ι → ℤ) : ι ⊕ ι → ℤ :=
  Sum.elim (fun i => -k i) (fun i => -k i - 1)

/-- The shift of an `x`-summand. -/
@[simp] theorem twoCellShift_inl {ι : Type u} (k : ι → ℤ) (i : ι) :
    twoCellShift k (Sum.inl i) = -k i := rfl

/-- The shift of a `y`-summand. -/
@[simp] theorem twoCellShift_inr {ι : Type u} (k : ι → ℤ) (i : ι) :
    twoCellShift k (Sum.inr i) = -k i - 1 := rfl

/-- The componentwise differential on a direct sum of copies of the algebra. This is the
differential of `directSumShifts`, which for a *left* module carries no sign. -/
def diagDiff (A : DifferentialGradedAlgebra R) {ι : Type u} :
    (⨁ _ : ι, A.A) →ₗ[R] (⨁ _ : ι, A.A) :=
  DFinsupp.mapRange.linearMap (fun _ : ι => A.d)

/-- The componentwise differential acts componentwise. -/
@[simp] theorem diagDiff_apply {ι : Type u} (x : ⨁ _ : ι, A.A) (i : ι) :
    diagDiff A x i = A.d (x i) := mapRange_linearMap_apply (fun _ : ι => A.d) x i

/-! ### Two-cell indices and bare indices

An index `i` with `b i = false` carries a *two-cell* `Q_{kᵢ}`, whose generators satisfy
`d xᵢ = yᵢ`; an index with `b i = true` carries a *bare* cell, whose generator satisfies
`d xᵢ = 0`. The two are distinguished by a single coefficient, `cellParity`, which is the
coefficient of `yᵢ` in `d (a xᵢ)`. -/

/-- The coefficient of `yᵢ` in `d (a xᵢ)`: the parity operator of `A` at a two-cell index,
where `d xᵢ = yᵢ`, and zero at a bare index, where `d xᵢ = 0`. -/
def cellParity (A : DifferentialGradedAlgebra R) {ι : Type u} (b : ι → Bool) (i : ι) :
    A.A →ₗ[R] A.A :=
  bif b i then 0 else DirectSum.parity A.grading

/-- At a bare index the off-diagonal coefficient vanishes. -/
theorem cellParity_of_bare {ι : Type u} (b : ι → Bool) {i : ι} (hi : b i = true) :
    cellParity A b i = 0 := by
  rw [cellParity, hi, Bool.cond_true]

/-- At a two-cell index the off-diagonal coefficient is the parity operator. -/
theorem cellParity_of_twoCell {ι : Type u} (b : ι → Bool) {i : ι} (hi : b i = false) :
    cellParity A b i = DirectSum.parity A.grading := by
  rw [cellParity, hi, Bool.cond_false]

/-- The off-diagonal coefficient preserves each graded piece: the parity operator scales a
homogeneous element, and zero is homogeneous of every degree. -/
theorem cellParity_mem {ι : Type u} (b : ι → Bool) (i : ι) {n : ℤ} {y : A.A}
    (hy : y ∈ A.grading n) : cellParity A b i y ∈ A.grading n := by
  cases hi : b i
  · rw [cellParity_of_twoCell b hi]
    exact DirectSum.parity_mem A.grading hy
  · rw [cellParity_of_bare b hi]
    simp

/-- The off-diagonal coefficient anticommutes with the differential of `A`. At a two-cell index
this is `parity_d_add_d_parity`; at a bare index both terms vanish. -/
theorem cellParity_d_add_d_cellParity {ι : Type u} (b : ι → Bool) (i : ι) (y : A.A) :
    cellParity A b i (A.d y) + A.d (cellParity A b i y) = 0 := by
  cases hi : b i
  · rw [cellParity_of_twoCell b hi]
    exact parity_d_add_d_parity A y
  · rw [cellParity_of_bare b hi]
    simp

/-- The off-diagonal coefficient obeys the Leibniz sign rule: for `a` homogeneous of degree `m`
and `y` homogeneous, `cellParity (a y) = (-1)^m a · cellParity y`. At a two-cell index this is
the multiplicativity of the Koszul sign; at a bare index both sides vanish. -/
theorem cellParity_mul {ι : Type u} (b : ι → Bool) (i : ι) {m p : ℤ} {a y : A.A}
    (ha : a ∈ A.grading m) (hy : y ∈ A.grading p) :
    cellParity A b i (a * y) = (m.negOnePow : ℤ) • (a * cellParity A b i y) := by
  cases hi : b i
  · rw [cellParity_of_twoCell b hi,
      DirectSum.parity_apply_of_mem A.grading (SetLike.mul_mem_graded ha hy),
      DirectSum.parity_apply_of_mem A.grading hy,
      show ((m + p).negOnePow : ℤ) = (m.negOnePow : ℤ) * (p.negOnePow : ℤ) by
        rw [Int.negOnePow_add]; push_cast; ring,
      mul_smul_comm, smul_smul]
  · rw [cellParity_of_bare b hi]
    simp

/-- The off-diagonal part of the differential of `⨁ᵢ Q_{kᵢ}`: it reads the `x`-components, applies
the off-diagonal coefficient of each cell, and writes the result into the matching
`y`-components. This is the term `d(a xᵢ) = ⋯ + (-1)^{deg a} a yᵢ` of the Leibniz rule, which is
absent at a bare index. -/
def twoCellCross (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (b : ι → Bool) : (⨁ _ : ι ⊕ ι, A.A) →ₗ[R] (⨁ _ : ι ⊕ ι, A.A) :=
  (inclIdx A Sum.inr).comp
    ((DFinsupp.mapRange.linearMap (cellParity A b)).comp
      (projIdx A Sum.inl Sum.inl_injective))

/-- The off-diagonal part of the differential has no `x`-components. -/
@[simp] theorem twoCellCross_apply_inl {ι : Type u} [DecidableEq ι] (b : ι → Bool)
    (x : ⨁ _ : ι ⊕ ι, A.A) (i : ι) : twoCellCross A b x (Sum.inl i) = 0 :=
  inclIdx_apply_of_ne A Sum.inr _ (fun j => by simp)

/-- The `y`-components of the off-diagonal part of the differential. -/
@[simp] theorem twoCellCross_apply_inr {ι : Type u} [DecidableEq ι] (b : ι → Bool)
    (x : ⨁ _ : ι ⊕ ι, A.A) (i : ι) :
    twoCellCross A b x (Sum.inr i) = cellParity A b i (x (Sum.inl i)) := by
  rw [twoCellCross, LinearMap.comp_apply, inclIdx_apply_eq A Sum.inr_injective,
    LinearMap.comp_apply, mapRange_linearMap_apply, projIdx_apply]

/-- The differential of `⨁ᵢ Q_{kᵢ}`: the componentwise differential of `A` together with the
off-diagonal term carrying `xᵢ` to `yᵢ` at every two-cell index. -/
def twoCellDiff (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (b : ι → Bool) : (⨁ _ : ι ⊕ ι, A.A) →ₗ[R] (⨁ _ : ι ⊕ ι, A.A) :=
  diagDiff A + twoCellCross A b

/-- The `x`-components of the differential of `⨁ᵢ Q_{kᵢ}`. -/
@[simp] theorem twoCellDiff_apply_inl {ι : Type u} [DecidableEq ι] (b : ι → Bool)
    (x : ⨁ _ : ι ⊕ ι, A.A) (i : ι) :
    twoCellDiff A b x (Sum.inl i) = A.d (x (Sum.inl i)) := by
  rw [twoCellDiff, LinearMap.add_apply, DirectSum.add_apply, diagDiff_apply,
    twoCellCross_apply_inl, add_zero]

/-- The `y`-components of the differential of `⨁ᵢ Q_{kᵢ}`. -/
@[simp] theorem twoCellDiff_apply_inr {ι : Type u} [DecidableEq ι] (b : ι → Bool)
    (x : ⨁ _ : ι ⊕ ι, A.A) (i : ι) :
    twoCellDiff A b x (Sum.inr i) =
      cellParity A b i (x (Sum.inl i)) + A.d (x (Sum.inr i)) := by
  rw [twoCellDiff, LinearMap.add_apply, DirectSum.add_apply, diagDiff_apply,
    twoCellCross_apply_inr, add_comm]

/-- `⨁ᵢ Q_{kᵢ}`, the direct sum of the cells of the proof of Stacks 09KN, as a left
differential graded `A`-module. The underlying left module is `⨁_{ι ⊕ ι} A`, the `inl i`
summand being the free summand `A xᵢ` on a generator of degree `kᵢ` and the `inr i` summand the
free summand `A yᵢ` on a generator of degree `kᵢ + 1`; the grading is that of
`directSumShifts A (twoCellShift k)` and the differential is `twoCellDiff A b`.

The flag `b i` selects the kind of the `i`-th cell. At a *two-cell* index (`b i = false`) the
differential sends `xᵢ` to `yᵢ`, so the pair of summands is the two-cell module `Q_{kᵢ}` of the
source. At a *bare* index (`b i = true`) it sends `xᵢ` to `0`, so the pair of summands is the
split sum `A[-kᵢ] ⊕ A[-kᵢ-1]` of two shifts of `A` and `xᵢ` is a cocycle; those are the cells
the source adds in order to lift cocycles. -/
@[implicit_reducible]
def twoCellSum (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι] (k : ι → ℤ)
    (b : ι → Bool) : LeftModule A where
  M := ⨁ _ : ι ⊕ ι, A.A
  grading := (directSumShifts A (twoCellShift k)).grading
  decomposition := (directSumShifts A (twoCellShift k)).decomposition
  isScalarTower := (directSumShifts A (twoCellShift k)).isScalarTower
  smul_mem := (directSumShifts A (twoCellShift k)).smul_mem
  d := twoCellDiff A b
  d_comp_d := by
    refine LinearMap.ext fun x => DirectSum.ext fun c => ?_
    change twoCellDiff A b (twoCellDiff A b x) c = 0
    cases c with
    | inl i =>
        rw [twoCellDiff_apply_inl, twoCellDiff_apply_inl]
        simpa using LinearMap.congr_fun A.d_comp_d (x (Sum.inl i))
    | inr i =>
        rw [twoCellDiff_apply_inr, twoCellDiff_apply_inl, twoCellDiff_apply_inr, map_add,
          show A.d (A.d (x (Sum.inr i))) = 0 by
            simpa using LinearMap.congr_fun A.d_comp_d (x (Sum.inr i)),
          add_zero, cellParity_d_add_d_cellParity]
  d_mem := by
    intro n x hx c
    cases c with
    | inl i =>
        rw [twoCellDiff_apply_inl,
          show n + 1 + twoCellShift k (Sum.inl i) = n + twoCellShift k (Sum.inl i) + 1 by
            simp only [twoCellShift_inl]; omega]
        exact A.d_mem _ _ (hx (Sum.inl i))
    | inr i =>
        rw [twoCellDiff_apply_inr]
        refine Submodule.add_mem _ ?_ ?_
        · rw [show n + 1 + twoCellShift k (Sum.inr i) = n + twoCellShift k (Sum.inl i) by
            simp only [twoCellShift_inl, twoCellShift_inr]; omega]
          exact cellParity_mem b i (hx (Sum.inl i))
        · rw [show n + 1 + twoCellShift k (Sum.inr i)
            = n + twoCellShift k (Sum.inr i) + 1 by simp only [twoCellShift_inr]; omega]
          exact A.d_mem _ _ (hx (Sum.inr i))
  leibniz := by
    intro m n a x ha hx
    refine DirectSum.ext fun c => ?_
    cases c with
    | inl i =>
        rw [twoCellDiff_apply_inl, DirectSum.add_apply, directSum_smul_apply,
          directSum_smul_apply, directSum_zsmul_apply, directSum_smul_apply,
          twoCellDiff_apply_inl]
        exact A.leibniz m _ a _ ha (hx (Sum.inl i))
    | inr i =>
        rw [twoCellDiff_apply_inr, DirectSum.add_apply, directSum_smul_apply,
          directSum_smul_apply, directSum_smul_apply, directSum_zsmul_apply,
          directSum_smul_apply, twoCellDiff_apply_inr,
          cellParity_mul b i ha (hx (Sum.inl i)),
          A.leibniz m _ a _ ha (hx (Sum.inr i))]
        simp only [mul_add, smul_add]
        abel

/-! ### The admissible short exact sequence -/

/-- Membership in the degree-`n` piece of `⨁ᵢ Q_{kᵢ}` is componentwise, with the shift of each
summand given by `twoCellShift`. -/
theorem mem_twoCellSum_grading {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (b : ι → Bool) (n : ℤ)
    (x : ⨁ _ : ι ⊕ ι, A.A) :
    x ∈ (twoCellSum A k b).grading n ↔ ∀ c, x c ∈ A.grading (n + twoCellShift k c) := Iff.rfl

/-- The differential of a direct sum of shifts is the componentwise one. -/
theorem directSumShifts_d_eq {ι : Type u} [DecidableEq ι] (j : ι → ℤ) (x : ⨁ _ : ι, A.A) :
    (directSumShifts A j).d x = diagDiff A x := rfl

/-- A relabelling projection is `A`-linear. -/
theorem projIdx_smul {ι κ : Type u} [DecidableEq ι] (A : DifferentialGradedAlgebra R)
    (f : ι → κ) (hf : Function.Injective f) (a : A.A) (x : ⨁ _ : κ, A.A) :
    projIdx A f hf (a • x) = a • projIdx A f hf x :=
  DirectSum.ext fun i => by
    rw [projIdx_apply, directSum_smul_apply, directSum_smul_apply, projIdx_apply]

/-- A relabelling inclusion is `A`-linear. -/
theorem inclIdx_smul {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    (A : DifferentialGradedAlgebra R) {f : ι → κ} (hf : Function.Injective f) (a : A.A)
    (x : ⨁ _ : ι, A.A) : inclIdx A f (a • x) = a • inclIdx A f x := by
  refine DirectSum.ext fun c => ?_
  by_cases hc : ∃ i, f i = c
  · obtain ⟨i, rfl⟩ := hc
    rw [inclIdx_apply_eq A hf, directSum_smul_apply, directSum_smul_apply,
      inclIdx_apply_eq A hf]
  · rw [inclIdx_apply_of_ne A f _ (fun i hi => hc ⟨i, hi⟩), directSum_smul_apply,
      inclIdx_apply_of_ne A f _ (fun i hi => hc ⟨i, hi⟩), mul_zero]

/-- Relabelling along `f` and back is the identity. -/
theorem projIdx_inclIdx {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    (A : DifferentialGradedAlgebra R) {f : ι → κ} (hf : Function.Injective f)
    (x : ⨁ _ : ι, A.A) : projIdx A f hf (inclIdx A f x) = x :=
  DirectSum.ext fun i => by rw [projIdx_apply, inclIdx_apply_eq A hf]

/-- Relabelling along `f` and then projecting along an index map with disjoint image
vanishes. -/
theorem projIdx_inclIdx_of_ne {ι ι' κ : Type u} [DecidableEq ι] [DecidableEq ι']
    [DecidableEq κ] (A : DifferentialGradedAlgebra R) (f : ι → κ) {g : ι' → κ}
    (hg : Function.Injective g) (h : ∀ i j, f i ≠ g j) (x : ⨁ _ : ι, A.A) :
    projIdx A g hg (inclIdx A f x) = 0 :=
  DirectSum.ext fun j => by
    rw [projIdx_apply, inclIdx_apply_of_ne A f _ (fun i => h i j)]
    simp

/-- An element of `⨁_{ι ⊕ ι} A` with no `x`-components is the image of its `y`-components. -/
theorem inclIdx_projIdx_inr (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (x : ⨁ _ : ι ⊕ ι, A.A) (hx : projIdx A Sum.inl Sum.inl_injective x = 0) :
    inclIdx A Sum.inr (projIdx A Sum.inr Sum.inr_injective x) = x := by
  have hx' : ∀ i, x (Sum.inl i) = 0 := fun i => by
    rw [← projIdx_apply A Sum.inl Sum.inl_injective x i, hx]
    simp
  refine DirectSum.ext fun c => ?_
  cases c with
  | inl i => rw [inclIdx_apply_of_ne A Sum.inr _ (fun j hj => by simp at hj), hx' i]
  | inr i => rw [inclIdx_apply_eq A Sum.inr_injective, projIdx_apply]

/-- The differential of `⨁ᵢ Q_{kᵢ}` restricts to the componentwise differential on the
`y`-summands: the inclusion of the `y`-summands is a chain map. -/
theorem twoCellDiff_inclIdx_inr (A : DifferentialGradedAlgebra R) {ι : Type u}
    [DecidableEq ι] (b : ι → Bool) (x : ⨁ _ : ι, A.A) :
    twoCellDiff A b (inclIdx A Sum.inr x) = inclIdx A Sum.inr (diagDiff A x) :=
  DirectSum.ext fun c => by
    cases c with
    | inl i =>
        rw [twoCellDiff_apply_inl,
          inclIdx_apply_of_ne A Sum.inr x (fun j hj => by simp at hj),
          inclIdx_apply_of_ne A Sum.inr (diagDiff A x) (fun j hj => by simp at hj), map_zero]
    | inr i =>
        rw [twoCellDiff_apply_inr,
          inclIdx_apply_of_ne A Sum.inr x (fun j hj => by simp at hj), map_zero, zero_add,
          inclIdx_apply_eq A Sum.inr_injective x i,
          inclIdx_apply_eq A Sum.inr_injective (diagDiff A x) i, diagDiff_apply]

/-- Projecting the differential of `⨁ᵢ Q_{kᵢ}` to the `x`-summands gives the componentwise
differential of the projection: the projection to the `x`-summands is a chain map. -/
theorem projIdx_twoCellDiff_inl (A : DifferentialGradedAlgebra R) {ι : Type u}
    [DecidableEq ι] (b : ι → Bool) (x : ⨁ _ : ι ⊕ ι, A.A) :
    projIdx A Sum.inl Sum.inl_injective (twoCellDiff A b x)
      = diagDiff A (projIdx A Sum.inl Sum.inl_injective x) :=
  DirectSum.ext fun i => by
    rw [projIdx_apply, twoCellDiff_apply_inl, diagDiff_apply, projIdx_apply]

/-- The inclusion `⨁ᵢ A[-kᵢ-1] ⟶ ⨁ᵢ Q_{kᵢ}` of the `y`-summands. -/
def twoCellIncl (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι] (k : ι → ℤ)
    (b : ι → Bool) : directSumShifts A (fun i => -k i - 1) ⟶ twoCellSum A k b where
  toFun := inclIdx A Sum.inr
  map_smul a x := inclIdx_smul A Sum.inr_injective a x
  map_grading n x hx := by
    intro c
    cases c with
    | inl i =>
        rw [inclIdx_apply_of_ne A Sum.inr x (fun j hj => by simp at hj)]
        simp
    | inr i =>
        rw [inclIdx_apply_eq A Sum.inr_injective x i, twoCellShift_inr]
        exact hx i
  map_d := LinearMap.ext fun x => by
    change inclIdx A Sum.inr (diagDiff A x) = twoCellDiff A b (inclIdx A Sum.inr x)
    exact (twoCellDiff_inclIdx_inr A b x).symm

/-- The projection `⨁ᵢ Q_{kᵢ} ⟶ ⨁ᵢ A[-kᵢ]` onto the `x`-summands. -/
def twoCellProj (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι] (k : ι → ℤ)
    (b : ι → Bool) : twoCellSum A k b ⟶ directSumShifts A (fun i => -k i) where
  toFun := projIdx A Sum.inl Sum.inl_injective
  map_smul a x := projIdx_smul A Sum.inl Sum.inl_injective a x
  map_grading n x hx := by
    intro i
    rw [projIdx_apply A Sum.inl Sum.inl_injective x i]
    exact hx (Sum.inl i)
  map_d := LinearMap.ext fun x => by
    change projIdx A Sum.inl Sum.inl_injective (twoCellDiff A b x)
      = diagDiff A (projIdx A Sum.inl Sum.inl_injective x)
    exact projIdx_twoCellDiff_inl A b x

/-- The retraction of `twoCellIncl` by a map of graded modules: project onto the `y`-summands.
It does not commute with the differentials, which is why the short exact sequence is admissible
rather than split. -/
def twoCellRetraction (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) (b : ι → Bool) :
    GradedHom (twoCellSum A k b) (directSumShifts A (fun i => -k i - 1)) where
  toFun := projIdx A Sum.inr Sum.inr_injective
  map_smul a x := projIdx_smul A Sum.inr Sum.inr_injective a x
  map_grading n x hx := by
    intro i
    rw [projIdx_apply A Sum.inr Sum.inr_injective x i]
    exact hx (Sum.inr i)

/-- The section of `twoCellProj` by a map of graded modules: include the `x`-summands. It does
not commute with the differentials. -/
def twoCellSection (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) (b : ι → Bool) :
    GradedHom (directSumShifts A (fun i => -k i)) (twoCellSum A k b) where
  toFun := inclIdx A Sum.inl
  map_smul a x := inclIdx_smul A Sum.inl_injective a x
  map_grading n x hx := by
    intro c
    cases c with
    | inl i =>
        rw [inclIdx_apply_eq A Sum.inl_injective x i, twoCellShift_inl]
        exact hx i
    | inr i =>
        rw [inclIdx_apply_of_ne A Sum.inl x (fun j hj => by simp at hj)]
        simp

/-- `⨁ᵢ Q_{kᵢ}` is an extension of `⨁ᵢ A[-kᵢ]` by `⨁ᵢ A[-kᵢ-1]` along an admissible short exact
sequence, whatever the kinds of its cells: the inclusion of the `y`-summands and the projection
to the `x`-summands are chain maps at a bare index too, since there the differential is the
componentwise one. This is part (3) of Stacks 09KN for left modules. -/
theorem twoCellSum_isAdmissibleShortExact (A : DifferentialGradedAlgebra R) {ι : Type u}
    [DecidableEq ι] (k : ι → ℤ) (b : ι → Bool) :
    IsAdmissibleShortExact (twoCellIncl A k b) (twoCellProj A k b) where
  injective := Function.LeftInverse.injective
    (g := fun x => projIdx A Sum.inr Sum.inr_injective x)
    (fun x => projIdx_inclIdx A Sum.inr_injective x)
  surjective := Function.RightInverse.surjective
    (g := fun x => inclIdx A Sum.inl x)
    (fun x => projIdx_inclIdx A Sum.inl_injective x)
  exact := by
    refine le_antisymm ?_ ?_
    · rintro z ⟨t, rfl⟩
      exact LinearMap.mem_ker.mpr
        (projIdx_inclIdx_of_ne A Sum.inr Sum.inl_injective (fun i j => by simp) t)
    · intro z hz
      exact ⟨projIdx A Sum.inr Sum.inr_injective z,
        inclIdx_projIdx_inr A z (LinearMap.mem_ker.mp hz)⟩
  admissibleMono := ⟨twoCellRetraction A k b, fun x => projIdx_inclIdx A Sum.inr_injective x⟩
  admissibleEpi := ⟨twoCellSection A k b, fun x => projIdx_inclIdx A Sum.inl_injective x⟩

/-! ### The cover of an arbitrary left module -/

/-- The algebra acts on a single summand of a direct sum of copies of itself by multiplication
in that summand. -/
theorem smul_lof {κ : Type u} [DecidableEq κ] (A : DifferentialGradedAlgebra R) (a : A.A)
    (c : κ) (b : A.A) :
    a • DirectSum.lof R κ (fun _ : κ => A.A) c b
      = DirectSum.lof R κ (fun _ : κ => A.A) c (a * b) :=
  DirectSum.ext fun c' => by
    simp [directSum_smul_apply, lof_apply_eq_ite]

/-- Multiplication of a fixed module element by algebra scalars, as an `R`-linear map
`A → N`. -/
def smulRight (N : LeftModule A) (y : N.M) : A.A →ₗ[R] N.M where
  toFun a := a • y
  map_add' a b := add_smul a b y
  map_smul' r a := smul_assoc r a y

/-- Values of `smulRight`. -/
theorem smulRight_apply (N : LeftModule A) (y : N.M) (a : A.A) : smulRight N y a = a • y := rfl

/-- Integer scalars pass through the action of the algebra. -/
theorem zsmul_smul_assoc (N : LeftModule A) (c : ℤ) (a : A.A) (y : N.M) :
    (c • a) • y = c • (a • y) := map_zsmul (smulRight N y) c a

/-- The left Leibniz rule with the degree-dependent sign absorbed into the parity operator:
for a homogeneous `y` and an arbitrary `a`,
`d (a y) = d(a) y + (parity a) d(y)`. -/
theorem d_smul_eq (N : LeftModule A) {n : ℤ} {y : N.M} (hy : y ∈ N.grading n) (a : A.A) :
    N.d (a • y) = A.d a • y + DirectSum.parity A.grading a • N.d y := by
  have h : N.d ∘ₗ smulRight N y
      = smulRight N y ∘ₗ A.d + smulRight N (N.d y) ∘ₗ DirectSum.parity A.grading :=
    DirectSum.linearMap_ext_of_mem A.grading fun p b hb => by
      show N.d (b • y) = A.d b • y + (DirectSum.parity A.grading b) • N.d y
      rw [N.leibniz p n b y hb hy, DirectSum.parity_apply_of_mem A.grading hb,
        zsmul_smul_assoc N]
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, smulRight_apply] using
    LinearMap.congr_fun h a

/-- The component of a single summand at its own index. -/
theorem lof_apply_same {κ : Type u} [DecidableEq κ] (A : DifferentialGradedAlgebra R) (c : κ)
    (a : A.A) : (DirectSum.lof R κ (fun _ : κ => A.A) c a) c = a := by
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]

/-- The components of a single summand away from its index. -/
theorem lof_apply_ne {κ : Type u} [DecidableEq κ] (A : DifferentialGradedAlgebra R) {c c' : κ}
    (hc : c' ≠ c) (a : A.A) : (DirectSum.lof R κ (fun _ : κ => A.A) c a) c' = 0 := by
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_of_ne (β := fun _ : κ => A.A) c c' a hc

/-- The differential on the generator `xᵢ` of a single `x`-summand: `d (a xᵢ)` has
`x`-component `d(a)` and `y`-component `cellParity a`, which is `(-1)^{deg a} a` at a two-cell
index and `0` at a bare one. -/
theorem twoCellDiff_lof_inl (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (b : ι → Bool) (i : ι) (a : A.A) :
    twoCellDiff A b (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inl i) a)
      = DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inl i) (A.d a)
        + DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inr i)
            (cellParity A b i a) :=
  DirectSum.ext fun c => by
    rcases c with p | p <;> by_cases h : i = p <;> simp [lof_apply_eq_ite, h]

/-- The differential on the generator `yᵢ` of a single `y`-summand: `d (a yᵢ) = d(a) yᵢ`. -/
theorem twoCellDiff_lof_inr (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (b : ι → Bool) (i : ι) (a : A.A) :
    twoCellDiff A b (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inr i) a)
      = DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inr i) (A.d a) :=
  DirectSum.ext fun c => by
    rcases c with p | p <;> by_cases h : i = p <;> simp [lof_apply_eq_ite, h]

/-- The `R`-linear map `⨁ᵢ Q_{kᵢ} → N` attached to a family `v` of elements of `N`: it sends the
generator `xᵢ` to `v i` and the generator `yᵢ` to `d (v i)`. -/
def freeCoverMap (N : LeftModule A) {ι : Type u} [DecidableEq ι] (v : ι → N.M) :
    (⨁ _ : ι ⊕ ι, A.A) →ₗ[R] N.M :=
  DirectSum.toModule R (ι ⊕ ι) N.M
    (Sum.elim (fun i => smulRight N (v i)) (fun i => smulRight N (N.d (v i))))

/-- The value of the cover map on an `x`-generator. -/
theorem freeCoverMap_lof_inl (N : LeftModule A) {ι : Type u} [DecidableEq ι] (v : ι → N.M)
    (i : ι) (a : A.A) :
    freeCoverMap N v (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inl i) a)
      = a • v i := by
  rw [freeCoverMap, DirectSum.toModule_lof]
  rfl

/-- The value of the cover map on a `y`-generator. -/
theorem freeCoverMap_lof_inr (N : LeftModule A) {ι : Type u} [DecidableEq ι] (v : ι → N.M)
    (i : ι) (a : A.A) :
    freeCoverMap N v (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inr i) a)
      = a • N.d (v i) := by
  rw [freeCoverMap, DirectSum.toModule_lof]
  rfl

/-- The cover map is `A`-linear. -/
theorem freeCoverMap_smul (N : LeftModule A) {ι : Type u} [DecidableEq ι] (v : ι → N.M)
    (a : A.A) (x : ⨁ _ : ι ⊕ ι, A.A) :
    freeCoverMap N v (a • x) = a • freeCoverMap N v x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of c b =>
      rw [← DirectSum.lof_eq_of R, smul_lof]
      cases c with
      | inl i => rw [freeCoverMap_lof_inl, freeCoverMap_lof_inl, mul_smul]
      | inr i => rw [freeCoverMap_lof_inr, freeCoverMap_lof_inr, mul_smul]
  | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]

/-- The cover map attached to a family of homogeneous elements is compatible with the gradings:
`xᵢ` has the degree of `v i` and `yᵢ` the degree of `d (v i)`. -/
theorem freeCoverMap_mem_grading (N : LeftModule A) {ι : Type u} [DecidableEq ι]
    (v : ι → N.M) (j : ι → ℤ) (hv : ∀ i, v i ∈ N.grading (j i)) (n : ℤ)
    (x : ⨁ _ : ι ⊕ ι, A.A) (hx : ∀ c, x c ∈ A.grading (n + twoCellShift j c)) :
    freeCoverMap N v x ∈ N.grading n := by
  classical
  rw [← DirectSum.sum_support_of x, map_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [← DirectSum.lof_eq_of R]
  have key : ∀ (m p : ℤ) (a : A.A) (y : N.M), n = m + p → a ∈ A.grading m → y ∈ N.grading p →
      a • y ∈ N.grading n := fun m p a y h ha hy => h ▸ N.smul_mem m p a y ha hy
  cases c with
  | inl i =>
      rw [freeCoverMap_lof_inl]
      exact key _ _ _ _ (by simp only [twoCellShift_inl]; omega) (hx (Sum.inl i)) (hv i)
  | inr i =>
      rw [freeCoverMap_lof_inr]
      exact key _ _ _ _ (by simp only [twoCellShift_inr]; omega) (hx (Sum.inr i))
        (N.d_mem (j i) (v i) (hv i))

/-- At a bare index the cover map kills the `y`-generator: the element covered there is a
cocycle, so the two coefficients that can appear in the Leibniz rule have the same effect on
`d (v i)`. -/
theorem cellParity_smul_d (N : LeftModule A) {ι : Type u} (b : ι → Bool) (v : ι → N.M)
    (hb : ∀ i, b i = true → N.d (v i) = 0) (i : ι) (a : A.A) :
    cellParity A b i a • N.d (v i) = DirectSum.parity A.grading a • N.d (v i) := by
  cases hi : b i
  · rw [cellParity_of_twoCell b hi]
  · rw [hb i hi, smul_zero, smul_zero]

/-- The cover map attached to a family of homogeneous elements is a chain map. This is the
Leibniz rule in `N`: on the generator `xᵢ` both sides are `d(a) v i + (parity a) d(v i)`, the
second term vanishing at a bare index because `v i` is then a cocycle. -/
theorem freeCoverMap_twoCellDiff (N : LeftModule A) {ι : Type u} [DecidableEq ι]
    (v : ι → N.M) (j : ι → ℤ) (hv : ∀ i, v i ∈ N.grading (j i)) (b : ι → Bool)
    (hb : ∀ i, b i = true → N.d (v i) = 0) (x : ⨁ _ : ι ⊕ ι, A.A) :
    freeCoverMap N v (twoCellDiff A b x) = N.d (freeCoverMap N v x) := by
  have h : freeCoverMap N v ∘ₗ twoCellDiff A b = N.d ∘ₗ freeCoverMap N v := by
    refine DirectSum.linearMap_ext (R := R) fun c => LinearMap.ext fun a => ?_
    cases c with
    | inl i =>
        show freeCoverMap N v (twoCellDiff A b
          (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inl i) a))
          = N.d (freeCoverMap N v
            (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inl i) a))
        rw [twoCellDiff_lof_inl, map_add, freeCoverMap_lof_inl, freeCoverMap_lof_inr,
          freeCoverMap_lof_inl, cellParity_smul_d N b v hb i a, d_smul_eq N (hv i)]
    | inr i =>
        show freeCoverMap N v (twoCellDiff A b
          (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inr i) a))
          = N.d (freeCoverMap N v
            (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inr i) a))
        rw [twoCellDiff_lof_inr, freeCoverMap_lof_inr, freeCoverMap_lof_inr,
          d_smul_eq N (N.d_mem (j i) (v i) (hv i))]
        have hdd : N.d (N.d (v i)) = 0 := by
          simpa using LinearMap.congr_fun N.d_comp_d (v i)
        rw [hdd, smul_zero, add_zero]
  exact LinearMap.congr_fun h x

/-- The homomorphism `⨁ᵢ Q_{kᵢ} ⟶ N` of left differential graded modules attached to a family
`v` of homogeneous elements of `N` of degrees `j`, sending the generator `xᵢ` to `v i` and the
generator `yᵢ` to `d (v i)`. At a bare index the element `v i` is required to be a cocycle, so
that the generator `xᵢ`, which is itself a cocycle there, maps to one. -/
def freeCover (N : LeftModule A) {ι : Type u} [DecidableEq ι] (v : ι → N.M) (j : ι → ℤ)
    (hv : ∀ i, v i ∈ N.grading (j i)) (b : ι → Bool)
    (hb : ∀ i, b i = true → N.d (v i) = 0) : twoCellSum A j b ⟶ N where
  toFun := freeCoverMap N v
  map_smul a x := freeCoverMap_smul N v a x
  map_grading n x hx := freeCoverMap_mem_grading N v j hv n x hx
  map_d := LinearMap.ext fun x => freeCoverMap_twoCellDiff N v j hv b hb x

/-- A cover map whose index set realizes every homogeneous element of `N` is surjective: a
homogeneous `m ∈ Nⁿ` is the image of the generator `x` of its own summand, and every element of
`N` is a finite sum of homogeneous ones. -/
theorem freeCoverMap_surjective (N : LeftModule A) {ι : Type u} [DecidableEq ι] (v : ι → N.M)
    (hv : ∀ (n : ℤ) (z : N.M), z ∈ N.grading n → ∃ i, v i = z) :
    Function.Surjective (freeCoverMap N v) := by
  intro y
  refine induction_homogeneous (M := N)
    (p := fun z => ∃ w, freeCoverMap N v w = z) y ?_ ?_ ?_
  · intro n z hz
    obtain ⟨i, hi⟩ := hv n z hz
    refine ⟨DirectSum.lof R _ (fun _ => A.A) (Sum.inl i) 1, ?_⟩
    rw [freeCoverMap_lof_inl, one_smul, hi]
  · exact ⟨0, map_zero _⟩
  · rintro z w ⟨zz, rfl⟩ ⟨ww, rfl⟩
    exact ⟨zz + ww, map_add _ _ _⟩

/-- The generator `xᵢ` is homogeneous of degree `kᵢ`: its only nonzero component is `1`, in a
summand shifted by `-kᵢ`. -/
theorem lof_inl_one_mem_grading (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) (b : ι → Bool) (i : ι) :
    DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inl i) 1
      ∈ (twoCellSum A k b).grading (k i) := by
  rw [mem_twoCellSum_grading]
  intro c
  rw [lof_apply_eq_ite]
  split_ifs with h
  · subst h
    simpa using SetLike.one_mem_graded A.grading
  · exact Submodule.zero_mem _

/-- At a bare index the generator `xᵢ` is a cocycle of `⨁ᵢ Q_{kᵢ}`: the off-diagonal term of the
differential is absent there, and `d 1 = 0`. -/
theorem twoCellDiff_lof_inl_one_of_bare (A : DifferentialGradedAlgebra R) {ι : Type u}
    [DecidableEq ι] (b : ι → Bool) {i : ι} (hi : b i = true) :
    twoCellDiff A b (DirectSum.lof R (ι ⊕ ι) (fun _ : ι ⊕ ι => A.A) (Sum.inl i) 1) = 0 := by
  rw [twoCellDiff_lof_inl, algebraDifferential_one, cellParity_of_bare b hi]
  simp

/-- **Stacks 09KN for left differential graded modules.** Let `(A, d)` be a differential graded
algebra over a commutative ring `R` and let `N` be a *left* differential graded `A`-module. Then
there are a family of degrees `k : ι → ℤ`, a family of cell kinds `b : ι → Bool` and a
homomorphism `f : ⨁ᵢ Q_{kᵢ} ⟶ N` such that

1. `f` is surjective;
2. a homogeneous cocycle of `N` of degree `m` is the image of a cocycle of degree `m`, and
   consequently `Ker(d) → Ker(d_N)` is surjective — part (2) of the source lemma; and
3. `⨁ᵢ Q_{kᵢ}` sits in an admissible short exact sequence
   `0 → ⨁ᵢ A[-kᵢ-1] → ⨁ᵢ Q_{kᵢ} → ⨁ᵢ A[-kᵢ] → 0`

whose two ends are direct sums of shifts of `A`.

The cover is indexed by the homogeneous elements of `N`, which give two-cells and supply (1),
together with the homogeneous *cocycles* of `N`, which give bare cells and supply (2): the
generator `xᵢ` of a bare cell is itself a cocycle, homogeneous of degree `kᵢ`, and it maps to
the cocycle it indexes. A general cocycle of `N` is the finite sum of its homogeneous
components, which are cocycles by `induction_cocycle`.

The degreewise form of (2) is recorded as well as the plain one because that is what the proof
of Stacks 09KT needs: the differential of a graded dual is precomposition with the *signed*
differential, and the sign is only known on a homogeneous element. -/
@[stacks 09KN]
theorem exists_cover (A : DifferentialGradedAlgebra R) (N : LeftModule A) :
    ∃ (ι : Type u) (_ : DecidableEq ι) (k : ι → ℤ) (b : ι → Bool)
      (f : twoCellSum A k b ⟶ N),
      Function.Surjective f.toFun ∧
      (∀ (m : ℤ) (z : N.M), z ∈ N.grading m → N.d z = 0 →
        ∃ q : (twoCellSum A k b).M, q ∈ (twoCellSum A k b).grading m ∧
          (twoCellSum A k b).d q = 0 ∧ f.toFun q = z) ∧
      (∀ z : N.M, N.d z = 0 →
        ∃ q : (twoCellSum A k b).M, (twoCellSum A k b).d q = 0 ∧ f.toFun q = z) ∧
      ∃ (i : directSumShifts A (fun c => -k c - 1) ⟶ twoCellSum A k b)
        (p : twoCellSum A k b ⟶ directSumShifts A (fun c => -k c)),
        IsAdmissibleShortExact i p := by
  classical
  let H : Type u := Σ n : ℤ, (N.grading n : Type u)
  let Z : Type u := Σ n : ℤ, {z : (N.grading n : Type u) // N.d (z : N.M) = 0}
  let I : Type u := H ⊕ Z
  let k : I → ℤ := Sum.elim (fun c : H => c.1) (fun c : Z => c.1)
  let b : I → Bool := Sum.elim (fun _ : H => false) (fun _ : Z => true)
  let v : I → N.M := Sum.elim (fun c : H => (c.2 : N.M)) (fun c : Z => (c.2.1 : N.M))
  have hv : ∀ i : I, v i ∈ N.grading (k i) := by
    intro i
    cases i with
    | inl c => exact c.2.2
    | inr c => exact c.2.1.2
  have hb : ∀ i : I, b i = true → N.d (v i) = 0 := by
    intro i hi
    cases i with
    | inl c => exact absurd hi (by simp [b])
    | inr c => exact c.2.2
  have hhom : ∀ (m : ℤ) (y : N.M), y ∈ N.grading m → N.d y = 0 →
      ∃ q : (twoCellSum A k b).M, q ∈ (twoCellSum A k b).grading m ∧
        (twoCellSum A k b).d q = 0 ∧ (freeCover N v k hv b hb).toFun q = y := by
    intro m y hy hdy
    refine ⟨DirectSum.lof R (I ⊕ I) (fun _ : I ⊕ I => A.A)
      (Sum.inl (Sum.inr ⟨m, ⟨⟨y, hy⟩, hdy⟩⟩)) 1, ?_, ?_, ?_⟩
    · exact lof_inl_one_mem_grading A k b (Sum.inr ⟨m, ⟨⟨y, hy⟩, hdy⟩⟩)
    · exact twoCellDiff_lof_inl_one_of_bare A b (by simp [b])
    · show freeCoverMap N v _ = y
      rw [freeCoverMap_lof_inl, one_smul]
      rfl
  refine ⟨I, inferInstance, k, b, freeCover N v k hv b hb, ?_, hhom, ?_,
    twoCellIncl A k b, twoCellProj A k b, twoCellSum_isAdmissibleShortExact A k b⟩
  · exact freeCoverMap_surjective N v fun n z hz => ⟨Sum.inl ⟨n, ⟨z, hz⟩⟩, rfl⟩
  · intro z hz
    refine induction_cocycle (N := N)
      (p := fun w => ∃ q : (twoCellSum A k b).M,
        (twoCellSum A k b).d q = 0 ∧ (freeCover N v k hv b hb).toFun q = w) z hz ?_ ?_ ?_
    · intro m y hy hdy
      obtain ⟨q, -, hq, hfq⟩ := hhom m y hy hdy
      exact ⟨q, hq, hfq⟩
    · exact ⟨0, map_zero _, map_zero _⟩
    · rintro y w ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
      exact ⟨q + q', by rw [map_add, hq, hq', add_zero], map_add _ _ _⟩

end DifferentialGraded.LeftModule

end

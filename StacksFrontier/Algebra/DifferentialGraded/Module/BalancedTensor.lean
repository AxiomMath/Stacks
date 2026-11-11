module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.LeftModule

/-!
# The tensor product of a right and a left differential graded module

Let `R` be a commutative ring, `(A, d)` a differential graded `R`-algebra, `M'` a right
differential graded `A`-module and `M` a left differential graded `A`-module. The tensor product
`M' ⊗_A M` is the complex of `R`-modules whose degree-`n` term is the quotient of
`⨁_{p + q = n} (M')^p ⊗_R M^q` by the balancing relations `x a ⊗ y - x ⊗ a y`, with differential
`d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` for `x` of degree `p`. Maps of complexes out of it are
exactly the balanced bilinear maps `M' × M → N` compatible with the differentials.

## Main definitions

* `DifferentialGraded.BalancedBilinear`: a bilinear map `M' × M → Q` on homogeneous pieces which
  is `A`-balanced and satisfies the signed Leibniz rule.
* `DifferentialGraded.tensorComplex` ([stacks 09LL]): the tensor product `M' ⊗_A M` as a
  complex of `R`-modules.
* `DifferentialGraded.tensorTmul` ([stacks 09LL]): the universal balanced bilinear map
  `(x, y) ↦ x ⊗ y`.
* `DifferentialGraded.tensorDesc`: the map of complexes induced by a balanced bilinear map.

## Main results

* `DifferentialGraded.tensorHomEquiv` ([stacks 09LL]): the universal property
  `Hom_{Comp(R)}(M' ⊗_A M, Q) = BalancedBilinear_A(M' × M, Q)`.
* `DifferentialGraded.tensorComplex_hom_ext`: a map of complexes out of `M' ⊗_A M` is determined
  by its values on homogeneous pure tensors.

## Implementation notes

The degree-`n` term is built as a quotient of the direct sum `⨁_i (M')^i ⊗_R M^{n - i}` indexed by
the degree of the left factor alone, so that an element of a homogeneous piece is placed by
`tensorMk` and the comparison of two placements reduces to comparing underlying elements
(`tensorMk_ext2`). Stability of the differential under the balancing relations is the single
computation `tensorRawD_relator`, which expresses the differential of one relation as a signed
combination of the three relations obtained by differentiating `x`, `a` and `y`.

The direct sum of tensor products of homogeneous pieces carries two definitionally equal but
syntactically distinct additive structures, which blocks the search for the quotient; the
reducible `tensorRawAddCommGroup` and `tensorRawAddCommMonoid` fix one of them as a local
instance, as elsewhere in this directory.

## References

* [Stacks Project, Tag 09LL](https://stacks.math.columbia.edu/tag/09LL)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct DirectSum

universe u v

namespace DifferentialGraded

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-- Re-indexing a homogeneous piece along an equality of degrees. -/
def gradingCast {X : Type*} [AddCommGroup X] [Module R X] (G : ℤ → Submodule R X)
    {q q' : ℤ} (h : q = q') : G q →ₗ[R] G q' where
  toFun x := ⟨(x : X), h ▸ x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `gradingCast` does not change the underlying element. -/
@[simp] theorem gradingCast_coe {X : Type*} [AddCommGroup X] [Module R X]
    (G : ℤ → Submodule R X) {q q' : ℤ} (h : q = q') (x : G q) :
    ((gradingCast G h x : G q') : X) = (x : X) := rfl

/-! ## Balanced bilinear maps -/

/-- A balanced bilinear map of differential graded modules. -/
structure BalancedBilinear (M' : DifferentialGradedModule.{u, v, u} A)
    (M : LeftModule A) (Q : CochainComplex (ModuleCat.{u} R) ℤ) where
  map : ∀ p q n : ℤ, p + q = n → M'.grading p →ₗ[R] M.grading q →ₗ[R] Q.X n
  balance : ∀ (p i q n : ℤ) (h₁ : p + i + q = n) (h₂ : p + (i + q) = n)
      (x : M'.grading p) (a : A.grading i) (y : M.grading q),
    map (p + i) q n h₁
        ⟨MulOpposite.op (a : A.A) • (x : M'.M), M'.smul_mem p i x a x.2 a.2⟩ y =
      map p (i + q) n h₂ x ⟨(a : A.A) • (y : M.M), M.smul_mem i q a y a.2 y.2⟩
  map_d : ∀ (p q n : ℤ) (h : p + q = n) (x : M'.grading p) (y : M.grading q),
    Q.d n (n + 1) (map p q n h x y) =
      map (p + 1) q (n + 1) (by omega) ⟨M'.d x, M'.d_mem p x x.2⟩ y +
        (p.negOnePow : ℤ) • map p (q + 1) (n + 1) (by omega) x ⟨M.d y, M.d_mem q y y.2⟩

/-- Two balanced bilinear maps with the same components agree. -/
theorem BalancedBilinear.ext {M' : DifferentialGradedModule.{u, v, u} A}
    {M : LeftModule A} {Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {b c : BalancedBilinear M' M Q}
    (h : ∀ (p q n : ℤ) (hpq : p + q = n) (x : M'.grading p) (y : M.grading q),
      b.map p q n hpq x y = c.map p q n hpq x y) : b = c := by
  have hm : b.map = c.map := by
    funext p q n hpq
    exact LinearMap.ext fun x => LinearMap.ext fun y => h p q n hpq x y
  cases b; cases c; cases hm; rfl

/-! ## The tensor product -/

variable (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)

/-- The degree-`n` part of the tensor product of the underlying graded modules over `R`. -/
abbrev tensorRaw (n : ℤ) : Type u := ⨁ i : ℤ, (M'.grading i ⊗[R] M.grading (n - i))

/-- The additive group structure of the direct sum `tensorRaw M' M n`. -/
@[reducible] noncomputable def tensorRawAddCommGroup (n : ℤ) :
    AddCommGroup (tensorRaw M' M n) := by
  classical
  unfold tensorRaw
  infer_instance

attribute [local instance] tensorRawAddCommGroup

/-- The additive monoid underlying `tensorRawAddCommGroup`. -/
@[reducible] noncomputable def tensorRawAddCommMonoid (n : ℤ) :
    AddCommMonoid (tensorRaw M' M n) :=
  (tensorRawAddCommGroup M' M n).toAddCommMonoid

attribute [local instance 2000] tensorRawAddCommMonoid

/-- The bilinear map placing `x ⊗ y` in degree `p + q` of `tensorRaw`. -/
noncomputable def tensorMk (n p q : ℤ) (h : p + q = n) :
    M'.grading p →ₗ[R] M.grading q →ₗ[R] tensorRaw M' M n :=
  (((TensorProduct.mk R (M'.grading p) (M.grading (n - p))).compl₂
      (gradingCast M.grading (show q = n - p by omega))).compr₂
    (DirectSum.lof R ℤ (fun i => M'.grading i ⊗[R] M.grading (n - i)) p))

/-- The degree-`i` component of the differential of `tensorRaw`. -/
noncomputable def tensorRawDComp (n i : ℤ) :
    M'.grading i →ₗ[R] M.grading (n - i) →ₗ[R] tensorRaw M' M (n + 1) :=
  (tensorMk M' M (n + 1) (i + 1) (n - i) (by omega)).comp (M'.gradedDifferential i) +
    (i.negOnePow : ℤ) •
      (tensorMk M' M (n + 1) i (n - i + 1) (by omega)).compl₂
        (LeftModule.gradedDifferential A M (n - i))

/-- The differential of `tensorRaw`, `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y`. -/
noncomputable def tensorRawD (n : ℤ) : tensorRaw M' M n →ₗ[R] tensorRaw M' M (n + 1) :=
  DirectSum.toModule R ℤ _ fun i => TensorProduct.lift (tensorRawDComp M' M n i)

/-- `tensorMk` depends on the second degree only through the underlying element. -/
theorem tensorMk_ext (n p q q' : ℤ) (h : p + q = n) (h' : p + q' = n)
    (x : M'.grading p) (y : M.grading q) (y' : M.grading q')
    (hy : (y : M.M) = (y' : M.M)) :
    tensorMk M' M n p q h x y = tensorMk M' M n p q' h' x y' := by
  have hq : q = q' := by omega
  subst hq
  obtain rfl : y = y' := Subtype.ext hy
  rfl

/-- The differential of `tensorRaw` on a homogeneous pure tensor:
`d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` for `x` of degree `p`. -/
theorem tensorRawD_mk (n p q : ℤ) (h : p + q = n) (x : M'.grading p) (y : M.grading q) :
    tensorRawD M' M n (tensorMk M' M n p q h x y) =
      tensorMk M' M (n + 1) (p + 1) q (by omega) (M'.gradedDifferential p x) y +
        (p.negOnePow : ℤ) •
          tensorMk M' M (n + 1) p (q + 1) (by omega) x
            (LeftModule.gradedDifferential A M q y) := by
  have h1 : tensorRawD M' M n (tensorMk M' M n p q h x y) =
      tensorRawDComp M' M n p x (gradingCast M.grading (show q = n - p by omega) y) := by
    change tensorRawD M' M n (DirectSum.lof R ℤ
      (fun i => M'.grading i ⊗[R] M.grading (n - i)) p
      (x ⊗ₜ[R] gradingCast M.grading (show q = n - p by omega) y)) = _
    rw [tensorRawD, DirectSum.toModule_lof]
    rfl
  rw [h1, tensorRawDComp]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.compl₂_apply]
  rw [tensorMk_ext M' M (n + 1) (p + 1) (n - p) q (by omega) (by omega)
    (M'.gradedDifferential p x) _ y rfl]
  rw [tensorMk_ext M' M (n + 1) p (n - p + 1) (q + 1) (by omega) (by omega) x
    (LeftModule.gradedDifferential A M (n - p)
      (gradingCast M.grading (show q = n - p by omega) y))
    (LeftModule.gradedDifferential A M q y) rfl]

/-- `tensorMk` depends on its two arguments only through their underlying elements. -/
theorem tensorMk_ext2 (n p q p' q' : ℤ) (h : p + q = n) (h' : p' + q' = n) (hp : p = p')
    (x : M'.grading p) (y : M.grading q) (x' : M'.grading p') (y' : M.grading q')
    (hx : (x : M'.M) = (x' : M'.M)) (hy : (y : M.M) = (y' : M.M)) :
    tensorMk M' M n p q h x y = tensorMk M' M n p' q' h' x' y' := by
  subst hp
  have hq : q = q' := by omega
  subst hq
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

/-- `tensorMk` in degrees `i` and `n - i` is the inclusion of `x ⊗ y` into the `i`-th summand. -/
theorem tensorMk_self (n i : ℤ) (h : i + (n - i) = n) (x : M'.grading i)
    (y : M.grading (n - i)) :
    tensorMk M' M n i (n - i) h x y =
      DirectSum.lof R ℤ (fun j => M'.grading j ⊗[R] M.grading (n - j)) i (x ⊗ₜ[R] y) := rfl

/-- Linear maps out of `tensorRaw` agree once they agree on the homogeneous pure tensors. -/
theorem tensorRaw_ext {n : ℤ} {Q : Type u} [AddCommGroup Q] [Module R Q]
    {f g : tensorRaw M' M n →ₗ[R] Q}
    (h : ∀ (p q : ℤ) (hpq : p + q = n) (x : M'.grading p) (y : M.grading q),
      f (tensorMk M' M n p q hpq x y) = g (tensorMk M' M n p q hpq x y)) : f = g := by
  refine DirectSum.linearMap_ext R fun i => TensorProduct.ext' fun x y => ?_
  have := h i (n - i) (by omega) x y
  rw [tensorMk_self] at this
  exact this

/-- The differential of `M'` on homogeneous pieces squares to zero. -/
theorem gradedDifferential_sq (p : ℤ) (x : M'.grading p) :
    M'.gradedDifferential (p + 1) (M'.gradedDifferential p x) = 0 :=
  Subtype.ext (LinearMap.congr_fun M'.d_comp_d (x : M'.M))

/-- The differential of `M` on homogeneous pieces squares to zero. -/
theorem leftGradedDifferential_sq (q : ℤ) (y : M.grading q) :
    LeftModule.gradedDifferential A M (q + 1) (LeftModule.gradedDifferential A M q y) = 0 :=
  Subtype.ext (LinearMap.congr_fun M.d_comp_d (y : M.M))

/-- The differential of `tensorRaw` squares to zero. -/
theorem tensorRawD_comp_d (n : ℤ) :
    (tensorRawD M' M (n + 1)).comp (tensorRawD M' M n) = 0 := by
  apply tensorRaw_ext M' M (Q := tensorRaw M' M (n + 1 + 1))
  intro p q h x y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [tensorRawD_mk, map_add, map_zsmul, tensorRawD_mk, tensorRawD_mk,
    gradedDifferential_sq, leftGradedDifferential_sq]
  simp only [map_zero, LinearMap.zero_apply, zero_add, Int.negOnePow_succ,
    Units.val_neg, neg_smul, smul_add, smul_smul]
  rw [tensorMk_ext2 M' M (n + 1 + 1) (p + 1) (q + 1) (p + 1) (q + 1) (by omega) (by omega) rfl
    (M'.gradedDifferential p x) (LeftModule.gradedDifferential A M q y)
    (M'.gradedDifferential p x) (LeftModule.gradedDifferential A M q y) rfl rfl]
  abel

/-- Right multiplication by a homogeneous element of `A`, on a homogeneous piece of `M'`. -/
def gradedRightSmul (p i : ℤ) (x : M'.grading p) (a : A.grading i) : M'.grading (p + i) :=
  ⟨MulOpposite.op (a : A.A) • (x : M'.M), M'.smul_mem p i x a x.2 a.2⟩

/-- Left multiplication by a homogeneous element of `A`, on a homogeneous piece of `M`. -/
def gradedLeftSmul (i q : ℤ) (a : A.grading i) (y : M.grading q) : M.grading (i + q) :=
  ⟨(a : A.A) • (y : M.M), M.smul_mem i q a y a.2 y.2⟩

/-- The underlying element of `gradedRightSmul M' p i x a` is `x a`. -/
@[simp] theorem gradedRightSmul_coe (p i : ℤ) (x : M'.grading p) (a : A.grading i) :
    ((gradedRightSmul M' p i x a : M'.grading (p + i)) : M'.M) =
      MulOpposite.op (a : A.A) • (x : M'.M) := rfl

/-- The underlying element of `gradedLeftSmul M i q a y` is `a y`. -/
@[simp] theorem gradedLeftSmul_coe (i q : ℤ) (a : A.grading i) (y : M.grading q) :
    ((gradedLeftSmul M i q a y : M.grading (i + q)) : M.M) = (a : A.A) • (y : M.M) := rfl

/-- The balancing relation `(x a) ⊗ y - x ⊗ (a y)` in degree `n`. -/
noncomputable def tensorRelator (p i q n : ℤ) (h : p + i + q = n)
    (x : M'.grading p) (a : A.grading i) (y : M.grading q) : tensorRaw M' M n :=
  tensorMk M' M n (p + i) q (by omega) (gradedRightSmul M' p i x a) y -
    tensorMk M' M n p (i + q) (by omega) x (gradedLeftSmul M i q a y)

/-- The submodule of balancing relations in degree `n`. -/
noncomputable def tensorRel (n : ℤ) : Submodule R (tensorRaw M' M n) :=
  Submodule.span R {z | ∃ (p i q : ℤ) (h : p + i + q = n) (x : M'.grading p) (a : A.grading i)
    (y : M.grading q), z = tensorRelator M' M p i q n h x a y}

/-- Each balancing relation lies in `tensorRel M' M n`. -/
theorem tensorRelator_mem (p i q n : ℤ) (h : p + i + q = n)
    (x : M'.grading p) (a : A.grading i) (y : M.grading q) :
    tensorRelator M' M p i q n h x a y ∈ tensorRel M' M n :=
  Submodule.subset_span ⟨p, i, q, h, x, a, y, rfl⟩

/-- If `z = z₁ + c • z₂`, then `z ⊗ y = z₁ ⊗ y + c • (z₂ ⊗ y)`. -/
theorem tensorMk_split_left (n P q : ℤ) (h : P + q = n) (c : ℤ)
    (z z₁ z₂ : M'.grading P) (y : M.grading q)
    (hz : (z : M'.M) = (z₁ : M'.M) + c • (z₂ : M'.M)) :
    tensorMk M' M n P q h z y =
      tensorMk M' M n P q h z₁ y + c • tensorMk M' M n P q h z₂ y := by
  obtain rfl : z = z₁ + c • z₂ := Subtype.ext (by simpa using hz)
  change ((tensorMk M' M n P q h).flip y) (z₁ + c • z₂) = _
  rw [map_add, map_zsmul]
  rfl

/-- If `w = w₁ + c • w₂`, then `x ⊗ w = x ⊗ w₁ + c • (x ⊗ w₂)`. -/
theorem tensorMk_split_right (n p Q : ℤ) (h : p + Q = n) (c : ℤ)
    (x : M'.grading p) (w w₁ w₂ : M.grading Q)
    (hw : (w : M.M) = (w₁ : M.M) + c • (w₂ : M.M)) :
    tensorMk M' M n p Q h x w =
      tensorMk M' M n p Q h x w₁ + c • tensorMk M' M n p Q h x w₂ := by
  obtain rfl : w = w₁ + c • w₂ := Subtype.ext (by simpa using hw)
  rw [map_add, map_zsmul]

/-- The differential of the balancing relation for `(x, a, y)` is the signed sum of the balancing
relations for `(d x, a, y)`, `(x, d a, y)` and `(x, a, d y)`, with signs `1`, `(-1)^p` and
`(-1)^(p + i)`. -/
theorem tensorRawD_relator (p i q n : ℤ) (h : p + i + q = n)
    (x : M'.grading p) (a : A.grading i) (y : M.grading q) :
    tensorRawD M' M n (tensorRelator M' M p i q n h x a y) =
      tensorRelator M' M (p + 1) i q (n + 1) (by omega) (M'.gradedDifferential p x) a y +
        (p.negOnePow : ℤ) • tensorRelator M' M p (i + 1) q (n + 1) (by omega) x
          ⟨A.d (a : A.A), A.d_mem i a a.2⟩ y +
        ((p + i).negOnePow : ℤ) • tensorRelator M' M p i (q + 1) (n + 1) (by omega) x a
          (LeftModule.gradedDifferential A M q y) := by
  have hW1 : MulOpposite.op (a : A.A) • M'.d (x : M'.M) ∈ M'.grading (p + i + 1) :=
    (by omega : p + 1 + i = p + i + 1) ▸
      M'.smul_mem (p + 1) i (M'.d (x : M'.M)) (a : A.A) (M'.d_mem p x x.2) a.2
  have hW2 : MulOpposite.op (A.d (a : A.A)) • (x : M'.M) ∈ M'.grading (p + i + 1) :=
    (by omega : p + (i + 1) = p + i + 1) ▸
      M'.smul_mem p (i + 1) (x : M'.M) (A.d (a : A.A)) x.2 (A.d_mem i a a.2)
  have hV1 : A.d (a : A.A) • (y : M.M) ∈ M.grading (i + q + 1) :=
    (by omega : i + 1 + q = i + q + 1) ▸
      M.smul_mem (i + 1) q (A.d (a : A.A)) (y : M.M) (A.d_mem i a a.2) y.2
  have hV2 : (a : A.A) • M.d (y : M.M) ∈ M.grading (i + q + 1) :=
    (by omega : i + (q + 1) = i + q + 1) ▸
      M.smul_mem i (q + 1) (a : A.A) (M.d (y : M.M)) a.2 (M.d_mem q y y.2)
  simp only [tensorRelator]
  rw [map_sub, tensorRawD_mk, tensorRawD_mk,
    tensorMk_split_left M' M (n + 1) (p + i + 1) q (by omega) (p.negOnePow : ℤ)
      (M'.gradedDifferential (p + i) (gradedRightSmul M' p i x a)) ⟨_, hW1⟩ ⟨_, hW2⟩ y
      (M'.leibniz p i (x : M'.M) (a : A.A) x.2 a.2),
    tensorMk_split_right M' M (n + 1) p (i + q + 1) (by omega) (i.negOnePow : ℤ) x
      (LeftModule.gradedDifferential A M (i + q) (gradedLeftSmul M i q a y))
      ⟨_, hV1⟩ ⟨_, hV2⟩ (M.leibniz i q (a : A.A) (y : M.M) a.2 y.2),
    tensorMk_ext2 M' M (n + 1) (p + 1 + i) q (p + i + 1) q (by omega) (by omega) (by omega)
      (gradedRightSmul M' (p + 1) i (M'.gradedDifferential p x) a) y ⟨_, hW1⟩ y rfl rfl,
    tensorMk_ext2 M' M (n + 1) (p + (i + 1)) q (p + i + 1) q (by omega) (by omega) (by omega)
      (gradedRightSmul M' p (i + 1) x ⟨A.d (a : A.A), A.d_mem i a a.2⟩) y ⟨_, hW2⟩ y rfl rfl,
    tensorMk_ext2 M' M (n + 1) p (i + 1 + q) p (i + q + 1) (by omega) (by omega) rfl
      x (gradedLeftSmul M (i + 1) q ⟨A.d (a : A.A), A.d_mem i a a.2⟩ y) x ⟨_, hV1⟩ rfl rfl,
    tensorMk_ext2 M' M (n + 1) p (i + (q + 1)) p (i + q + 1) (by omega) (by omega) rfl
      x (gradedLeftSmul M i (q + 1) a (LeftModule.gradedDifferential A M q y)) x ⟨_, hV2⟩
      rfl rfl,
    Int.negOnePow_add, Units.val_mul]
  simp only [smul_sub, smul_add, smul_smul]
  abel

/-- The components of a balanced bilinear map depend on the degrees only through the
underlying elements. -/
theorem BalancedBilinear.map_congr {Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (b : BalancedBilinear M' M Q) (p q q' n : ℤ) (h : p + q = n) (h' : p + q' = n)
    (x : M'.grading p) (y : M.grading q) (y' : M.grading q')
    (hy : (y : M.M) = (y' : M.M)) : b.map p q n h x y = b.map p q' n h' x y' := by
  have hq : q = q' := by omega
  subst hq
  obtain rfl : y = y' := Subtype.ext hy
  rfl

/-- The differential of `tensorRaw` maps balancing relations to balancing relations. -/
theorem tensorRel_le_comap (n : ℤ) :
    tensorRel M' M n ≤ Submodule.comap (tensorRawD M' M n) (tensorRel M' M (n + 1)) := by
  rw [tensorRel, Submodule.span_le]
  rintro z ⟨p, i, q, h, x, a, y, rfl⟩
  change tensorRawD M' M n (tensorRelator M' M p i q n h x a y) ∈ tensorRel M' M (n + 1)
  rw [tensorRawD_relator]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (tensorRelator_mem M' M _ _ _ _ _ _ _ _)
      (zsmul_mem (tensorRelator_mem M' M _ _ _ _ _ _ _ _) _))
    (zsmul_mem (tensorRelator_mem M' M _ _ _ _ _ _ _ _) _)

/-- The degree-`n` part of the tensor product `M' ⊗_A M`. -/
abbrev tensorDeg (n : ℤ) : Type u := tensorRaw M' M n ⧸ tensorRel M' M n

/-- The differential of `M' ⊗_A M`. -/
noncomputable def tensorDegD (n : ℤ) : tensorDeg M' M n →ₗ[R] tensorDeg M' M (n + 1) :=
  Submodule.mapQ _ _ (tensorRawD M' M n) (tensorRel_le_comap M' M n)

/-- The differential of `M' ⊗_A M` squares to zero. -/
theorem tensorDegD_comp (n : ℤ) :
    (tensorDegD M' M (n + 1)).comp (tensorDegD M' M n) = 0 := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  change tensorDegD M' M (n + 1) (tensorDegD M' M n (Submodule.Quotient.mk z)) = 0
  have hz : tensorRawD M' M (n + 1) (tensorRawD M' M n z) = 0 := by
    simpa using LinearMap.congr_fun (tensorRawD_comp_d M' M n) z
  rw [tensorDegD, tensorDegD, Submodule.mapQ_apply, Submodule.mapQ_apply, hz]
  simp

/-- The tensor product `M' ⊗_A M` of a right and a left differential graded `A`-module, as a
complex of `R`-modules with differential `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y`. Its degree-`n`
term is the degree-`n` piece of the balanced tensor product of the underlying modules
(`DifferentialGraded.balancedTensorGradedEquiv`). -/
@[stacks 09LL "M ⊗_A N is a differential graded R-module"]
noncomputable def tensorComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (tensorDeg M' M n))
    (fun n => ModuleCat.ofHom (tensorDegD M' M n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact tensorDegD_comp M' M n)

/-- The differential of `tensorComplex M' M` from degree `n` to `n + 1` is `tensorDegD M' M n`. -/
theorem tensorComplex_d (n : ℤ) :
    (tensorComplex M' M).d n (n + 1) = ModuleCat.ofHom (tensorDegD M' M n) := by
  simp [tensorComplex]

/-- The universal balanced bilinear map `(x, y) ↦ x ⊗ y` into `M' ⊗_A M`: it is `A`-balanced,
compatible with the gradings and compatible with the differentials. -/
@[stacks 09LL "the map M × N → M ⊗_A N in the differential graded case"]
noncomputable def tensorTmul : BalancedBilinear M' M (tensorComplex M' M) where
  map p q n h := (tensorMk M' M n p q h).compr₂ (tensorRel M' M n).mkQ
  balance p i q n h₁ h₂ x a y :=
    (Submodule.Quotient.eq (tensorRel M' M n)).2 (tensorRelator_mem M' M p i q n (by omega) x a y)
  map_d p q n h x y := by
    change (tensorComplex M' M).d n (n + 1) ((tensorRel M' M n).mkQ (tensorMk M' M n p q h x y)) = _
    rw [tensorComplex_d]
    change tensorDegD M' M n ((tensorRel M' M n).mkQ (tensorMk M' M n p q h x y)) = _
    rw [tensorDegD, Submodule.mkQ_apply, Submodule.mapQ_apply, tensorRawD_mk]
    change (tensorRel M' M (n + 1)).mkQ _ = _
    rw [map_add, map_zsmul]
    rfl

/-- `tensorTmul M' M` sends `(x, y)` to the class of `x ⊗ y`. -/
theorem tensorTmul_map (p q n : ℤ) (h : p + q = n) (x : M'.grading p) (y : M.grading q) :
    (tensorTmul M' M).map p q n h x y = (tensorRel M' M n).mkQ (tensorMk M' M n p q h x y) := rfl

/-- The composite of a balanced bilinear map with a map of complexes. -/
noncomputable def BalancedBilinear.comp {Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (b : BalancedBilinear M' M Q) (f : Q ⟶ Q') : BalancedBilinear M' M Q' where
  map p q n h := (b.map p q n h).compr₂ (f.f n).hom
  balance p i q n h₁ h₂ x a y := congrArg (f.f n).hom (b.balance p i q n h₁ h₂ x a y)
  map_d p q n h x y := by
    have hc := ConcreteCategory.congr_hom (f.comm n (n + 1)) (b.map p q n h x y)
    change (Q'.d n (n + 1)).hom ((f.f n).hom (b.map p q n h x y)) = _
    rw [show (Q'.d n (n + 1)).hom ((f.f n).hom (b.map p q n h x y)) =
      (f.f (n + 1)).hom ((Q.d n (n + 1)).hom (b.map p q n h x y)) from hc, b.map_d]
    simp only [map_add, map_zsmul]
    rfl

/-- The linear map out of the ungraded tensor product determined by a balanced bilinear map. -/
noncomputable def tensorRawDesc (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : BalancedBilinear M' M Q) (n : ℤ) : tensorRaw M' M n →ₗ[R] Q.X n :=
  DirectSum.toModule R ℤ _ fun i => TensorProduct.lift (b.map i (n - i) n (by omega))

/-- `tensorRawDesc` sends `x ⊗ y` to `b.map p q n h x y`. -/
theorem tensorRawDesc_mk (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : BalancedBilinear M' M Q) (n p q : ℤ) (h : p + q = n)
    (x : M'.grading p) (y : M.grading q) :
    tensorRawDesc M' M Q b n (tensorMk M' M n p q h x y) = b.map p q n h x y := by
  change tensorRawDesc M' M Q b n (DirectSum.lof R ℤ
    (fun i => M'.grading i ⊗[R] M.grading (n - i)) p
    (x ⊗ₜ[R] gradingCast M.grading (show q = n - p by omega) y)) = _
  rw [tensorRawDesc, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  exact BalancedBilinear.map_congr M' M b p (n - p) q n (by omega) h x _ y rfl

/-- `tensorRawDesc` vanishes on the balancing relations. -/
theorem tensorRawDesc_rel (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : BalancedBilinear M' M Q) (n : ℤ) :
    tensorRel M' M n ≤ LinearMap.ker (tensorRawDesc M' M Q b n) := by
  rw [tensorRel, Submodule.span_le]
  rintro z ⟨p, i, q, h, x, a, y, rfl⟩
  change tensorRawDesc M' M Q b n (tensorRelator M' M p i q n h x a y) = 0
  simp only [tensorRelator]
  rw [map_sub, tensorRawDesc_mk, tensorRawDesc_mk, sub_eq_zero]
  exact b.balance p i q n (by omega) (by omega) x a y

/-- The map out of the degree-`n` part of `M' ⊗_A M` determined by a balanced bilinear map. -/
noncomputable def tensorDegDesc (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : BalancedBilinear M' M Q) (n : ℤ) : tensorDeg M' M n →ₗ[R] Q.X n :=
  Submodule.liftQ _ (tensorRawDesc M' M Q b n) (tensorRawDesc_rel M' M Q b n)

/-- Linear maps out of the degree-`n` part of `M' ⊗_A M` agree once they agree on the classes
of homogeneous pure tensors. -/
theorem tensorDeg_linearMap_ext {n : ℤ} {Q : Type u} [AddCommGroup Q] [Module R Q]
    {f g : tensorDeg M' M n →ₗ[R] Q}
    (h : ∀ (p q : ℤ) (hpq : p + q = n) (x : M'.grading p) (y : M.grading q),
      f ((tensorRel M' M n).mkQ (tensorMk M' M n p q hpq x y)) =
        g ((tensorRel M' M n).mkQ (tensorMk M' M n p q hpq x y))) : f = g :=
  Submodule.linearMap_qext _ (tensorRaw_ext M' M (Q := Q) fun p q hpq x y => h p q hpq x y)

/-- The maps `tensorDegDesc M' M Q b n` commute with the differentials. -/
theorem tensorDesc_comm (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : BalancedBilinear M' M Q) (n : ℤ) :
    ModuleCat.ofHom (tensorDegDesc M' M Q b n) ≫ Q.d n (n + 1) =
      (tensorComplex M' M).d n (n + 1) ≫ ModuleCat.ofHom (tensorDegDesc M' M Q b (n + 1)) := by
  refine ModuleCat.hom_ext (tensorDeg_linearMap_ext M' M fun p q hpq x y => ?_)
  change (Q.d n (n + 1)).hom (tensorDegDesc M' M Q b n
      ((tensorRel M' M n).mkQ (tensorMk M' M n p q hpq x y))) =
    tensorDegDesc M' M Q b (n + 1) ((tensorComplex M' M).d n (n + 1)
      ((tensorRel M' M n).mkQ (tensorMk M' M n p q hpq x y)))
  rw [tensorComplex_d]
  change _ = tensorDegDesc M' M Q b (n + 1)
    (tensorDegD M' M n ((tensorRel M' M n).mkQ (tensorMk M' M n p q hpq x y)))
  rw [tensorDegD, Submodule.mkQ_apply, Submodule.mapQ_apply, tensorRawD_mk, tensorDegDesc,
    tensorDegDesc, Submodule.liftQ_apply, Submodule.liftQ_apply, tensorRawDesc_mk,
    map_add, map_zsmul, tensorRawDesc_mk, tensorRawDesc_mk, b.map_d]
  rfl

/-- The map of complexes `M' ⊗_A M ⟶ Q` determined by a balanced bilinear map. -/
noncomputable def tensorDesc (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : BalancedBilinear M' M Q) : tensorComplex M' M ⟶ Q :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (tensorDegDesc M' M Q b n))
    (tensorDesc_comm M' M Q b)

/-- `tensorDesc M' M Q b` sends the class of `x ⊗ y` to `b.map p q n h x y`. -/
theorem tensorDesc_apply (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : BalancedBilinear M' M Q) (p q n : ℤ) (h : p + q = n)
    (x : M'.grading p) (y : M.grading q) :
    ((tensorDesc M' M Q b).f n).hom ((tensorTmul M' M).map p q n h x y) = b.map p q n h x y := by
  change tensorDegDesc M' M Q b n ((tensorRel M' M n).mkQ (tensorMk M' M n p q h x y)) = _
  rw [tensorDegDesc, Submodule.mkQ_apply, Submodule.liftQ_apply, tensorRawDesc_mk]

/-- Maps of complexes out of `M' ⊗_A M` agree once they agree on homogeneous pure tensors. -/
theorem tensorComplex_hom_ext {Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {f g : tensorComplex M' M ⟶ Q}
    (h : ∀ (p q n : ℤ) (hpq : p + q = n) (x : M'.grading p) (y : M.grading q),
      (f.f n).hom ((tensorTmul M' M).map p q n hpq x y) =
        (g.f n).hom ((tensorTmul M' M).map p q n hpq x y)) : f = g :=
  HomologicalComplex.Hom.ext <| funext fun n => ModuleCat.hom_ext <|
    tensorDeg_linearMap_ext M' M fun p q hpq x y => h p q n hpq x y

/-- **The universal property of `M' ⊗_A M`.** Maps of complexes of `R`-modules out of
`M' ⊗_A M` are the balanced bilinear maps out of `M'` and `M`:
`DifferentialGradedBilinear_A(M' × M, Q) = Hom_{Comp(R)}(M' ⊗_A M, Q)`. -/
@[stacks 09LL "DifferentialGradedBilinear_A(M × N, Q) = Hom_{Comp(R)}(M ⊗_A N, Q)"]
noncomputable def tensorHomEquiv (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorComplex M' M ⟶ Q) ≃ BalancedBilinear M' M Q where
  toFun f := (tensorTmul M' M).comp M' M f
  invFun b := tensorDesc M' M Q b
  left_inv f := by
    refine tensorComplex_hom_ext M' M fun p q n hpq x y => ?_
    exact tensorDesc_apply M' M Q _ p q n hpq x y
  right_inv b := by
    refine BalancedBilinear.ext fun p q n hpq x y => ?_
    exact tensorDesc_apply M' M Q b p q n hpq x y

end DifferentialGraded

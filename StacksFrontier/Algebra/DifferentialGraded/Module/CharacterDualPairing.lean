module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BalancedTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDual
public import StacksFrontier.Algebra.Homology.DoubleComplexesOfModules

/-!
# Maps into the character dual of a left differential graded module

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, let `M` be a *left*
differential graded `A`-module and let `N` be a *right* differential graded `A`-module. The
character dual `M^∨ = Hom^•(M^•, ℚ/ℤ)` is a right differential graded `A`-module, the relative
tensor product `N ⊗_A M` is a complex of `R`-modules, and Stacks 09K3 is the chain of
identifications

`Hom_{Mod_{(A, d)}}(N, M^∨) = Hom_{Comp(ℤ)}(N ⊗_A M, ℚ/ℤ)
  = DifferentialGradedBilinear_A(N × M, ℚ/ℤ)`.

Here `Hom_{Comp(ℤ)}` is taken between complexes of *abelian groups*: the dualizing object `ℚ/ℤ`
carries no `R`-module structure, so the tensor complex is pushed through the forgetful functor
and `ℚ/ℤ` is placed in degree `0`.

## Main definitions

* `DifferentialGraded.CharacterBilinear`: a differential graded `A`-bilinear pairing
  `N × M → ℚ/ℤ` of total degree zero, which is `DifferentialGradedBilinear_A(N × M, ℚ/ℤ)`.
* `DifferentialGraded.LeftModule.dualGradingEquiv`: the degree-`n` part of `M^∨` is the
  character module of `M^{-n}`, together with the formulas `dualGradingEquiv_d` and
  `dualGradingEquiv_smul` for the differential and the right action read through it.
* `CharacterModule.coinduceEquiv`: an additive character of an `R`-module `Y` with values in
  `ℚ/ℤ` is the same thing as an `R`-linear map `Y → Hom_ℤ(R, ℚ/ℤ)`.

## Main results

* `DifferentialGraded.homTensorCharacterEquiv`: the first equality of Stacks 09K3,
  `Hom_{Mod_{(A, d)}}(N, M^∨) = Hom_{Comp(ℤ)}(N ⊗_A M, ℚ/ℤ)`, pinned on homogeneous pure
  tensors by `homTensorCharacterEquiv_apply`.
* `DifferentialGraded.tensorCharacterBilinearEquiv`: the second equality of Stacks 09K3,
  `Hom_{Comp(ℤ)}(N ⊗_A M, ℚ/ℤ) = DifferentialGradedBilinear_A(N × M, ℚ/ℤ)`, pinned by
  `tensorCharacterBilinearEquiv_apply`.
* `DifferentialGraded.homCharacterBilinearEquiv`: the composite of the two, identifying
  homomorphisms `N → M^∨` with pairings directly by `φ ↦ ((x, y) ↦ φ(x)(y))`.

## Implementation notes

*Both identifications are constructed, not merely asserted to exist.* Each is an `Equiv` with
an explicitly written inverse and both round trips proved, so the identification itself — and
not only its existence — is available downstream; this is why the pinning lemmas are `rfl`.

*The pairings are additive, not `R`-bilinear, by design.* The source takes
`DifferentialGradedBilinear_A(N × M, ℚ/ℤ)` over `ℤ`, so `CharacterBilinear` asks only for
biadditivity together with `A`-balancedness. `R`-balancedness is then a consequence
(`CharacterBilinear.smul_balanced`), because `algebraMap R A r` is a homogeneous element of
degree zero acting as `r` on both sides.

*The route through the coinduced module.* A map of complexes of abelian groups from a complex
`X` of `R`-modules to `ℚ/ℤ` in degree `0` is the same thing as a map of complexes of
`R`-modules from `X` to `Hom_ℤ(R, ℚ/ℤ)` in degree `0` (`homToCoefficient`,
`coefficientToHom`). This reduces the second equality to the `R`-linear universal property
`DifferentialGraded.tensorHomEquiv` of the tensor complex of Section 09LL, which is where the
relations defining `N ⊗_A M` are consumed.

*Universes.* The base ring `R` lies in `Type u` and the algebra in `Type v`; the two module
carriers lie in `Type u`, as the encodings of left differential graded modules and of the
tensor complex require. The universe lift on `ℚ/ℤ` is forced: the complexes in play are
complexes of abelian groups in `Type u`, while `ℚ/ℤ` lives in `Type 0`.

## References

* [Stacks Project, Tag 09K3](https://stacks.math.columbia.edu/tag/09K3)
* [Stacks Project, Tag 0FQC](https://stacks.math.columbia.edu/tag/0FQC)
* [Stacks Project, Tag 0FQD](https://stacks.math.columbia.edu/tag/0FQD)
* [Stacks Project, Tag 09LL](https://stacks.math.columbia.edu/tag/09LL)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u v

namespace CharacterModule

variable {R : Type u} [CommRing R] {Y : Type u} [AddCommGroup Y] [Module R Y]

/-- The character `r ↦ c (r y)` of `R` attached to a character `c` of an `R`-module `Y` and a
point `y` of `Y`. -/
def coinduce (c : CharacterModule Y) (y : Y) : CharacterModule R :=
  (AddMonoidHom.mk' (fun r : R => c (r • y)) (fun r s => by rw [add_smul, map_add]) :
    R →+ AddCircle (1 : ℚ))

/-- The character `coinduce c y` takes `r` to `c (r y)`. -/
@[simp] theorem coinduce_apply (c : CharacterModule Y) (y : Y) (r : R) :
    coinduce c y r = c (r • y) := rfl

/-- **Coinduction for character modules.** An additive character of an `R`-module `Y` is the
same thing as an `R`-linear map `Y → Hom_ℤ(R, ℚ/ℤ)`, by `c ↦ (y ↦ (r ↦ c (r y)))`; the inverse
evaluates at `1`. -/
def coinduceEquiv (R : Type u) [CommRing R] (Y : Type u) [AddCommGroup Y] [Module R Y] :
    CharacterModule Y ≃ₗ[R] (Y →ₗ[R] CharacterModule R) where
  toFun c :=
    { toFun := coinduce c
      map_add' := fun y y' => by
        ext r
        change c (r • (y + y')) = c (r • y) + c (r • y')
        rw [smul_add, map_add]
      map_smul' := fun s y => by
        ext r
        change c (r • s • y) = c ((s • r) • y)
        rw [smul_smul, smul_eq_mul, mul_comm] }
  map_add' c c' := by ext y r; rfl
  map_smul' s c := by
    ext y r
    change c (s • r • y) = c ((s • r) • y)
    rw [smul_smul, smul_eq_mul]
  invFun g := (AddMonoidHom.mk' (fun y => g y (1 : R))
    (fun y y' => by rw [map_add]; rfl) : Y →+ AddCircle (1 : ℚ))
  left_inv c := by
    ext y
    change c ((1 : R) • y) = c y
    rw [one_smul]
  right_inv g := by
    ext y r
    change g (r • y) (1 : R) = g y r
    rw [map_smul]
    change g y (r • (1 : R)) = g y r
    rw [smul_eq_mul, mul_one]

/-- The image of a character `c` under `coinduceEquiv` takes `y` and `r` to `c (r y)`. -/
@[simp] theorem coinduceEquiv_apply (c : CharacterModule Y) (y : Y) (r : R) :
    coinduceEquiv R Y c y r = c (r • y) := rfl

/-- The inverse of `coinduceEquiv` evaluates an `R`-linear map `g` at `1`: it sends `y` to
`g y 1`. -/
@[simp] theorem coinduceEquiv_symm_apply (g : Y →ₗ[R] CharacterModule R) (y : Y) :
    (coinduceEquiv R Y).symm g y = g y (1 : R) := rfl

end CharacterModule

namespace DifferentialGraded

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-! ## Differential graded bilinear pairings into `ℚ/ℤ` -/

/-- A differential graded `A`-bilinear pairing `N × M → ℚ/ℤ` of total degree zero, for `N` a
right and `M` a left differential graded `A`-module: a family of biadditive maps
`N^p × M^{-p} → ℚ/ℤ` which is `A`-balanced and compatible with the differentials, the target
`ℚ/ℤ` being the complex concentrated in degree `0` with zero differential. -/
structure CharacterBilinear (N : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A) where
  /-- The pairing on homogeneous pieces of complementary degrees. -/
  pairing (p : ℤ) : N.grading p →+ CharacterModule (M.grading (-p))
  /-- `A`-balancedness: `b (x a, y) = b (x, a y)`. -/
  balanced (p m : ℤ) (x : N.grading p) (a : A.grading m) (y : M.grading (-(p + m))) :
    pairing (p + m) ⟨MulOpposite.op (a : A.A) • (x : N.M),
        N.smul_mem p m (x : N.M) (a : A.A) x.2 a.2⟩ y =
      pairing p x ⟨(a : A.A) • (y : M.M), by
        simpa only [show m + -(p + m) = -p by omega] using
          M.smul_mem m (-(p + m)) (a : A.A) (y : M.M) a.2 y.2⟩
  /-- Compatibility with the differentials: since the target has zero differential and is
  concentrated in degree `0`, the Leibniz identity in total degree `-1` reads
  `b (d x, y) + (-1)^p b (x, d y) = 0`. -/
  compat_d (p : ℤ) (x : N.grading p) (y : M.grading (-(p + 1))) :
    pairing (p + 1) ⟨N.d (x : N.M), N.d_mem p (x : N.M) x.2⟩ y +
      (p.negOnePow : ℤ) • pairing p x ⟨M.d (y : M.M), by
        simpa only [show -(p + 1) + 1 = -p by omega] using
          M.d_mem (-(p + 1)) (y : M.M) y.2⟩ = 0

/-- Two differential graded bilinear pairings into `ℚ/ℤ` with the same components agree. -/
theorem CharacterBilinear.ext {N : DifferentialGradedModule.{u, v, u} A} {M : LeftModule A}
    {b c : CharacterBilinear N M} (h : ∀ p, b.pairing p = c.pairing p) : b = c := by
  have hp : b.pairing = c.pairing := funext h
  cases b; cases c; cases hp; rfl

/-- The balancing law of a pairing, with the degree of the product named. -/
theorem CharacterBilinear.balanced' {N : DifferentialGradedModule.{u, v, u} A} {M : LeftModule A}
    (b : CharacterBilinear N M) (p m n : ℤ) (h : p + m = n) (x : N.grading p)
    (a : A.grading m) (y : M.grading (-n)) (hx : MulOpposite.op (a : A.A) • (x : N.M) ∈ N.grading n)
    (hy : (a : A.A) • (y : M.M) ∈ M.grading (-p)) :
    b.pairing n ⟨MulOpposite.op (a : A.A) • (x : N.M), hx⟩ y = b.pairing p x ⟨_, hy⟩ := by
  subst h; exact b.balanced p m x a y

/-- A homogeneous element of degree zero of the algebra: the image of a scalar. -/
theorem algebraMap_mem_grading_zero (A : DifferentialGradedAlgebra.{u, v} R) (r : R) :
    algebraMap R A.A r ∈ A.grading 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A.grading 0).smul_mem r (SetLike.one_mem_graded A.grading)

/-- A differential graded `A`-bilinear pairing into `ℚ/ℤ` is `R`-balanced: this is the special
case of `A`-balancedness at the degree-zero homogeneous element `algebraMap R A r`. -/
theorem CharacterBilinear.smul_balanced {N : DifferentialGradedModule.{u, v, u} A}
    {M : LeftModule A} (b : CharacterBilinear N M) (p : ℤ) (r : R) (x : N.grading p)
    (y : M.grading (-p)) :
    b.pairing p (r • x) y = b.pairing p x (r • y) := by
  have hr : algebraMap R A.A r ∈ A.grading 0 := algebraMap_mem_grading_zero A r
  have hopx : MulOpposite.op (algebraMap R A.A r) • (x : N.M) = r • (x : N.M) := by
    rw [show MulOpposite.op (algebraMap R A.A r) = algebraMap R A.Aᵐᵒᵖ r from rfl,
      IsScalarTower.algebraMap_smul A.Aᵐᵒᵖ r (x : N.M)]
  have hay : (algebraMap R A.A r) • (y : M.M) = r • (y : M.M) :=
    IsScalarTower.algebraMap_smul A.A r (y : M.M)
  have hx : MulOpposite.op (algebraMap R A.A r) • (x : N.M) ∈ N.grading p := by
    rw [hopx]; exact (N.grading p).smul_mem r x.2
  have hy : (algebraMap R A.A r) • (y : M.M) ∈ M.grading (-p) := by
    rw [hay]; exact (M.grading (-p)).smul_mem r y.2
  have := b.balanced' p 0 p (add_zero p) x ⟨_, hr⟩ y hx hy
  convert this using 3 <;> simp only [Subtype.ext_iff, hopx, hay] <;> rfl

/-! ## The graded pieces of the character dual -/

namespace LeftModule

/-- Reading a point of the graded dual `M^∨` as a character of `M`, `R`-linearly. -/
def dualCharLinear (M : LeftModule A) : (dual M).M →ₗ[R] CharacterModule M.M where
  toFun := dualChar
  map_add' := dualChar_add
  map_smul' := dualChar_smul

/-- The degree-`n` part of `M^∨`, restricted to the graded piece `M^{-n}` it is supported on. -/
def dualGradingRestrict (M : LeftModule A) (n : ℤ) :
    (dual M).grading n →ₗ[R] CharacterModule (M.grading (-n)) :=
  (CharacterModule.dual (M.grading (-n)).subtype).comp
    ((dualCharLinear M).comp ((dual M).grading n).subtype)

/-- The restriction of a homogeneous point `x` of `M^∨` takes `y ∈ M^{-n}` to `x (y)`. -/
@[simp] theorem dualGradingRestrict_apply (M : LeftModule A) (n : ℤ) (x : (dual M).grading n)
    (y : M.grading (-n)) : dualGradingRestrict M n x y = dualChar (x : (dual M).M) (y : M.M) :=
  rfl

/-- A homogeneous point of `M^∨` is determined by its restriction to `M^{-n}`. -/
theorem dualGradingRestrict_injective (M : LeftModule A) (n : ℤ) :
    Function.Injective (dualGradingRestrict M n) := by
  intro x x' h
  refine Subtype.ext (dualChar_injective (M := M) ?_)
  have hx : (⟨dualChar (x : (dual M).M), mem_dual_grading.mp x.2⟩ : dualPiece M n) =
      ⟨dualChar (x' : (dual M).M), mem_dual_grading.mp x'.2⟩ :=
    dualPieceRestrict_injective M n (by ext y; exact congrFun (congrArg _ h) y)
  exact congrArg (fun l : dualPiece M n => (l : CharacterModule M.M)) hx

/-- Every character of `M^{-n}` is the restriction of a homogeneous point of `M^∨` of
degree `n`. -/
theorem dualGradingRestrict_surjective (M : LeftModule A) (n : ℤ) :
    Function.Surjective (dualGradingRestrict M n) := by
  intro μ
  obtain ⟨l, hl⟩ := dualPieceRestrict_surjective M n μ
  have hmem : (l : CharacterModule M.M) ∈ dualCarrier M := Submodule.mem_iSup_of_mem n l.2
  refine ⟨⟨dualOf (l : CharacterModule M.M) hmem, mem_dual_grading.mpr l.2⟩, ?_⟩
  ext y
  exact congrFun (congrArg _ hl) y

/-- **The degree-`n` part of `M^∨` is the character module of `M^{-n}`.** -/
def dualGradingEquiv (M : LeftModule A) (n : ℤ) :
    (dual M).grading n ≃ₗ[R] CharacterModule (M.grading (-n)) :=
  LinearEquiv.ofBijective (dualGradingRestrict M n)
    ⟨dualGradingRestrict_injective M n, dualGradingRestrict_surjective M n⟩

/-- The character of `M^{-n}` attached to a homogeneous point `x` of `M^∨` takes `y` to
`x (y)`. -/
@[simp] theorem dualGradingEquiv_apply (M : LeftModule A) (n : ℤ) (x : (dual M).grading n)
    (y : M.grading (-n)) : dualGradingEquiv M n x y = dualChar (x : (dual M).M) (y : M.M) :=
  rfl

/-- The differential of `M^∨`, read through the identification of its degree-`n` part with the
character module of `M^{-n}`: it is `f ↦ (-1)^{n+1} f ∘ d`. -/
theorem dualGradingEquiv_d (M : LeftModule A) (n : ℤ) (x : (dual M).grading n)
    (y : M.grading (-(n + 1))) :
    dualGradingEquiv M (n + 1)
        ⟨(dual M).d (x : (dual M).M), (dual M).d_mem n (x : (dual M).M) x.2⟩ y =
      ((n + 1).negOnePow : ℤ) • dualGradingEquiv M n x
        ⟨M.d (y : M.M), by
          simpa only [show -(n + 1) + 1 = -n by omega] using M.d_mem (-(n + 1)) (y : M.M) y.2⟩ := by
  rw [dualGradingEquiv_apply, dualGradingEquiv_apply, dualChar_d, dualD0_apply,
    signedDifferential_apply_mem M y.2, map_zsmul, Int.negOnePow_neg]

/-- The right action of a homogeneous `a ∈ A^m` on `M^∨`, read through the identification of the
degree-`n` part with the character module of `M^{-n}`: it is `f ↦ f ∘ a`, with no sign. -/
theorem dualGradingEquiv_smul (M : LeftModule A) (n m : ℤ) (x : (dual M).grading n)
    (a : A.grading m) (y : M.grading (-(n + m))) :
    dualGradingEquiv M (n + m)
        ⟨MulOpposite.op (a : A.A) • (x : (dual M).M),
          (dual M).smul_mem n m (x : (dual M).M) (a : A.A) x.2 a.2⟩ y =
      dualGradingEquiv M n x
        ⟨(a : A.A) • (y : M.M), by
          simpa only [show m + -(n + m) = -n by omega] using
            M.smul_mem m (-(n + m)) (a : A.A) (y : M.M) a.2 y.2⟩ := by
  rw [dualGradingEquiv_apply, dualGradingEquiv_apply, dualChar_op_smul, charSMul_apply]
  rfl

end LeftModule

/-! ## Homomorphisms into the character dual -/

section FirstEquality

variable {N : DifferentialGradedModule.{u, v, u} A} {M : LeftModule A}

/-- The pairing of a differential graded bilinear map into `ℚ/ℤ`, as an `R`-linear map: the
`R`-balancedness `b (r x, y) = b (x, r y)` is exactly `R`-linearity into the character module of
`M^{-p}`. -/
def CharacterBilinear.pairingLinear (b : CharacterBilinear N M) (p : ℤ) :
    N.grading p →ₗ[R] CharacterModule (M.grading (-p)) where
  toFun := b.pairing p
  map_add' := (b.pairing p).map_add
  map_smul' r x := by ext y; exact b.smul_balanced p r x y

/-- The homomorphism `N → M^∨` of underlying `R`-modules attached to a differential graded
bilinear pairing: on a homogeneous element of degree `p` it is the pairing with that element,
read back as a homogeneous point of `M^∨` of degree `p`. -/
def characterBilinearToLinearMap (b : CharacterBilinear N M) :
    N.M →ₗ[R] (LeftModule.dual M).M :=
  (DirectSum.toModule R ℤ (LeftModule.dual M).M (fun p =>
      ((LeftModule.dual M).grading p).subtype.comp
        ((LeftModule.dualGradingEquiv M p).symm.toLinearMap.comp (b.pairingLinear p)))).comp
    (DirectSum.decomposeLinearEquiv N.grading).toLinearMap

/-- On a homogeneous element `x` of degree `p`, the map attached to `b` is the homogeneous point
of `M^∨` of degree `p` whose character of `M^{-p}` is `b (x, -)`. -/
theorem characterBilinearToLinearMap_apply (b : CharacterBilinear N M) (p : ℤ)
    (x : N.grading p) :
    characterBilinearToLinearMap b (x : N.M) =
      ((LeftModule.dualGradingEquiv M p).symm (b.pairing p x) : (LeftModule.dual M).M) := by
  simp [characterBilinearToLinearMap, CharacterBilinear.pairingLinear]

/-- The map attached to a pairing preserves degrees. -/
theorem characterBilinearToLinearMap_mem (b : CharacterBilinear N M) (p : ℤ) (x : N.M)
    (hx : x ∈ N.grading p) :
    characterBilinearToLinearMap b x ∈ (LeftModule.dual M).grading p := by
  rw [characterBilinearToLinearMap_apply b p ⟨x, hx⟩]
  exact ((LeftModule.dualGradingEquiv M p).symm (b.pairing p ⟨x, hx⟩)).2

/-- On the degree-`p` piece, the map attached to `b` is the inverse of `dualGradingEquiv`
applied to `b (x, -)`. -/
theorem characterBilinearToLinearMap_graded (b : CharacterBilinear N M) (p : ℤ)
    (x : N.grading p) :
    (⟨characterBilinearToLinearMap b (x : N.M),
        characterBilinearToLinearMap_mem b p (x : N.M) x.2⟩ : (LeftModule.dual M).grading p) =
      (LeftModule.dualGradingEquiv M p).symm (b.pairing p x) :=
  Subtype.ext (characterBilinearToLinearMap_apply b p x)

/-- The map attached to `b` takes `x` to a point `w` of `M^∨` as soon as `b (x, -)` is the
character of `M^{-n}` attached to `w`. -/
private theorem characterBilinearToLinearMap_eq_of_pairing (b : CharacterBilinear N M) (n : ℤ)
    (x : N.grading n) (w : (LeftModule.dual M).M) (hw : w ∈ (LeftModule.dual M).grading n)
    (h : ∀ y, b.pairing n x y = LeftModule.dualGradingEquiv M n ⟨w, hw⟩ y) :
    characterBilinearToLinearMap b (x : N.M) = w := by
  rw [characterBilinearToLinearMap_apply]
  exact congrArg Subtype.val ((LinearEquiv.symm_apply_eq _).2 (CharacterModule.ext _ h))

/-- `A`-balancedness of the pairing makes the attached map commute with the right action. -/
theorem characterBilinearToLinearMap_op_smul (b : CharacterBilinear N M) (p m : ℤ)
    (x : N.grading p) (a : A.grading m) :
    characterBilinearToLinearMap b (MulOpposite.op (a : A.A) • (x : N.M)) =
      MulOpposite.op (a : A.A) • characterBilinearToLinearMap b (x : N.M) := by
  refine characterBilinearToLinearMap_eq_of_pairing b (p + m)
    ⟨_, N.smul_mem p m (x : N.M) (a : A.A) x.2 a.2⟩ _
    ((LeftModule.dual M).smul_mem p m _ _ (characterBilinearToLinearMap_mem b p _ x.2) a.2)
    fun y => Eq.trans ?_ (LeftModule.dualGradingEquiv_smul M p m
      ⟨_, characterBilinearToLinearMap_mem b p _ x.2⟩ a y).symm
  rw [characterBilinearToLinearMap_graded, LinearEquiv.apply_symm_apply]
  exact b.balanced p m x a y

/-- Compatibility of the pairing with the differentials makes the attached map a chain map. -/
theorem characterBilinearToLinearMap_d (b : CharacterBilinear N M) (p : ℤ) (x : N.grading p) :
    characterBilinearToLinearMap b (N.d (x : N.M)) =
      (LeftModule.dual M).d (characterBilinearToLinearMap b (x : N.M)) := by
  refine characterBilinearToLinearMap_eq_of_pairing b (p + 1) ⟨_, N.d_mem p (x : N.M) x.2⟩ _
    ((LeftModule.dual M).d_mem p _ (characterBilinearToLinearMap_mem b p _ x.2))
    fun y => Eq.trans ?_ (LeftModule.dualGradingEquiv_d M p
      ⟨_, characterBilinearToLinearMap_mem b p _ x.2⟩ y).symm
  rw [characterBilinearToLinearMap_graded, LinearEquiv.apply_symm_apply]
  simpa [Int.negOnePow_add] using eq_neg_of_add_eq_zero_left (b.compat_d p x y)

/-- The homomorphism `N → M^∨` of right differential graded `A`-modules attached to a
differential graded bilinear pairing `N × M → ℚ/ℤ`. -/
def characterBilinearToHom (b : CharacterBilinear N M) :
    DifferentialGradedModule.Hom N (LeftModule.dual M) where
  toFun := characterBilinearToLinearMap b
  map_grading := characterBilinearToLinearMap_mem b
  map_smul x a := by
    induction x using DirectSum.Decomposition.inductionOn N.grading with
    | zero => simp
    | @homogeneous p x =>
      induction a using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | @homogeneous m a => exact characterBilinearToLinearMap_op_smul b p m x a
      | add a a' ha ha' => simp only [MulOpposite.op_add, add_smul, map_add, ha, ha']
    | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']
  map_d := by
    apply DirectSum.decompose_lhom_ext N.grading
    intro p
    ext x
    exact characterBilinearToLinearMap_d b p x

end FirstEquality

/-- The differential graded bilinear pairing `N × M → ℚ/ℤ` attached to a homomorphism
`N → M^∨` of right differential graded `A`-modules: it is `(x, y) ↦ φ(x)(y)`. -/
def homToCharacterBilinear (N : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)
    (φ : DifferentialGradedModule.Hom N (LeftModule.dual M)) : CharacterBilinear N M where
  pairing p := ((LeftModule.dualGradingEquiv M p).toLinearMap.comp (φ.gradedMap p)).toAddMonoidHom
  balanced p m x a y := by
    have hφ : φ.gradedMap (p + m) ⟨MulOpposite.op (a : A.A) • (x : N.M),
          N.smul_mem p m (x : N.M) (a : A.A) x.2 a.2⟩ =
        ⟨MulOpposite.op (a : A.A) • ((φ.gradedMap p x : (LeftModule.dual M).M)),
          (LeftModule.dual M).smul_mem p m _ _ (φ.gradedMap p x).2 a.2⟩ :=
      Subtype.ext (φ.map_smul (x : N.M) (a : A.A))
    change (LeftModule.dualGradingEquiv M (p + m)) (φ.gradedMap (p + m) _) y = _
    rw [hφ]
    exact LeftModule.dualGradingEquiv_smul M p m (φ.gradedMap p x) a y
  compat_d p x y := by
    have hφ : φ.gradedMap (p + 1) ⟨N.d (x : N.M), N.d_mem p (x : N.M) x.2⟩ =
        ⟨(LeftModule.dual M).d ((φ.gradedMap p x : (LeftModule.dual M).M)),
          (LeftModule.dual M).d_mem p _ (φ.gradedMap p x).2⟩ :=
      Subtype.ext (LinearMap.congr_fun φ.map_d (x : N.M))
    change (LeftModule.dualGradingEquiv M (p + 1)) (φ.gradedMap (p + 1) _) y + _ = 0
    rw [hφ, LeftModule.dualGradingEquiv_d]
    simp [Int.negOnePow_add]

/-- For a right differential graded `A`-module `N` and a left differential graded `A`-module
`M`, homomorphisms of right differential graded `A`-modules `N → M^∨` into the character dual
are exactly the differential graded `A`-bilinear pairings `N × M → ℚ/ℤ` of total degree
zero. -/
def homCharacterBilinearEquiv (N : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A) :
    DifferentialGradedModule.Hom N (LeftModule.dual M) ≃ CharacterBilinear N M where
  toFun := homToCharacterBilinear N M
  invFun := characterBilinearToHom
  left_inv φ := by
    apply DifferentialGradedModule.Hom.ext
    apply DirectSum.decompose_lhom_ext N.grading
    intro p
    ext x
    change characterBilinearToLinearMap (homToCharacterBilinear N M φ) (x : N.M) = φ.toFun x
    rw [characterBilinearToLinearMap_apply]
    change (((LeftModule.dualGradingEquiv M p).symm
      (LeftModule.dualGradingEquiv M p (φ.gradedMap p x)) : (LeftModule.dual M).grading p) :
        (LeftModule.dual M).M) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  right_inv b := by
    refine CharacterBilinear.ext fun p => ?_
    ext x y
    change LeftModule.dualGradingEquiv M p
      ⟨characterBilinearToLinearMap b (x : N.M),
        characterBilinearToLinearMap_mem b p (x : N.M) x.2⟩ y = _
    rw [characterBilinearToLinearMap_graded, LinearEquiv.apply_symm_apply]

/-- The identification of Stacks 09K3 sends a homomorphism `φ : N → M^∨` to the pairing
`(x, y) ↦ φ(x)(y)`; this determines it. -/
theorem homCharacterBilinearEquiv_apply (N : DifferentialGradedModule.{u, v, u} A)
    (M : LeftModule A) (φ : DifferentialGradedModule.Hom N (LeftModule.dual M)) (p : ℤ)
    (x : N.grading p) (y : M.grading (-p)) :
    (homCharacterBilinearEquiv N M φ).pairing p x y =
      LeftModule.dualChar (φ.toFun (x : N.M)) (y : M.M) := rfl

/-! ## The two targets of `Hom_{Comp(ℤ)}(N ⊗_A M, ℚ/ℤ)` -/

/-- `ℚ/ℤ`, placed in degree `0`, as a complex of abelian groups: the target of
`Hom_{Comp(ℤ)}(-, ℚ/ℤ)`. -/
abbrev characterTarget : CochainComplex AddCommGrpCat.{u} ℤ :=
  (HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).obj
    (AddCommGrpCat.of (ULift.{u} (AddCircle (1 : ℚ))))

/-- `Hom_ℤ(R, ℚ/ℤ)`, placed in degree `0`, as a complex of `R`-modules: the coinduced form of
the target of `Hom_{Comp(ℤ)}(-, ℚ/ℤ)`. -/
abbrev coefficientTarget (R : Type u) [CommRing R] : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of R (CharacterModule R))

/-- The degree-`n` part of the coefficient target vanishes for `n ≠ 0`. -/
theorem coefficientTarget_subsingleton (n : ℤ) (hn : n ≠ 0) :
    Subsingleton ((coefficientTarget R).X n) :=
  ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ n hn)

/-- A point of the degree-`0` part of the coefficient target, read as a character of `R`. -/
def coefficientValue (z : (coefficientTarget R).X 0) : CharacterModule R := z

/-- Lowering a universe-lifted element of `ℚ/ℤ`. -/
def charDown : ULift.{u} (AddCircle (1 : ℚ)) →+ AddCircle (1 : ℚ) :=
  AddMonoidHom.mk' (fun z => z.down) (fun _ _ => rfl)

/-- Evaluation at `1`, from `Hom_ℤ(R, ℚ/ℤ)` to `ℚ/ℤ`, universe-lifted. -/
def charEvalOne (R : Type u) [CommRing R] :
    CharacterModule R →+ ULift.{u} (AddCircle (1 : ℚ)) :=
  AddMonoidHom.mk' (fun c => ULift.up (c (1 : R))) (fun _ _ => rfl)

/-! ## Pairings from maps of complexes out of the tensor product -/

/-- The Leibniz rule for a balanced bilinear map, with the target degree named. -/
theorem BalancedBilinear.map_d_of_eq {M' : DifferentialGradedModule.{u, v, u} A}
    {M : LeftModule A} {Q : CochainComplex (ModuleCat.{u} R) ℤ} (b : BalancedBilinear M' M Q)
    (p q n m : ℤ) (h : p + q = n) (hm : n + 1 = m) (x : M'.grading p) (y : M.grading q) :
    Q.d n m (b.map p q n h x y) =
      b.map (p + 1) q m (by omega) ⟨M'.d (x : M'.M), M'.d_mem p (x : M'.M) x.2⟩ y +
        (p.negOnePow : ℤ) • b.map p (q + 1) m (by omega) x
          ⟨M.d (y : M.M), M.d_mem q (y : M.M) y.2⟩ := by
  subst hm
  exact b.map_d p q n h x y

/-- A map of complexes of abelian groups into `ℚ/ℤ` placed in degree `0` kills every incoming
differential. -/
theorem additiveHom_d_apply_zero (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj X ⟶ characterTarget.{u}) (i : ℤ)
    (x : X.X i) : φ.f 0 (X.d i 0 x) = 0 := by
  have hc := φ.comm i 0
  simp only [HomologicalComplex.single_obj_d, Limits.comp_zero] at hc
  exact (congrArg (fun f => f x) hc).symm

section TensorSide

variable (N : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)

/-- The value of a map of complexes of abelian groups `N ⊗_A M → ℚ/ℤ` on a homogeneous pure
tensor. -/
def tensorCharacterValue
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶ characterTarget.{u})
    (p : ℤ) (x : N.grading p) (y : M.grading (-p)) : AddCircle (1 : ℚ) :=
  ((φ.f 0) ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x y) :
    ULift.{u} (AddCircle (1 : ℚ))).down

/-- The pairing on homogeneous pieces attached to a map of complexes of abelian groups
`N ⊗_A M → ℚ/ℤ`: it is `(x, y) ↦ φ (x ⊗ y)`. -/
def tensorCharacterPairing
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶ characterTarget.{u})
    (p : ℤ) : N.grading p →+ CharacterModule (M.grading (-p)) :=
  AddMonoidHom.mk' (fun x =>
      (AddMonoidHom.mk' (fun y => tensorCharacterValue N M φ p x y) (fun y z => by
        change ((φ.f 0) ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x (y + z))).down = _
        rw [map_add, map_add]
        rfl) : M.grading (-p) →+ AddCircle (1 : ℚ)))
    (fun x x' => by
      ext y
      change ((φ.f 0) ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) (x + x') y)).down = _
      rw [map_add ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p)), LinearMap.add_apply,
        map_add]
      rfl)

/-- The pairing attached to `φ` takes `(x, y)` to the value of `φ` on `x ⊗ y`. -/
@[simp] theorem tensorCharacterPairing_apply
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶ characterTarget.{u})
    (p : ℤ) (x : N.grading p) (y : M.grading (-p)) :
    tensorCharacterPairing N M φ p x y = tensorCharacterValue N M φ p x y := rfl

/-- The differential graded bilinear pairing `N × M → ℚ/ℤ` attached to a map of complexes of
abelian groups `N ⊗_A M → ℚ/ℤ`: the balancing and Leibniz laws of the universal pairing
`(x, y) ↦ x ⊗ y` become those of the pairing, the second because `φ` kills the image of the
differential in degree `0`. -/
def tensorToCharacterBilinear
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶ characterTarget.{u}) :
    CharacterBilinear N M where
  pairing := tensorCharacterPairing N M φ
  balanced p m x a y := by
    have hbal := (tensorTmul N M).balance p m (-(p + m)) 0 (by omega) (by omega) x a y
    have hcg := BalancedBilinear.map_congr N M (tensorTmul N M) p (m + -(p + m)) (-p) 0
      (by omega) (add_neg_cancel p) x
      ⟨(a : A.A) • (y : M.M), M.smul_mem m (-(p + m)) (a : A.A) (y : M.M) a.2 y.2⟩
      ⟨(a : A.A) • (y : M.M), by
        simpa only [show m + -(p + m) = -p by omega] using
          M.smul_mem m (-(p + m)) (a : A.A) (y : M.M) a.2 y.2⟩ rfl
    exact congrArg (fun z => ((φ.f 0) z : ULift.{u} (AddCircle (1 : ℚ))).down) (hbal.trans hcg)
  compat_d p x y := by
    have hd := (tensorTmul N M).map_d_of_eq p (-(p + 1)) (-1) 0 (by omega) (by omega) x y
    have hcg := BalancedBilinear.map_congr N M (tensorTmul N M) p (-(p + 1) + 1) (-p) 0
      (by omega) (add_neg_cancel p) x
      ⟨M.d (y : M.M), M.d_mem (-(p + 1)) (y : M.M) y.2⟩
      ⟨M.d (y : M.M), by
        simpa only [show -(p + 1) + 1 = -p by omega] using
          M.d_mem (-(p + 1)) (y : M.M) y.2⟩ rfl
    rw [hcg] at hd
    have hzero := congrArg (fun z => ((φ.f 0) z : ULift.{u} (AddCircle (1 : ℚ))).down) hd
    rw [additiveHom_d_apply_zero (tensorComplex N M) φ (-1)] at hzero
    change (0 : AddCircle (1 : ℚ)) = ((φ.f 0) (_ + (p.negOnePow : ℤ) • _)).down at hzero
    rw [map_add, map_zsmul] at hzero
    exact hzero.symm

end TensorSide

/-! ## Maps of complexes out of the tensor product from pairings -/

section PairingToHom

variable {N : DifferentialGradedModule.{u, v, u} A} {M : LeftModule A}

/-- The coinduced form of the pairing: `x ↦ y ↦ (r ↦ b (x, r y))`, on pieces of complementary
degrees. -/
def CharacterBilinear.coinducedMap (b : CharacterBilinear N M) (p q : ℤ) (h : q = -p) :
    N.grading p →ₗ[R] M.grading q →ₗ[R] CharacterModule R :=
  ((CharacterModule.coinduceEquiv R (M.grading (-p))).toLinearMap.comp
    (b.pairingLinear p)).compl₂ (gradingCast M.grading h)

/-- The coinduced form of `b` takes `x`, `y` and `r` to `b (x, r y)`. -/
@[simp] theorem CharacterBilinear.coinducedMap_apply (b : CharacterBilinear N M) (p q : ℤ)
    (h : q = -p) (x : N.grading p) (y : M.grading q) (r : R) :
    b.coinducedMap p q h x y r = b.pairing p x (r • gradingCast M.grading h y) := rfl

/-- The balanced bilinear map into `Hom_ℤ(R, ℚ/ℤ)` placed in degree `0` attached to a
differential graded bilinear pairing `N × M → ℚ/ℤ`. It vanishes outside total degree `0`,
where the target does, and is the coinduced pairing there. -/
def characterBilinearToCoefficient (b : CharacterBilinear N M) :
    BalancedBilinear N M (coefficientTarget R) where
  map p q n h :=
    if hn : n = 0 then
      hn.symm ▸ (show N.grading p →ₗ[R] M.grading q →ₗ[R] (coefficientTarget R).X 0 from
        b.coinducedMap p q (by omega))
    else 0
  balance p i q n h₁ h₂ x a y := by
    dsimp only
    split_ifs with hn
    · subst hn
      have hq : q = -(p + i) := by omega
      subst hq
      refine CharacterModule.ext R fun r => ?_
      change b.pairing (p + i) _ (r • gradingCast M.grading (by omega : -(p + i) = -(p + i)) y) =
        b.pairing p x (r • gradingCast M.grading (by omega : i + -(p + i) = -p) _)
      refine (b.balanced p i x a (r • y)).trans (congrArg (fun z => b.pairing p x z) ?_)
      exact Subtype.ext (smul_comm (a : A.A) r (y : M.M))
    · rfl
  map_d p q n h x y := by
    have hdzero : (coefficientTarget R).d n (n + 1) = 0 :=
      HomologicalComplex.single_obj_d _ _ _ _ _
    rw [hdzero]
    change (0 : (coefficientTarget R).X (n + 1)) = _
    dsimp only
    split_ifs with hn
    · have hn' : n = -1 := by omega
      subst hn'
      have hq : q = -(p + 1) := by omega
      subst hq
      refine CharacterModule.ext R fun r => ?_
      change (0 : AddCircle (1 : ℚ)) =
        b.pairing (p + 1) _ (r • gradingCast M.grading (by omega : -(p + 1) = -(p + 1)) y) +
          (p.negOnePow : ℤ) • b.pairing p x
            (r • gradingCast M.grading (by omega : -(p + 1) + 1 = -p) _)
      refine (Eq.trans ?_ (b.compat_d p x (r • y))).symm
      refine congrArg₂ (fun u w => u + (p.negOnePow : ℤ) • w) rfl ?_
      exact congrArg (fun z => b.pairing p x z) (Subtype.ext (M.d.map_smul r (y : M.M)).symm)
    · simp

end PairingToHom

/-! ## Maps into `ℚ/ℤ` and into `Hom_ℤ(R, ℚ/ℤ)` -/

/-- A map of complexes of abelian groups into `ℚ/ℤ`, out of a complex of `R`-modules, read as a
map of complexes of `R`-modules into `Hom_ℤ(R, ℚ/ℤ)`. -/
def homToCoefficient (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj X ⟶ characterTarget.{u}) :
    X ⟶ coefficientTarget R :=
  HomologicalComplex.mkHomToSingle
    (ModuleCat.ofHom (CharacterModule.coinduceEquiv R (X.X 0)
      (charDown.comp (AddCommGrpCat.Hom.hom (φ.f 0))))) (by
      intro i _
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      refine CharacterModule.ext R fun r => ?_
      change ((φ.f 0) (r • (X.d i 0 x)) : ULift.{u} (AddCircle (1 : ℚ))).down = 0
      rw [← map_smul (X.d i 0).hom r x, additiveHom_d_apply_zero]
      rfl)

/-- In degree `0`, the coinduced form of `φ` takes `x` to the character `r ↦ φ (r x)` of `R`. -/
theorem homToCoefficient_apply (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj X ⟶ characterTarget.{u}) (x : X.X 0)
    (r : R) :
    coefficientValue ((homToCoefficient X φ).f 0 x) r =
      ((φ.f 0) (r • x) : ULift.{u} (AddCircle (1 : ℚ))).down := rfl

/-- A map of complexes of `R`-modules into `Hom_ℤ(R, ℚ/ℤ)`, read as a map of the underlying
complexes of abelian groups into `ℚ/ℤ`. -/
def coefficientToHom (X : CochainComplex (ModuleCat.{u} R) ℤ) (g : X ⟶ coefficientTarget R) :
    (CochainComplex.forget₂AddCommGrpCat R).obj X ⟶ characterTarget.{u} :=
  HomologicalComplex.mkHomToSingle
    (AddCommGrpCat.ofHom ((charEvalOne R).comp (g.f 0).hom.toAddMonoidHom)) (by
      intro i _
      have hc := g.comm i 0
      simp only [HomologicalComplex.single_obj_d, Limits.comp_zero] at hc
      apply AddCommGrpCat.hom_ext
      refine AddMonoidHom.ext fun x => ?_
      change charEvalOne R (g.f 0 (X.d i 0 x)) = 0
      rw [show g.f 0 (X.d i 0 x) = 0 from congrArg (fun f => f x) hc.symm]
      rfl)

/-- In degree `0`, the map of abelian groups attached to `g` takes `x` to `g (x) (1)`. -/
theorem coefficientToHom_apply (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : X ⟶ coefficientTarget R) (x : X.X 0) :
    ((coefficientToHom X g).f 0 x : ULift.{u} (AddCircle (1 : ℚ))).down =
      coefficientValue (g.f 0 x) 1 := rfl

/-- A map of complexes of abelian groups into `ℚ/ℤ` is determined by its coinduced form. -/
theorem homToCoefficient_injective (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    Function.Injective (homToCoefficient.{u} X) := by
  intro φ ψ h
  apply HomologicalComplex.to_single_hom_ext
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext fun x => ?_
  apply ULift.ext
  have hx := congrArg (fun g : X ⟶ coefficientTarget R => coefficientValue (g.f 0 x) 1) h
  simpa only [homToCoefficient_apply, one_smul] using hx

/-! ## The two equalities of Stacks 09K3 -/

section SecondEquality

variable (N : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)

/-- On homogeneous pure tensors, the coinduced form of a map of complexes of abelian groups
`N ⊗_A M → ℚ/ℤ` is the coinduced form of its pairing. -/
theorem homToCoefficient_tmul
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶ characterTarget.{u})
    (p q n : ℤ) (h : p + q = n) (x : N.grading p) (y : M.grading q) :
    ((homToCoefficient (tensorComplex N M) φ).f n).hom ((tensorTmul N M).map p q n h x y) =
      (characterBilinearToCoefficient (tensorToCharacterBilinear N M φ)).map p q n h x y := by
  by_cases hn : n = 0
  · subst hn
    have hq : q = -p := by omega
    subst hq
    refine CharacterModule.ext R fun r => ?_
    show ((φ.f 0) (r • (tensorTmul N M).map p (-p) 0 h x y) :
        ULift.{u} (AddCircle (1 : ℚ))).down =
      ((φ.f 0) ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x (r • y)) :
        ULift.{u} (AddCircle (1 : ℚ))).down
    rw [map_smul ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x) r y]
  · have := coefficientTarget_subsingleton (R := R) n hn
    exact Subsingleton.elim _ _

/-- A map of complexes of abelian groups `N ⊗_A M → ℚ/ℤ` is determined by its pairing. -/
theorem tensorToCharacterBilinear_injective :
    Function.Injective (tensorToCharacterBilinear N M) := by
  intro φ ψ hφψ
  apply homToCoefficient_injective (tensorComplex N M)
  refine tensorComplex_hom_ext N M fun p q n hpq x y => ?_
  rw [homToCoefficient_tmul, homToCoefficient_tmul, hφψ]

/-- Every differential graded bilinear pairing `N × M → ℚ/ℤ` is the pairing of a map of
complexes of abelian groups `N ⊗_A M → ℚ/ℤ`, namely of the one coinduced from the map of
complexes of `R`-modules the universal property of `N ⊗_A M` produces. -/
theorem tensorToCharacterBilinear_coefficientToHom (b : CharacterBilinear N M) :
    tensorToCharacterBilinear N M (coefficientToHom (tensorComplex N M)
      (tensorDesc N M (coefficientTarget R) (characterBilinearToCoefficient b))) = b := by
  refine CharacterBilinear.ext fun p => ?_
  refine AddMonoidHom.ext fun x => ?_
  refine CharacterModule.ext (M.grading (-p)) fun y => ?_
  show ((coefficientToHom (tensorComplex N M)
      (tensorDesc N M (coefficientTarget R) (characterBilinearToCoefficient b))).f 0
      ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x y) :
        ULift.{u} (AddCircle (1 : ℚ))).down = _
  rw [coefficientToHom_apply]
  show coefficientValue (((tensorDesc N M (coefficientTarget R)
    (characterBilinearToCoefficient b)).f 0).hom
      ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x y)) 1 = _
  rw [tensorDesc_apply]
  show b.pairing p x ((1 : R) • gradingCast M.grading (rfl : -p = -p) y) = _
  rw [one_smul]
  exact congrArg (fun z => b.pairing p x z) (Subtype.ext rfl)

/-- **Stacks 09K3, second equality.** For a right differential graded `A`-module `N` and a left
differential graded `A`-module `M`, maps of complexes of abelian groups `N ⊗_A M → ℚ/ℤ` are
exactly the differential graded `A`-bilinear pairings `N × M → ℚ/ℤ`. -/
@[stacks 09K3 "differential graded bilinear maps"]
def tensorCharacterBilinearEquiv :
    ((CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶ characterTarget.{u}) ≃
      CharacterBilinear N M where
  toFun := tensorToCharacterBilinear N M
  invFun b := coefficientToHom (tensorComplex N M)
    (tensorDesc N M (coefficientTarget R) (characterBilinearToCoefficient b))
  left_inv φ := tensorToCharacterBilinear_injective N M
    (tensorToCharacterBilinear_coefficientToHom N M (tensorToCharacterBilinear N M φ))
  right_inv := tensorToCharacterBilinear_coefficientToHom N M

/-- The second equality of Stacks 09K3 sends `φ` to the pairing `(x, y) ↦ φ (x ⊗ y)`; this
determines it. -/
theorem tensorCharacterBilinearEquiv_apply
    (φ : (CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶ characterTarget.{u})
    (p : ℤ) (x : N.grading p) (y : M.grading (-p)) :
    (tensorCharacterBilinearEquiv N M φ).pairing p x y =
      ((φ.f 0) ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x y) :
        ULift.{u} (AddCircle (1 : ℚ))).down := rfl

/-- **Stacks 09K3, first equality.** For a right differential graded `A`-module `N` and a left
differential graded `A`-module `M`, homomorphisms of right differential graded `A`-modules
`N → M^∨` into the character dual are exactly the maps of complexes of abelian groups
`N ⊗_A M → ℚ/ℤ`. -/
@[stacks 09K3 "maps into the dual"]
def homTensorCharacterEquiv :
    DifferentialGradedModule.Hom N (LeftModule.dual M) ≃
      ((CochainComplex.forget₂AddCommGrpCat R).obj (tensorComplex N M) ⟶
        characterTarget.{u}) :=
  (homCharacterBilinearEquiv N M).trans (tensorCharacterBilinearEquiv N M).symm

/-- The first equality of Stacks 09K3 sends a homomorphism `φ : N → M^∨` to the map of
complexes taking `x ⊗ y` to `φ(x)(y)`; this determines it. -/
theorem homTensorCharacterEquiv_apply
    (φ : DifferentialGradedModule.Hom N (LeftModule.dual M)) (p : ℤ) (x : N.grading p)
    (y : M.grading (-p)) :
    (((homTensorCharacterEquiv N M φ).f 0)
        ((tensorTmul N M).map p (-p) 0 (add_neg_cancel p) x y) :
          ULift.{u} (AddCircle (1 : ℚ))).down =
      LeftModule.dualChar (φ.toFun (x : N.M)) (y : M.M) := by
  have he := (tensorCharacterBilinearEquiv N M).apply_symm_apply
    (homCharacterBilinearEquiv N M φ)
  exact congrArg (fun b : CharacterBilinear N M => b.pairing p x y) he

end SecondEquality

end DifferentialGraded

end

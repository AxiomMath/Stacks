module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDual
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyLifting
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleHom
public import StacksFrontier.Algebra.DirectSum.ParityOperator
public import StacksFrontier.Algebra.Module.CharacterModule.Duality

/-! # Maps into a shift of the dual module in the homotopy category

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `A^∨` be its
graded `ℚ/ℤ`-dual, the right differential graded `A`-module
`DifferentialGradedModule.dualRegularModule`. A homomorphism `f : N ⟶ A^∨[k]` of right
differential graded `A`-modules is determined by the character `x ↦ f(x)(1)` of `N`, which is a
cocycle of the dual complex `N^∨` supported in degree `-k`, and it is null-homotopic as soon as
that character is a coboundary. Since `ℚ/ℤ` is divisible, hence injective, character duality is
exact, so for an acyclic `N` every such character *is* a coboundary. Consequently every shift of
`A^∨` lies in the right orthogonal of the acyclic objects of the homotopy category `K(A, d)`.

This is the input to Stacks 09KS that the modules with property (I) are assembled from, exactly
as `DifferentialGradedModule.leftOrthogonal_shift_regularModule` is the input to Stacks 09KM
that the modules with property (P) are assembled from.

## Main results

* `DifferentialGradedModule.d_gradedProjection_eq_zero`: the graded components of an element
  killed by the differential are killed by it.
* `DifferentialGradedModule.homotopic_zero_of_acyclic_hom_dualShift`: every homomorphism from an
  acyclic differential graded module into a shift of `A^∨` is null-homotopic.
* `DifferentialGradedModule.rightOrthogonal_acyclic_shift_dualRegularModule` and
  `rightOrthogonal_acyclic_shiftFunctor_dualRegularModule`: a shift of `A^∨` lies in the right
  orthogonal of the acyclic objects, in the two forms in which the shift of
  `(toHomotopyCategory A).obj (dualRegularModule A)` is presented.

## Implementation notes

The null-homotopy is written down explicitly rather than extracted from the identification of
the graded Hom into `A^∨` (Stacks 09K4): if `f : N ⟶ A^∨[k]` has character `λ` and `ν` is a
character of `N` with `ν ∘ d_N = λ`, then `x ↦ (a ↦ ν (x a))` is a homotopy from `f` to `0`.
Only one direction of 09K4 is used, and it is used in the elementary form `f(x)(a) = λ(x a)`,
which is immediate from `A`-linearity of `f` and `a · 1 = a`.

Two points need the grading rather than just the module structure. First, `λ` kills every
cocycle of `N`, which is where acyclicity enters: `λ` vanishes on the homogeneous pieces of
degree other than `-k` because `f(x)` is then a character supported away from `A^0`, and on the
piece of degree `-k` because a cocycle there is a coboundary. Second, the primitive `ν` produced
by exactness of character duality is replaced by its composite with the projection onto the
piece of degree `-k + 1`; this does not disturb `ν ∘ d_N = λ`, and it is what makes
`x ↦ (a ↦ ν (x a))` land in the graded dual and have the right degree.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following the Stacks Tag 09JJ formalization.

## References

* [Stacks Project, Tag 09K4](https://stacks.math.columbia.edu/tag/09K4) is the identification
  of the homotopy classes of maps into `A^∨[k]` with the cohomology of the dual complex, of
  which the vanishing below is the consequence used by
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS).
-/

@[expose] public noncomputable section

open CategoryTheory MulOpposite DifferentialGraded

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- The graded components of an element killed by the differential are themselves killed by it:
the differential is a grading-preserving map into the once-shifted module, so it commutes with
taking graded components. -/
theorem d_gradedProjection_eq_zero {A : DifferentialGradedAlgebra.{u, u} R}
    (N : DifferentialGradedModule.{u, u, u} A) {z : N.M} (hz : N.d z = 0) (n : ℤ) :
    N.d (DirectSum.gradedProjection N.grading n z) = 0 := by
  have h := DirectSum.coe_decompose_apply_map N.grading (shift N 1).grading N.d
    (fun i x hx => N.d_mem i x hx) z n
  rw [DirectSum.gradedProjection_apply, ← h, hz]
  simp

section Dual

variable {A : DifferentialGradedAlgebra.{u, u} R} (k : ℤ) {N : DifferentialGradedModule.{u, u, u} A}

/-! ### The interface to the dual module

Everything below sees `A^∨` only through the character of `A` underlying an element of it, the
right action and the differential computed on that character, and the description of
homogeneity as support in a single degree. -/

/-- The character of `A` underlying an element of `A^∨`. -/
private abbrev dualVal {A : DifferentialGradedAlgebra.{u, u} R} (x : (dualRegularModule A).M) :
    CharacterModule A.A := Subtype.val x

/-- An element of `A^∨` from a character lying in the graded dual. -/
private def dualMk {A : DifferentialGradedAlgebra.{u, u} R} (l : CharacterModule A.A)
    (hl : l ∈ LeftModule.dualCarrier (LeftModule.regular A)) : (dualRegularModule A).M :=
  ⟨l, hl⟩

/-- The character underlying an element built from a character is that character. -/
private theorem dualVal_dualMk (l : CharacterModule A.A)
    (hl : l ∈ LeftModule.dualCarrier (LeftModule.regular A)) : dualVal (dualMk l hl) = l := rfl

/-- An element of `A^∨` is determined by its underlying character. -/
private theorem dualVal_injective (A : DifferentialGradedAlgebra.{u, u} R) :
    Function.Injective (dualVal (A := A)) := Subtype.val_injective

/-- Addition in `A^∨` is addition of the underlying characters. -/
private theorem dualVal_add (x y : (dualRegularModule A).M) :
    dualVal (x + y) = dualVal x + dualVal y := rfl

/-- The right action on `A^∨`, computed on the underlying character. -/
private theorem dualVal_smul (c : A.Aᵐᵒᵖ) (x : (dualRegularModule A).M) (y : A.A) :
    dualVal (c • x) y = dualVal x (c.unop * y) := rfl

/-- Integer multiples in `A^∨`, computed on the underlying character. -/
private theorem dualVal_zsmul (c : ℤ) (x : (dualRegularModule A).M) (y : A.A) :
    dualVal (c • x) y = c • dualVal x y := rfl

/-- The differential of `A^∨`, computed on the underlying character: precomposition with
the signed differential of the algebra. -/
private theorem dualVal_d (x : (dualRegularModule A).M) (y : A.A) :
    dualVal ((dualRegularModule A).d x) y
      = dualVal x (LeftModule.signedDifferential (LeftModule.regular A) y) := rfl

/-- Homogeneity of degree `n` in `A^∨` is support of the underlying character in
degree `-n`. -/
private theorem mem_dualGrading_iff {n : ℤ} {x : (dualRegularModule A).M} :
    x ∈ (dualRegularModule A).grading n
      ↔ ∀ m : ℤ, m ≠ -n → ∀ y ∈ A.grading m, dualVal x y = 0 := Iff.rfl

/-- A sum of characters, evaluated. -/
private theorem charAdd_apply (l l' : CharacterModule A.A) (y : A.A) :
    (l + l') y = l y + l' y := rfl

/-- The signed differential of the algebra on a homogeneous element. -/
private theorem signedDiff_apply_mem {m : ℤ} {y : A.A} (hy : y ∈ A.grading m) :
    LeftModule.signedDifferential (LeftModule.regular A) y = (m.negOnePow : ℤ) • A.d y :=
  LeftModule.signedDifferential_apply_mem (LeftModule.regular A) hy

/-- The signed differential of the algebra kills the unit, since the unit is a cocycle of
degree zero. -/
private theorem signedDiff_one (A : DifferentialGradedAlgebra.{u, u} R) :
    LeftModule.signedDifferential (LeftModule.regular A) (1 : A.A) = 0 := by
  rw [signedDiff_apply_mem (SetLike.one_mem_graded A.grading), algebraDifferential_one,
    smul_zero]

/-- Two characters of a differential graded algebra agreeing on homogeneous elements are
equal. -/
private theorem char_eq_of_apply_grading (A : DifferentialGradedAlgebra.{u, u} R)
    {l l' : CharacterModule A.A}
    (h : ∀ (m : ℤ) (y : A.A), y ∈ A.grading m → l y = l' y) : l = l' := by
  refine CharacterModule.ext _ fun y => ?_
  exact LeftModule.induction_homogeneous (M := LeftModule.regular A) (p := fun z => l z = l' z)
    y h (by rw [map_zero, map_zero]) (fun z w hz hw => by rw [map_add, map_add, hz, hw])

/-! ### The character of a homomorphism into a shift of the dual -/

/-- The character of `N` attached to a homomorphism `N ⟶ A^∨[k]`: evaluation of the image
character at the unit of the algebra. -/
private def dualHomChar (f : N ⟶ shift (dualRegularModule A) k) : CharacterModule N.M where
  toFun x := dualVal (f.toFun x) (1 : A.A)
  map_zero' := by
    change dualVal (f.toFun 0) (1 : A.A) = 0
    rw [map_zero]
    rfl
  map_add' x y := by
    change dualVal (f.toFun (x + y)) (1 : A.A)
      = dualVal (f.toFun x) (1 : A.A) + dualVal (f.toFun y) (1 : A.A)
    rw [map_add]
    rfl

/-- A character of `N`, cut down to the graded piece of degree `q` by composing with the
projection onto that piece. -/
private def charProj (nu : CharacterModule N.M) (q : ℤ) : CharacterModule N.M where
  toFun z := nu (DirectSum.gradedProjection N.grading q z)
  map_zero' := by simp
  map_add' a b := by simp

/-- The cut-down character, evaluated. -/
private theorem charProj_apply (nu : CharacterModule N.M) (q : ℤ) (z : N.M) :
    charProj nu q z = nu (DirectSum.gradedProjection N.grading q z) := rfl

/-- A homomorphism into a shift of the dual is right multiplication followed by its character:
`f(x)(a) = λ(x a)`. This is the one direction of Stacks 09K4 that the null-homotopy needs. -/
private theorem dualVal_apply_eq (f : N ⟶ shift (dualRegularModule A) k) (x : N.M) (a : A.A) :
    dualVal (f.toFun x) a = dualHomChar k f (op a • x) := by
  show dualVal (f.toFun x) a = dualVal (f.toFun (op a • x)) (1 : A.A)
  rw [show f.toFun (op a • x) = op a • f.toFun x from f.map_smul x a, dualVal_smul,
    MulOpposite.unop_op, mul_one]

/-- The character of a homomorphism into a shift of the dual kills every coboundary of `N`. -/
private theorem dualHomChar_d (f : N ⟶ shift (dualRegularModule A) k) (x : N.M) :
    dualHomChar k f (N.d x) = 0 := by
  show dualVal (f.toFun (N.d x)) (1 : A.A) = 0
  rw [show f.toFun (N.d x) = (shift (dualRegularModule A) k).d (f.toFun x) from
    LinearMap.congr_fun f.map_d x, shift_d, LinearMap.smul_apply, Units.smul_def,
    dualVal_zsmul, dualVal_d, signedDiff_one, map_zero, smul_zero]

/-- The character of a homomorphism into `A^∨[k]` vanishes on every homogeneous piece of degree
other than `-k`, because the image character is then supported away from `A^0`. -/
private theorem dualHomChar_eq_zero_of_mem (f : N ⟶ shift (dualRegularModule A) k) {n : ℤ}
    {x : N.M} (hx : x ∈ N.grading n) (hn : n ≠ -k) : dualHomChar k f x = 0 := by
  show dualVal (f.toFun x) (1 : A.A) = 0
  have hmem : f.toFun x ∈ (dualRegularModule A).grading (n + k) := f.map_grading n x hx
  exact mem_dualGrading_iff.mp hmem 0 (by omega) (1 : A.A) (SetLike.one_mem_graded A.grading)

/-- The character of a homomorphism into `A^∨[k]` out of an acyclic module kills every cocycle
of `N`: the homogeneous pieces of degree other than `-k` are killed outright, and a cocycle in
degree `-k` is a coboundary. -/
private theorem dualHomChar_eq_zero_of_d_eq_zero (hN : N.toCochainComplex.Acyclic)
    (f : N ⟶ shift (dualRegularModule A) k) {z : N.M} (hz : N.d z = 0) :
    dualHomChar k f z = 0 := by
  classical
  rw [show z = ∑ n ∈ DFinsupp.support (DirectSum.decompose N.grading z),
      ((DirectSum.decompose N.grading z) n : N.M) from
    (DirectSum.sum_support_decompose N.grading z).symm, map_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  have hmem : ((DirectSum.decompose N.grading z) n : N.M) ∈ N.grading n :=
    ((DirectSum.decompose N.grading z) n).2
  by_cases hn : n = -k
  · subst hn
    have hdz : N.d ((DirectSum.decompose N.grading z) (-k) : N.M) = 0 := by
      have := d_gradedProjection_eq_zero N hz (-k)
      rwa [DirectSum.gradedProjection_apply] at this
    obtain ⟨y, _, hyd⟩ := exists_d_eq_of_acyclic hN (-k - 1)
      ((DirectSum.decompose N.grading z) (-k) : N.M) (by rwa [show -k - 1 + 1 = -k by ring])
      hdz
    rw [← hyd]
    exact dualHomChar_d k f y
  · exact dualHomChar_eq_zero_of_mem k f hmem hn

/-- Exactness of character duality: the character of a homomorphism into `A^∨[k]` out of an
acyclic module has a primitive, which may moreover be taken supported in degree `-k + 1`. -/
private theorem exists_primitive (hN : N.toCochainComplex.Acyclic)
    (f : N ⟶ shift (dualRegularModule A) k) :
    ∃ nu : CharacterModule N.M, (∀ x : N.M, nu (N.d x) = dualHomChar k f x) ∧
      ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0 := by
  have hexact : Function.Exact ((LinearMap.ker N.d).subtype) N.d := fun b =>
    ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, by rintro ⟨⟨c, hc⟩, rfl⟩; exact hc⟩
  have hvanish :
      CharacterModule.dual (R := R) (LinearMap.ker N.d).subtype (dualHomChar k f) = 0 := by
    refine CharacterModule.ext _ fun z => ?_
    show dualHomChar k f (z : N.M) = 0
    exact dualHomChar_eq_zero_of_d_eq_zero k hN f z.2
  obtain ⟨nu, hnu⟩ :=
    (CharacterModule.dual_exact (R := R) (LinearMap.ker N.d).subtype N.d hexact
      (dualHomChar k f)).mp hvanish
  refine ⟨charProj nu (-k + 1), ?_, ?_⟩
  · intro x
    induction x using DirectSum.Decomposition.inductionOn N.grading with
    | zero => simp [charProj_apply]
    | @homogeneous j x =>
        rw [charProj_apply]
        by_cases hj : j = -k
        · subst hj
          rw [DirectSum.gradedProjection_of_mem_same N.grading
            (show N.d (x : N.M) ∈ N.grading (-k + 1) from N.d_mem (-k) _ x.2)]
          exact DFunLike.congr_fun hnu (x : N.M)
        · rw [DirectSum.gradedProjection_of_mem_ne N.grading
            (show N.d (x : N.M) ∈ N.grading (j + 1) from N.d_mem j _ x.2)
            (by omega), map_zero]
          exact (dualHomChar_eq_zero_of_mem k f x.2 hj).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro q z hz hq
    rw [charProj_apply, DirectSum.gradedProjection_of_mem_ne N.grading hz hq, map_zero]

/-! ### The null-homotopy -/

/-- The character of `A` attached to an element of `N` by a primitive `ν`: the right
multiplication pairing `a ↦ ν (x a)`. -/
private def homotopyFun (nu : CharacterModule N.M) (x : N.M) : CharacterModule A.A where
  toFun a := nu (op a • x)
  map_zero' := by simp
  map_add' a b := by rw [MulOpposite.op_add, add_smul, map_add]

/-- The right multiplication pairing, evaluated. -/
private theorem homotopyFun_apply (nu : CharacterModule N.M) (x : N.M) (a : A.A) :
    homotopyFun nu x a = nu (op a • x) := rfl

/-- The right multiplication pairing with zero is zero. -/
private theorem homotopyFun_zero (nu : CharacterModule N.M) : homotopyFun nu (0 : N.M) = 0 :=
  CharacterModule.ext _ fun a => by
    rw [homotopyFun_apply, smul_zero, map_zero]
    rfl

/-- The right multiplication pairing is additive in the element. -/
private theorem homotopyFun_add (nu : CharacterModule N.M) (x y : N.M) :
    homotopyFun nu (x + y) = homotopyFun nu x + homotopyFun nu y :=
  CharacterModule.ext _ fun a => by
    rw [homotopyFun_apply, smul_add, map_add, charAdd_apply, homotopyFun_apply,
      homotopyFun_apply]

/-- The pairing with a primitive supported in degree `-k + 1` is supported in the degree a
homotopy into `A^∨[k]` requires, namely one less than the degree of its argument. -/
private theorem homotopyFun_mem (nu : CharacterModule N.M)
    (hnu : ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0) {j : ℤ} {x : N.M}
    (hx : x ∈ N.grading j) :
    homotopyFun nu x ∈ LeftModule.dualPiece (LeftModule.regular A) (j + k - 1) := by
  intro p hp a ha
  rw [homotopyFun_apply]
  exact hnu (j + p) _ (N.smul_mem j p x a hx ha) (by omega)

/-- The pairing with a primitive supported in degree `-k + 1` lands in the graded dual. -/
private theorem homotopyFun_mem_dualCarrier (nu : CharacterModule N.M)
    (hnu : ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0) (x : N.M) :
    homotopyFun nu x ∈ LeftModule.dualCarrier (LeftModule.regular A) := by
  induction x using DirectSum.Decomposition.inductionOn N.grading with
  | zero =>
      rw [homotopyFun_zero]
      exact Submodule.zero_mem _
  | @homogeneous j x =>
      exact Submodule.mem_iSup_of_mem (j + k - 1) (homotopyFun_mem k nu hnu x.2)
  | add x y hx hy =>
      rw [homotopyFun_add]
      exact Submodule.add_mem _ hx hy

/-- The pairing with a primitive, as an element of `A^∨`. -/
private def homotopyElt (nu : CharacterModule N.M)
    (hnu : ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0) (x : N.M) :
    (dualRegularModule A).M :=
  dualMk (homotopyFun nu x) (homotopyFun_mem_dualCarrier k nu hnu x)

/-- The character underlying the pairing is the pairing. -/
private theorem dualVal_homotopyElt (nu : CharacterModule N.M)
    (hnu : ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0) (x : N.M) (a : A.A) :
    dualVal (homotopyElt k nu hnu x) a = nu (op a • x) := rfl

@[simp] private theorem homotopyElt_zero (nu : CharacterModule N.M)
    (hnu : ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0) :
    homotopyElt k nu hnu (0 : N.M) = 0 :=
  dualVal_injective A (homotopyFun_zero nu)

@[simp] private theorem homotopyElt_add (nu : CharacterModule N.M)
    (hnu : ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0) (x y : N.M) :
    homotopyElt k nu hnu (x + y) = homotopyElt k nu hnu x + homotopyElt k nu hnu y :=
  dualVal_injective A (homotopyFun_add nu x y)

/-- The pairing is compatible with the right action of the algebra. -/
private theorem homotopyElt_smul (nu : CharacterModule N.M)
    (hnu : ∀ (q : ℤ) (z : N.M), z ∈ N.grading q → q ≠ -k + 1 → nu z = 0) (c : A.Aᵐᵒᵖ)
    (x : N.M) : homotopyElt k nu hnu (c • x) = c • homotopyElt k nu hnu x :=
  dualVal_injective A (char_eq_of_apply_grading A fun _ a _ => by
    rw [dualVal_homotopyElt, dualVal_smul, dualVal_homotopyElt, smul_smul]
    rfl)

/-- **Every homomorphism from an acyclic differential graded module into a shift of `A^∨` is
null-homotopic.** The character of the homomorphism is a cocycle of the dual complex of `N`;
acyclicity of `N` and exactness of character duality make it a coboundary, and the pairing with
a primitive is a null-homotopy. -/
theorem homotopic_zero_of_acyclic_hom_dualShift (A : DifferentialGradedAlgebra.{u, u} R) (k : ℤ)
    {N : DifferentialGradedModule.{u, u, u} A} (hN : N.toCochainComplex.Acyclic)
    (f : N ⟶ shift (dualRegularModule A) k) : Homotopic f 0 := by
  obtain ⟨nu, hnud, hnu⟩ := exists_primitive k hN f
  refine ⟨{
    toLinearMap :=
      { toFun := homotopyElt k nu hnu
        map_add' := homotopyElt_add k nu hnu
        map_smul' := homotopyElt_smul k nu hnu }
    map_grading := ?_
    homotopy_eq := ?_ }⟩
  · intro n x hx
    have h := homotopyFun_mem k nu hnu hx
    rw [show n + k - 1 = n - 1 + k by ring] at h
    exact mem_dualGrading_iff.mpr fun m hm a ha => h m hm a ha
  · intro x
    rw [Hom.hom_zero_toFun]
    simp only [LinearMap.zero_apply, sub_zero, LinearMap.coe_mk, AddHom.coe_mk]
    induction x using DirectSum.Decomposition.inductionOn N.grading with
    | zero => simp
    | @homogeneous j x =>
        refine dualVal_injective A (char_eq_of_apply_grading A fun p a ha => ?_)
        rw [dualVal_add, charAdd_apply]
        have hlhs : dualVal (f.toFun (x : N.M)) a
            = nu (op a • N.d (x : N.M))
              + ((j.negOnePow : ℤ) • nu (op (A.d a) • (x : N.M))) := by
          rw [dualVal_apply_eq k f (x : N.M) a, ← hnud, leibniz_apply N j (x : N.M) x.2 a,
            map_add, map_zsmul]
        have hrhs : dualVal ((shift (dualRegularModule A) k).d
              (homotopyElt k nu hnu (x : N.M))) a
            = ((k.negOnePow : ℤ) * (p.negOnePow : ℤ)) • nu (op (A.d a) • (x : N.M)) := by
          rw [shift_d, LinearMap.smul_apply, Units.smul_def, dualVal_zsmul, dualVal_d,
            dualVal_homotopyElt, signedDiff_apply_mem ha,
            show op ((p.negOnePow : ℤ) • A.d a) • (x : N.M)
                = (p.negOnePow : ℤ) • (op (A.d a) • (x : N.M)) from by
              rw [← smul_assoc]
              rfl,
            map_zsmul, smul_smul]
        -- the two signs agree wherever the pairing is nonzero
        have hcancel : (j.negOnePow : ℤ) • nu (op (A.d a) • (x : N.M))
            = ((k.negOnePow : ℤ) * (p.negOnePow : ℤ)) • nu (op (A.d a) • (x : N.M)) := by
          by_cases hdeg : j + (p + 1) = -k + 1
          · have hsign : (j.negOnePow : ℤ) = (k.negOnePow : ℤ) * (p.negOnePow : ℤ) := by
              rw [show j = -(k + p) by omega, Int.negOnePow_neg, Int.negOnePow_add]
              push_cast
              ring
            rw [hsign]
          · rw [hnu _ _ (N.smul_mem j (p + 1) (x : N.M) (A.d a) x.2 (A.d_mem p a ha)) hdeg,
              smul_zero, smul_zero]
        rw [hlhs, hrhs, dualVal_homotopyElt, hcancel]
        abel
    | add x y hx hy =>
        simp only [map_add, homotopyElt_add]
        rw [hx, hy]
        abel

/-- A shift of `A^∨` lies in the right orthogonal of the acyclic objects of the homotopy
category. -/
theorem rightOrthogonal_acyclic_shift_dualRegularModule (A : DifferentialGradedAlgebra.{u, u} R)
    (k : ℤ) :
    (acyclic' A).rightOrthogonal
      ((toHomotopyCategory.{u, u, u} A).obj (shift (dualRegularModule A) k)) :=
  (rightOrthogonal_acyclic_iff _).mpr
    fun _ hN f => homotopic_zero_of_acyclic_hom_dualShift A k hN f

/-- The same statement for the shift taken in the homotopy category. -/
theorem rightOrthogonal_acyclic_shiftFunctor_dualRegularModule
    (A : DifferentialGradedAlgebra.{u, u} R) (k : ℤ) :
    (acyclic' A).rightOrthogonal
      (((toHomotopyCategory.{u, u, u} A).obj (dualRegularModule A))⟦k⟧) := by
  rw [CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ (dualRegularModule A) k]
  exact rightOrthogonal_acyclic_shift_dualRegularModule A k

end Dual

end DifferentialGradedModule

end

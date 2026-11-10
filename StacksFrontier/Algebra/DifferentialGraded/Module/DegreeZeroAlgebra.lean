module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.Quotient
public import StacksFrontier.Algebra.DifferentialGraded.Module.Abelian
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedForgetful

/-! # An ordinary algebra as a differential graded algebra in degree zero

Let `R` be a commutative ring and `S` an `R`-algebra, not necessarily commutative. Grading `S` by
putting it in degree zero and taking the zero differential makes it a differential graded
`R`-algebra `DifferentialGradedAlgebra.degreeZero R S`. A right differential graded module over it
is the same thing as a cochain complex of right `S`-modules: the right action of `S` preserves
each homogeneous component, so the components are right `S`-modules and the differential is
`S`-linear.

Right `S`-modules are left modules over any `R`-algebra `A` identified with `Sᵐᵒᵖ`; such an
identification is the class `DifferentialGradedAlgebra.IsOppositeAlgebra R S A`. Both the case
`A = Sᵐᵒᵖ` and, for commutative `S`, the case `A = S` are instances, so the identification below
reads simultaneously as an equivalence with complexes of `Sᵐᵒᵖ`-modules and, for commutative `S`,
with complexes of `S`-modules.

This file makes that identification precise and carries it to derived categories, which is what
lets a statement about the derived category of an ordinary ring be read in the differential
graded world.

## Main definitions

* `DifferentialGradedAlgebra.degreeZero`: the ordinary algebra `S` as a differential graded
  `R`-algebra concentrated in degree zero with zero differential.
* `DifferentialGradedAlgebra.IsOppositeAlgebra`: an identification of `S` with the opposite
  algebra of `A`, and `DifferentialGradedAlgebra.oppositeEquiv` the resulting ring isomorphism
  `A ≃+* Sᵐᵒᵖ`.
* `DifferentialGradedModule.degreeZeroTotalFunctor`: a cochain complex of `A`-modules read as a
  differential graded module over `degreeZero R S`, by taking the direct sum of its terms.
* `DifferentialGradedModule.degreeZeroComponentFunctor`: the inverse construction, taking the
  homogeneous components of a differential graded module.
* `DifferentialGradedModule.degreeZeroEquivalence`: the resulting equivalence
  `Mod_(degreeZero R S) ≌ CochainComplex (ModuleCat A) ℤ`.
* `DifferentialGradedModule.degreeZeroDerivedEquivalence`: the induced equivalence
  `D(degreeZero R S, d) ≌ D(A)`.

## Main results

* `DifferentialGradedModule.degreeZeroTotalForgetIso`: the complex of `R`-modules underlying the
  differential graded module attached to `K` is `K` with scalars restricted to `R`.
* `DifferentialGradedModule.degreeZeroDerivedFactorization`: the quasi-inverse of the derived
  equivalence is the total-direct-sum functor read through the localizations.

## Implementation notes

Both the base ring, the algebra and the modules live in a single universe `u`, which is the
encoding of the differential graded chapter in this tree (Tag 09JJ).

The algebra in degree zero, `degreeZero R S`, is built for an arbitrary `R`-algebra `S`. The
identification with cochain complexes is by *right* `S`-modules, which is what the differential
graded encoding of a right module over `degreeZero R S` asks for; a right `S`-module is a left
`A`-module for any `A` identified with `Sᵐᵒᵖ`, and that identification — rather than
commutativity of the algebra — is what carries the right action across. For a commutative
algebra the identification is `AlgEquiv.toOpposite`, so the equivalence with complexes of modules
over the algebra itself is a literal instance of the statement here.

The `R`-module structures on the terms of a complex of `A`-modules are the restrictions along
`R → A`, recorded as local instances.

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) for differential graded
  modules, and [Tag 061V](https://stacks.math.columbia.edu/tag/061V) for differential graded
  algebras.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace DifferentialGradedAlgebra

section DegreeZero

variable (R : Type u) [CommRing R] (A : Type u) [Ring A] [Algebra R A]

/-- The grading of an `R`-algebra that puts the whole of it in degree zero. -/
def degreeZeroGrading (n : ℤ) : Submodule R A := if n = 0 then ⊤ else ⊥

/-- The degree-zero part of the degree-zero grading is the whole algebra. -/
theorem degreeZeroGrading_zero : degreeZeroGrading R A 0 = ⊤ := by
  simp [degreeZeroGrading]

/-- Every nonzero degree of the degree-zero grading is zero. -/
theorem degreeZeroGrading_eq_bot {n : ℤ} (hn : n ≠ 0) : degreeZeroGrading R A n = ⊥ := by
  simp [degreeZeroGrading, hn]

/-- The degree-zero grading is a graded-algebra structure: the direct sum decomposition is the
one-term decomposition. -/
noncomputable instance instGradedAlgebraDegreeZeroGrading :
    GradedAlgebra (degreeZeroGrading R A) where
  one_mem := by simp [degreeZeroGrading]
  mul_mem := by
    intro i j a b ha hb
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · simp [degreeZeroGrading, hj]
      · have hb0 : b = 0 := by simpa [degreeZeroGrading, hj] using hb
        simp [hb0]
    · have ha0 : a = 0 := by simpa [degreeZeroGrading, hi] using ha
      subst a
      simp
  decompose' a := DirectSum.of (fun n => degreeZeroGrading R A n) 0
    ⟨a, by simp [degreeZeroGrading]⟩
  left_inv := by intro a; simp
  right_inv := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact map_zero _
    | of n a =>
      by_cases hn : n = 0
      · subst n; simp
      · have ha : a = 0 := by
          apply Subtype.ext
          simpa [degreeZeroGrading, hn] using a.property
        subst a
        simp only [map_zero]
        exact map_zero _
    | add x y hx hy =>
      simp only [map_add]
      change DirectSum.of _ 0
        (⟨(DirectSum.coeAddMonoidHom _ x), by simp [degreeZeroGrading]⟩ +
          ⟨(DirectSum.coeAddMonoidHom _ y), by simp [degreeZeroGrading]⟩) = x + y
      rw [map_add]
      exact congrArg₂ (· + ·) hx hy

/-- An ordinary `R`-algebra `A`, regarded as a differential graded `R`-algebra concentrated in
degree zero with zero differential. -/
noncomputable abbrev degreeZero : DifferentialGradedAlgebra.{u, u} R where
  A := A
  grading := degreeZeroGrading R A
  d := 0
  d_comp_d := by simp
  d_mem := by intros; simp
  leibniz := by intros; simp

end DegreeZero

/-! ### Opposite algebras

A right module over `S` is a left module over any algebra identified with the opposite algebra of
`S`. The identification is data, carried by the class below; its two instances are a commutative
algebra, which is its own opposite, and `Sᵐᵒᵖ` for an arbitrary `S`. -/

/-- An identification of `S` with the opposite algebra of `A`, as `R`-algebras. A right
`S`-module is then a left `A`-module, by `DifferentialGradedAlgebra.oppositeEquiv`.

`S` is an output: it is the algebra whose right modules are the `A`-modules, and letting
instance resolution produce it from `A` is what keeps the degree-zero comparison usable with the
algebra alone named. -/
class IsOppositeAlgebra (R : Type u) [CommRing R] (S : outParam (Type u)) [Ring S] [Algebra R S]
    (A : Type u) [Ring A] [Algebra R A] where
  /-- The identification of `S` with the opposite algebra of `A`. -/
  equiv : S ≃ₐ[R] Aᵐᵒᵖ

/-- A commutative algebra is its own opposite. -/
instance instIsOppositeAlgebraSelf (R : Type u) [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] : IsOppositeAlgebra R A A := ⟨AlgEquiv.toOpposite R A⟩

/-- The opposite algebra of `S` is `Sᵐᵒᵖ`. -/
instance instIsOppositeAlgebraOp (R : Type u) [CommRing R] (S : Type u) [Ring S]
    [Algebra R S] : IsOppositeAlgebra R S Sᵐᵒᵖ := ⟨AlgEquiv.opOp R S⟩

/-- `A` is the opposite algebra of `Aᵐᵒᵖ`: this is the identification that reads a statement
about left `A`-modules, for the algebra `A` one is given, as one about right `Aᵐᵒᵖ`-modules.

Deliberately not an instance. `S` is an output of `IsOppositeAlgebra`, and as an instance this
would compete with `DifferentialGradedAlgebra.instIsOppositeAlgebraSelf` and
`DifferentialGradedAlgebra.instIsOppositeAlgebraOp` for the same goal and silently change which
algebra the differential graded side is taken over; supply it with `letI` where it is wanted. -/
@[instance_reducible] def IsOppositeAlgebra.opSelf (R : Type u) [CommRing R] (A : Type u)
    [Ring A] [Algebra R A] : IsOppositeAlgebra R Aᵐᵒᵖ A := ⟨AlgEquiv.refl⟩

section Opposite

variable (R : Type u) [CommRing R] (S : Type u) [Ring S] [Algebra R S]
  (A : Type u) [Ring A] [Algebra R A] [IsOppositeAlgebra R S A]

/-- The ring isomorphism `A ≃+* Sᵐᵒᵖ` attached to an identification of `S` with `Aᵐᵒᵖ`: the right
action of `a : A` on a right `S`-module is the action of `oppositeEquiv R S A a`. -/
def oppositeEquiv : A ≃+* Sᵐᵒᵖ :=
  (RingEquiv.opOp A).trans
    (RingEquiv.op (IsOppositeAlgebra.equiv (R := R) (S := S) (A := A)).symm.toRingEquiv)

/-- The value of `oppositeEquiv R S A` on `a : A`, in terms of `IsOppositeAlgebra.equiv`. -/
theorem oppositeEquiv_apply (a : A) :
    oppositeEquiv R S A a =
      MulOpposite.op ((IsOppositeAlgebra.equiv (R := R) (S := S) (A := A)).symm
        (MulOpposite.op a)) := rfl

/-- The inverse of `oppositeEquiv R S A`, in terms of `IsOppositeAlgebra.equiv`. -/
theorem oppositeEquiv_symm_apply (s : Sᵐᵒᵖ) :
    (oppositeEquiv R S A).symm s =
      ((IsOppositeAlgebra.equiv (R := R) (S := S) (A := A)) (MulOpposite.unop s)).unop := rfl

/-- The identification of `A` with `Sᵐᵒᵖ` is `R`-linear. -/
theorem oppositeEquiv_smul (r : R) (a : A) :
    oppositeEquiv R S A (r • a) = r • oppositeEquiv R S A a :=
  congrArg MulOpposite.op
    (map_smul (IsOppositeAlgebra.equiv (R := R) (S := S) (A := A)).symm r (MulOpposite.op a))

/-- The identification of `Sᵐᵒᵖ` with `A` is `R`-linear. -/
theorem oppositeEquiv_symm_smul (r : R) (s : Sᵐᵒᵖ) :
    (oppositeEquiv R S A).symm (r • s) = r • (oppositeEquiv R S A).symm s :=
  congrArg MulOpposite.unop
    (map_smul (IsOppositeAlgebra.equiv (R := R) (S := S) (A := A)) r (MulOpposite.unop s))

/-- The identification of `A` with `Sᵐᵒᵖ` is a homomorphism of `R`-algebras. -/
theorem oppositeEquiv_algebraMap (r : R) :
    oppositeEquiv R S A (algebraMap R A r) = algebraMap R Sᵐᵒᵖ r := by
  rw [oppositeEquiv_apply,
    show MulOpposite.op (algebraMap R A r) = algebraMap R Aᵐᵒᵖ r from rfl,
    AlgEquiv.commutes]
  rfl

end Opposite

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]

/-! ### A complex of `A`-modules as a differential graded module in degree zero -/

/-- The `R`-module structure on a term of a complex of `A`-modules, by restriction along
`R → A`. -/
@[instance_reducible] noncomputable def complexModuleR
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) : Module R (K.X n) :=
  @Module.compHom A R (K.X n) _ _ _ _ (algebraMap R A)

attribute [local instance] complexModuleR

/-- The `R`-action on a term of a complex of `A`-modules is compatible with the `A`-action. -/
theorem complexModuleR_isScalarTower (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    IsScalarTower R A (K.X n) where
  smul_assoc r a x := by
    change (r • a) • x = algebraMap R A r • (a • x)
    rw [Algebra.smul_def, mul_smul]

attribute [local instance] complexModuleR_isScalarTower

/-- The direct sum of the terms of a complex of `A`-modules. -/
abbrev complexTotal (K : CochainComplex (ModuleCat.{u} A) ℤ) :=
  DirectSum ℤ (fun n => K.X n)

/-- The degree-`n` part of the direct sum of the terms of a complex. -/
noncomputable def complexGrading (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    Submodule R (complexTotal K) :=
  LinearMap.range (DirectSum.lof R ℤ (fun n => K.X n) n)

/-- The direct-sum decomposition of `⊕_n K^n` by the degrees. -/
noncomputable def complexDecompose (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    complexTotal K →ₗ[R] DirectSum ℤ (fun n => complexGrading (R := R) K n) :=
  DirectSum.toModule R ℤ _ (fun n =>
    (DirectSum.lof R ℤ (fun n => complexGrading (R := R) K n) n).comp
      (DirectSum.lof R ℤ (fun n => K.X n) n).rangeRestrict)

/-- The degrees decompose the direct sum of the terms of a complex. -/
@[instance_reducible] noncomputable def complexGradingDecomposition
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    DirectSum.Decomposition (complexGrading (R := R) K) := by
  apply DirectSum.Decomposition.ofLinearMap (complexGrading (R := R) K)
    (complexDecompose (R := R) K)
  · apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap (complexGrading (R := R) K)
      (complexDecompose (R := R) K (DirectSum.lof R ℤ (fun n => K.X n) n x)) = _
    rw [complexDecompose, DirectSum.toModule_lof]
    exact DirectSum.coeLinearMap_lof (complexGrading (R := R) K) n
      ((DirectSum.lof R ℤ (fun n => K.X n) n).rangeRestrict x)
  · apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    rintro ⟨x, y, rfl⟩
    change complexDecompose (R := R) K
      (DirectSum.coeLinearMap (complexGrading (R := R) K)
        (DirectSum.lof R ℤ (fun n => complexGrading (R := R) K n) n _)) = _
    rw [DirectSum.coeLinearMap_lof]
    change complexDecompose (R := R) K (DirectSum.lof R ℤ (fun n => K.X n) n y) = _
    rw [complexDecompose, DirectSum.toModule_lof]
    rfl

/-- The differential of a complex of `A`-modules, read on the direct sum of its terms. -/
noncomputable def complexDifferential (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    complexTotal K →ₗ[R] complexTotal K :=
  DirectSum.toModule R ℤ (complexTotal K) (fun n =>
    (DirectSum.lof R ℤ (fun n => K.X n) (n + 1)).comp
      (LinearMap.restrictScalars R (K.d n (n + 1)).hom))

/-- The total differential on a homogeneous element of degree `n`, written with `DirectSum.lof`,
is the differential `K.d n (n + 1)` of the complex. -/
theorem complexDifferential_lof (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (x : K.X n) :
    complexDifferential (R := R) K (DirectSum.lof R ℤ (fun n => K.X n) n x) =
      DirectSum.lof R ℤ (fun n => K.X n) (n + 1) (K.d n (n + 1) x) := by
  simp [complexDifferential]

/-- The total differential on a homogeneous element of degree `n`, written with `DirectSum.of`,
is the differential `K.d n (n + 1)` of the complex. -/
theorem complexDifferential_of (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (x : K.X n) :
    complexDifferential (R := R) K (DirectSum.of (fun n => K.X n) n x) =
      DirectSum.of (fun n => K.X n) (n + 1) (K.d n (n + 1) x) :=
  complexDifferential_lof K n x

/-- The total differential of a complex of `A`-modules is `A`-linear. -/
theorem complexDifferential_smul (K : CochainComplex (ModuleCat.{u} A) ℤ) (a : A)
    (x : complexTotal K) :
    complexDifferential (R := R) K (a • x) = a • complexDifferential (R := R) K x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x =>
    rw [← DirectSum.lof_eq_of A, ← map_smul]
    simp only [DirectSum.lof_eq_of, complexDifferential_of]
    change DirectSum.lof A ℤ (fun n => K.X n) (n + 1)
      (K.d n (n + 1) (a • x)) = a • DirectSum.lof A ℤ (fun n => K.X n) (n + 1)
        (K.d n (n + 1) x)
    simp only [map_smul]
  | add x y hx hy => simp [smul_add, map_add, hx, hy]

/-- The degree-`n` part of `⊕_m K^m` is `K^n`. -/
noncomputable def complexComponent (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    complexGrading (R := R) K n ≃ₗ[R] K.X n where
  toFun x := DirectSum.component R ℤ (fun n => K.X n) n x
  invFun x := ⟨DirectSum.lof R ℤ (fun n => K.X n) n x, ⟨x, rfl⟩⟩
  left_inv := by
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    simp
  right_inv x := by simp
  map_add' x y := map_add _ _ _
  map_smul' r x := map_smul _ _ _

/-! ### Reading a complex of `A`-modules as a differential graded module over `S`

From here on `S` is an `R`-algebra whose opposite is identified with `A`; a complex of
`A`-modules is then a complex of right `S`-modules. -/

variable {S : Type u} [Ring S] [Algebra R S] [IsOppositeAlgebra R S A]

/-- A cochain complex of `A`-modules, read as a differential graded module over `S` in degree
zero: the direct sum of its terms, graded by the degree, with the differential of the
complex. -/
noncomputable def degreeZeroTotal (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    DifferentialGradedModule (degreeZero R S) := by
  letI : Module (degreeZero R S).Aᵐᵒᵖ (complexTotal K) :=
    Module.compHom _ (oppositeEquiv R S A).symm.toRingHom
  haveI : IsScalarTower R (degreeZero R S).Aᵐᵒᵖ (complexTotal K) := by
    constructor
    intro r a x
    change ((oppositeEquiv R S A).symm (r • a) : A) • x =
      r • (((oppositeEquiv R S A).symm a : A) • x)
    rw [oppositeEquiv_symm_smul]
    exact smul_assoc r ((oppositeEquiv R S A).symm a : A) x
  letI := complexGradingDecomposition (R := R) K
  refine {
    M := complexTotal K
    grading := complexGrading (R := R) K
    smul_mem := ?_
    d := complexDifferential (R := R) K
    d_comp_d := ?_
    d_mem := ?_
    leibniz := ?_ }
  · intro n m x a hx ha
    change ((oppositeEquiv R S A).symm (MulOpposite.op a) : A) • x ∈
      complexGrading (R := R) K (n + m)
    by_cases hm : m = 0
    · subst m
      simp only [add_zero]
      rcases hx with ⟨y, rfl⟩
      exact ⟨((oppositeEquiv R S A).symm (MulOpposite.op a) : A) • y,
        (DirectSum.lof A ℤ (fun n => K.X n) n).map_smul _ y⟩
    · have ha0 : a = 0 := by
        simpa [degreeZero, degreeZeroGrading, hm] using ha
      rw [ha0, MulOpposite.op_zero, map_zero, zero_smul]
      exact Submodule.zero_mem _
  · apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, complexDifferential_lof]
    have hd := congrArg (fun f : K.X n ⟶ K.X (n + 1 + 1) => f x)
      (K.d_comp_d n (n + 1) (n + 1 + 1))
    change (K.d (n + 1) (n + 1 + 1)) (K.d n (n + 1) x) = 0 at hd
    simp only [hd, map_zero, LinearMap.zero_apply]
  · rintro n _ ⟨x, rfl⟩
    exact ⟨K.d n (n + 1) x, (complexDifferential_lof K n x).symm⟩
  · intro n m x a hx ha
    change complexDifferential (R := R) K
        (((oppositeEquiv R S A).symm (MulOpposite.op a) : A) • x) =
      ((oppositeEquiv R S A).symm (MulOpposite.op a) : A) • complexDifferential (R := R) K x +
        (n.negOnePow : ℤ) •
          (((oppositeEquiv R S A).symm (MulOpposite.op ((0 : S →ₗ[R] S) a)) : A) • x)
    rw [complexDifferential_smul]
    simp

/-- A cochain map, read as a homomorphism of differential graded modules in degree zero. -/
noncomputable def degreeZeroTotalMap {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L) :
    degreeZeroTotal (R := R) (S := S) K ⟶ degreeZeroTotal (R := R) (S := S) L where
  toFun := (DirectSum.lmap (fun n => (f.f n).hom)).restrictScalars R
  map_smul x a := (DirectSum.lmap (fun n => (f.f n).hom)).map_smul _ x
  map_grading n x hx := by
    rcases hx with ⟨x, rfl⟩
    exact ⟨f.f n x, (DirectSum.lmap_lof (fun n => (f.f n).hom) n x).symm⟩
  map_d := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change (DirectSum.lmap (fun n => (f.f n).hom))
        (complexDifferential (R := R) K (DirectSum.lof R ℤ (fun n => K.X n) n x)) =
      complexDifferential (R := R) L
        ((DirectSum.lmap (fun n => (f.f n).hom)) (DirectSum.lof R ℤ (fun n => K.X n) n x))
    simp only [DirectSum.lof_eq_of, complexDifferential_of, DirectSum.lmap_of, ModuleCat.Hom.hom]
    apply congrArg (DirectSum.of (fun n => L.X n) (n + 1))
    exact (congrArg (fun g : K.X n ⟶ L.X (n + 1) => g x) (f.comm n (n + 1))).symm

/-- Cochain complexes of `A`-modules as differential graded modules over `S` in degree zero. -/
noncomputable def degreeZeroTotalFunctor (R : Type u) [CommRing R] {S : Type u} [Ring S]
    [Algebra R S] (A : Type u) [Ring A] [Algebra R A] [IsOppositeAlgebra R S A] :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ DifferentialGradedModule (degreeZero R S) where
  obj K := degreeZeroTotal (R := R) (S := S) K
  map f := degreeZeroTotalMap (R := R) (S := S) f
  map_id K := by
    apply DifferentialGradedModule.Hom.ext
    change (DirectSum.lmap
      (fun n => (𝟙 (K.X n) : K.X n ⟶ K.X n).hom)).restrictScalars R = LinearMap.id
    simp
  map_comp f g := by
    apply DifferentialGradedModule.Hom.ext
    change (DirectSum.lmap (fun n => (f.f n ≫ g.f n).hom)).restrictScalars R =
      ((DirectSum.lmap (fun n => (g.f n).hom)).restrictScalars R).comp
        ((DirectSum.lmap (fun n => (f.f n).hom)).restrictScalars R)
    simp [DirectSum.lmap_comp]

/-! ### The homogeneous components of a differential graded module in degree zero -/

/-- The right `S`-action on a differential graded module over `S` in degree zero, as an action of
the opposite ring of `S` itself. -/
@[instance_reducible] noncomputable def degreeZeroOppositeModule
    (M : DifferentialGradedModule (degreeZero R S)) : Module Sᵐᵒᵖ M.M :=
  M.rmodule

attribute [local instance] degreeZeroOppositeModule

/-- The `Sᵐᵒᵖ`-action on a differential graded module over `S` in degree zero is compatible with
the `R`-action. -/
theorem degreeZeroOppositeModule_isScalarTower (M : DifferentialGradedModule (degreeZero R S)) :
    IsScalarTower R Sᵐᵒᵖ M.M :=
  M.isScalarTower

attribute [local instance] degreeZeroOppositeModule_isScalarTower

/-- The `A`-action on a homogeneous component of a differential graded module over `S` in degree
zero: the right action of `S` preserves the degree, because `S` sits in degree zero, and `A` acts
through the identification of `A` with `Sᵐᵒᵖ`. -/
@[instance_reducible] noncomputable def degreeZeroComponentModule
    (M : DifferentialGradedModule (degreeZero R S)) (n : ℤ) : Module A (M.grading n) := by
  letI : SMul A (M.grading n) := ⟨fun a x =>
    ⟨oppositeEquiv R S A a • (x : M.M), by
      simpa using M.smul_mem n 0 x ((oppositeEquiv R S A a).unop) x.property
        (by simp [degreeZero, degreeZeroGrading])⟩⟩
  exact {
    one_smul := by
      intro x
      apply Subtype.ext
      change oppositeEquiv R S A 1 • (x : M.M) = (x : M.M)
      rw [map_one, one_smul]
    mul_smul := by
      intro a b x
      apply Subtype.ext
      change oppositeEquiv R S A (a * b) • (x : M.M) =
        oppositeEquiv R S A a • (oppositeEquiv R S A b • (x : M.M))
      rw [map_mul, mul_smul]
    smul_add := by intro a x y; apply Subtype.ext; exact smul_add _ _ _
    smul_zero := by intro a; apply Subtype.ext; exact smul_zero _
    add_smul := by
      intro a b x
      apply Subtype.ext
      change oppositeEquiv R S A (a + b) • (x : M.M) =
        oppositeEquiv R S A a • (x : M.M) + oppositeEquiv R S A b • (x : M.M)
      rw [map_add, add_smul]
    zero_smul := by
      intro x
      apply Subtype.ext
      change oppositeEquiv R S A 0 • (x : M.M) = 0
      rw [map_zero, zero_smul] }

attribute [local instance] degreeZeroComponentModule

/-- The differential of a differential graded module over `S` in degree zero is `A`-linear on
each homogeneous component. -/
noncomputable def degreeZeroDifferential (M : DifferentialGradedModule (degreeZero R S))
    (n : ℤ) : M.grading n →ₗ[A] M.grading (n + 1) where
  toFun := M.gradedDifferential n
  map_add' := map_add _
  map_smul' a x := by
    apply Subtype.ext
    change M.d (oppositeEquiv R S A a • (x : M.M)) = oppositeEquiv R S A a • M.d x
    simpa using M.leibniz n 0 x ((oppositeEquiv R S A a).unop) x.property
      (by simp [degreeZero, degreeZeroGrading])

/-- The cochain complex of `A`-modules of the homogeneous components of a differential graded
module over `S` in degree zero. -/
noncomputable def degreeZeroComplex (M : DifferentialGradedModule (degreeZero R S)) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of A (M.grading n))
    (fun n => ModuleCat.ofHom (degreeZeroDifferential (A := A) M n)) (fun n => by
      ext x
      exact LinearMap.congr_fun M.d_comp_d x)

/-- A homomorphism of differential graded modules over `S` in degree zero, read on the
homogeneous components. -/
noncomputable def degreeZeroComplexMap {M N : DifferentialGradedModule (degreeZero R S)}
    (f : M ⟶ N) : degreeZeroComplex (A := A) M ⟶ degreeZeroComplex (A := A) N :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom {
    toFun := f.gradedMap n
    map_add' := map_add _
    map_smul' a x := Subtype.ext (f.map_smul x ((oppositeEquiv R S A a).unop)) }) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change M.grading n at x
      apply Subtype.ext
      simp only [degreeZeroComplex, CochainComplex.of_d]
      exact (LinearMap.congr_fun f.map_d (x : M.M)).symm)

/-- Differential graded modules over `S` in degree zero as cochain complexes of `A`-modules. -/
noncomputable def degreeZeroComponentFunctor (R : Type u) [CommRing R] {S : Type u} [Ring S]
    [Algebra R S] (A : Type u) [Ring A] [Algebra R A] [IsOppositeAlgebra R S A] :
    DifferentialGradedModule (degreeZero R S) ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj := degreeZeroComplex
  map := degreeZeroComplexMap
  map_id M := by ext n x; rfl
  map_comp f g := by ext n x; rfl

/-! ### The two constructions are mutually inverse -/

/-- The right `S`-action on a differential graded module over `S` in degree zero, read as a left
`A`-action through the identification of `A` with `Sᵐᵒᵖ`. -/
@[instance_reducible] noncomputable def degreeZeroLeftModule
    (M : DifferentialGradedModule (degreeZero R S)) : Module A M.M :=
  Module.compHom M.M (oppositeEquiv R S A).toRingHom

attribute [local instance] degreeZeroLeftModule

/-- The `A`-action on a differential graded module over `S` in degree zero is compatible with the
`R`-action. -/
theorem degreeZeroLeftModule_isScalarTower (M : DifferentialGradedModule (degreeZero R S)) :
    IsScalarTower R A M.M where
  smul_assoc r a x := by
    change oppositeEquiv R S A (r • a) • x = r • (oppositeEquiv R S A a • x)
    rw [oppositeEquiv_smul]
    exact smul_assoc r (oppositeEquiv R S A a) x

attribute [local instance] degreeZeroLeftModule_isScalarTower

/-- The right action of `s : Sᵐᵒᵖ` on a differential graded module over `S` in degree zero is the
left action of the element of `A` it corresponds to. -/
theorem oppositeEquiv_symm_smul_eq (M : DifferentialGradedModule (degreeZero R S)) (s : Sᵐᵒᵖ)
    (x : M.M) : ((oppositeEquiv R S A).symm s : A) • x = s • x := by
  change oppositeEquiv R S A ((oppositeEquiv R S A).symm s) • x = s • x
  rw [RingEquiv.apply_symm_apply]

/-- The inclusion of a homogeneous component of a differential graded module over `S` in degree
zero into the module. -/
noncomputable def degreeZeroInclusion (M : DifferentialGradedModule (degreeZero R S)) (n : ℤ) :
    (degreeZeroComplex (A := A) M).X n →ₗ[A] M.M where
  toFun x := (x : (M.grading n : Submodule R M.M)).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Summing the homogeneous components of a differential graded module over `S` in degree zero
recovers its underlying module. -/
noncomputable def degreeZeroTotalLinear (M : DifferentialGradedModule (degreeZero R S)) :
    complexTotal (degreeZeroComplex (A := A) M) →ₗ[A] M.M :=
  DirectSum.toModule A ℤ M.M (degreeZeroInclusion (A := A) M)

/-- `degreeZeroTotalLinear` sends a homogeneous component `x` of degree `n` to the underlying
element of the module. -/
theorem degreeZeroTotalLinear_of (M : DifferentialGradedModule (degreeZero R S)) (n : ℤ)
    (x : (degreeZeroComplex (A := A) M).X n) :
    degreeZeroTotalLinear (A := A) M
        (DirectSum.of (fun n => (degreeZeroComplex (A := A) M).X n) n x) =
      (x : (M.grading n : Submodule R M.M)).val := by
  change DirectSum.toModule A ℤ M.M (degreeZeroInclusion (A := A) M)
      (DirectSum.lof A ℤ (fun n => (degreeZeroComplex (A := A) M).X n) n x) = _
  rw [DirectSum.toModule_lof]
  rfl

/-- The comparison from the direct sum of the homogeneous components of a differential graded
module over `S` in degree zero back to the module. -/
noncomputable def degreeZeroTotalHom (M : DifferentialGradedModule (degreeZero R S)) :
    degreeZeroTotal (R := R) (S := S) (degreeZeroComplex (A := A) M) ⟶ M where
  toFun := (degreeZeroTotalLinear (A := A) M).restrictScalars R
  map_smul x a := by
    rw [← oppositeEquiv_symm_smul_eq (A := A) M (MulOpposite.op a)]
    exact (degreeZeroTotalLinear (A := A) M).map_smul _ x
  map_grading n x hx := by
    rcases hx with ⟨y, rfl⟩
    change degreeZeroTotalLinear (A := A) M
      (DirectSum.of (fun n => (degreeZeroComplex (A := A) M).X n) n y) ∈ M.grading n
    rw [degreeZeroTotalLinear_of]
    exact (y : M.grading n).property
  map_d := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change degreeZeroTotalLinear (A := A) M
        (complexDifferential (R := R) (degreeZeroComplex (A := A) M)
          (DirectSum.of (fun n => (degreeZeroComplex (A := A) M).X n) n x)) =
      M.d (degreeZeroTotalLinear (A := A) M
        (DirectSum.of (fun n => (degreeZeroComplex (A := A) M).X n) n x))
    rw [complexDifferential_of, degreeZeroTotalLinear_of, degreeZeroTotalLinear_of]
    simp only [degreeZeroComplex, CochainComplex.of_d]
    rfl

/-- The comparison `degreeZeroTotalHom` from the direct sum of the homogeneous components to the
module is bijective. -/
theorem degreeZeroTotalHom_bijective (M : DifferentialGradedModule (degreeZero R S)) :
    Function.Bijective (degreeZeroTotalHom (A := A) M).toFun := by
  have key : ∀ x : complexTotal (degreeZeroComplex (A := A) M),
      (degreeZeroTotalHom (A := A) M).toFun x = DirectSum.coeAddMonoidHom M.grading x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero =>
      exact (map_zero (degreeZeroTotalLinear (A := A) M)).trans
        (map_zero (DirectSum.coeAddMonoidHom M.grading)).symm
    | of n y =>
      exact (degreeZeroTotalLinear_of M n y).trans
        (DirectSum.coeAddMonoidHom_of M.grading n y).symm
    | add x y hx hy =>
      refine (map_add (degreeZeroTotalLinear (A := A) M) x y).trans
        ((congrArg₂ (· + ·) hx hy).trans ?_)
      exact (map_add (DirectSum.coeAddMonoidHom M.grading) x y).symm
  change Function.Bijective fun x : complexTotal (degreeZeroComplex (A := A) M) =>
    (degreeZeroTotalHom (A := A) M).toFun x
  rw [show (fun x : complexTotal (degreeZeroComplex (A := A) M) =>
      (degreeZeroTotalHom (A := A) M).toFun x) =
      (DirectSum.decompose M.grading).symm from funext key]
  exact (DirectSum.decompose M.grading).symm.bijective

/-- Taking the homogeneous components and summing them back up is the identity on differential
graded modules over `S` in degree zero. -/
noncomputable def degreeZeroTotalIso :
    degreeZeroComponentFunctor R A ⋙ degreeZeroTotalFunctor R A ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M =>
    Hom.isoOfBijective (degreeZeroTotalHom (A := A) M) (degreeZeroTotalHom_bijective M)) (by
      intro M N f
      apply DifferentialGradedModule.Hom.ext
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro x
      have h1 := congrArg (degreeZeroTotalLinear (A := A) N)
        (DirectSum.lmap_of (fun n => ((degreeZeroComplexMap (A := A) f).f n).hom) n x)
      have h2 := degreeZeroTotalLinear_of N n (((degreeZeroComplexMap (A := A) f).f n).hom x)
      have h3 := congrArg f.toFun (degreeZeroTotalLinear_of (A := A) M n x)
      exact (h1.trans h2).trans h3.symm)

/-- The degree-`n` component of the differential graded module attached to a complex `K` is
`K^n`, as `A`-modules. -/
noncomputable def degreeZeroComplexComponent (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (degreeZeroComplex (A := A) (degreeZeroTotal (R := R) (S := S) K)).X n ≃ₗ[A] K.X n where
  __ := (complexComponent (R := R) K n).toAddEquiv
  map_smul' a x := by
    change complexGrading (R := R) K n at x
    change DirectSum.component A ℤ (fun n => K.X n) n
        (((oppositeEquiv R S A).symm (oppositeEquiv R S A a) : A) • (x : complexTotal K)) =
      a • DirectSum.component A ℤ (fun n => K.X n) n x
    rw [RingEquiv.symm_apply_apply]
    exact map_smul _ _ _

/-- The complex of homogeneous components of the differential graded module attached to a
complex `K` is `K`. -/
noncomputable def degreeZeroComplexIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    degreeZeroComplex (A := A) (degreeZeroTotal (R := R) (S := S) K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (degreeZeroComplexComponent (R := R) (S := S) K n).toModuleIso) (by
      intro n m h
      change n + 1 = m at h
      subst m
      simp only [degreeZeroComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y, rfl⟩
      change K.d n (n + 1)
          (DirectSum.component R ℤ (fun n => K.X n) n (DirectSum.lof R ℤ _ n y)) =
        DirectSum.component R ℤ (fun n => K.X n) (n + 1)
          (complexDifferential (R := R) K (DirectSum.lof R ℤ _ n y))
      rw [complexDifferential_lof]
      simp)

/-- Summing a complex up and taking the homogeneous components again is the identity on cochain
complexes of `A`-modules. -/
noncomputable def degreeZeroComplexNatIso :
    degreeZeroTotalFunctor R A ⋙ degreeZeroComponentFunctor R A ≅ 𝟭 _ :=
  NatIso.ofComponents (degreeZeroComplexIso (R := R) (S := S)) (by
    intro K L f
    ext n x
    rcases x with ⟨x, y, rfl⟩
    change DirectSum.component R ℤ (fun n => L.X n) n
        (DirectSum.lmap (fun n => (f.f n).hom) (DirectSum.of _ n y)) =
      f.f n (DirectSum.component R ℤ (fun n => K.X n) n (DirectSum.of _ n y))
    rw [DirectSum.lmap_of]
    simp only [← DirectSum.lof_eq_of R, DirectSum.component.of]
    simp)

/-- Differential graded modules over an ordinary algebra `S` placed in degree zero are cochain
complexes of `A`-modules, for any `A` identified with the opposite algebra of `S`. -/
noncomputable def degreeZeroEquivalence :
    DifferentialGradedModule (degreeZero R S) ≌ CochainComplex (ModuleCat.{u} A) ℤ :=
  CategoryTheory.Equivalence.mk (degreeZeroComponentFunctor R A) (degreeZeroTotalFunctor R A)
    degreeZeroTotalIso.symm degreeZeroComplexNatIso

/-! ### The underlying complexes of `R`-modules -/

/-- The complex of `R`-modules underlying the differential graded module attached to a complex
`K` of `A`-modules is `K` with its scalars restricted to `R`. -/
noncomputable def degreeZeroTotalForgetIso :
    degreeZeroTotalFunctor R A ⋙ forgetToCochainComplex (degreeZero R S) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun K =>
    HomologicalComplex.Hom.isoOfComponents
      (fun n => (complexComponent (R := R) K n).toModuleIso) (by
        intro n m h
        change n + 1 = m at h
        subst m
        simp only [Functor.comp_obj, forgetToCochainComplex, toCochainComplex,
          CochainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        rintro ⟨x, y, rfl⟩
        change K.d n (n + 1)
            (DirectSum.component R ℤ (fun n => K.X n) n (DirectSum.lof R ℤ _ n y)) =
          DirectSum.component R ℤ (fun n => K.X n) (n + 1)
            (complexDifferential (R := R) K (DirectSum.lof R ℤ _ n y))
        rw [complexDifferential_lof]
        simp)) (by
      intro K L f
      ext n x
      rcases x with ⟨x, y, rfl⟩
      change DirectSum.component R ℤ (fun n => L.X n) n
          (DirectSum.lmap (fun n => (f.f n).hom) (DirectSum.of _ n y)) =
        f.f n (DirectSum.component R ℤ (fun n => K.X n) n (DirectSum.of _ n y))
      rw [DirectSum.lmap_of]
      simp only [← DirectSum.lof_eq_of R, DirectSum.component.of]
      simp)

/-- The complex of homogeneous components of a differential graded module over `S` in degree
zero, with scalars restricted to `R`, is the complex of `R`-modules underlying it. -/
noncomputable def degreeZeroForgetIso :
    degreeZeroComponentFunctor R A ⋙
        (ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ) ≅
      forgetToCochainComplex (degreeZero R S) :=
  NatIso.ofComponents (fun M => HomologicalComplex.Hom.isoOfComponents
    (fun n => (show ((ModuleCat.restrictScalars (algebraMap R A)).obj
        ((degreeZeroComplex (A := A) M).X n)) ≃ₗ[R] M.grading n from {
      toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        change M.grading n at x
        change oppositeEquiv R S A (algebraMap R A r) • (x : M.M) = r • (x : M.M)
        rw [oppositeEquiv_algebraMap]
        exact IsScalarTower.algebraMap_smul Sᵐᵒᵖ r (x : M.M) }).toModuleIso)
    (by
      intro n m h
      change n + 1 = m at h
      subst m
      ext x
      change M.grading n at x
      change (M.toCochainComplex.d n (n + 1)) x = (degreeZeroComplex (A := A) M).d n (n + 1) x
      simp only [degreeZeroComplex, toCochainComplex, CochainComplex.of_d]
      rfl))
    (by intro M N f; ext n x; rfl)

/-! ### Homotopies and quasi-isomorphisms -/

/-- The differential of the complex of homogeneous components, as a morphism between its own
terms. -/
noncomputable def degreeZeroComplexDiff (M : DifferentialGradedModule (degreeZero R S)) (i : ℤ) :
    (degreeZeroComplex (A := A) M).X i ⟶ (degreeZeroComplex (A := A) M).X (i + 1) :=
  ModuleCat.ofHom (degreeZeroDifferential (A := A) M i)

/-- The differential of the complex of homogeneous components from degree `i` to `i + 1` is
`degreeZeroComplexDiff M i`. -/
theorem degreeZeroComplex_d_self (M : DifferentialGradedModule (degreeZero R S)) (i : ℤ) :
    (degreeZeroComplex (A := A) M).d i (i + 1) = degreeZeroComplexDiff M i := by
  simp [degreeZeroComplex, degreeZeroComplexDiff]

/-- A homotopy between homomorphisms of differential graded modules over `S` in degree zero is a
homotopy of the complexes of homogeneous components. -/
noncomputable def degreeZeroHomotopy {M N : DifferentialGradedModule (degreeZero R S)}
    {f g : M ⟶ N} (h : DifferentialGradedModule.Homotopy f g) :
    _root_.Homotopy (degreeZeroComplexMap (A := A) f) (degreeZeroComplexMap (A := A) g) := by
  let k (i j : ℤ) (_ : j + 1 = i) :
      (degreeZeroComplex (A := A) M).X i ⟶ (degreeZeroComplex (A := A) N).X j :=
    ModuleCat.ofHom (show M.grading i →ₗ[A] N.grading j from {
      toFun := fun x => ⟨h.toLinearMap x, by
        simpa only [show i - 1 = j by omega] using h.map_grading i x x.property⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' r x := Subtype.ext (h.toLinearMap.map_smul (oppositeEquiv R S A r) x) })
  refine {
    hom := fun i j => if hij : j + 1 = i then k i j hij else 0
    zero := fun _ _ hnm => dite_eq_right hnm
    comm := ?_ }
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [dNext_eq _ (i' := m + 1 + 1) rfl, prevD_eq _ (j' := m) rfl,
    dite_eq_left (rfl : m + 1 + 1 = m + 1 + 1), dite_eq_left (rfl : m + 1 = m + 1),
    degreeZeroComplex_d_self (A := A) M (m + 1), degreeZeroComplex_d_self (A := A) N m]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M.grading (m + 1) at x
  apply Subtype.ext
  have he := h.homotopy_eq (x : M.M)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp]
  change f.toFun (x : M.M) =
    h.toLinearMap (M.d (x : M.M)) + N.d (h.toLinearMap (x : M.M)) + g.toFun (x : M.M)
  rw [sub_eq_iff_eq_add.mp he]
  abel

/-- For naturally isomorphic functors `F` and `G` to cochain complexes, `F.map f` is a
quasi-isomorphism if and only if `G.map f` is. -/
theorem quasiIso_map_iff_of_natIso {C : Type*} [Category* C] {B : Type*} [Category* B]
    [Abelian B] {F G : C ⥤ CochainComplex B ℤ} (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    QuasiIso (F.map f) ↔ QuasiIso (G.map f) :=
  quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)

/-- A homomorphism of differential graded modules over `S` in degree zero is a
quasi-isomorphism of the complexes of homogeneous components exactly when it is one of the
underlying complexes of `R`-modules. -/
theorem degreeZeroComplexMap_quasiIso_iff {M N : DifferentialGradedModule (degreeZero R S)}
    (f : M ⟶ N) : QuasiIso (degreeZeroComplexMap (A := A) f) ↔ QuasiIso f.toCochainMap := by
  let U := ModuleCat.restrictScalars.{u} (algebraMap R A)
  let _ : Limits.PreservesFiniteLimits U := ⟨fun _ _ _ => ⟨inferInstance⟩⟩
  let _ : Limits.PreservesFiniteColimits U := ⟨fun _ _ _ => ⟨inferInstance⟩⟩
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (degreeZeroComplexMap (A := A) f) U).symm.trans
      (quasiIso_map_iff_of_natIso degreeZeroForgetIso f)

/-! ### The derived categories -/

section Derived

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- Taking homogeneous components and then localizing at quasi-isomorphisms of complexes of
`A`-modules is a localization at the morphisms whose complexes of homogeneous components are
quasi-isomorphisms. -/
theorem degreeZeroComponentFunctor_comp_Q_isLocalization :
    (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
        (degreeZeroComponentFunctor R A (S := S))) := by
  apply Functor.IsLocalization.of_equivalence_source DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) _ _ degreeZeroEquivalence.symm
  · intro X Y f hf
    apply MorphismProperty.le_isoClosure
    change HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
      ((degreeZeroComponentFunctor R A).map (degreeZeroEquivalence.inverse.map f))
    exact ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoMk (degreeZeroEquivalence.counitIso.app X)
        (degreeZeroEquivalence.counitIso.app Y)
        (degreeZeroEquivalence.counitIso.hom.naturality f).symm)).mpr hf
  · intro X Y f hf
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) _ hf
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight degreeZeroEquivalence.counitIso DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q

/-- The localization of differential graded modules over `S` in degree zero at the
quasi-isomorphisms is a localization at the morphisms whose complexes of homogeneous components
are quasi-isomorphisms of complexes of `A`-modules. -/
theorem degreeZero_localization :
    (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q).IsLocalization
      ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
        (degreeZeroComponentFunctor R A)) := by
  let W := (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
    (degreeZeroComponentFunctor R A)
  let L := degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q
  have : L.IsLocalization W := degreeZeroComponentFunctor_comp_Q_isLocalization
  have h : (homotopyRel (degreeZero R S)).FactorsThroughLocalization W := by
    intro M N f g ⟨h⟩
    exact (areEqualizedByLocalization_iff L W f g).mpr
      (DerivedCategory.Q_map_eq_of_homotopy _ (degreeZeroHomotopy (A := A) h))
  have hW : W = (quasiIsomorphisms' (degreeZero R S)).inverseImage
      (toHomotopyCategory (degreeZero R S)) := by
    ext M N f
    exact (degreeZeroComplexMap_quasiIso_iff (A := A) f).trans
      (quasiIsomorphisms_map_iff' (degreeZero R S) f).symm
  exact Functor.IsLocalization.mk' _ _
    (h.strictUniversalPropertyFixedTarget' hW _)
    (h.strictUniversalPropertyFixedTarget' hW _)

/-- **The derived category of a ring, read in the differential graded world.** The derived
category of differential graded modules over `S` placed in degree zero is the derived category
of `A`-modules, for any `A` identified with the opposite algebra of `S`. -/
noncomputable def degreeZeroDerivedEquivalence :
    derivedCategory' (degreeZero R S) ≌ DerivedCategory (ModuleCat.{u} A) := by
  let W := (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
    (degreeZeroComponentFunctor R A)
  have := degreeZero_localization (R := R) (S := S) (A := A)
  have : (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q).IsLocalization W :=
    degreeZeroComponentFunctor_comp_Q_isLocalization
  exact Localization.uniq
    (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q)
    (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q) W

/-- The quasi-inverse of the derived equivalence is the total-direct-sum functor read through
the localizations: a complex of `A`-modules becomes the differential graded module it is the
direct sum of. -/
noncomputable def degreeZeroDerivedFactorization :
    DerivedCategory.Q ⋙ (degreeZeroDerivedEquivalence (R := R) (S := S) (A := A)).inverse ≅
      degreeZeroTotalFunctor R A ⋙ toHomotopyCategory (degreeZero R S) ⋙
        (quasiIsomorphisms' (degreeZero R S)).Q := by
  let F := degreeZeroComponentFunctor R A
  let V := degreeZeroTotalFunctor R A
  let Q := toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q
  let W := (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage F
  have := degreeZero_localization (R := R) (S := S) (A := A)
  have : (F ⋙ DerivedCategory.Q).IsLocalization W :=
    degreeZeroComponentFunctor_comp_Q_isLocalization
  change DerivedCategory.Q ⋙ (Localization.uniq Q (F ⋙ DerivedCategory.Q) W).inverse ≅ V ⋙ Q
  exact (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight degreeZeroComplexNatIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft V ((Functor.associator _ _ _).symm ≪≫
      Localization.compUniqInverse Q (F ⋙ DerivedCategory.Q) W)

end Derived

end DifferentialGradedModule

end

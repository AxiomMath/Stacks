module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.Examples.Algebra.DualNumberPolynomialAlgebra

/-!
# A compact direct summand of the regular module of `k[x, y]/(y²)`

Let `A = k[x, y]/(y²)` be the differential graded algebra of [Stacks, Tag 09R4] over
`k = ZMod 2`. Multiplication by `x` is an endomorphism of the regular module which becomes
idempotent in the homotopy category `K(A, d)`, the homotopy being multiplication by `y`.
Idempotents split in `K(A, d)`, so the image of that idempotent in the derived category
`D(A, d)` is a direct summand of the regular module there, hence a compact object. Its
degree-zero cohomology is the image of the idempotent `(0, 1)` acting on
`H⁰(A) = k[x]/(x² - x) = k × k`, and it has no cohomology in any other degree.

## Main definitions

* `Stacks.Examples.charTwoRegularModule`: the algebra of Tag 09R4 as a right module over itself.
* `Stacks.Examples.regularLeftMul`: multiplication by a degree-zero element, as an endomorphism
  of the regular module.
* `Stacks.Examples.charTwoRegularCohomologyEquiv`: the identification `H⁰(A) = k × k` given by
  evaluating a degree-zero cocycle at the two roots of `x² - x`.

## Main results

* `Stacks.Examples.regularLeftMulHomotopy`: multiplication by `y` is a homotopy from the square
  of multiplication by `x` to multiplication by `x`.
* `Stacks.Examples.exists_isCompactObject_retract_charTwoRegularModule`: `D(A, d)` contains a
  compact object which is a retract of the regular module, the composite retraction being
  multiplication by `x`.
* `Stacks.Examples.isZero_gradedCohomology_charTwoRegularModule`: the regular module has no
  cohomology outside degree zero.
* `Stacks.Examples.charTwoRegularCohomologyEquiv_map_regularLeftMul`: on `H⁰(A) = k × k`,
  multiplication by `x` is multiplication by `(0, 1)`.

## Implementation notes

Both pre-triangulated structures on `K(A, d)` are in scope here; the cone-triangle structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory` is given priority, as it is the
one in which the cohomology functors on `D(A, d)` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedCohomology.lean` are read. The splitting of
idempotents is a statement about the category alone, so it is insensitive to that choice.

Degree-`n` cohomology is used in its explicit form, cocycles modulo coboundaries, so that the
computation for the regular module is a computation with dual numbers over `k[x]`.

## References

* [Stacks Project, Tag 09R4](https://stacks.math.columbia.edu/tag/09R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DifferentialGradedModule

namespace Stacks.Examples

/- The cohomology functors on `D(A, d)` are read in the cone-triangle structure on `K(A, d)`,
which is therefore the structure given priority here. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-! ### Multiplication by a degree-zero element of the dual numbers -/

/-- Left multiplication by `c : S` on the dual numbers, as an `R`-linear map. -/
def dualNumberLeftMul (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (c : S) :
    DualNumber S →ₗ[R] DualNumber S where
  toFun a := TrivSqZeroExt.inl c * a
  map_add' := mul_add _
  map_smul' r a := by apply TrivSqZeroExt.ext <;> simp

/-- Left multiplication by `ε` on the dual numbers, as a map of right modules over
themselves. -/
def dualNumberLeftMulEps (S : Type*) [CommRing S] :
    DualNumber S →ₗ[MulOpposite (DualNumber S)] DualNumber S where
  toFun a := DualNumber.eps * a
  map_add' := mul_add _
  map_smul' a b := by
    change DualNumber.eps * (b * a.unop) = DualNumber.eps * b * a.unop
    exact (mul_assoc _ _ _).symm

/-- Left multiplication by `c : S` on the regular module of `S⟨y⟩`, as a homomorphism of
differential graded modules: it is right `S⟨y⟩`-linear by associativity, preserves the grading
because `c` has degree zero, and commutes with the differential because `c` does. -/
def regularLeftMul {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p c : S) :
    regularModule (dualNumberDGAlgebra R S p) ⟶ regularModule (dualNumberDGAlgebra R S p) where
  toFun := dualNumberLeftMul R S c
  map_smul := by
    intro a b
    change DualNumber S at a b
    change (TrivSqZeroExt.inl c : DualNumber S) * (a * b) = TrivSqZeroExt.inl c * a * b
    exact (mul_assoc _ _ _).symm
  map_grading := by
    intro n a ha
    exact zero_add n ▸ dualNumberGrading_mul 0 n (TrivSqZeroExt.inl c) a
      (by simp [mem_dualNumberGrading]) ha
  map_d := by
    apply LinearMap.ext
    intro a
    change DualNumber S at a
    change (TrivSqZeroExt.inl c : DualNumber S) * TrivSqZeroExt.inl (p * a.snd) =
      TrivSqZeroExt.inl (p * (TrivSqZeroExt.inl c * a).snd)
    apply TrivSqZeroExt.ext <;> simp [mul_left_comm]

/-- **Multiplication by `c` is idempotent up to homotopy on the regular module of `S⟨y⟩` with
`d y = c² - c`**, the homotopy being multiplication by `y`: indeed
`d (y a) + y (d a) = (c² - c) a = c (c a) - c a`. -/
def regularLeftMulHomotopy {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (c : S) :
    Homotopy (regularLeftMul (R := R) (c ^ 2 - c) c ≫ regularLeftMul (R := R) (c ^ 2 - c) c)
      (regularLeftMul (R := R) (c ^ 2 - c) c) where
  toLinearMap := dualNumberLeftMulEps S
  map_grading := by
    intro n a ha
    change DualNumber S at a
    change DualNumber.eps * a ∈ dualNumberGrading R S (n - 1)
    rw [show n - 1 = -1 + n by omega]
    exact dualNumberGrading_mul (-1) n DualNumber.eps a (by simp [mem_dualNumberGrading]) ha
  homotopy_eq := by
    intro a
    change DualNumber S at a
    change (TrivSqZeroExt.inl c : DualNumber S) * (TrivSqZeroExt.inl c * a) -
        TrivSqZeroExt.inl c * a =
      TrivSqZeroExt.inl ((c ^ 2 - c) * (DualNumber.eps * a).snd) +
        DualNumber.eps * TrivSqZeroExt.inl ((c ^ 2 - c) * a.snd)
    apply TrivSqZeroExt.ext <;> simp <;> ring

/-- Multiplication by `c` is an idempotent of the homotopy category `K(S⟨y⟩, d)` when
`d y = c² - c`. -/
theorem toHomotopyCategory_map_regularLeftMul_idem {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (c : S) :
    (toHomotopyCategory (dualNumberDGAlgebra R S (c ^ 2 - c))).map (regularLeftMul _ c) ≫
        (toHomotopyCategory (dualNumberDGAlgebra R S (c ^ 2 - c))).map (regularLeftMul _ c) =
      (toHomotopyCategory (dualNumberDGAlgebra R S (c ^ 2 - c))).map (regularLeftMul _ c) := by
  rw [← CategoryTheory.Functor.map_comp]
  exact CategoryTheory.Quotient.sound _ ⟨regularLeftMulHomotopy c⟩

/-! ### The compact summand -/

/-- The algebra of Tag 09R4, regarded as a right differential graded module over itself. -/
abbrev charTwoRegularModule : DifferentialGradedModule.{0, 0, 0} charTwoDualNumberDGAlgebra :=
  regularModule charTwoDualNumberDGAlgebra

/-- **The derived category of the algebra of Tag 09R4 contains a compact object cut out by
multiplication by `x`**: that idempotent splits in `K(A, d)`, and the image of its splitting in
`D(A, d)` is a retract of the regular module, hence compact, with the composite retraction equal
to multiplication by `x`. -/
theorem exists_isCompactObject_retract_charTwoRegularModule :
    ∃ (E : derivedCategory charTwoDualNumberDGAlgebra)
      (i : E ⟶ (toDerivedCategory charTwoDualNumberDGAlgebra).obj charTwoRegularModule)
      (r : (toDerivedCategory charTwoDualNumberDGAlgebra).obj charTwoRegularModule ⟶ E),
      IsCompactObject.{0} E ∧ i ≫ r = 𝟙 E ∧
        r ≫ i = (toDerivedCategory charTwoDualNumberDGAlgebra).map
          (regularLeftMul _ Polynomial.X) := by
  have hidem : IsIdempotentComplete (HomotopyCategory.{0, 0, 0} charTwoDualNumberDGAlgebra) :=
    (Pretriangulated.isIdempotentComplete_of_hasCountableProducts_or_coproducts
      (HomotopyCategory.{0, 0, 0} charTwoDualNumberDGAlgebra)).1
  obtain ⟨Y, i, r, hir, hri⟩ := hidem.idempotents_split
    ((toHomotopyCategory charTwoDualNumberDGAlgebra).obj charTwoRegularModule)
    ((toHomotopyCategory charTwoDualNumberDGAlgebra).map (regularLeftMul _ Polynomial.X))
    (toHomotopyCategory_map_regularLeftMul_idem Polynomial.X)
  have h : (quasiIsomorphisms charTwoDualNumberDGAlgebra).Q.map i ≫
      (quasiIsomorphisms charTwoDualNumberDGAlgebra).Q.map r =
        𝟙 ((quasiIsomorphisms charTwoDualNumberDGAlgebra).Q.obj Y) := by
    rw [← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  refine ⟨(quasiIsomorphisms charTwoDualNumberDGAlgebra).Q.obj Y,
    (quasiIsomorphisms charTwoDualNumberDGAlgebra).Q.map i,
    (quasiIsomorphisms charTwoDualNumberDGAlgebra).Q.map r,
    isCompactObject_of_retract (isCompactObject_q_regularModule charTwoDualNumberDGAlgebra) _ _ h,
    h, ?_⟩
  rw [← CategoryTheory.Functor.map_comp, hri]
  rfl

/-! ### The cohomology of the regular module -/

/-- A degree-`n` cocycle of the algebra of Tag 09R4 vanishes for `n ≠ 0`: its `y`-part vanishes
because `x² - x` is a nonzerodivisor, and its degree-zero part vanishes by homogeneity. -/
theorem charTwoRegularModule_cocycle_eq_zero (n : ℤ) (hn : n ≠ 0)
    (z : charTwoRegularModule.gradedCocycles n) :
    (z.1.1 : DualNumber (Polynomial (ZMod 2))) = 0 :=
  TrivSqZeroExt.ext (((mem_dualNumberGrading n z.1.1).1 z.1.2).1 hn)
    ((dualNumberDifferential_eq_zero_iff z.1.1).1 (congrArg Subtype.val (mem_gradedCocycles.1 z.2)))

/-- **The regular module of the algebra of Tag 09R4 has no cohomology outside degree zero.** -/
theorem isZero_gradedCohomology_charTwoRegularModule (n : ℤ) (hn : n ≠ 0) :
    IsZero ((gradedCohomologyFunctor charTwoDualNumberDGAlgebra n).obj charTwoRegularModule) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have h (a : charTwoRegularModule.gradedCocycles n) : a = 0 :=
    Subtype.ext (Subtype.ext (charTwoRegularModule_cocycle_eq_zero n hn a))
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    induction y using Submodule.Quotient.induction_on with
    | H b => rw [h a, h b]

/-- Evaluation of a degree-zero cocycle of the algebra of Tag 09R4 at the two roots of `x² - x`,
as a linear map to `k × k`. -/
def charTwoRegularAugmentation :
    charTwoRegularModule.gradedCocycles 0 →ₗ[ZMod 2] ZMod 2 × ZMod 2 where
  toFun z := dualNumberAugmentation (ZMod 2) z.1.1
  map_add' _ _ := map_add (dualNumberAugmentation (ZMod 2)) _ _
  map_smul' r _ := map_smul (dualNumberAugmentation (ZMod 2)).toLinearMap r _

/-- The degree-zero cocycles killed by the augmentation are exactly the coboundaries. -/
theorem ker_charTwoRegularAugmentation :
    LinearMap.ker charTwoRegularAugmentation = charTwoRegularModule.gradedCoboundaries 0 := by
  ext z
  rw [LinearMap.mem_ker, mem_gradedCoboundaries]
  constructor
  · intro h
    obtain ⟨c, hc, hdc⟩ := exists_boundary_of_dualNumberAugmentation_eq_zero 0 z.1.1 z.1.2
      (congrArg Subtype.val (mem_gradedCocycles.1 z.2)) (fun _ => h)
    exact ⟨⟨c, hc⟩, hdc⟩
  · rintro ⟨y, hy⟩
    show dualNumberAugmentation (ZMod 2) z.1.1 = 0
    rw [← hy]
    exact dualNumberAugmentation_differential _

/-- The augmentation is surjective on degree-zero cocycles. -/
theorem charTwoRegularAugmentation_surjective :
    Function.Surjective charTwoRegularAugmentation := by
  intro b
  obtain ⟨a, ha, hda, hab⟩ := exists_cycle_dualNumberAugmentation b
  exact ⟨⟨⟨a, ha⟩, Subtype.ext hda⟩, hab⟩

/-- **`H⁰` of the algebra of Tag 09R4 is `k[x]/(x² - x) = k × k`**: a degree-zero cocycle is a
polynomial, two of them are cohomologous exactly when they agree at the two roots of `x² - x`,
and every pair of values is attained. -/
def charTwoRegularCohomologyEquiv :
    (gradedCohomologyFunctor charTwoDualNumberDGAlgebra 0).obj charTwoRegularModule ≃ₗ[ZMod 2]
      ZMod 2 × ZMod 2 :=
  LinearEquiv.ofBijective
    ((charTwoRegularModule.gradedCoboundaries 0).liftQ charTwoRegularAugmentation
      ker_charTwoRegularAugmentation.ge)
    ⟨LinearMap.ker_eq_bot.1
      (Submodule.ker_liftQ_eq_bot _ _ _ ker_charTwoRegularAugmentation.le),
     fun b => by
       obtain ⟨z, hz⟩ := charTwoRegularAugmentation_surjective b
       exact ⟨Submodule.Quotient.mk z, hz⟩⟩

/-- The class of a degree-zero cocycle is sent by `charTwoRegularCohomologyEquiv` to its values
at the two roots of `x² - x`. -/
@[simp] theorem charTwoRegularCohomologyEquiv_mk (z : charTwoRegularModule.gradedCocycles 0) :
    charTwoRegularCohomologyEquiv (Submodule.Quotient.mk z) =
      dualNumberAugmentation (ZMod 2) z.1.1 := rfl

/-- **On `H⁰(A) = k × k`, multiplication by `x` is multiplication by the idempotent `(0, 1)`.** -/
theorem charTwoRegularCohomologyEquiv_map_regularLeftMul
    (z : (gradedCohomologyFunctor charTwoDualNumberDGAlgebra 0).obj charTwoRegularModule) :
    charTwoRegularCohomologyEquiv
        (((gradedCohomologyFunctor charTwoDualNumberDGAlgebra 0).map
          (regularLeftMul _ Polynomial.X)).hom z) =
      (0, 1) * charTwoRegularCohomologyEquiv z := by
  induction z using Submodule.Quotient.induction_on with
  | H a =>
    show charTwoRegularCohomologyEquiv (Submodule.Quotient.mk
      (gradedCocyclesMap (regularLeftMul _ Polynomial.X) 0 a)) = _
    rw [charTwoRegularCohomologyEquiv_mk, charTwoRegularCohomologyEquiv_mk]
    exact dualNumberAugmentation_mul_X _

end Stacks.Examples

end

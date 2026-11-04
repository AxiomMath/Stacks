module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical multiplication on the integer tensor powers of an invertible object

Let `L` be an invertible object of a monoidal category `D`, in the sense that tensoring on the
right by `L` is an autoequivalence `e = - ⊗ L`. Its integer tensor powers are
`L^{⊗ n} = (e ^ n).obj (𝟙_ D)`, and Tag 01CU asserts that they carry canonical multiplication
isomorphisms `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` which are normalised by the unit and
associativity constraints of the monoidal category and by the defining iteration in degree
`(n, 1)`. This file constructs that multiplication and proves those normalisations, for an
arbitrary monoidal category, and then specialises them to sheaves of modules, where the monoidal
structure is the one of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict` whose tensor product is the tensor
product sheaf of Tag 01CA.

The whole development rests on two inputs which are proved elsewhere: the addition law
`CategoryTheory.Equivalence.powAdd` for the integer powers of an autoequivalence together with its
cocycle identity `powAdd_assoc` (in `StacksFrontier.CategoryTheory.Equivalence.Pow`), and the
coherence of the tensor product sheaf (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence`). What this file adds is the
bridge between the two: the comparison `powFunctorIso` identifying the `n`-fold iterate of
`- ⊗ L` with `- ⊗ L^{⊗ n}`, and the three inductions on the exponent which turn statements about
composites of functors into statements about tensor products of objects.

## Main definitions

The general development lives in `Stacks.MonoidalCategory`, the sheaf-theoretic specialisation in
`Stacks.SheafOfModules.TensorPower`.

* `Stacks.MonoidalCategory.pow`: the `n`th tensor power `L^{⊗ n}` of an invertible object, for
  `n : ℤ`.
* `Stacks.MonoidalCategory.powSuccIso`: the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ p}` for
  `n + 1 = p`.
* `Stacks.MonoidalCategory.powFunctorIso`: **tensoring `n` times by `L` is tensoring once by
  `L^{⊗ n}`**, `(e ^ n).functor ≅ - ⊗ L^{⊗ n}`. This is the comparison the whole file turns on.
* `Stacks.MonoidalCategory.mul` and `Stacks.SheafOfModules.TensorPower.mulIso`: **the canonical
  multiplication** `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ p}` for `n + m = p`.
* `Stacks.MonoidalCategory.powOneIso`, `powLeftUnitor`, `powRightUnitor`, `powAppOne`,
  `powAppUnit`: the unit constraints and the values of `powFunctorIso` at the exponents `0` and
  `1`, named so that their ascribed types use the tensor-power spelling; see the implementation
  notes.
* `Stacks.MonoidalCategory.mulConj` and `mulFunctorConj`: the two sides of the key compatibility,
  the multiplication and the addition law read as comparisons of right-tensor functors.

## Main results

* `Stacks.MonoidalCategory.powFunctorIso_succ`: **the uniform recursion.** `powFunctorIso` is
  built by two separate recursions, upwards from the exponent `0` and downwards from it, but it
  satisfies one and the same one-step recursion at *every* integer exponent. All three inductions
  below are run against this single statement rather than against the two constructions.
* `Stacks.MonoidalCategory.mul_zero_right` and `mul_one_right`: multiplication by the zeroth power
  on the right is the right unit constraint, and multiplication by the first power is the
  successor comparison of the defining iteration. The latter is the normalisation which removes
  the cocycle ambiguity from the multiplication.
* `Stacks.MonoidalCategory.powAppUnit_hom` and `mul_zero_left`: **multiplication by the zeroth
  power on the left is the left unit constraint.** This is an induction on the exponent whose two
  one-step cases are both `leftUnitor_powSucc`, itself the unit coherence `leftUnitor_tensor`
  together with naturality of the left unit constraint.
* `Stacks.MonoidalCategory.mul_succ_hom`: **the multiplication satisfies the one-step recursion in
  its right exponent**, which is the precise content of the assertion in Tag 01CU that
  associativity determines the multiplication in every degree from its value in degree `(n, 1)`.
* `Stacks.MonoidalCategory.mulConj_eq`: **the key compatibility.** The multiplication, read as a
  comparison of right-tensor functors, *is* the addition law for the powers of `- ⊗ L`. It is an
  induction on the exponent whose one-step cases are `mulConj_succ` and `mulFunctorConj_succ`,
  and whose residual coherence is `conj_step_mul` (the pentagon) and `conj_step_functor`
  (`whisker_exchange` and naturality of the associativity constraint).
* `Stacks.MonoidalCategory.mul_assoc`: **associativity of the multiplication**, against the
  associativity constraint of the monoidal category. It is the cocycle identity
  `CategoryTheory.Equivalence.powAdd_assoc` read through `mulConj_eq`.
* `Stacks.SheafOfModules.TensorPower.tensorRightFunctor_eq` and `tensorPower_eq_pow`: the
  right-tensor functor and the integer tensor powers of Tag 01CU *are* those of the invertible
  object `L` in the monoidal category of sheaves of modules, so the general development above is
  a development about Tag 01CU and not merely an analogue of one.
* `Stacks.SheafOfModules.TensorPower.mulIso_zero_left`, `mulIso_zero_right`, `mulIso_one_right`
  and `mulIso_assoc`: the four normalisations of Tag 01CU, in the vocabulary of the tensor product
  sheaf — against `Stacks.SheafOfModules.tensorSheafLeftUnitor`, `tensorLeftFunctorObjUnitIso`, the
  successor comparison, and `tensorSheafAssociator`.

## Implementation notes

What is *forced*. Every statement here is at the level of objects, morphisms and the equivalence
API, and none computes on sections. That is forced twice over: for `n < 0` the power `e ^ n`
applies a *chosen* quasi-inverse, so it has no description in terms of objects, let alone
sections; and the associativity and unit constraints of the tensor product sheaf come from
sheafification and have no sectionwise formula either. The universes are those of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal`: the site `C : Type u` with
`Category.{v} C` is arbitrary, while the ring sheaf and the modules share the single universe `w`,
because Mathlib's monoidal structure on presheaves of modules is stated only in that form.
**Nothing is narrowed**; in particular no `GrothendieckTopology.HasSheafCompose` hypothesis is
used, and invertibility is taken in the form `(tensorRight L).IsEquivalence`, which
`isEquivalence_tensorRight_iff` identifies with the hypothesis of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower`.

What is *chosen*: the **spelling discipline**, and it is not cosmetic. `pow L 0` is definitionally
`𝟙_ D`, `pow L 1` is definitionally `𝟙_ D ⊗ L`, and `((tensorRight L).asEquivalence ^ 1).functor`
is definitionally `tensorRight L` — but none of these is definitional *syntactically*, and a
composite mixing two such spellings is not type-correct at `implicit` transparency, after which
`rw` and `simp` refuse to fire on it with no error that names the cause. Every constraint
occurring at a literal exponent is therefore given a name whose ascribed type uses the
tensor-power spelling (`powOneIso`, `powLeftUnitor`, `powRightUnitor`, `powAppOne`, `powAppUnit`,
`powSuccFunctorIso`), each proof works at the level of morphisms rather than of isomorphisms
(where a rewrite cannot change the ambient type), and the one place where the reduced spelling is
needed — the pure coherence residue at the exponents `0` and `1` — is reached by `change` and then
discharged by the `monoidal` tactic.

Also *chosen*: the exponents are carried as an explicit target together with an equation
(`mul L n m p (h : n + m = p)` rather than `mul L n m` landing in `pow L (n + m)`). This is the
`shiftFunctorAdd'` idiom of `CategoryTheory.Shift.Basic`, inherited from
`StacksFrontier.CategoryTheory.Equivalence.Pow`, and it is what keeps the associativity statement
free of reindexing isomorphisms: in this form `mul_assoc` has no transport in it at all.

The commutativity normalisation of Tag 01CU — that the multiplication agrees with itself after the
symmetry constraint — is **not** proved here. It is not a consequence of the symmetric monoidal
axioms: in a general symmetric monoidal category an invertible object only satisfies `β² = 1`, with
super vector spaces as the counterexample, so the normalisation needs the rank-one local structure
of an invertible sheaf of modules. That input is available, as
`StacksDraft.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints.braidingScalar_eq_id`, which
gives the symmetry constraint on `L^{⊗ n} ⊗ L^{⊗ n}` for every `n`; what is missing is the
two-variable induction, from the diagonal to the off-diagonal degrees, which consumes
`Stacks.SheafOfModules.tensorSheafBraiding_hexagon_forward` and `mul_assoc` at each step.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- Transport of right-tensoring along an isomorphism of the tensor factor. -/
noncomputable def tensorRightMapIso {A B : D} (i : A ≅ B) :
    CategoryTheory.MonoidalCategory.tensorRight A ≅ CategoryTheory.MonoidalCategory.tensorRight B :=
  (tensoringRight D).mapIso i

/-- The component of `tensorRightMapIso i` at `X` is `X ◁ i.hom`. -/
@[simp]
theorem tensorRightMapIso_hom_app {A B : D} (i : A ≅ B) (X : D) :
    (tensorRightMapIso i).hom.app X = X ◁ i.hom := rfl

/-- The inverse component of `tensorRightMapIso i` at `X` is `X ◁ i.inv`. -/
@[simp]
theorem tensorRightMapIso_inv_app {A B : D} (i : A ≅ B) (X : D) :
    (tensorRightMapIso i).inv.app X = X ◁ i.inv := rfl

omit [MonoidalCategory D] in
/-- Cancellation of an equivalence composed on the right. -/
noncomputable def cancelRightEquiv (F : D ⥤ D) [F.IsEquivalence] {P Q : D ⥤ D}
    (i : P ⋙ F ≅ Q ⋙ F) : P ≅ Q :=
  NatIso.ofComponents (fun X => F.preimageIso (i.app X))
    (fun {X Y} f => F.map_injective (by
      rw [F.map_comp, F.map_comp, Functor.preimageIso_hom,
        Functor.preimageIso_hom, Functor.map_preimage, Functor.map_preimage]
      exact i.hom.naturality f))

omit [MonoidalCategory D] in
/-- Applying `F` to a component of `cancelRightEquiv F i` recovers the component of `i`. -/
@[simp]
theorem map_cancelRightEquiv_hom_app (F : D ⥤ D) [F.IsEquivalence] {P Q : D ⥤ D}
    (i : P ⋙ F ≅ Q ⋙ F) (X : D) :
    F.map ((cancelRightEquiv F i).hom.app X) = i.hom.app X :=
  F.map_preimage (i.app X).hom

omit [MonoidalCategory D] in
/-- Whiskering `cancelRightEquiv F i` on the right by `F` recovers `i`. -/
theorem isoWhiskerRight_cancelRightEquiv (F : D ⥤ D) [F.IsEquivalence] {P Q : D ⥤ D}
    (i : P ⋙ F ≅ Q ⋙ F) :
    Functor.isoWhiskerRight (cancelRightEquiv F i) F = i := by
  ext X
  exact map_cancelRightEquiv_hom_app F i X

omit [MonoidalCategory D] in
/-- Equal autoequivalences have equal integer powers. The two `IsEquivalence` arguments are
propositions, so after substituting the equality they are definitionally equal. -/
theorem pow_functor_congr {F G : D ⥤ D} [F.IsEquivalence] [G.IsEquivalence] (h : F = G) (n : ℤ) :
    (F.asEquivalence ^ n).functor = (G.asEquivalence ^ n).functor := by
  subst h
  rfl

section Pow

variable (L : D) [(CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence]

/-- The autoequivalence given by tensoring on the right by an invertible object. -/
noncomputable abbrev tensorRightEquiv : D ≌ D :=
  (CategoryTheory.MonoidalCategory.tensorRight L).asEquivalence

/-- The `n`th tensor power of an invertible object, for `n : ℤ`. -/
noncomputable def pow (n : ℤ) : D := ((tensorRightEquiv L) ^ n).functor.obj (𝟙_ D)

/-- The zeroth tensor power is the tensor unit. -/
theorem pow_zero : pow L 0 = 𝟙_ D := rfl

/-- The first tensor power is `𝟙_ D ⊗ L`. -/
theorem pow_one : pow L 1 = 𝟙_ D ⊗ L := rfl

/-- The successor comparison `(e ^ n).functor ⋙ - ⊗ L ≅ (e ^ p).functor` for the iterated
autoequivalence `e = tensorRightEquiv L`, where `n + 1 = p`. -/
noncomputable def powSuccFunctorIso (n p : ℤ) (h : n + 1 = p) :
    ((tensorRightEquiv L) ^ n).functor ⋙ CategoryTheory.MonoidalCategory.tensorRight L ≅
      ((tensorRightEquiv L) ^ p).functor :=
  CategoryTheory.Equivalence.powSucc (tensorRightEquiv L) n p h

/-- The successor comparison for tensor powers. -/
noncomputable def powSuccIso (n p : ℤ) (h : n + 1 = p) : pow L n ⊗ L ≅ pow L p :=
  (powSuccFunctorIso L n p h).app (𝟙_ D)

/-- Tensoring on the right by `L^{⊗ (n+1)}` is tensoring by `L^{⊗ n}` and then by `L`. -/
noncomputable def powStepIso (n p : ℤ) (h : n + 1 = p) :
    CategoryTheory.MonoidalCategory.tensorRight (pow L p) ≅
      CategoryTheory.MonoidalCategory.tensorRight (pow L n) ⋙
        CategoryTheory.MonoidalCategory.tensorRight L :=
  (tensorRightMapIso (powSuccIso L n p h)).symm ≪≫ tensorRightTensor (pow L n) L

/-- The comparison `(e ^ k).functor ≅ - ⊗ L^{⊗ k}` at a natural exponent `k`, where
`e = tensorRightEquiv L`. -/
noncomputable def powFunctorIsoNat : (k : ℕ) →
    (((tensorRightEquiv L) ^ (Int.ofNat k)).functor ≅
      CategoryTheory.MonoidalCategory.tensorRight (pow L (Int.ofNat k)))
  | 0 => (rightUnitorNatIso D).symm
  | k + 1 =>
      (powSuccFunctorIso L (Int.ofNat k) (Int.ofNat (k + 1)) rfl).symm ≪≫
        Functor.isoWhiskerRight (powFunctorIsoNat k)
          (CategoryTheory.MonoidalCategory.tensorRight L) ≪≫
        (powStepIso L (Int.ofNat k) (Int.ofNat (k + 1)) rfl).symm

/-- One step down in the exponent, by cancelling the equivalence `- ⊗ L`. -/
noncomputable def powFunctorIsoPred (n p : ℤ) (h : n + 1 = p)
    (x : ((tensorRightEquiv L) ^ p).functor ≅
      CategoryTheory.MonoidalCategory.tensorRight (pow L p)) :
    ((tensorRightEquiv L) ^ n).functor ≅ CategoryTheory.MonoidalCategory.tensorRight (pow L n) :=
  cancelRightEquiv (CategoryTheory.MonoidalCategory.tensorRight L)
    (powSuccFunctorIso L n p h ≪≫ x ≪≫ powStepIso L n p h)

/-- The comparison `(e ^ n).functor ≅ - ⊗ L^{⊗ n}` at a negative exponent `n = -(k + 1)`, where
`e = tensorRightEquiv L`. -/
noncomputable def powFunctorIsoNegSucc : (k : ℕ) →
    (((tensorRightEquiv L) ^ (Int.negSucc k)).functor ≅
      CategoryTheory.MonoidalCategory.tensorRight (pow L (Int.negSucc k)))
  | 0 => powFunctorIsoPred L (Int.negSucc 0) (Int.ofNat 0) rfl (powFunctorIsoNat L 0)
  | k + 1 =>
      powFunctorIsoPred L (Int.negSucc (k + 1)) (Int.negSucc k) rfl (powFunctorIsoNegSucc k)

/-- Tensoring `n` times by `L` is tensoring once by `L^{⊗ n}`. -/
noncomputable def powFunctorIso : (n : ℤ) →
    (((tensorRightEquiv L) ^ n).functor ≅ CategoryTheory.MonoidalCategory.tensorRight (pow L n))
  | Int.ofNat k => powFunctorIsoNat L k
  | Int.negSucc k => powFunctorIsoNegSucc L k

/-- **The uniform recursion for `powFunctorIso`**, valid at every integer exponent. -/
theorem powFunctorIso_succ (n p : ℤ) (h : n + 1 = p) :
    powFunctorIso L p =
      (powSuccFunctorIso L n p h).symm ≪≫
        Functor.isoWhiskerRight (powFunctorIso L n)
          (CategoryTheory.MonoidalCategory.tensorRight L) ≪≫
        (powStepIso L n p h).symm := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    obtain rfl : p = ((k + 1 : ℕ) : ℤ) := by omega
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = Int.negSucc k := ⟨(-n - 1).toNat, by omega⟩
    have hp : powFunctorIso L (Int.negSucc k) =
        powFunctorIsoPred L (Int.negSucc k) p h (powFunctorIso L p) := by
      cases k with
      | zero =>
          obtain rfl : p = (0 : ℤ) := by omega
          rfl
      | succ j =>
          obtain rfl : p = Int.negSucc j := by omega
          rfl
    rw [hp, powFunctorIsoPred, isoWhiskerRight_cancelRightEquiv]
    simp [Iso.trans_assoc]

/-- `powFunctorIso` evaluated at an object, with its target written as a tensor product. -/
noncomputable def powFunctorIsoApp (m : ℤ) (X : D) :
    ((tensorRightEquiv L) ^ m).functor.obj X ≅ X ⊗ pow L m :=
  (powFunctorIso L m).app X

/-- The addition law for the iterated autoequivalence, evaluated at the unit. -/
noncomputable def powAddIso (n m p : ℤ) (h : n + m = p) :
    ((tensorRightEquiv L) ^ m).functor.obj (pow L n) ≅ pow L p :=
  (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) n m p h).app (𝟙_ D)

/-- The forward map of `powAddIso` is the component at the unit of the addition law. -/
theorem powAddIso_hom (n m p : ℤ) (h : n + m = p) :
    (powAddIso L n m p h).hom =
      (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) n m p h).hom.app (𝟙_ D) := rfl

/-- **The multiplication isomorphism of the integer tensor powers.** -/
noncomputable def mul (n m p : ℤ) (h : n + m = p) : pow L n ⊗ pow L m ≅ pow L p :=
  (powFunctorIsoApp L m (pow L n)).symm ≪≫ powAddIso L n m p h

/-! ### Ascribed spellings of the unit constraints

`pow L 0` is definitionally `𝟙_ D` and `pow L 1` is definitionally `𝟙_ D ⊗ L`, but neither is
syntactically so; likewise `((tensorRightEquiv L) ^ 1).functor.obj X` is definitionally `X ⊗ L`.
Mixing two such spellings in one composite produces a term which is not type-correct at `implicit`
transparency, and then `rw` and `simp` silently refuse to fire on it. Every constraint occurring at
a literal exponent is therefore given a name whose ascribed type uses the tensor-power spelling. -/

/-- The first tensor power is `L`, via the left unit constraint. -/
noncomputable def powOneIso : pow L 1 ≅ L := λ_ L

/-- The right unit constraint, with the unit written as the zeroth tensor power. -/
noncomputable def powRightUnitor (X : D) : X ⊗ pow L 0 ≅ X := ρ_ X

/-- The left unit constraint, with the unit written as the zeroth tensor power. -/
noncomputable def powLeftUnitor (X : D) : pow L 0 ⊗ X ≅ X := λ_ X

/-- `powFunctorIso` at the exponent one, with its source written as a tensor product. -/
noncomputable def powAppOne (X : D) : X ⊗ L ≅ X ⊗ pow L 1 := powFunctorIsoApp L 1 X

/-! ### The component recursion -/

/-- The component form of the uniform recursion for `powFunctorIso`. -/
theorem powFunctorIsoApp_succ_hom (n p : ℤ) (h : n + 1 = p) (X : D) :
    (powFunctorIsoApp L p X).hom =
      (powSuccFunctorIso L n p h).inv.app X ≫ ((powFunctorIsoApp L n X).hom ▷ L) ≫
        (α_ X (pow L n) L).hom ≫ (X ◁ (powSuccIso L n p h).hom) := by
  rw [powFunctorIsoApp, powFunctorIso_succ L n p h, powStepIso]
  simp [powFunctorIsoApp]

/-- At the exponent zero, `powFunctorIsoApp` is the inverse of the right unit constraint. -/
theorem powFunctorIsoApp_zero_hom (X : D) :
    (powFunctorIsoApp L 0 X).hom = (powRightUnitor L X).inv := rfl

/-- The first-power comparison: `L^{⊗ 1}` sits inside the tensor product via the left unit
constraint of `L`. It is the triangle identity. -/
theorem powAppOne_eq (X : D) : powAppOne L X = whiskerLeftIso X (powOneIso L).symm := by
  apply Iso.ext
  show (powFunctorIsoApp L 1 X).hom = X ◁ (powOneIso L).inv
  refine (powFunctorIsoApp_succ_hom L 0 1 rfl X).trans ?_
  show 𝟙 (X ⊗ L) ≫ ((ρ_ X).inv ▷ L) ≫ (α_ X (𝟙_ D) L).hom ≫ (X ◁ 𝟙 (𝟙_ D ⊗ L)) =
    X ◁ (λ_ L).inv
  monoidal

/-! ### The unit normalisations -/

/-- The addition law at right exponent zero is the identity. -/
theorem powAddIso_zero_right_hom (n : ℤ) (h : n + 0 = n) :
    (powAddIso L n 0 n h).hom = 𝟙 (pow L n) :=
  (NatTrans.congr_app (congrArg Iso.hom
    (CategoryTheory.Equivalence.powAdd_zero_right (tensorRightEquiv L) n)) (𝟙_ D)).trans rfl

/-- The addition law at left exponent zero is the identity. -/
theorem powAddIso_zero_left_hom (n : ℤ) (h : 0 + n = n) :
    (powAddIso L 0 n n h).hom = 𝟙 (pow L n) :=
  (NatTrans.congr_app (congrArg Iso.hom
    (CategoryTheory.Equivalence.powAdd_zero_left (tensorRightEquiv L) n)) (𝟙_ D)).trans rfl

/-- **Multiplication by the zeroth power on the right is the right unit constraint.** -/
theorem mul_zero_right (n : ℤ) (h : n + 0 = n) :
    mul L n 0 n h = powRightUnitor L (pow L n) := by
  apply Iso.ext
  show (powRightUnitor L (pow L n)).hom ≫ (powAddIso L n 0 n h).hom =
    (powRightUnitor L (pow L n)).hom
  rw [powAddIso_zero_right_hom]
  simp

/-- Multiplication by the first power, unfolded as `powAppOne` followed by the successor
comparison. -/
theorem mul_one_right_eq (n p : ℤ) (h : n + 1 = p) :
    mul L n 1 p h = (powAppOne L (pow L n)).symm ≪≫ powSuccIso L n p h := rfl

/-- **Multiplication by the first power is the successor comparison** of the defining
iteration. -/
theorem mul_one_right (n p : ℤ) (h : n + 1 = p) :
    mul L n 1 p h = whiskerLeftIso (pow L n) (powOneIso L) ≪≫ powSuccIso L n p h := by
  rw [mul_one_right_eq, powAppOne_eq]
  apply Iso.ext
  simp

/-- `powFunctorIso` at the tensor unit, with its source written as the tensor power. -/
noncomputable def powAppUnit (n : ℤ) : pow L n ≅ pow L 0 ⊗ pow L n :=
  powFunctorIsoApp L n (pow L 0)

/-- The component recursion at the tensor unit, in the tensor-power spelling. -/
theorem powAppUnit_succ_hom (n p : ℤ) (h : n + 1 = p) :
    (powAppUnit L p).hom =
      (powSuccIso L n p h).inv ≫ ((powAppUnit L n).hom ▷ L) ≫
        (α_ (pow L 0) (pow L n) L).hom ≫ (pow L 0 ◁ (powSuccIso L n p h).hom) :=
  powFunctorIsoApp_succ_hom L n p h (pow L 0)

/-- The one-step identity behind the left unit normalisation: the left unit constraint of a tensor
power, read through the successor comparison. It is `leftUnitor_tensor` together with naturality of
the left unit constraint. -/
theorem leftUnitor_powSucc (n p : ℤ) (h : n + 1 = p) :
    ((powLeftUnitor L (pow L n)).inv ▷ L) ≫ (α_ (pow L 0) (pow L n) L).hom ≫
        (pow L 0 ◁ (powSuccIso L n p h).hom) =
      (powSuccIso L n p h).hom ≫ (powLeftUnitor L (pow L p)).inv := by
  show ((λ_ (pow L n)).inv ▷ L) ≫ (α_ (𝟙_ D) (pow L n) L).hom ≫
      (𝟙_ D ◁ (powSuccIso L n p h).hom) = (powSuccIso L n p h).hom ≫ (λ_ (pow L p)).inv
  simp only [MonoidalCategory.leftUnitor_inv_whiskerRight_assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.leftUnitor_inv_naturality]

/-- The left unit normalisation at the exponent `p = n + 1` is equivalent to the one at `n`. -/
private theorem powAppUnit_hom_iff (n p : ℤ) (h : n + 1 = p) :
    (powAppUnit L p).hom = (powLeftUnitor L (pow L p)).inv ↔
      (powAppUnit L n).hom = (powLeftUnitor L (pow L n)).inv := by
  have key := leftUnitor_powSucc L n p h
  rw [powAppUnit_succ_hom L n p h]
  constructor
  · intro H
    apply (CategoryTheory.MonoidalCategory.tensorRight L).map_injective
    show (powAppUnit L n).hom ▷ L = (powLeftUnitor L (pow L n)).inv ▷ L
    rw [← cancel_mono ((α_ (pow L 0) (pow L n) L).hom ≫ (pow L 0 ◁ (powSuccIso L n p h).hom)),
      key, ← H, Iso.hom_inv_id_assoc]
  · intro H
    rw [H, key]
    simp

/-- **The left unit normalisation, in its functorial form**: `powFunctorIso` at the tensor unit is
the inverse of the left unit constraint of the tensor power. This is the single statement to which
the left unit normalisation of Tag 01CU reduces, and it is an induction on the exponent whose two
one-step cases are both `leftUnitor_powSucc`. -/
theorem powAppUnit_hom (n : ℤ) :
    (powAppUnit L n).hom = (powLeftUnitor L (pow L n)).inv := by
  induction n using Int.induction_on with
  | zero =>
      show (ρ_ (𝟙_ D)).inv = (λ_ (𝟙_ D)).inv
      exact MonoidalCategory.unitors_inv_equal.symm
  | succ i ih =>
      exact (powAppUnit_hom_iff L i (i + 1) rfl).2 ih
  | pred i ih => exact (powAppUnit_hom_iff L (-(i : ℤ) - 1) (-(i : ℤ)) (by omega)).1 ih

/-- The addition law at left exponent zero, with both ends written as the tensor power. -/
noncomputable def powAddZeroLeftIso (n : ℤ) (h : 0 + n = n) : pow L n ≅ pow L n :=
  powAddIso L 0 n n h

/-- The addition law at left exponent zero is the identity isomorphism. -/
theorem powAddZeroLeftIso_eq (n : ℤ) (h : 0 + n = n) : powAddZeroLeftIso L n h = Iso.refl _ :=
  Iso.ext (powAddIso_zero_left_hom L n h)

/-- Multiplication by the zeroth power on the left, unfolded as the inverse of `powAppUnit`
followed by `powAddZeroLeftIso`. -/
theorem mul_zero_left_eq (n : ℤ) (h : 0 + n = n) :
    mul L 0 n n h = (powAppUnit L n).symm ≪≫ powAddZeroLeftIso L n h := rfl

/-- **Multiplication by the zeroth power on the left is the left unit constraint.** -/
theorem mul_zero_left (n : ℤ) (h : 0 + n = n) :
    mul L 0 n n h = powLeftUnitor L (pow L n) := by
  rw [mul_zero_left_eq, powAddZeroLeftIso_eq, Iso.trans_refl]
  apply Iso.ext
  show (powAppUnit L n).inv = (powLeftUnitor L (pow L n)).hom
  rw [← cancel_epi (powAppUnit L n).hom, Iso.hom_inv_id, powAppUnit_hom]
  simp

/-! ### The one-step recursion for the multiplication -/

/-- The component recursion for the inverse of `powFunctorIsoApp`. -/
theorem powFunctorIsoApp_succ_inv (n p : ℤ) (h : n + 1 = p) (X : D) :
    (powFunctorIsoApp L p X).inv =
      (X ◁ (powSuccIso L n p h).inv) ≫ (α_ X (pow L n) L).inv ≫
        ((powFunctorIsoApp L n X).inv ▷ L) ≫ (powSuccFunctorIso L n p h).hom.app X := by
  rw [← cancel_epi (powFunctorIsoApp L p X).hom, Iso.hom_inv_id,
    powFunctorIsoApp_succ_hom L n p h X]
  simp

/-- **The addition law satisfies the one-step recursion in its right exponent.** It is the cocycle
identity `CategoryTheory.Equivalence.powAdd_assoc` at right exponent one. -/
theorem powAdd_succ_right (m k t k' t' : ℤ) (h : m + k = t) (hk : k + 1 = k')
    (ht : t + 1 = t') (X : D) :
    ((CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m k t h).hom.app X ▷ L) ≫
        (powSuccFunctorIso L t t' ht).hom.app X =
      (powSuccFunctorIso L k k' hk).hom.app (((tensorRightEquiv L) ^ m).functor.obj X) ≫
        (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m k' t'
          (by omega)).hom.app X := by
  have hassoc := CategoryTheory.Equivalence.powAdd_assoc (tensorRightEquiv L) m k 1 t k' t' h hk ht
  exact NatTrans.congr_app (congrArg Iso.hom hassoc) X

/-- The inverted form of `powAdd_succ_right`: the addition law at right exponent `k + 1`. -/
private theorem powAdd_succ_right_inv_app (m k t k' t' : ℤ) (h : m + k = t) (hk : k + 1 = k')
    (ht : t + 1 = t') (X : D) :
    (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m k' t' (by omega)).hom.app X =
      (powSuccFunctorIso L k k' hk).inv.app (((tensorRightEquiv L) ^ m).functor.obj X) ≫
        ((CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m k t h).hom.app X ▷ L) ≫
          (powSuccFunctorIso L t t' ht).hom.app X := by
  rw [powAdd_succ_right L m k t k' t' h hk ht X, ← Category.assoc, Iso.inv_hom_id_app,
    Category.id_comp]

/-- The forward map of the multiplication is the inverse of `powFunctorIsoApp` followed by the
addition law. -/
theorem mul_hom (n m p : ℤ) (h : n + m = p) :
    (mul L n m p h).hom = (powFunctorIsoApp L m (pow L n)).inv ≫ (powAddIso L n m p h).hom := rfl

/-- **The canonical multiplication satisfies the one-step recursion in its right exponent.** This
is the precise sense in which, as Tag 01CU puts it, the value of the multiplication in degree
`(n, 1)` together with associativity determines it in every degree: the recursion identifies
`L^{⊗ m} ⊗ L^{⊗ (k+1)} ≅ L^{⊗ (t+1)}` with the composite
`L^{⊗ m} ⊗ (L^{⊗ k} ⊗ L) ≅ (L^{⊗ m} ⊗ L^{⊗ k}) ⊗ L ≅ L^{⊗ t} ⊗ L ≅ L^{⊗ (t+1)}`. -/
theorem mul_succ_hom (m k t k' t' : ℤ) (h : m + k = t) (hk : k + 1 = k') (ht : t + 1 = t') :
    (mul L m k' t' (by omega)).hom =
      (pow L m ◁ (powSuccIso L k k' hk).inv) ≫ (α_ (pow L m) (pow L k) L).inv ≫
        ((mul L m k t h).hom ▷ L) ≫ (powSuccIso L t t' ht).hom := by
  have hP : (powAddIso L m k' t' (by omega)).hom =
      (powSuccFunctorIso L k k' hk).inv.app (pow L m) ≫
        ((powAddIso L m k t h).hom ▷ L) ≫ (powSuccIso L t t' ht).hom :=
    powAdd_succ_right_inv_app L m k t k' t' h hk ht (𝟙_ D)
  rw [mul_hom L m k' t', powFunctorIsoApp_succ_inv L k k' hk (pow L m), hP, mul_hom L m k t h]
  simp

/-! ### The key compatibility, and associativity -/
omit [(CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence] in
/-- Pure coherence, with two generic morphisms: the conjugation identity behind the recursion of
`mulFunctorConj`. It is `whisker_exchange` followed by naturality of the associativity constraint
in its first variable. -/
@[reassoc]
theorem conj_step_functor {W Y A B' : D} (g : W ⟶ Y) (f : B' ⟶ A ⊗ L) :
    (g ▷ B') ≫ (Y ◁ f) ≫ (α_ Y A L).inv =
      (W ◁ f) ≫ (α_ W A L).inv ≫ ((g ▷ A) ▷ L) := by
  rw [← whisker_exchange_assoc, MonoidalCategory.associator_inv_naturality_left]

omit [(CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence] in
/-- Pure coherence, with two generic morphisms: the conjugation identity behind the recursion of
`mulConj`. It is the pentagon together with naturality of the associativity constraint. -/
@[reassoc]
theorem conj_step_mul {X B A A' T : D} (f : A' ⟶ A ⊗ L) (u : B ⊗ A ⟶ T) :
    (α_ X B A').hom ≫ (X ◁ (B ◁ f)) ≫ (X ◁ (α_ B A L).inv) ≫ (X ◁ (u ▷ L)) ≫
        (α_ X T L).inv =
      ((X ⊗ B) ◁ f) ≫ (α_ (X ⊗ B) A L).inv ≫ ((α_ X B A).hom ▷ L) ≫ ((X ◁ u) ▷ L) := by
  monoidal

/-- The component of the addition law at right exponent zero is the identity. -/
theorem powAdd_zero_right_app (m : ℤ) (h : m + 0 = m) (X : D) :
    (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m 0 m h).hom.app X = 𝟙 _ :=
  (NatTrans.congr_app (congrArg Iso.hom
    (CategoryTheory.Equivalence.powAdd_zero_right (tensorRightEquiv L) m)) X).trans rfl

/-- Naturality of the inverse of `powFunctorIsoApp` in the object. -/
@[reassoc]
theorem powFunctorIsoApp_inv_naturality (k : ℤ) {Y Z : D} (f : Y ⟶ Z) :
    (f ▷ pow L k) ≫ (powFunctorIsoApp L k Z).inv =
      (powFunctorIsoApp L k Y).inv ≫ ((tensorRightEquiv L) ^ k).functor.map f :=
  (powFunctorIso L k).inv.naturality f

/-- The cocycle identity `CategoryTheory.Equivalence.powAdd_assoc`, evaluated at an object. -/
theorem powAdd_assoc_app (n m k p t s : ℤ) (h₁ : n + m = p) (h₂ : m + k = t) (h₃ : p + k = s)
    (X : D) :
    ((tensorRightEquiv L) ^ k).functor.map
          ((CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) n m p h₁).hom.app X) ≫
        (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) p k s h₃).hom.app X =
      (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m k t h₂).hom.app
          (((tensorRightEquiv L) ^ n).functor.obj X) ≫
        (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) n t s (by omega)).hom.app X :=
  NatTrans.congr_app (congrArg Iso.hom
    (CategoryTheory.Equivalence.powAdd_assoc (tensorRightEquiv L) n m k p t s h₁ h₂ h₃)) X

/-- The cocycle identity for the addition law, evaluated at the unit. -/
theorem powAddIso_assoc (n m k p t s : ℤ) (h₁ : n + m = p) (h₂ : m + k = t) (h₃ : p + k = s) :
    ((tensorRightEquiv L) ^ k).functor.map (powAddIso L n m p h₁).hom ≫
        (powAddIso L p k s h₃).hom =
      (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m k t h₂).hom.app (pow L n) ≫
        (powAddIso L n t s (by omega)).hom :=
  powAdd_assoc_app L n m k p t s h₁ h₂ h₃ (𝟙_ D)

/-- The multiplication, conjugated into a comparison of the two right-tensor functors. -/
noncomputable def mulConj (m k t : ℤ) (h : m + k = t) (X : D) :
    (X ⊗ pow L m) ⊗ pow L k ⟶ ((tensorRightEquiv L) ^ t).functor.obj X :=
  (α_ X (pow L m) (pow L k)).hom ≫ (X ◁ (mul L m k t h).hom) ≫ (powFunctorIsoApp L t X).inv

/-- The addition law for the iterated autoequivalence, conjugated the same way. -/
noncomputable def mulFunctorConj (m k t : ℤ) (h : m + k = t) (X : D) :
    (X ⊗ pow L m) ⊗ pow L k ⟶ ((tensorRightEquiv L) ^ t).functor.obj X :=
  ((powFunctorIsoApp L m X).inv ▷ pow L k) ≫
    (powFunctorIsoApp L k (((tensorRightEquiv L) ^ m).functor.obj X)).inv ≫
      (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) m k t h).hom.app X

/-- The conjugation by which the two sides of the key compatibility both recurse. -/
noncomputable def mulConjStep (m k k' : ℤ) (hk : k + 1 = k') (X : D) :
    ((X ⊗ pow L m) ⊗ pow L k) ⊗ L ≅ (X ⊗ pow L m) ⊗ pow L k' :=
  α_ (X ⊗ pow L m) (pow L k) L ≪≫ whiskerLeftIso (X ⊗ pow L m) (powSuccIso L k k' hk)

/-- The one-step recursion of `mulConj` in its right exponent. -/
theorem mulConj_succ (m k t k' t' : ℤ) (h : m + k = t) (hk : k + 1 = k') (ht : t + 1 = t')
    (X : D) :
    mulConj L m k' t' (by omega) X =
      (mulConjStep L m k k' hk X).inv ≫ (mulConj L m k t h X ▷ L) ≫
        (powSuccFunctorIso L t t' ht).hom.app X := by
  rw [mulConj, mul_succ_hom L m k t k' t' h hk ht, powFunctorIsoApp_succ_inv L t t' ht X,
    mulConjStep, mulConj]
  simp only [Iso.trans_inv, whiskerLeftIso_inv, whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  rw [← whiskerLeft_comp_assoc X (powSuccIso L t t' ht).hom (powSuccIso L t t' ht).inv,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp, conj_step_mul_assoc]

/-- The one-step recursion of `mulFunctorConj` in its right exponent. -/
theorem mulFunctorConj_succ (m k t k' t' : ℤ) (h : m + k = t) (hk : k + 1 = k')
    (ht : t + 1 = t') (X : D) :
    mulFunctorConj L m k' t' (by omega) X =
      (mulConjStep L m k k' hk X).inv ≫ (mulFunctorConj L m k t h X ▷ L) ≫
        (powSuccFunctorIso L t t' ht).hom.app X := by
  have hP' := powAdd_succ_right_inv_app L m k t k' t' h hk ht X
  rw [mulFunctorConj, hP',
    powFunctorIsoApp_succ_inv L k k' hk (((tensorRightEquiv L) ^ m).functor.obj X),
    mulConjStep, mulFunctorConj]
  simp only [Iso.trans_inv, whiskerLeftIso_inv, Category.assoc, comp_whiskerRight,
    Iso.hom_inv_id_app_assoc]
  rw [conj_step_functor_assoc]

/-- **The key compatibility.** The multiplication isomorphism, read as a comparison of right-tensor
functors, is the addition law for the powers of the autoequivalence `- ⊗ L`. Everything else about
the multiplication follows from this: it is what lets the cocycle identity
`CategoryTheory.Equivalence.powAdd_assoc`, a statement about composites of functors, be read as
associativity of the multiplication. -/
theorem mulConj_eq (m k : ℤ) : ∀ (t : ℤ) (h : m + k = t) (X : D),
    mulConj L m k t h X = mulFunctorConj L m k t h X := by
  induction k using Int.induction_on with
  | zero =>
      intro t h X
      obtain rfl : t = m := by omega
      have hz : (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) t 0 t h).hom.app X =
          𝟙 (((tensorRightEquiv L) ^ t).functor.obj X) :=
        powAdd_zero_right_app L t h X
      rw [mulConj, mulFunctorConj, mul_zero_right]
      show (α_ X (pow L t) (𝟙_ D)).hom ≫ (X ◁ (ρ_ (pow L t)).hom) ≫
          (powFunctorIsoApp L t X).inv =
        ((powFunctorIsoApp L t X).inv ▷ 𝟙_ D) ≫
          ((ρ_ (((tensorRightEquiv L) ^ t).functor.obj X)).hom ≫
            (CategoryTheory.Equivalence.powAdd (tensorRightEquiv L) t 0 t h).hom.app X)
      rw [hz, Category.comp_id]
      simp
  | succ i ih =>
      intro t' h X
      rw [mulConj_succ L m i (t' - 1) (i + 1) t' (by omega) rfl (by omega) X,
        mulFunctorConj_succ L m i (t' - 1) (i + 1) t' (by omega) rfl (by omega) X,
        ih (t' - 1) (by omega) X]
  | pred i ih =>
      intro t h X
      have key := ih (t + 1) (by omega) X
      rw [mulConj_succ L m (-(i : ℤ) - 1) t (-(i : ℤ)) (t + 1) h (by omega) rfl X,
        mulFunctorConj_succ L m (-(i : ℤ) - 1) t (-(i : ℤ)) (t + 1) h (by omega) rfl X] at key
      rw [Iso.cancel_iso_inv_left] at key
      rw [cancel_mono] at key
      exact (CategoryTheory.MonoidalCategory.tensorRight L).map_injective key

/-- **Associativity of the canonical multiplication**, against the associativity constraint of the
monoidal category. It is the cocycle identity for the integer powers of the autoequivalence
`- ⊗ L` read through `mulConj_eq`. -/
theorem mul_assoc (n m k p t s : ℤ) (h₁ : n + m = p) (h₂ : m + k = t) (h₃ : p + k = s) :
    ((mul L n m p h₁).hom ▷ pow L k) ≫ (mul L p k s h₃).hom =
      (α_ (pow L n) (pow L m) (pow L k)).hom ≫ (pow L n ◁ (mul L m k t h₂).hom) ≫
        (mul L n t s (by omega)).hom := by
  have hK := mulConj_eq L m k t h₂ (pow L n)
  have hR : (α_ (pow L n) (pow L m) (pow L k)).hom ≫ (pow L n ◁ (mul L m k t h₂).hom) ≫
      (mul L n t s (by omega)).hom =
      mulConj L m k t h₂ (pow L n) ≫ (powAddIso L n t s (by omega)).hom := by
    rw [mulConj, mul_hom L n t s]
    simp only [Category.assoc]
  have hL : ((mul L n m p h₁).hom ▷ pow L k) ≫ (mul L p k s h₃).hom =
      mulFunctorConj L m k t h₂ (pow L n) ≫ (powAddIso L n t s (by omega)).hom := by
    rw [mul_hom L n m p, mul_hom L p k s, mulFunctorConj, comp_whiskerRight, Category.assoc,
      powFunctorIsoApp_inv_naturality_assoc]
    simp only [Category.assoc]
    rw [powAddIso_assoc L n m k p t s h₁ h₂ h₃]
  rw [hL, hR, hK]

end Pow

end Stacks.MonoidalCategory

namespace Stacks.SheafOfModules.TensorPower

open CategoryTheory MonoidalCategory Stacks.MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- **The right-tensor functor of Tag 01CU is the right-tensor functor of the monoidal structure
whose tensor product is the tensor product sheaf.** The two agree on objects by definition; on
morphisms this is `Stacks.SheafOfModules.whiskerRight_eq_sheafify_map`. -/
theorem tensorRightFunctor_eq : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L =
    CategoryTheory.MonoidalCategory.tensorRight L := by
  refine CategoryTheory.Functor.ext (fun X => rfl) (fun X Y f => ?_)
  show ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).map f = 𝟙 _ ≫ (CategoryTheory.MonoidalCategory.tensorRight L).map f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map O hO f L).symm

/-- Invertibility of `L` in the sense used by Tag 01CU is invertibility in the sense of the
monoidal structure. -/
theorem isEquivalence_tensorRight_iff :
    (CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence ↔
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          L).IsEquivalence :=
  Iff.of_eq (congrArg Functor.IsEquivalence (tensorRightFunctor_eq O hO L)).symm

/-- **The integer tensor powers of Tag 01CU are the integer tensor powers of the invertible object
`L` in the monoidal category of sheaves of modules.** -/
theorem tensorPower_eq_pow [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    [(CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence] (n : ℤ) :
    tensorPower O hO L n = pow L n :=
  congrArg (fun F => Functor.obj F (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))
    (@Stacks.MonoidalCategory.pow_functor_congr _ _ _ _ ‹_› ‹_› (tensorRightFunctor_eq O hO L) n)

variable [(CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence]

/-- **The canonical multiplication on the integer tensor powers of an invertible sheaf of
modules**, `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ p}` for `n + m = p`. -/
noncomputable def mulIso (n m p : ℤ) (h : n + m = p) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (pow (D := SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L n)).obj
        (pow (D := SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L m) ≅
      pow (D := SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L p :=
  Stacks.MonoidalCategory.mul L n m p h

/-- **Multiplication by the zeroth tensor power on the left is the left unit constraint of the
tensor product sheaf.** -/
@[stacks 01CU "left unit normalisation of the canonical multiplication"]
theorem mulIso_zero_left (n : ℤ) (h : 0 + n = n) :
    mulIso O hO L 0 n n h = Stacks.SheafOfModules.tensorSheafLeftUnitor O hO (pow L n) := by
  rw [mulIso, Stacks.MonoidalCategory.mul_zero_left]
  exact Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor O hO (pow L n)

/-- **Multiplication by the zeroth tensor power on the right is the right unit constraint of the
tensor product sheaf.** -/
theorem mulIso_zero_right (n : ℤ) (h : n + 0 = n) :
    mulIso O hO L n 0 n h = Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO (pow L n) := by
  rw [mulIso, Stacks.MonoidalCategory.mul_zero_right]
  exact Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor O hO (pow L n)

/-- **Multiplication by the first tensor power is the successor comparison** of the defining
iteration, after identifying `L^{⊗ 1}` with `L`. This is the normalisation which removes the
cocycle ambiguity from the multiplication. -/
theorem mulIso_one_right (n p : ℤ) (h : n + 1 = p) :
    mulIso O hO L n 1 p h =
      tensorSheafMapIso O hO (Iso.refl (pow L n)) (powOneIso L) ≪≫
        Stacks.MonoidalCategory.powSuccIso L n p h := by
  rw [mulIso, Stacks.MonoidalCategory.mul_one_right]
  apply Iso.ext
  show _ = (tensorSheafMapIso O hO (Iso.refl (pow L n)) (powOneIso L)).hom ≫ _
  rw [Stacks.SheafOfModules.tensorSheafMapIso_hom_eq]
  simp
  rfl

/-- **Associativity of the canonical multiplication, against the associativity constraint of the
tensor product sheaf.** -/
@[stacks 01CU "associativity of the canonical multiplication"]
theorem mulIso_assoc (n m k p t s : ℤ) (h₁ : n + m = p) (h₂ : m + k = t) (h₃ : p + k = s) :
    tensorSheafMapIso O hO (mulIso O hO L n m p h₁) (Iso.refl (pow L k)) ≪≫
        mulIso O hO L p k s h₃ =
      Stacks.SheafOfModules.tensorSheafAssociator O hO (pow L n) (pow L m) (pow L k) ≪≫
        tensorSheafMapIso O hO (Iso.refl (pow L n)) (mulIso O hO L m k t h₂) ≪≫
          mulIso O hO L n t s (by omega) := by
  apply Iso.ext
  refine Eq.trans (congrArg (· ≫ (mulIso O hO L p k s h₃).hom)
    ((Stacks.SheafOfModules.tensorSheafMapIso_hom_eq O hO (mulIso O hO L n m p h₁)
      (Iso.refl (pow L k))).trans
        (MonoidalCategory.tensorHom_id
          (C := SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
          (mulIso O hO L n m p h₁).hom (pow L k)))) ?_
  refine Eq.trans (Stacks.MonoidalCategory.mul_assoc L n m k p t s h₁ h₂ h₃) ?_
  exact congrArg₂ (· ≫ ·)
    (congrArg Iso.hom
      (Stacks.SheafOfModules.associator_eq_tensorSheafAssociator O hO (pow L n) (pow L m)
        (pow L k)))
    (congrArg (· ≫ (mulIso O hO L n t s (by omega)).hom)
      ((MonoidalCategory.id_tensorHom
          (C := SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
          (pow L n) (mulIso O hO L m k t h₂).hom).symm.trans
        (Stacks.SheafOfModules.tensorSheafMapIso_hom_eq O hO (Iso.refl (pow L n))
          (mulIso O hO L m k t h₂)).symm))

end Stacks.SheafOfModules.TensorPower

end

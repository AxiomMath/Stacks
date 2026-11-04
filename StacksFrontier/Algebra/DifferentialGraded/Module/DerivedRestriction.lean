module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.LeftModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPresentation
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory

/-! # Restriction of scalars is derived Hom out of the regular bimodule

Let `φ : A → B` be a homomorphism of differential graded algebras over a commutative ring `R`.
Example 22.33.2 views `B` as a differential graded `(A, B)`-bimodule — the right action is
multiplication in `B`, the left action of `A` is multiplication through `φ` — and observes that
Hom out of that bimodule is restriction of scalars, by evaluation at the unit:

`Hom_{Mod^{dg}_{(B,d)}}(B, N) ⟶ N_A,  f ↦ f(1)`.

This file constructs the bimodule, proves the evaluation-at-one identification degreewise, as an
isomorphism of differential graded `A`-modules, and naturally — so that the internal hom functor
of Tag 0FQQ out of the regular bimodule *is* restriction of scalars, on differential graded
modules and on homotopy categories. It also constructs restriction of scalars on derived
categories, as the descent of restriction on homotopy categories through the localization at the
quasi-isomorphisms.

## Main definitions

* `DifferentialGradedModule.regularLeftModule`: `B`, as a *left* differential graded `A`-module
  through `φ`.
* `DifferentialGradedModule.regularBimoduleStructure` and `DifferentialGraded.Bimodule.regular`:
  the compatible left `A`-action on the regular right `B`-module (Tag 0FQI), and the resulting
  differential graded `(A, B)`-bimodule. Tensoring with it is the extension of scalars
  `- ⊗_A B : D(A, d) ⥤ D(B, d)`.
* `DifferentialGradedModule.regularHomogeneousEquiv`: evaluation at the unit, degreewise.
* `DifferentialGradedModule.regularHomModuleData`: restriction of scalars, as a presentation of
  the internal hom out of the regular bimodule (Tag 0FQR).
* `DifferentialGradedModule.restrictScalarsFunctor`,
  `DifferentialGradedModule.restrictScalarsHomotopyFunctor` and
  `DifferentialGradedModule.derivedRestriction`: restriction of scalars on differential graded
  modules, on homotopy categories and on derived categories.

## Main results

* `DifferentialGradedModule.regularBimoduleStructure_action`: the left action of the regular
  bimodule is multiplication by `φ a`.
* `DifferentialGradedModule.homModuleRegularIso` and
  `DifferentialGradedModule.homModuleFunctorRegularIso`: evaluation at one identifies the
  internal hom out of the regular bimodule with restriction of scalars, naturally.
* `DifferentialGradedModule.homHomotopyDescent`: the internal hom functor of Tag 0FQQ on
  homotopy categories is the descent of the internal hom functor on differential graded modules.
* `DifferentialGradedModule.homHomotopyFunctorRegularIso`: the same identification on homotopy
  categories.
* `DifferentialGradedModule.restrictScalars_toCochainComplex` and
  `DifferentialGradedModule.restrictScalarsHom_toCochainMap`: restriction changes neither the
  underlying cochain complex nor the underlying cochain map.
* `DifferentialGradedModule.quasiIsomorphisms_restrictScalarsHomotopyFunctor_map`,
  `DifferentialGradedModule.quasiIsomorphisms_isInvertedBy_restrictScalars` and
  `DifferentialGradedModule.quasiIsomorphisms_isInvertedBy_homToDerivedCategory_regular`:
  restriction of scalars carries quasi-isomorphisms to quasi-isomorphisms and therefore inverts
  them after localization, hence so does the functor of which derived Hom out of the regular
  bimodule is the right derived functor.
* `DifferentialGradedModule.derivedRestrictionFactorization`: the square of homotopy and derived
  categories commutes.

## Implementation notes

*Why a left module first.* A `DifferentialGradedModule.BimoduleStructure` is a left differential
graded action on the *cochain complex* underlying the right module, recorded cochain by cochain
(Tag 0FQ3). Rather than verify the unit, multiplicativity and graded-commutator axioms for
multiplication by `φ a` directly, the left action is obtained from
`DifferentialGraded.LeftModule.leftAction`, which proves all three for an arbitrary left
differential graded module; only the module itself and the right `B`-linearity of its action are
new here. The identification of the two underlying complexes is the identity, since a left
differential graded module and a right differential graded module with the same grading and the
same differential have the same underlying complex.

*Why the degreewise identification is reproved.* `DifferentialGradedModule.evaluationAtOne`
(`StacksFrontier/Algebra/DifferentialGraded/Module/EvaluationAtOne.lean`) already carries the
degreewise bijection, but its interface exposes only the value of the evaluation morphism, not a
formula for the bijection itself, and records nothing about the right `A`-action — which is
exactly the field of `DifferentialGradedModule.HomModuleData` that identifies the internal hom.
`DifferentialGradedModule.regularHomogeneousEquiv` is therefore built here with the formulas
`x ↦ (b ↦ x b)` and `f ↦ f 1` available as simp lemmas.

*Why derived restriction is a descent and not a derived functor.* Restriction of scalars does not
change the underlying cochain complex, so it preserves quasi-isomorphisms; the functor out of the
homotopy category therefore already inverts them and descends to the localization with no
resolutions. In particular the hypothesis of
`DifferentialGradedModule.DerivedHomData.ofResolutions` — the existence of property (I)
resolutions, Tag 09KU — is not used anywhere in this file.

*Universes.* The differential graded algebras and their modules are taken at main's
single-universe encoding `StacksDraft.Ch22.Sec4.Tag09JJ`, in which
`DifferentialGradedAlgebra : Type u → Type u` and a module over it again lies in `Type u`. The
Stacks source is universe-polymorphic in the base ring and in each algebra separately; widening
the encoding is an addition of universe parameters rather than a change of content, and nothing
below depends on the universes being equal.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX); the bimodule notion is
  [Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), the compatibility of the two actions is
  [Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI), the internal hom and its presentations
  are [Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR), the internal hom functor is
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ), restriction as a differential graded
  functor is [Tag 09LD](https://stacks.math.columbia.edu/tag/09LD), and derived Hom is
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI).
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- A differential graded algebra `B`, viewed as a *left* differential graded module over `A`
through a homomorphism `φ : A → B`: the action is `a • b = φ a * b`, and the grading and the
differential are those of `B`. -/
def regularLeftModule (φ : A.Hom B) : DifferentialGraded.LeftModule A := by
  letI : Module A.A B.A := Module.compHom B.A φ.toAlgebraHom.toRingHom
  haveI : IsScalarTower R A.A B.A := IsScalarTower.of_algebraMap_smul fun r x => by
    change φ.toAlgebraHom (algebraMap R A.A r) * x = r • x
    rw [AlgHom.commutes, Algebra.smul_def]
  exact
    { M := B.A
      grading := B.grading
      smul_mem := by
        intro m n a x ha hx
        exact SetLike.mul_mem_graded (φ.map_grading m a ha) hx
      d := B.d
      d_comp_d := B.d_comp_d
      d_mem := B.d_mem
      leibniz := by
        intro m n a x ha hx
        change B.d (φ.toAlgebraHom a * x) =
          φ.toAlgebraHom (A.d a) * x + (m.negOnePow : ℤ) • (φ.toAlgebraHom a * B.d x)
        rw [φ.map_d a]
        exact B.leibniz m n (φ.toAlgebraHom a) x (φ.map_grading m a ha) hx }

/-- The underlying cochain complex of `B` as a left differential graded `A`-module through `φ`
is the underlying cochain complex of the regular right differential graded `B`-module: both have
the homogeneous pieces of `B` as terms and the differential of `B` as differential. -/
def regularLeftModuleCochainIso (φ : A.Hom B) :
    DifferentialGraded.LeftModule.toCochainComplex A (regularLeftModule φ) ≅
      (regularModule B).toCochainComplex :=
  Iso.refl _

/-- Left multiplication by an element of `A` through `φ`, as an `R`-linear endomorphism of the
underlying module of `B`. -/
def leftMulAlongₗ (φ : A.Hom B) (a : A.A) : B.A →ₗ[R] B.A where
  toFun x := φ.toAlgebraHom a * x
  map_add' _ _ := mul_add _ _ _
  map_smul' r x := mul_smul_comm r _ x

/-- `leftMulAlongₗ φ a` sends `x` to `φ a * x`. -/
@[simp] theorem leftMulAlongₗ_apply (φ : A.Hom B) (a : A.A) (x : B.A) :
    leftMulAlongₗ φ a x = φ.toAlgebraHom a * x := rfl

/-- Left multiplication by a homogeneous element of `A`, through `φ`, as a homogeneous right
`B`-linear endomorphism of the regular right differential graded `B`-module. -/
def leftMulAlong (φ : A.Hom B) {n : ℤ} (a : A.grading n) :
    HomogeneousMap B (regularModule B) (regularModule B) n :=
  ⟨leftMulAlongₗ φ (a : A.A), by
    rw [mem_homogeneousMapSubmodule]
    refine ⟨fun i x hx => ?_, fun b x => ?_⟩
    · rw [leftMulAlongₗ_apply, add_comm i n]
      exact SetLike.mul_mem_graded (φ.map_grading n a a.property) hx
    · simp only [leftMulAlongₗ_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      rw [mul_assoc]⟩

/-- The underlying map of `leftMulAlong φ a` sends `x` to `φ a * x`. -/
@[simp] theorem leftMulAlong_val_apply (φ : A.Hom B) {n : ℤ} (a : A.grading n) (x : B.A) :
    (leftMulAlong φ a).1 x = φ.toAlgebraHom (a : A.A) * x := rfl

/-- The left differential graded action of `A` on the complex underlying the regular right
differential graded `B`-module, by multiplication through `φ`. -/
def regularLeftActionCochain (φ : A.Hom B) :
    A.LeftAction (regularModule B).toCochainComplex :=
  DifferentialGraded.LeftModule.leftAction A (regularLeftModule φ)
    (regularModule B).toCochainComplex (regularLeftModuleCochainIso φ)

/-- The cochain through which a homogeneous element of `A` acts on the regular right differential
graded `B`-module is multiplication by its image under `φ`. -/
theorem regularLeftActionCochain_apply (φ : A.Hom B) (n p : ℤ) (a : A.grading n)
    (x : (regularModule B).grading p) :
    ((show (regularModule B).grading (p + n) from
      ((regularLeftActionCochain φ).action n a).v p (p + n) (by omega) x) :
        (regularModule B).M) = φ.toAlgebraHom (a : A.A) * (x : B.A) :=
  congrArg Subtype.val
    (DifferentialGraded.LeftModule.leftAction_apply A (regularLeftModule φ)
      (regularModule B).toCochainComplex (regularLeftModuleCochainIso φ) n p a x)

/-- A homomorphism `φ : A → B` of differential graded algebras makes the regular right differential
graded `B`-module into a differential graded `(A, B)`-bimodule: `A` acts on the left by
multiplication through `φ`, and that action is right `B`-linear by associativity. -/
@[stacks 0BYX "the regular bimodule structure"]
def regularBimoduleStructure (φ : A.Hom B) : BimoduleStructure A B (regularModule B) :=
  ⟨regularLeftActionCochain φ, fun n a => ⟨leftMulAlong φ a, fun p x => by
    rw [leftMulAlong_val_apply]
    exact regularLeftActionCochain_apply φ n p a x⟩⟩

/-- The left action of the regular bimodule is multiplication by `φ a`. -/
theorem regularBimoduleStructure_action (φ : A.Hom B) (n p : ℤ) (a : A.grading n)
    (x : (regularModule B).grading p) :
    ((show (regularModule B).grading (p + n) from
      ((regularBimoduleStructure φ).1.action n a).v p (p + n) (by omega) x) :
        (regularModule B).M) = φ.toAlgebraHom (a : A.A) * (x : B.A) :=
  regularLeftActionCochain_apply φ n p a x

/-! ### Evaluation at one: homogeneous Hom out of the regular module -/

/-- A degree-`n` element `x` of a right differential graded `B`-module `P` gives the degree-`n`
homogeneous right `B`-linear map `b ↦ x b` out of the regular module. -/
def regularHomogeneousMapₗ (P : DifferentialGradedModule B) (n : ℤ) :
    P.grading n →ₗ[R] HomogeneousMap B (regularModule B) P n where
  toFun x :=
    ⟨{ toFun := fun b => MulOpposite.op b • (x : P.M)
       map_add' := fun b c => by rw [MulOpposite.op_add, add_smul]
       map_smul' := fun r b => by
         rw [RingHom.id_apply, MulOpposite.op_smul, smul_assoc] },
      by
        rw [mem_homogeneousMapSubmodule]
        refine ⟨fun i b hb => ?_, fun c b => ?_⟩
        · change MulOpposite.op b • (x : P.M) ∈ P.grading (i + n)
          simpa only [add_comm i n] using P.smul_mem n i (x : P.M) b x.property hb
        · change MulOpposite.op (MulOpposite.op c • b) • (x : P.M) =
            MulOpposite.op c • (MulOpposite.op b • (x : P.M))
          rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, MulOpposite.op_mul, mul_smul]⟩
  map_add' x y :=
    Subtype.ext (LinearMap.ext fun b => smul_add (MulOpposite.op b) (x : P.M) (y : P.M))
  map_smul' r x := Subtype.ext (LinearMap.ext fun b => smul_comm (MulOpposite.op b) r (x : P.M))

/-- The homogeneous map attached to `x` sends `b` to `x b`. -/
@[simp] theorem regularHomogeneousMapₗ_apply (P : DifferentialGradedModule B) (n : ℤ)
    (x : P.grading n) (b : B.A) :
    (regularHomogeneousMapₗ P n x).1 b = MulOpposite.op b • (x : P.M) := rfl

/-- Evaluation at the unit of `B`, from the degree-`n` homogeneous right `B`-linear maps out of
the regular module to the degree-`n` part of the target. -/
def regularEvaluationₗ (P : DifferentialGradedModule B) (n : ℤ) :
    HomogeneousMap B (regularModule B) P n →ₗ[R] P.grading n where
  toFun f := ⟨f.1 1, by
    simpa only [zero_add] using f.2.1 0 1 (SetLike.one_mem_graded B.grading)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- `regularEvaluationₗ P n f` is the value of `f` at the unit of `B`. -/
@[simp] theorem regularEvaluationₗ_apply (P : DifferentialGradedModule B) (n : ℤ)
    (f : HomogeneousMap B (regularModule B) P n) :
    (regularEvaluationₗ P n f : P.M) = f.1 1 := rfl

/-- A homogeneous right `B`-linear map out of the regular module is multiplication of its value
at the unit: `f b = f(1) b`. -/
theorem regularHomogeneousMap_eq_smul_one (P : DifferentialGradedModule B) (n : ℤ)
    (f : HomogeneousMap B (regularModule B) P n) (b : B.A) :
    f.1 b = MulOpposite.op b • f.1 1 := by
  have h := f.2.2 b (1 : B.A)
  rwa [show MulOpposite.op b • (1 : (regularModule B).M) = b by
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]] at h

/-- **Evaluation at one.** The degree-`n` homogeneous right `B`-linear maps out of the regular
differential graded `B`-module are the degree-`n` elements of the target, by evaluation at the
unit. This is the degreewise half of Example 22.33.2. -/
@[stacks 0BYX "evaluation at one, degreewise"]
def regularHomogeneousEquiv (P : DifferentialGradedModule B) (n : ℤ) :
    P.grading n ≃ₗ[R] HomogeneousMap B (regularModule B) P n :=
  LinearEquiv.ofLinearMap (regularHomogeneousMapₗ P n) (regularEvaluationₗ P n)
    (LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun b =>
      (regularHomogeneousMap_eq_smul_one P n f b).symm))
    (LinearMap.ext fun x => Subtype.ext (by
      change MulOpposite.op (1 : B.A) • (x : P.M) = (x : P.M)
      rw [MulOpposite.op_one, one_smul]))

/-- The homogeneous map `regularHomogeneousEquiv P n x` sends `b` to `x b`. -/
@[simp] theorem regularHomogeneousEquiv_apply (P : DifferentialGradedModule B) (n : ℤ)
    (x : P.grading n) (b : B.A) :
    (regularHomogeneousEquiv P n x).1 b = MulOpposite.op b • (x : P.M) := rfl

/-- The inverse of `regularHomogeneousEquiv P n` is evaluation at the unit of `B`. -/
@[simp] theorem regularHomogeneousEquiv_symm_apply (P : DifferentialGradedModule B) (n : ℤ)
    (f : HomogeneousMap B (regularModule B) P n) :
    ((regularHomogeneousEquiv P n).symm f : P.M) = f.1 1 := rfl

/-! ### Restriction of scalars as a functor, and its descent to the derived category -/

/-- Restriction of scalars along `φ` on homomorphisms: the same underlying `R`-linear map, whose
`A`-linearity is the `B`-linearity of the original at the image elements. -/
def restrictScalarsHom (φ : A.Hom B) {N N' : DifferentialGradedModule B}
    (f : N ⟶ N') : restrictScalars φ N ⟶ restrictScalars φ N' where
  toFun := f.toFun
  map_smul x a := f.map_smul x (φ.toAlgebraHom a)
  map_grading := f.map_grading
  map_d := f.map_d

/-- The underlying map of `restrictScalarsHom φ f` is the underlying map of `f`. -/
@[simp] theorem restrictScalarsHom_toFun (φ : A.Hom B)
    {N N' : DifferentialGradedModule B} (f : N ⟶ N') :
    (restrictScalarsHom φ f).toFun = f.toFun := rfl

/-- Restriction of scalars along `φ`, as a functor between the categories of differential graded
modules. A homomorphism is unchanged: a `B`-linear map is `A`-linear through `φ`. -/
@[stacks 0BYX "restriction of scalars as a functor", ega "II 2.8.6" "more general"]
def restrictScalarsFunctor (φ : A.Hom B) :
    DifferentialGradedModule B ⥤ DifferentialGradedModule A where
  obj N := restrictScalars φ N
  map f := restrictScalarsHom φ f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `restrictScalarsFunctor φ` sends `N` to `restrictScalars φ N`. -/
@[simp] theorem restrictScalarsFunctor_obj (φ : A.Hom B) (N : DifferentialGradedModule B) :
    (restrictScalarsFunctor φ).obj N = restrictScalars φ N := rfl

/-- `restrictScalarsFunctor φ` does not change the underlying map of a homomorphism. -/
@[simp] theorem restrictScalarsFunctor_map_toFun (φ : A.Hom B)
    {N N' : DifferentialGradedModule B} (f : N ⟶ N') :
    ((restrictScalarsFunctor φ).map f).toFun = f.toFun := rfl

/-- Restriction of scalars does not change the underlying cochain complex of `R`-modules: the
grading and the differential are those of the differential graded `B`-module. -/
theorem restrictScalarsFunctor_comp_forget (φ : A.Hom B) :
    restrictScalarsFunctor φ ⋙ forgetToCochainComplex A = forgetToCochainComplex B := rfl

/-- Restriction of scalars does not change the underlying cochain complex of one module: the
module, the grading and the differential are those of the original differential graded
module. -/
theorem restrictScalars_toCochainComplex (φ : A.Hom B) (N : DifferentialGradedModule B) :
    (restrictScalars φ N).toCochainComplex = N.toCochainComplex :=
  rfl

/-- The cochain map underlying a restricted homomorphism is the cochain map underlying the
original one. The type of the equation is pinned to the cochain complexes of the unrestricted
modules, which is where both sides live by `restrictScalars_toCochainComplex`; elaborating the
equation freely makes the two presentations meet in the unifier instead. -/
theorem restrictScalarsHom_toCochainMap (φ : A.Hom B)
    {N N' : DifferentialGradedModule B} (f : N ⟶ N') :
    @Eq (N.toCochainComplex ⟶ N'.toCochainComplex)
      (restrictScalarsHom φ f).toCochainMap f.toCochainMap :=
  rfl

/-- The restriction along `φ` of a homotopy between homomorphisms of differential graded
`B`-modules: the same underlying map, which is `A`-linear through `φ`. -/
def Homotopy.restrictScalars (φ : A.Hom B) {N N' : DifferentialGradedModule B} {f g : N ⟶ N'}
    (h : Homotopy f g) :
    Homotopy ((restrictScalarsFunctor φ).map f) ((restrictScalarsFunctor φ).map g) where
  toLinearMap :=
    { toFun := h.toLinearMap
      map_add' := h.toLinearMap.map_add
      map_smul' := fun a x =>
        h.toLinearMap.map_smul (MulOpposite.op (φ.toAlgebraHom (MulOpposite.unop a))) x }
  map_grading := h.map_grading
  homotopy_eq := h.homotopy_eq

/-- Restriction of scalars carries homotopic homomorphisms to homotopic homomorphisms. -/
theorem Homotopic.restrictScalars (φ : A.Hom B) {N N' : DifferentialGradedModule B}
    {f g : N ⟶ N'} (h : Homotopic f g) :
    Homotopic ((restrictScalarsFunctor φ).map f) ((restrictScalarsFunctor φ).map g) :=
  ⟨Homotopy.restrictScalars φ h.some⟩

/-- Restriction of scalars along `φ` on the homotopy categories: it descends through the homotopy
quotient because it preserves homotopies. -/
@[stacks 0BYX "restriction of scalars on homotopy categories"]
def restrictScalarsHomotopyFunctor (φ : A.Hom B) : HomotopyCategory B ⥤ HomotopyCategory A :=
  CategoryTheory.Quotient.lift (homotopyRel B)
    (restrictScalarsFunctor φ ⋙ toHomotopyCategory A)
    (fun _ _ _ _ h => CategoryTheory.Quotient.sound (homotopyRel A)
      ⟨Homotopy.restrictScalars φ h.some⟩)

/-- Restriction of scalars on homotopy categories restricts the underlying differential graded
module. -/
def restrictScalarsHomotopyFunctorIso (φ : A.Hom B) :
    toHomotopyCategory B ⋙ restrictScalarsHomotopyFunctor φ ≅
      restrictScalarsFunctor φ ⋙ toHomotopyCategory A :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- The functor on homotopy categories induced by restriction of scalars sends the homotopy
class of a homomorphism to the homotopy class of its restriction. -/
theorem restrictScalarsHomotopyFunctor_map_toHomotopyCategory_map (φ : A.Hom B)
    {N N' : DifferentialGradedModule B} (f : N ⟶ N') :
    (restrictScalarsHomotopyFunctor φ).map ((toHomotopyCategory B).map f) =
      (toHomotopyCategory A).map (restrictScalarsHom φ f) :=
  rfl

/-- Restriction of scalars carries the quasi-isomorphisms of the homotopy category of `B` to
quasi-isomorphisms in the homotopy category of `A`: the underlying cochain complexes and cochain
maps are unchanged. -/
theorem quasiIsomorphisms_restrictScalarsHomotopyFunctor_map (φ : A.Hom B)
    {X Y : HomotopyCategory B} (f : X ⟶ Y) (hf : quasiIsomorphisms' B f) :
    quasiIsomorphisms' A ((restrictScalarsHomotopyFunctor φ).map f) := by
  obtain ⟨N⟩ := X
  obtain ⟨N'⟩ := Y
  induction f using Quot.inductionOn with
  | h g =>
    exact (quasiIsomorphisms_map_iff' A ((restrictScalarsFunctor φ).map g)).mpr (hf g rfl)

/-- The quasi-isomorphisms of differential graded `B`-modules are inverted by restriction of
scalars followed by localization: restriction does not change the underlying complex, so it
preserves quasi-isomorphisms. -/
theorem quasiIsomorphisms_isInvertedBy_restrictScalars (φ : A.Hom B) :
    (quasiIsomorphisms' B).IsInvertedBy
      (restrictScalarsHomotopyFunctor φ ⋙ (quasiIsomorphisms' A).Q) := fun _ _ f hf =>
  Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _
    (quasiIsomorphisms_restrictScalarsHomotopyFunctor_map φ f hf)

/-- Restriction of scalars along `φ` on the derived categories, obtained by descending restriction
on the homotopy categories through the localization at the quasi-isomorphisms. This is the functor
`R Hom(B, -) : D(B, d) ⥤ D(A, d)` of Example 22.33.2, whose identification with derived Hom out of
the regular bimodule is the content of that example. -/
@[stacks 0BYX "restriction of scalars on derived categories"]
def derivedRestriction (φ : A.Hom B) : derivedCategory' B ⥤ derivedCategory' A :=
  Localization.lift (restrictScalarsHomotopyFunctor φ ⋙ (quasiIsomorphisms' A).Q)
    (quasiIsomorphisms_isInvertedBy_restrictScalars φ) (quasiIsomorphisms' B).Q

/-- Derived restriction of scalars is restriction of scalars read through the localizations: the
square of homotopy and derived categories commutes up to this canonical isomorphism. -/
@[stacks 0BYX "the factorization of derived restriction"]
def derivedRestrictionFactorization (φ : A.Hom B) :
    (quasiIsomorphisms' B).Q ⋙ derivedRestriction φ ≅
      restrictScalarsHomotopyFunctor φ ⋙ (quasiIsomorphisms' A).Q :=
  Localization.fac _ (quasiIsomorphisms_isInvertedBy_restrictScalars φ) _

/-! ### The internal hom out of the regular bimodule is restriction of scalars -/

/-- A homomorphism of differential graded modules is determined by its values on homogeneous
elements. -/
theorem Hom.ext_of_grading {M N : DifferentialGradedModule A} {f g : M ⟶ N}
    (h : ∀ (n : ℤ) (x : M.grading n), f.toFun (x : M.M) = g.toFun (x : M.M)) : f = g := by
  apply Hom.ext
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | @homogeneous n x => exact h n x
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The Leibniz rule in the form needed to identify the differential of a presentation of the
internal hom out of the regular module: for `y` homogeneous of degree `n`, multiplying `d y` on
the right by `b` is the differential of the differential graded category applied to `b ↦ y b`. -/
theorem op_smul_d_eq_sub_gradedSign (P : DifferentialGradedModule B) (n : ℤ) {y : P.M}
    (hy : y ∈ P.grading n) (b : B.A) :
    MulOpposite.op b • P.d y =
      P.d (MulOpposite.op b • y) -
        DifferentialGraded.gradedSign R n • (MulOpposite.op (B.d b) • y) := by
  rw [P.leibniz_apply n y hy b, ← Int.cast_smul_eq_zsmul R,
    DifferentialGraded.intCast_negOnePow, add_sub_cancel_right]

/-- Acting by `φ a` and then multiplying on the right by `b` is multiplying by `φ a * b`. -/
theorem op_smul_op_smul_eq_op_mul (φ : A.Hom B) (P : DifferentialGradedModule B)
    (y : P.M) (a : A.A) (b : B.A) :
    MulOpposite.op b • (MulOpposite.op (φ.toAlgebraHom a) • y) =
      MulOpposite.op (φ.toAlgebraHom a * b) • y := by
  rw [← mul_smul, ← MulOpposite.op_mul]

/-- Restriction of scalars along `φ` presents the internal hom out of the regular differential
graded `(A, B)`-bimodule: its degree-`n` part is the degree-`n` homogeneous right `B`-linear maps
`B → P`, by evaluation at the unit, and the right `A`-action matches precomposition with
multiplication through `φ`. -/
@[stacks 0BYX "restriction of scalars presents the internal hom", ega "III 7.2.2" "more general"]
def regularHomModuleData (φ : A.Hom B) (P : DifferentialGradedModule B) :
    HomModuleData A B (regularModule B) P (regularBimoduleStructure φ) where
  module := restrictScalars φ P
  homogeneousEquiv n := regularHomogeneousEquiv P n
  map_d n f :=
    Subtype.ext (LinearMap.ext fun b => op_smul_d_eq_sub_gradedSign P n f.property b)
  map_smul n m p f a x :=
    (op_smul_op_smul_eq_op_mul φ P f.1 (a : A.A) (x : B.A)).trans
      (congrArg ((regularHomogeneousEquiv P n) f).1
        (regularBimoduleStructure_action φ m p a x).symm)

/-- The chosen presentation of the internal hom out of the regular differential graded
`(A, B)`-bimodule, abbreviated. -/
abbrev regularHomPresentation (φ : A.Hom B) (P : DifferentialGradedModule B) :
    HomModuleData A B (regularModule B) P (regularBimoduleStructure φ) :=
  homModulePresentation A B (regularModule B) (regularBimoduleStructure φ) P

/-- The internal hom functor out of the regular differential graded `(A, B)`-bimodule,
abbreviated. -/
abbrev regularHomFunctor (φ : A.Hom B) :
    DifferentialGradedModule B ⥤ DifferentialGradedModule A :=
  homModuleFunctor A B (regularModule B) (regularBimoduleStructure φ)

/-- Evaluation at the unit identifies the internal hom out of the regular differential graded
`(A, B)`-bimodule with restriction of scalars along `φ`. -/
@[stacks 0BYX "evaluation at one"]
def homModuleRegularIso (φ : A.Hom B) (P : DifferentialGradedModule B) :
    (regularHomFunctor φ).obj P ≅ (restrictScalarsFunctor φ).obj P :=
  HomModuleData.compare (regularHomPresentation φ P) (regularHomModuleData φ P)

/-- The comparison is evaluation at one: it sends a homogeneous element of the internal hom to
the value at `1` of the homogeneous map it presents. -/
theorem homModuleRegularIso_hom_apply (φ : A.Hom B) (P : DifferentialGradedModule B) (n : ℤ)
    (g : (regularHomPresentation φ P).module.grading n) :
    ((regularHomPresentation φ P).homogeneousEquiv n g).1 1 =
      (homModuleRegularIso φ P).hom.toFun g.1 :=
  (HomModuleData.compareHom_apply_grading (regularHomPresentation φ P)
    (regularHomModuleData φ P) n g).symm

/-- The internal hom functor acts by postcomposition, read through the chosen presentations. -/
theorem regularHomFunctor_map_apply_grading (φ : A.Hom B)
    {P P' : DifferentialGradedModule B} (f : P ⟶ P') (n : ℤ)
    (g : (regularHomPresentation φ P).module.grading n) :
    ((regularHomFunctor φ).map f).toFun g.1 =
      (((regularHomPresentation φ P').homogeneousEquiv (0 + n)).symm
        (homogeneousMapComp B (rfl : (0 : ℤ) + n = 0 + n) (cocycleOfHom B f).1
          ((regularHomPresentation φ P).homogeneousEquiv n g))).1 :=
  homPostcompHomogeneousMap_apply A B (regularModule B) (regularBimoduleStructure φ)
    (regularHomPresentation φ P) (regularHomPresentation φ P') 0 n (cocycleOfHom B f).1 g

/-- Evaluation at one turns the action of the internal hom functor into the action of `f`:
`(f ∘ g)(1) = f(g(1))`. -/
theorem homModuleRegularIso_hom_map (φ : A.Hom B) {P P' : DifferentialGradedModule B}
    (f : P ⟶ P') (n : ℤ) (g : (regularHomPresentation φ P).module.grading n) :
    (homModuleRegularIso φ P').hom.toFun (((regularHomFunctor φ).map f).toFun g.1) =
      f.toFun ((homModuleRegularIso φ P).hom.toFun g.1) := by
  rw [regularHomFunctor_map_apply_grading φ f n g,
    ← homModuleRegularIso_hom_apply φ P' (0 + n)
      (((regularHomPresentation φ P').homogeneousEquiv (0 + n)).symm
        (homogeneousMapComp B (rfl : (0 : ℤ) + n = 0 + n) (cocycleOfHom B f).1
          ((regularHomPresentation φ P).homogeneousEquiv n g))),
    LinearEquiv.apply_symm_apply, homogeneousMapComp_val, cocycleOfHom_val]
  exact congrArg f.toFun (homModuleRegularIso_hom_apply φ P n g)

/-- Evaluation at one is natural: the internal hom functor out of the regular differential graded
`(A, B)`-bimodule is restriction of scalars along `φ`. -/
@[stacks 0BYX "evaluation at one is natural"]
def homModuleFunctorRegularIso (φ : A.Hom B) :
    regularHomFunctor φ ≅ restrictScalarsFunctor φ :=
  NatIso.ofComponents (fun P => homModuleRegularIso φ P)
    (fun {_ _} f => Hom.ext_of_grading fun n g => homModuleRegularIso_hom_map φ f n ⟨g.1, g.2⟩)

/-! ### Evaluation at one on homotopy categories, and derived restriction -/

/-- The equivalence of homotopy categories carries the internal hom functor on differential
graded modules to the differential graded functor's action on homotopy classes: both send the
class of `f` to the class of postcomposition with `f`. -/
theorem homotopyCategoryEquivalence_functor_map_homModuleFunctor_map
    (N : DifferentialGradedModule B) (L : BimoduleStructure A B N)
    {P P' : DifferentialGradedModule B} (f : P ⟶ P') :
    (homotopyCategoryEquivalence A).functor.map
        ((toHomotopyCategory A).map ((homModuleFunctor A B N L).map f)) =
      (homDGFunctorData A B N L).functor.onK.map
        ((homotopyCategoryEquivalence B).functor.map ((toHomotopyCategory B).map f)) := by
  show Quotient.mk _ (cocycleOfHom A ((homModuleFunctor A B N L).map f)) =
    (homDGFunctorData A B N L).functor.mapHomotopyClass
      (Quotient.mk _ (cocycleOfHom B f))
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The internal hom functor on homotopy categories is the descent of the internal hom functor on
differential graded modules: both send `P` to the chosen presentation of `Hom^•_B(N, P)` and a
homotopy class to the class of the postcomposition. -/
@[stacks 0FQQ "descent of the functor on DG modules"]
def homHomotopyDescent (N : DifferentialGradedModule B) (L : BimoduleStructure A B N) :
    toHomotopyCategory B ⋙ homHomotopyCategoryFunctor A B N L ≅
      homModuleFunctor A B N L ⋙ toHomotopyCategory A :=
  Functor.fullyFaithfulCancelRight (homotopyCategoryEquivalence A).functor
    (NatIso.ofComponents
      (fun P => (homotopyCategoryEquivalence A).counitIso.app
        (show (dgCategory A).K from (homModuleFunctor A B N L).obj P))
      (by
        intro P P' f
        change (homotopyCategoryEquivalence A).functor.map
              ((homotopyCategoryEquivalence A).inverse.map
                ((homDGFunctorData A B N L).functor.onK.map
                  ((homotopyCategoryEquivalence B).functor.map
                    ((toHomotopyCategory B).map f)))) ≫
            ((homotopyCategoryEquivalence A).counitIso.app _).hom =
          ((homotopyCategoryEquivalence A).counitIso.app _).hom ≫
            (homotopyCategoryEquivalence A).functor.map
              ((toHomotopyCategory A).map ((homModuleFunctor A B N L).map f))
        rw [homotopyCategoryEquivalence_functor_map_homModuleFunctor_map N L f]
        exact (homotopyCategoryEquivalence A).counitIso.hom.naturality _))

/-- Evaluation at one on homotopy categories: the internal hom functor out of the regular
differential graded `(A, B)`-bimodule is restriction of scalars along `φ`. This is the
identification `R Hom(B, -) = (-)_A` of Example 22.33.2, before localizing. -/
@[stacks 0BYX "evaluation at one on homotopy categories"]
def homHomotopyFunctorRegularIso (φ : A.Hom B) :
    homHomotopyCategoryFunctor A B (regularModule B) (regularBimoduleStructure φ) ≅
      restrictScalarsHomotopyFunctor φ :=
  CategoryTheory.Quotient.natIsoLift _
    (homHomotopyDescent (regularModule B) (regularBimoduleStructure φ) ≪≫
      Functor.isoWhiskerRight (homModuleFunctorRegularIso φ) (toHomotopyCategory A) ≪≫
        (restrictScalarsHomotopyFunctorIso φ).symm)

/-- The functor whose right derived functor is derived Hom out of the regular differential graded
`(A, B)`-bimodule already inverts the quasi-isomorphisms: it is restriction of scalars followed by
localization, and restriction does not change the underlying complex. -/
@[stacks 0BYX "derived Hom out of the regular bimodule needs no resolutions"]
theorem quasiIsomorphisms_isInvertedBy_homToDerivedCategory_regular (φ : A.Hom B) :
    (quasiIsomorphisms' B).IsInvertedBy
      (homToDerivedCategory A B (regularModule B) (regularBimoduleStructure φ)) :=
  (MorphismProperty.IsInvertedBy.iff_of_iso (quasiIsomorphisms' B)
    (Functor.isoWhiskerRight (homHomotopyFunctorRegularIso φ) (quasiIsomorphisms' A).Q)).mpr
      (quasiIsomorphisms_isInvertedBy_restrictScalars φ)

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- The regular differential graded `(A, B)`-bimodule of a homomorphism `φ : A → B` of differential
graded algebras: `B` itself, with `B` acting on the right by multiplication and `A` acting on the
left through `φ`. Tensoring with it is the extension of scalars `- ⊗_A B : D(A, d) ⥤ D(B, d)` of
Example 22.33.2. -/
@[stacks 0BYX "the regular bimodule"]
def regular (φ : A.Hom B) : Bimodule A B where
  rightModule := regularModule B
  leftAction := regularBimoduleStructure φ

end DifferentialGraded.Bimodule

end

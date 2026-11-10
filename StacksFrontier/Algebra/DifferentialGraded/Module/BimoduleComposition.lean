module

public import StacksFrontier.Algebra.DGA.BimoduleTensorExact
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimodulePropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTotalization
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorAlgebraComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The composite of two differential graded bimodules

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, B)`-bimodule and let `N'` be a differential graded
`(B, C)`-bimodule. The relative tensor product `N ⊗_B N'` of the right `B`-module underlying `N`
with `N'` is a right differential graded `C`-module, and the left `A`-action on `N` carries over
to it: a homogeneous `a ∈ A^n` acts by the image of left multiplication by `a` under the
differential graded tensor functor of Tag 09LM, which is a homogeneous right `C`-linear
endomorphism of degree `n`. This makes `N ⊗_B N'` a differential graded `(A, C)`-bimodule, the
bimodule `N''` of Stacks Tag 0BZ3.

Tag 0BZ5 asserts that, as soon as the canonical map
`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` of Tag 0BZ4 is an isomorphism in
`D(C, d)`, the composite of the derived tensor functors of `N` and of `N'` is isomorphic to the
derived tensor functor of such a composite bimodule — namely of `Ñ ⊗_B Ñ'`, where `Ñ` and `Ñ'`
are property-(P) replacements of `N` and of `N'`. That bimodule and that isomorphism are the
second half of this file.

## Main definitions

* `DifferentialGradedModule.homogeneousMapCochain`: a homogeneous right-linear endomorphism of a
  differential graded module, read as a cochain of its underlying complex.
* `DifferentialGraded.Bimodule.leftMulHomogeneous`: left multiplication by a homogeneous element
  of `A` on a differential graded `(A, B)`-bimodule, as a homogeneous right `B`-linear
  endomorphism.
* `DifferentialGraded.Bimodule.compLeftAction`: the resulting left differential graded `A`-action
  on the complex underlying `N ⊗_B N'`.
* `DifferentialGraded.Bimodule.compTensor`: the composite differential graded `(A, C)`-bimodule
  `N'' = N ⊗_B N'`.
* `DifferentialGraded.Bimodule.propertyPResolution` and
  `DifferentialGraded.Bimodule.propertyPResolutionHom`: a property-(P) replacement of a
  differential graded bimodule and the quasi-isomorphism out of it, chosen from Tag 0FQK.
* `DifferentialGraded.Bimodule.compTensorResolution`: the differential graded `(A, C)`-bimodule
  `N''` of Tag 0BZ5, the composite of the property-(P) replacements of `N` and of `N'`.
* `DifferentialGraded.Bimodule.baseChangeComparisonIso`: the identification separating the
  canonical map of Tag 0BZ4 from the comparison of Tag 09LS at `(A ⊗_R B)_B`.
* `DifferentialGraded.Bimodule.QuasiIsoInvertsDerivedTensor`,
  `DifferentialGraded.Bimodule.DerivedTensorCompositionData` and
  `DifferentialGraded.Bimodule.BaseChangeDevissage`: the three inputs of Tag 0BZ5 that the
  library does not have, namely the second assertion of Tag 09S3, Tag 0BZ3, and the dévissage
  performed in the proof of Tag 0BZ5.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompIso`: Tag 0BZ5 itself, the isomorphism
  `(- ⊗_A^𝐋 N) ⋙ (- ⊗_B^𝐋 N') ≅ - ⊗_A^𝐋 N''`.

## Main results

* `DifferentialGradedModule.totalizeCochain_homogeneousMapCochain` and
  `DifferentialGradedModule.totalizeCochain_injective`: a homogeneous right-linear endomorphism
  and the cochain it defines determine one another.
* `DifferentialGraded.Bimodule.compTensor_leftActionTotal_tensorPure`: on a pure tensor the left
  `A`-action of `N''` is `a • (x ⊗ y) = (a • x) ⊗ y`.
* `DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_iff`: the hypothesis of
  Tag 0BZ5 is the hypothesis of Tag 0BZ3 for the pair `((A ⊗_R B)_B, {}_B(B ⊗_R C)_C)`.

## Implementation notes

*What is and is not proved here.* Tag 0BZ3 asserts that, when the canonical map from the derived
to the plain tensor product `N_B ⊗_B^𝐋 N' → (N ⊗_B N')_C` is an isomorphism, the composite of the
derived tensor functors of `N` and of `N'` is isomorphic to the derived tensor functor of
`N'' = N ⊗_B N'`. Only the bimodule `N''` named in that statement is constructed here; the
comparison of functors is not, and it is one of the three assumptions of Tag 0BZ5 below.

*The three assumptions of Tag 0BZ5.* Its proof opens by replacing `N` and `N'` by
quasi-isomorphic bimodules with property (P), which is licensed by the second assertion of Tag
09S3; it then shows, by a dévissage along the property-(P) filtrations, that the hypothesis of
Tag 0BZ3 holds for the replacements as soon as the map of Tag 0BZ4 is an isomorphism; and it
concludes by Tag 0BZ3. The library has the construction of `1 ⊗ f` of Tag 09S3 but not its
invertibility for a quasi-isomorphism `f`, and has neither the dévissage nor Tag 0BZ3. Each of
the three is therefore a named hypothesis, documented at its own definition, and the tag on
`DifferentialGraded.Bimodule.derivedTensorFunctorCompIso` records them. No clause of the
statement is weakened: `N`, `N'` and the three algebras are arbitrary, the bimodule `N''` is a
definition rather than something extracted from the conclusion, and the hypothesis of the source
is the hypothesis assumed. What is proved from the three assumptions is the replacement argument
itself, together with the identification of the hypothesis of Tag 0BZ4 with the hypothesis of
Tag 0BZ3 at the base-change pair.

*The action is transported through the differential graded tensor functor.* The tensor product
`N ⊗_B N'` is specified by `DifferentialGraded.Bimodule.TensorDGFunctorData` and not by a
presentation, so the only handle on it is that datum: its underlying differential graded functor
`dgCategory B ⥤ dgCategory C` sends a homogeneous right `B`-linear endomorphism of degree `n` of
`N` to one of `N ⊗_B N'`, `R`-linearly and compatibly with identities, composition and the
differential, which are exactly the three axioms of a left differential graded action. The
action is therefore defined without choosing anything, and its right `C`-linearity — the
condition that makes it a bimodule structure — is automatic, since the morphisms of
`dgCategory C` are the right `C`-linear maps.

*Cochains versus homogeneous maps.* `DifferentialGradedAlgebra.LeftAction` is stated in terms of
cochains of the underlying complex, while the differential graded functor produces homogeneous
right-linear maps. `homogeneousMapCochain` converts the latter to the former, and
`totalizeCochain_injective` makes the conversion injective, so each of the three action axioms
reduces to an identity of `R`-linear endomorphisms, where
`DifferentialGraded.leftActionTotal_one`, `_mul` and `_leibniz` apply.

*Universes.* The bimodule stack is stated at the single-universe slice of the encoding of
`StacksDraft.Ch22.Sec4.Tag09JJ`, since `DifferentialGradedModule.BimoduleStructure` has result
type `Type u`; `TensorDGFunctorData` is stated there too. This file is therefore at one universe
as well, apart from the cochain conversion lemmas, which are polymorphic in the algebra and
module universes as the differential graded category is.

## References

* [Stacks Project, Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3); the tensor functor whose
  differential graded form carries the action is
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), and the correspondence between
  compatible left actions and right-linear endomorphisms is
  [Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI).
* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5); its hypothesis is the
  map of [Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the derived tensor functor and
  its comparison with the plain one are [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) and
  [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2), the transformation attached to a
  homomorphism of bimodules is [Tag 09S3](https://stacks.math.columbia.edu/tag/09S3), the
  property-(P) replacements are [Tag 0FQK](https://stacks.math.columbia.edu/tag/0FQK) and their
  telescopes [Tag 0FQL](https://stacks.math.columbia.edu/tag/0FQL).
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]

/-! ### Homogeneous right-linear endomorphisms as cochains -/

/-- A homogeneous right `C`-linear endomorphism of degree `n` of a differential graded
`C`-module `T`, read as a degree-`n` cochain of the complex underlying `T`. -/
def homogeneousMapCochain (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ) (f : HomogeneousMap C T T n) :
    Cochain T.toCochainComplex T.toCochainComplex n :=
  Cochain.mk fun p q hpq => ModuleCat.ofHom
    { toFun := fun x => ⟨f.1 (x : T.M), by rw [← hpq]; exact f.2.1 p (x : T.M) x.2⟩
      map_add' := fun x y => Subtype.ext (f.1.map_add (x : T.M) (y : T.M))
      map_smul' := fun r x => Subtype.ext (f.1.map_smul r (x : T.M)) }

/-- On a homogeneous element, the cochain of a homogeneous right-linear endomorphism is that
endomorphism. -/
theorem homogeneousMapCochain_v (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ) (f : HomogeneousMap C T T n)
    (p q : ℤ) (hpq : p + n = q) (x : T.grading p) :
    ((show T.grading q from ((homogeneousMapCochain C T n f).v p q hpq).hom x) : T.M) =
      f.1 (x : T.M) := rfl

/-- `DifferentialGradedModule.homogeneousMapCochain_v`, with the cochain component applied
through the concrete-category coercion. -/
theorem homogeneousMapCochain_v' (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ) (f : HomogeneousMap C T T n)
    (p q : ℤ) (hpq : p + n = q) (x : T.grading p) :
    ((show T.grading q from ((homogeneousMapCochain C T n f).v p q hpq) x) : T.M) =
      f.1 (x : T.M) := rfl

/-- Assembling the cochain of a homogeneous right-linear endomorphism recovers it. -/
theorem totalizeCochain_homogeneousMapCochain (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ) (f : HomogeneousMap C T T n) :
    totalizeCochain C T n (homogeneousMapCochain C T n f) = f.1 := by
  ext x
  induction x using DirectSum.Decomposition.inductionOn T.grading with
  | zero => simp [totalizeCochain]
  | add x y hx hy => simp only [map_add, hx, hy]
  | @homogeneous p x =>
    rw [totalizeCochain_apply C T n p _ x]
    exact homogeneousMapCochain_v C T n f p (p + n) rfl x

/-- A cochain is determined by the `R`-linear endomorphism it assembles to. -/
theorem totalizeCochain_injective (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ)
    {f g : Cochain T.toCochainComplex T.toCochainComplex n}
    (h : totalizeCochain C T n f = totalizeCochain C T n g) : f = g := by
  refine Cochain.ext f g fun p q hpq => ?_
  subst hpq
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let x' : T.grading p := x
  have hx := congrArg (fun φ : T.M →ₗ[R] T.M => φ (x' : T.M)) h
  rw [totalizeCochain_apply C T n p f x', totalizeCochain_apply C T n p g x'] at hx
  exact Subtype.ext hx

/-- The cochain of a sum of homogeneous right-linear endomorphisms is the sum of their cochains. -/
theorem homogeneousMapCochain_add (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ) (f g : HomogeneousMap C T T n) :
    homogeneousMapCochain C T n (f + g) =
      homogeneousMapCochain C T n f + homogeneousMapCochain C T n g := by
  refine totalizeCochain_injective C T n ?_
  simp only [totalizeCochain_add, totalizeCochain_homogeneousMapCochain]
  rfl

/-- The cochain of a scalar multiple of a homogeneous right-linear endomorphism is that scalar
multiple of its cochain. -/
theorem homogeneousMapCochain_smul (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ) (r : R) (f : HomogeneousMap C T T n) :
    homogeneousMapCochain C T n (r • f) = r • homogeneousMapCochain C T n f := by
  refine totalizeCochain_injective C T n ?_
  simp only [totalizeCochain_smul, totalizeCochain_homogeneousMapCochain]
  rfl

/-- The identity is read as the identity cochain. -/
theorem homogeneousMapCochain_id (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) :
    homogeneousMapCochain C T 0 ((dgCategory C).id T) =
      Cochain.ofHom (𝟙 T.toCochainComplex) := by
  refine totalizeCochain_injective C T 0 ?_
  rw [totalizeCochain_homogeneousMapCochain, totalizeCochain_id, dgCategory_id_val]

/-- Composition of homogeneous right-linear endomorphisms is read as composition of cochains, in
the opposite order. -/
theorem homogeneousMapCochain_comp (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) {m n k : ℤ} (h : m + n = k)
    (g : HomogeneousMap C T T m) (f : HomogeneousMap C T T n) :
    homogeneousMapCochain C T k ((dgCategory C).comp h g f) =
      (homogeneousMapCochain C T n f).comp (homogeneousMapCochain C T m g) (by omega) := by
  refine totalizeCochain_injective C T k ?_
  rw [totalizeCochain_homogeneousMapCochain, totalizeCochain_comp C T n m k (by omega),
    totalizeCochain_homogeneousMapCochain, totalizeCochain_homogeneousMapCochain,
    dgCategory_comp_val]

/-- The differential of the differential graded category is read as the cochain differential. -/
theorem homogeneousMapCochain_differential (C : DifferentialGradedAlgebra.{u, v} R)
    (T : DifferentialGradedModule.{u, v, w} C) (n : ℤ) (f : HomogeneousMap C T T n) :
    homogeneousMapCochain C T (n + 1) ((dgCategory C).d f) =
      δ n (n + 1) (homogeneousMapCochain C T n f) := by
  refine totalizeCochain_injective C T (n + 1) ?_
  rw [totalizeCochain_homogeneousMapCochain, dgCategory_d_val]
  ext x
  rw [totalizeCochain_delta_apply C T n (homogeneousMapCochain C T n f) x,
    totalizeCochain_homogeneousMapCochain]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  rw [← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow,
    DifferentialGraded.gradedSign_succ, neg_smul, ← sub_eq_add_neg]

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-! ### Left multiplication on a bimodule as a homogeneous right-linear endomorphism -/

/-- Left multiplication by a homogeneous element of `A` on a differential graded
`(A, B)`-bimodule, as a homogeneous right `B`-linear endomorphism of degree `n` of its
underlying right differential graded `B`-module. -/
def leftMulHomogeneous (N : Bimodule A B) {n : ℤ} (a : A.grading n) :
    HomogeneousMap B N.rightModule N.rightModule n :=
  ⟨leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A), by
    rw [mem_homogeneousMapSubmodule]
    refine ⟨fun i x hx => leftActionTotal_apply_mem A B N.rightModule N.leftAction.1 a
      (⟨x, hx⟩ : N.rightModule.grading i), fun b x => ?_⟩
    induction b using DirectSum.Decomposition.inductionOn B.grading with
    | zero => simp
    | @homogeneous q b =>
      exact leftActionTotal_commutes A B N.rightModule N.leftAction.1 N.leftAction.2 a b x
    | add b c hb hc => simp only [MulOpposite.op_add, add_smul, map_add, hb, hc]⟩

/-- The underlying `R`-linear endomorphism of `leftMulHomogeneous N a` is the total left action
of `a`. -/
@[simp] theorem leftMulHomogeneous_val (N : Bimodule A B) {n : ℤ} (a : A.grading n) :
    (leftMulHomogeneous N a).1 = leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) :=
  rfl

/-- Left multiplication by a sum is the sum of the left multiplications. -/
theorem leftMulHomogeneous_add (N : Bimodule A B) {n : ℤ} (a b : A.grading n) :
    leftMulHomogeneous N (a + b) = leftMulHomogeneous N a + leftMulHomogeneous N b :=
  Subtype.ext (map_add (leftActionTotal A B N.rightModule N.leftAction.1) (a : A.A) b)

/-- Left multiplication by a scalar multiple is the scalar multiple of the left multiplication. -/
theorem leftMulHomogeneous_smul (N : Bimodule A B) {n : ℤ} (r : R) (a : A.grading n) :
    leftMulHomogeneous N (r • a) = r • leftMulHomogeneous N a :=
  Subtype.ext (map_smul (leftActionTotal A B N.rightModule N.leftAction.1) r (a : A.A))

/-- The unit of `A` acts as the identity. -/
theorem leftMulHomogeneous_one (N : Bimodule A B) :
    leftMulHomogeneous N (⟨1, SetLike.one_mem_graded A.grading⟩ : A.grading 0) =
      (dgCategory B).id N.rightModule :=
  Subtype.ext (leftActionTotal_one A B N.rightModule N.leftAction.1)

/-- A product of homogeneous elements acts as the composite of their actions. -/
theorem leftMulHomogeneous_mul (N : Bimodule A B) {n m : ℤ} (a : A.grading n) (b : A.grading m) :
    leftMulHomogeneous N
        (⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ :
          A.grading (n + m)) =
      (dgCategory B).comp (rfl : n + m = n + m) (leftMulHomogeneous N a)
        (leftMulHomogeneous N b) :=
  Subtype.ext (by
    rw [dgCategory_comp_val, leftMulHomogeneous_val, leftMulHomogeneous_val,
      leftMulHomogeneous_val, leftActionTotal_mul A B N.rightModule N.leftAction.1 a b,
      leftActionTotal_apply A B N.rightModule N.leftAction.1 n a,
      leftActionTotal_apply A B N.rightModule N.leftAction.1 m b, Module.End.mul_eq_comp])

/-- The differential of `A` acts by the differential of the differential graded category. -/
theorem leftMulHomogeneous_d (N : Bimodule A B) {n : ℤ} (a : A.grading n) :
    leftMulHomogeneous N (⟨A.d a, A.d_mem n a a.property⟩ : A.grading (n + 1)) =
      (dgCategory B).d (leftMulHomogeneous N a) :=
  Subtype.ext (by
    rw [dgCategory_d_val]
    ext x
    have h := leftActionTotal_leibniz A B N.rightModule N.leftAction.1 a x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      leftMulHomogeneous_val]
    rw [← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow] at h
    change leftActionTotal A B N.rightModule N.leftAction.1 (A.d (a : A.A)) x = _
    rw [h]
    abel)

/-! ### The composite bimodule -/

/-- Left multiplication by a homogeneous element of `A` on `N ⊗_B N'`, as a degree-`n` cochain of
the underlying complex: it is the image, under the differential graded tensor functor with `N'`,
of left multiplication by that element on `N`. -/
def compAction (N : Bimodule A B) (N' : Bimodule B C) (n : ℤ) :
    A.grading n →ₗ[R] Cochain (tensorObj N' N.rightModule).toCochainComplex
      (tensorObj N' N.rightModule).toCochainComplex n where
  toFun a := homogeneousMapCochain C (tensorObj N' N.rightModule) n
    ((tensorDGFunctor N').functor.map (leftMulHomogeneous N a))
  map_add' a b := by
    rw [leftMulHomogeneous_add, (tensorDGFunctor N').functor.map_add,
      homogeneousMapCochain_add]
  map_smul' r a := by
    rw [RingHom.id_apply, leftMulHomogeneous_smul, (tensorDGFunctor N').functor.map_smul,
      homogeneousMapCochain_smul]

/-- `compAction N N' n a` is the cochain of the image of `leftMulHomogeneous N a` under the
differential graded tensor functor with `N'`. -/
theorem compAction_apply (N : Bimodule A B) (N' : Bimodule B C) (n : ℤ) (a : A.grading n) :
    compAction N N' n a = homogeneousMapCochain C (tensorObj N' N.rightModule) n
      ((tensorDGFunctor N').functor.map (leftMulHomogeneous N a)) := rfl

/-- The left differential graded `A`-action on the complex underlying `N ⊗_B N'`: a homogeneous
element of `A` acts by the image, under the differential graded tensor functor with `N'`, of left
multiplication by that element on `N`. -/
def compLeftAction (N : Bimodule A B) (N' : Bimodule B C) :
    A.LeftAction (tensorObj N' N.rightModule).toCochainComplex where
  action := compAction N N'
  map_one := by
    rw [compAction_apply, leftMulHomogeneous_one, (tensorDGFunctor N').functor.map_id,
      homogeneousMapCochain_id]
  map_mul n m a b := by
    rw [compAction_apply, compAction_apply, compAction_apply, leftMulHomogeneous_mul,
      (tensorDGFunctor N').functor.map_comp, homogeneousMapCochain_comp]
  map_d n a := by
    rw [compAction_apply, compAction_apply, leftMulHomogeneous_d,
      (tensorDGFunctor N').functor.map_d, homogeneousMapCochain_differential]

/-- **Stacks Tag 0BZ3.** The composite of a differential graded `(A, B)`-bimodule `N` with a
differential graded `(B, C)`-bimodule `N'`: the relative tensor product `N ⊗_B N'` of the right
`B`-module underlying `N` with `N'`, carrying the left `A`-action inherited from `N`. This is the
bimodule `N''` of Tag 0BZ3. -/
@[stacks 0BZ3 "the composite bimodule N'' = N (x)_B N' as an (A, C)-bimodule"]
def compTensor (N : Bimodule A B) (N' : Bimodule B C) : Bimodule A C where
  rightModule := tensorObj N' N.rightModule
  leftAction :=
    ⟨compLeftAction N N', fun n a =>
      ⟨(tensorDGFunctor N').functor.map (leftMulHomogeneous N a), fun p x =>
        homogeneousMapCochain_v' C (tensorObj N' N.rightModule) n _ p (p + n) rfl x⟩⟩

/-- The right differential graded `C`-module underlying the composite bimodule is the relative
tensor product `N ⊗_B N'`. -/
theorem compTensor_rightModule (N : Bimodule A B) (N' : Bimodule B C) :
    (compTensor N N').rightModule = tensorObj N' N.rightModule := rfl

/-- The left `A`-action on the composite bimodule `N ⊗_B N'`, on a pure tensor: it is the action
on the left factor. -/
theorem compTensor_leftActionTotal_tensorPure (N : Bimodule A B) (N' : Bimodule B C) {n : ℤ}
    (a : A.grading n) (x : N.rightModule.M) (y : N'.rightModule.M) :
    leftActionTotal A C (compTensor N N').rightModule (compTensor N N').leftAction.1 (a : A.A)
        ((tensorPure N' N.rightModule).toLinearMap x y) =
      (tensorPure N' N.rightModule).toLinearMap
        (leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) x) y := by
  rw [leftActionTotal_apply A C (compTensor N N').rightModule (compTensor N N').leftAction.1 n a]
  change totalizeCochain C (tensorObj N' N.rightModule) n
    (compAction N N' n a) _ = _
  rw [compAction_apply, totalizeCochain_homogeneousMapCochain]
  exact (tensorDGFunctor N').map_pure (leftMulHomogeneous N a) x y

/-! ### Property-(P) replacements of a bimodule -/

/-- A property-(P) replacement of a differential graded `(A, B)`-bimodule `N`: the source of the
quasi-isomorphism `P ⟶ N` produced by Tag 0FQK, chosen once and for all. -/
def propertyPResolution (N : Bimodule A B) : Bimodule A B :=
  (DifferentialGraded.Bimodule.exists_propertyP_resolution A B N).choose

/-- The quasi-isomorphism from the property-(P) replacement of a differential graded
`(A, B)`-bimodule to the bimodule itself. -/
def propertyPResolutionHom (N : Bimodule A B) : propertyPResolution N ⟶ N :=
  (DifferentialGraded.Bimodule.exists_propertyP_resolution A B N).choose_spec.choose

/-- The map out of the property-(P) replacement is a quasi-isomorphism. -/
theorem quasiIso_propertyPResolutionHom (N : Bimodule A B) :
    QuasiIso ((forgetToCochainComplex B).map (propertyPResolutionHom N).rightHom) :=
  (DifferentialGraded.Bimodule.exists_propertyP_resolution A B N).choose_spec.choose_spec.1

/-- The property-(P) replacement has property (P), recorded as a property-(P) filtration of the
right differential graded `Aᵒᵖ ⊗_R B`-module it is by Tag 0FQJ. -/
theorem nonempty_propertyPFiltration_propertyPResolution (N : Bimodule A B) :
    Nonempty (PropertyPFiltration (toTensorModule A B (propertyPResolution N))) :=
  (DifferentialGraded.Bimodule.exists_propertyP_resolution A B N).choose_spec.choose_spec.2

/-- **The bimodule `N''` of Stacks Tag 0BZ5.** Given a differential graded `(A, B)`-bimodule `N`
and a differential graded `(B, C)`-bimodule `N'`, it is the composite `Ñ ⊗_B Ñ'` of their
property-(P) replacements, viewed as a differential graded `(A, C)`-bimodule. -/
@[stacks 0BZ5 "the bimodule N'' described in the proof"]
def compTensorResolution (N : Bimodule A B) (N' : Bimodule B C) : Bimodule A C :=
  compTensor (propertyPResolution N) (propertyPResolution N')

/-! ### The hypothesis of Tag 0BZ3, and the hypothesis of Tag 0BZ5 -/

/-- The identification in `D(C, d)` by which the canonical map of Tag 0BZ4 differs from the
comparison of Tag 09LS at the right differential graded `B`-module `(A ⊗_R B)_B`: the
compatibility of ordinary tensoring with the passage to homotopy classes, followed by the
identification `(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C = (A ⊗_R B ⊗_R C)_C`. -/
def baseChangeComparisonIso (A B C : DifferentialGradedAlgebra.{u, u} R) :
    (tensorFunctorToDerivedCategory (baseChangeBimodule B C)).obj
        ((toHomotopyCategory B).obj (baseChangeModule A B)) ≅
      (quasiIsomorphisms' C).Q.obj
        ((toHomotopyCategory C).obj (baseChangeModule (A.tensorProduct B) C)) :=
  (quasiIsomorphisms' C).Q.mapIso
      ((tensorCompFunctor_quotient (baseChangeBimodule B C)).app (baseChangeModule A B)).symm ≪≫
    (quasiIsomorphisms' C).Q.mapIso ((toHomotopyCategory C).mapIso (tripleTensorIso A B C))

/-- The canonical map of Tag 0BZ4 is the comparison of Tag 09LS at `(A ⊗_R B)_B` followed by an
isomorphism. -/
theorem derivedTensorBaseChangeComparison_eq (A B C : DifferentialGradedAlgebra.{u, u} R) :
    derivedTensorBaseChangeComparison A B C =
      (derivedTensorFunctorCounit (baseChangeBimodule B C)).app
          ((toHomotopyCategory B).obj (baseChangeModule A B)) ≫
        (baseChangeComparisonIso A B C).hom := rfl

/-- **The hypothesis of Stacks Tag 0BZ5 is the hypothesis of Stacks Tag 0BZ3 for the base-change
pair.** The canonical map `(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` of Tag 0BZ4 is
an isomorphism in `D(C, d)` if and only if the comparison of Tag 09LS from the derived to the
plain tensor product with `{}_B(B ⊗_R C)_C` is an isomorphism at `(A ⊗_R B)_B`. -/
theorem isIso_derivedTensorBaseChangeComparison_iff (A B C : DifferentialGradedAlgebra.{u, u} R) :
    IsIso (derivedTensorBaseChangeComparison A B C) ↔
      IsIso ((derivedTensorFunctorCounit (baseChangeBimodule B C)).app
        ((toHomotopyCategory B).obj (baseChangeModule A B))) := by
  rw [derivedTensorBaseChangeComparison_eq]
  exact ⟨fun _ => IsIso.of_isIso_comp_right _ (baseChangeComparisonIso A B C).hom,
    fun _ => inferInstance⟩

/-! ### The inputs that the library does not have -/

/-- **The second assertion of Stacks Tag 09S3**: a quasi-isomorphism `f : N ⟶ N'` of differential
graded `(A, B)`-bimodules induces an isomorphism `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` of functors.

This property is **proved unconditionally** as
`DifferentialGraded.Bimodule.quasiIsoInvertsDerivedTensor` in
`StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorQuasiIsoDevissage`, which carries
`@[stacks 09S3]`; it is obtained from `derivedTensorTwoOutOfThree` rather than by the source's
own route. The predicate is kept as a named `Prop` because several statements quantify over it,
not because it is open. The construction of `1 ⊗ f` itself is
`DifferentialGraded.Bimodule.derivedTensorNatTrans`, and the source's argument — filtering a
differential graded `A`-module with property (P) and reducing to the shifts `A[k]` — is recorded
at `DifferentialGraded.Bimodule.isIso_derivedTensorNatTrans_of_propertyP`. -/
def QuasiIsoInvertsDerivedTensor (A B : DifferentialGradedAlgebra.{u, u} R) : Prop :=
  ∀ {N N' : Bimodule A B} (f : N ⟶ N'),
    QuasiIso ((forgetToCochainComplex B).map f.rightHom) → IsIso (derivedTensorNatTrans f)

/-- **Stacks Tag 0BZ3, as data.** For a differential graded `(A, B)`-bimodule `N` and a
differential graded `(B, C)`-bimodule `N'` such that the comparison of Tag 09LS from the derived
to the plain tensor product with `N'` is an isomorphism at `N_B` — which is the hypothesis
`N_B ⊗_B^𝐋 N' ⟶ (N ⊗_B N')_C` of Tag 0BZ3 — an isomorphism between the composite of the two
derived tensor functors and the derived tensor functor of `N'' = N ⊗_B N'`.

The source builds the isomorphism by a dévissage of `D(A, d)` along the modules with property (P),
where the transformation is the comparison of Tag 09LS at `M ⊗_A N` and the hypothesis is what
makes it invertible on the shifts `A[k]`. That construction is not available, so the data is
assumed where it is needed. -/
def DerivedTensorCompositionData (A B C : DifferentialGradedAlgebra.{u, u} R) : Type _ :=
  ∀ (N : Bimodule A B) (N' : Bimodule B C),
    IsIso ((derivedTensorFunctorCounit N').app ((toHomotopyCategory B).obj N.rightModule)) →
      (derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅ derivedTensorFunctor (compTensor N N'))

/-- **The dévissage carried out in the proof of Stacks Tag 0BZ5**: if the hypothesis of Tag 0BZ3
holds for the base-change pair `((A ⊗_R B)_B, {}_B(B ⊗_R C)_C)` — equivalently, by
`DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_iff`, if the canonical map of
Tag 0BZ4 is an isomorphism — then it holds for every differential graded `(A, B)`-bimodule `P` and
every differential graded `(B, C)`-bimodule `P'` having property (P): the comparison of Tag 09LS
from the derived to the plain tensor product with `P'` is an isomorphism at `P_B`.

The source proves it by telescoping the property-(P) filtration of `P` (Tag 0FQL), using that
`- ⊗_B^𝐋 P'` is exact and commutes with direct sums while `- ⊗_B P'` preserves admissible exact
sequences and direct sums, to reduce to the graded pieces of the filtration, which are direct sums
of shifts of `(A ⊗_R B)_B`; the same dévissage along a property-(P) filtration of `P'` then
reduces to the shifts of `{}_B(B ⊗_R C)_C`, where the map is the one assumed invertible. None of
that reduction is available, so it is assumed where it is needed. -/
def BaseChangeDevissage (A B C : DifferentialGradedAlgebra.{u, u} R) : Prop :=
  IsIso ((derivedTensorFunctorCounit (baseChangeBimodule B C)).app
      ((toHomotopyCategory B).obj (baseChangeModule A B))) →
    ∀ (P : Bimodule A B) (P' : Bimodule B C),
      Nonempty (PropertyPFiltration (toTensorModule A B P)) →
        Nonempty (PropertyPFiltration (toTensorModule B C P')) →
          IsIso ((derivedTensorFunctorCounit P').app ((toHomotopyCategory B).obj P.rightModule))

/-! ### Tag 0BZ5 -/

/-- **Stacks Tag 0BZ5.** *"Let `R` be a ring. Let `(A, d)`, `(B, d)`, and `(C, d)` be differential
graded `R`-algebras. Assume that (0BZ4) is an isomorphism. Let `N` be a differential graded
`(A, B)`-bimodule. Let `N'` be a differential graded `(B, C)`-bimodule. Then the composition
`D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to `- ⊗_A^𝐋 N''` for
a differential graded `(A, C)`-bimodule `N''` described in the proof."*

The bimodule `N''` is `DifferentialGraded.Bimodule.compTensorResolution N N'`, the composite
`Ñ ⊗_B Ñ'` of property-(P) replacements of `N` and `N'`, exactly as in the source; it is a
definition and not a choice extracted from the conclusion.

The hypotheses `hAB` and `hBC`, `hcomp` and `hdev` are the inputs the library does not have, each
named and documented at its own definition: the second assertion of Tag 09S3, which is what
licenses replacing `N` and `N'` by quasi-isomorphic bimodules; Tag 0BZ3, which is the isomorphism
of functors once the hypothesis `N_B ⊗_B^𝐋 N' ⟶ (N ⊗_B N')_C` holds; and the dévissage of the
present proof, which derives that hypothesis for the replacements. The remaining steps are
proved: the replacements exist by Tag 0FQK, and the passage from the hypothesis of Tag 0BZ4 to the
hypothesis fed to the dévissage is
`DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_iff`. -/
def derivedTensorFunctorCompIso
    (hAB : QuasiIsoInvertsDerivedTensor A B) (hBC : QuasiIsoInvertsDerivedTensor B C)
    (hcomp : DerivedTensorCompositionData A B C) (hdev : BaseChangeDevissage A B C)
    (hiso : IsIso (derivedTensorBaseChangeComparison A B C))
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  have _hN := hAB (propertyPResolutionHom N) (quasiIso_propertyPResolutionHom N)
  have _hN' := hBC (propertyPResolutionHom N') (quasiIso_propertyPResolutionHom N')
  Functor.isoWhiskerRight (asIso (derivedTensorNatTrans (propertyPResolutionHom N))).symm
      (derivedTensorFunctor N') ≪≫
    Functor.isoWhiskerLeft (derivedTensorFunctor (propertyPResolution N))
      (asIso (derivedTensorNatTrans (propertyPResolutionHom N'))).symm ≪≫
    hcomp (propertyPResolution N) (propertyPResolution N')
      (hdev ((isIso_derivedTensorBaseChangeComparison_iff A B C).1 hiso) _ _
        (nonempty_propertyPFiltration_propertyPResolution N)
        (nonempty_propertyPFiltration_propertyPResolution N'))

end DifferentialGraded.Bimodule

end


module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionFunctor
public import StacksFrontier.CategoryTheory.Adjunction.Quotient
public import StacksFrontier.Algebra.DGA.BimoduleTensorExact
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorPureSpan

/-! # The tensor–Hom adjunction for differential graded bimodules

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Stacks 09LN says that tensoring with `N` is left
adjoint to the internal hom out of `N`: there is a canonical identification

`Hom_{Mod^{dg}_{(B, d)}}(M ⊗_A N, P) = Hom_{Mod^{dg}_{(A, d)}}(M, Hom^•_B(N, P))`,

natural in the right differential graded `A`-module `M` and the right differential graded
`B`-module `P`. This file constructs that bijection, assembles it into an adjunction between the
functor of Tag 09LM and the functor of Tag 0FQQ, and descends the adjunction to the homotopy
categories `K(A, d)` and `K(B, d)`.

The homotopy-category form is the hypothesis `hadj` of
`DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHom`, the deduction of Stacks 09LT.

## Main definitions

* `DifferentialGraded.Bimodule.tensorHomEquiv`: the bijection above.
* `DifferentialGraded.Bimodule.tensorCompFunctor_adj_homModuleFunctor`: **Stacks 09LN** on the
  categories of differential graded modules, as an adjunction.
* `DifferentialGraded.Bimodule.tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor`:
  **Stacks 09LN** on the homotopy categories.
* `DifferentialGraded.Bimodule.exists_tensorHomLift`: the inverse direction of the bijection,
  recorded by its value on a pure tensor.
* `DifferentialGraded.Bimodule.exists_tensorHomComplexIso`: **Stacks 09LN in every degree**, the
  isomorphism of Hom complexes of which the bijection above is the degree-zero part.

## Implementation notes

*Only degree-zero closed maps are needed.* The source states Stacks 09LN as an isomorphism of
Hom *complexes*, i.e. in every degree. What is constructed here is the degree-zero part, which is
the bijection of morphism groups of the two categories of differential graded modules; that is
what an adjunction is, and that is what Tag 09LT consumes. The all-degrees statement would need a
*graded* universal property of the relative tensor product, which
`DifferentialGraded.Bimodule.TensorDGFunctorData` does not record: its `universal` field
characterizes the tensor product by homomorphisms of differential graded modules, i.e. by closed
maps of degree zero. The three `@[stacks 09LN]` attributes below are therefore part-qualified
"in degree zero", and the part strings also distinguish them from the ungraded case of the same
tag, which is formalized separately as
`Bimod.tensorHomEquiv` (`StacksFrontier/Algebra/Category/ModuleCat/Bimod/TensorHom.lean`).

*The all-degrees statement is here too.* `DifferentialGraded.Bimodule.exists_tensorHomComplexIso`
at the end of the file is the isomorphism of Hom complexes that the source asserts, and it
carries a fourth `@[stacks 09LN]` attribute whose part string says so; the three attributes just
mentioned stay part-qualified because each of them is the degree-zero part of it. What that last
section needs beyond the degree-zero bijection is not a graded universal property of the relative
tensor product but two things that are available: the pure tensors generate `M ⊗_A N`, and the
evaluation `Hom^•_B(N, P) ⊗_A N ⟶ P` is closed, so a degree-`n` homogeneous map
`M ⟶ Hom^•_B(N, P)` can be tensored with `N` by the functoriality of Tag 09LM on homogeneous
morphisms and then evaluated.

*The two directions.* From a homomorphism `g : M ⊗_A N ⟶ P` the homogeneous element `x ∈ M^p` is
sent to the degree-`p` homogeneous map `y ↦ g (x ⊗ y)`, read into the chosen presentation
`DifferentialGradedModule.homModulePresentation` of the internal hom; the components are
assembled over the grading of `M` by `DirectSum.toModule`. The right `A`-linearity of the result
is exactly the `balance` field of the universal pure tensor against the `map_smul` field of the
presentation, and its compatibility with the differentials is the `map_d` field of the universal
pure tensor against the `map_d` field of the presentation. Conversely a homomorphism
`φ : M ⟶ Hom^•_B(N, P)` gives the balanced bilinear map `(x, y) ↦ (φ x)(y)`, and the universal
property of the relative tensor product turns that into a homomorphism out of `M ⊗_A N`.

*Spellings.* `tensorCompFunctor` and `homModuleFunctor` are the differential graded functors
conjugated by the equivalences of Tag 09LC, so `(tensorCompFunctor N).obj M` and
`(homModuleFunctor A B N.rightModule N.leftAction).obj P` are definitionally — but not
*reducibly* — the underlying tensor product and the chosen presentation of the internal hom.
Everything below is therefore stated at one of the two spellings throughout and the boundary is
crossed only by `exact`, which checks definitional equality at default transparency; a `rewrite`
across it fails, because `rewrite` re-checks type correctness at `implicit` transparency.

*The descent to the homotopy categories* is purely formal: the unit and the counit are the
images of the unit and the counit downstairs. It is `CategoryTheory.Quotient.adjunctionOfSquares`
applied to the two compatibility isomorphisms that are already available, Tag 09LM's
`DifferentialGraded.Bimodule.tensorCompFunctor_quotient` and Tag 0FQQ's
`DifferentialGradedModule.homHomotopyDescent`.

## References

* [Stacks Project, Tag 09LN](https://stacks.math.columbia.edu/tag/09LN); the two functors are
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) and
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ), and the consumer of the
  homotopy-category form is [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

open DifferentialGradedModule

/-! ### Evaluation out of the presented internal hom -/

/-- Evaluation on the degree-`p` part of the presented internal hom: a homogeneous element is
read as the homogeneous right-`B`-linear map `N → P` that it presents. -/
private def homEvalComponent (N : Bimodule A B) (P : DifferentialGradedModule B) (p : ℤ) :
    (homPresentation N P).module.grading p →ₗ[R] N.rightModule.M →ₗ[R] P.M :=
  (homogeneousMapSubmodule B N.rightModule P p).subtype.comp
    ((homPresentation N P).homogeneousEquiv p).toLinearMap

/-- Evaluation: the presented internal hom `Hom^•_B(N, P)` maps `R`-linearly to the
right-`B`-linear maps `N → P`, by reading each homogeneous piece through its presentation. -/
private def homEval (N : Bimodule A B) (P : DifferentialGradedModule B) :
    (homPresentation N P).module.M →ₗ[R] N.rightModule.M →ₗ[R] P.M :=
  (DirectSum.toModule R ℤ _ (homEvalComponent N P)).comp
    (DirectSum.decomposeLinearEquiv (homPresentation N P).module.grading).toLinearMap

/-- A linear map assembled from its homogeneous components by `DirectSum.toModule` acts on a
homogeneous element through the component of its degree. -/
private theorem toModule_decompose_apply {C : DifferentialGradedAlgebra R}
    (X : DifferentialGradedModule C) {T : Type*} [AddCommMonoid T] [Module R T]
    (f : ∀ p, X.grading p →ₗ[R] T) (p : ℤ) (x : X.M) (hx : x ∈ X.grading p) :
    (DirectSum.toModule R ℤ _ f) (DirectSum.decomposeLinearEquiv X.grading x) = f p ⟨x, hx⟩ := by
  change (DirectSum.toModule R ℤ _ f)
    (DirectSum.decomposeLinearEquiv X.grading ((⟨x, hx⟩ : X.grading p) : X.M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]

/-- Evaluation at a homogeneous element is the homogeneous map that element presents. -/
private theorem homEval_apply (N : Bimodule A B) (P : DifferentialGradedModule B) (p : ℤ)
    (z : (homPresentation N P).module.M) (hz : z ∈ (homPresentation N P).module.grading p) :
    homEval N P z = ((homPresentation N P).homogeneousEquiv p ⟨z, hz⟩).1 :=
  toModule_decompose_apply _ (homEvalComponent N P) p z hz

/-- `homEval_apply` with the homogeneous element given as an element of the graded piece. -/
private theorem homEval_apply' (N : Bimodule A B) (P : DifferentialGradedModule B) (p : ℤ)
    (v : (homPresentation N P).module.grading p) :
    homEval N P (v : (homPresentation N P).module.M) =
      ((homPresentation N P).homogeneousEquiv p v).1 :=
  homEval_apply N P p (v : (homPresentation N P).module.M) v.property

/-- Every value of evaluation is right `B`-linear, being a sum of right `B`-linear maps. -/
private theorem homEval_op_smul (N : Bimodule A B) (P : DifferentialGradedModule B)
    (z : (homPresentation N P).module.M) (y : N.rightModule.M) (b : B.A) :
    homEval N P z (MulOpposite.op b • y) = MulOpposite.op b • homEval N P z y := by
  induction z using DirectSum.Decomposition.inductionOn (homPresentation N P).module.grading with
  | zero => simp
  | @homogeneous p v =>
    rw [homEval_apply N P p (v : (homPresentation N P).module.M) v.property]
    exact ((homPresentation N P).homogeneousEquiv p ⟨_, v.property⟩).2.2 b y
  | add z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw, smul_add]

/-! ### From a homomorphism into the internal hom to a balanced bilinear map -/

/-- The balanced bilinear map attached to a homomorphism `φ : M ⟶ Hom^•_B(N, P)`: send `x` and
`y` to the value at `y` of the homogeneous map presented by `φ x`. -/
private def balancedOfHom (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (φ : M ⟶ (homPresentation N P).module) :
    BalancedBilinearMap M N P where
  toLinearMap := (homEval N P).comp φ.toFun
  map_grading p q x y := by
    have hv : φ.toFun (x : M.M) ∈ (homPresentation N P).module.grading p :=
      φ.map_grading p (x : M.M) x.property
    change homEval N P (φ.toFun (x : M.M)) (y : N.rightModule.M) ∈ P.grading (p + q)
    rw [homEval_apply N P p _ hv]
    simpa only [add_comm q p] using
      ((homPresentation N P).homogeneousEquiv p ⟨_, hv⟩).2.1 q (y : N.rightModule.M) y.property
  map_d p x y := by
    have hv : φ.toFun (x : M.M) ∈ (homPresentation N P).module.grading p :=
      φ.map_grading p (x : M.M) x.property
    have hdx : φ.toFun (M.d (x : M.M)) =
        ((homPresentation N P).module.gradedDifferential p ⟨_, hv⟩ :
          (homPresentation N P).module.M) :=
      LinearMap.congr_fun φ.map_d (x : M.M)
    have hmd := (homPresentation N P).map_d p ⟨_, hv⟩
    change P.d (homEval N P (φ.toFun (x : M.M)) y) =
      homEval N P (φ.toFun (M.d (x : M.M))) y +
        (p.negOnePow : ℤ) • homEval N P (φ.toFun (x : M.M)) (N.rightModule.d y)
    rw [hdx, homEval_apply N P (p + 1) _
        ((homPresentation N P).module.gradedDifferential p ⟨_, hv⟩).property,
      show (⟨((homPresentation N P).module.gradedDifferential p ⟨_, hv⟩ :
          (homPresentation N P).module.M),
          ((homPresentation N P).module.gradedDifferential p ⟨_, hv⟩).property⟩ :
            (homPresentation N P).module.grading (p + 1)) =
        (homPresentation N P).module.gradedDifferential p ⟨_, hv⟩ from rfl,
      hmd, homEval_apply N P p _ hv, homogeneousMapDifferential_val]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow]
    abel
  balance p q n x y a := by
    have hv : φ.toFun (x : M.M) ∈ (homPresentation N P).module.grading p :=
      φ.map_grading p (x : M.M) x.property
    have hw : MulOpposite.op (a : A.A) • φ.toFun (x : M.M) ∈
        (homPresentation N P).module.grading (p + n) :=
      (homPresentation N P).module.smul_mem p n _ (a : A.A) hv a.property
    have hsm : φ.toFun (MulOpposite.op (a : A.A) • (x : M.M)) =
        MulOpposite.op (a : A.A) • φ.toFun (x : M.M) :=
      φ.map_smul (x : M.M) (a : A.A)
    change homEval N P (φ.toFun (MulOpposite.op (a : A.A) • (x : M.M)))
        (y : N.rightModule.M) =
      homEval N P (φ.toFun (x : M.M))
        ((show N.rightModule.grading (q + n) from
          (N.leftAction.1.action n a).v q (q + n) (by omega) y) : N.rightModule.M)
    rw [hsm, homEval_apply N P (p + n) _ hw, homEval_apply N P p _ hv]
    exact (homPresentation N P).map_smul p n q ⟨_, hv⟩ a y
  map_right x y b := homEval_op_smul N P (φ.toFun x) y b

/-! ### From a homomorphism out of the tensor product to a homomorphism into the internal hom -/

/-- Restricting a homomorphism out of `M ⊗_A N` to the pure tensors with a fixed homogeneous
`x ∈ M^p` gives a degree-`p` homogeneous right-`B`-linear map `N → P`. -/
private def pureHom (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) (p : ℤ) :
    M.grading p →ₗ[R] HomogeneousMap B N.rightModule P p where
  toFun x := ⟨g.toFun.comp (((tensorDGFunctor N).pure M).toLinearMap (x : M.M)), by
    constructor
    · intro i y hy
      change g.toFun (((tensorDGFunctor N).pure M).toLinearMap (x : M.M) y) ∈ P.grading (i + p)
      simpa only [add_comm i p] using
        g.map_grading (p + i) _ (((tensorDGFunctor N).pure M).map_grading p i x ⟨y, hy⟩)
    · intro b y
      change g.toFun (((tensorDGFunctor N).pure M).toLinearMap (x : M.M)
          (MulOpposite.op b • y)) =
        MulOpposite.op b • g.toFun (((tensorDGFunctor N).pure M).toLinearMap (x : M.M) y)
      rw [((tensorDGFunctor N).pure M).map_right (x : M.M) y b, g.map_smul]⟩
  map_add' x y := Subtype.ext (LinearMap.ext fun z => by simp)
  map_smul' r x := Subtype.ext (LinearMap.ext fun z => by simp)

/-- `pureHom` is restriction to the pure tensors with a fixed first factor. -/
private theorem pureHom_apply (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) (p : ℤ)
    (x : M.M) (hx : x ∈ M.grading p) (y : N.rightModule.M) :
    (pureHom N M g p ⟨x, hx⟩).1 y = g.toFun (((tensorDGFunctor N).pure M).toLinearMap x y) :=
  rfl

/-- The degree-`p` component of the homomorphism `M ⟶ Hom^•_B(N, P)` attached to a homomorphism
out of `M ⊗_A N`. -/
private def homOfTensorComponent (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) (p : ℤ) :
    M.grading p →ₗ[R] (homPresentation N P).module.M :=
  ((homPresentation N P).module.grading p).subtype.comp
    (((homPresentation N P).homogeneousEquiv p).symm.toLinearMap.comp (pureHom N M g p))

/-- The underlying linear map of the homomorphism `M ⟶ Hom^•_B(N, P)` attached to a homomorphism
out of `M ⊗_A N`, assembled from its homogeneous components. -/
private def homOfTensorLinear (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) :
    M.M →ₗ[R] (homPresentation N P).module.M :=
  (DirectSum.toModule R ℤ _ (homOfTensorComponent N M g)).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- The value at a homogeneous element of the homomorphism attached to `g`. -/
private theorem homOfTensorLinear_apply (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) (p : ℤ)
    (x : M.M) (hx : x ∈ M.grading p) :
    homOfTensorLinear N M g x =
      (((homPresentation N P).homogeneousEquiv p).symm (pureHom N M g p ⟨x, hx⟩) :
        (homPresentation N P).module.M) :=
  toModule_decompose_apply M (homOfTensorComponent N M g) p x hx

/-- The value at a homogeneous element of degree `p`, packaged as an element of the degree-`p`
piece of the internal hom together with the homogeneous map it presents. -/
private theorem homOfTensor_exists_grading (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) (p : ℤ)
    (x : M.M) (hx : x ∈ M.grading p) :
    ∃ u : (homPresentation N P).module.grading p,
      (homPresentation N P).homogeneousEquiv p u = pureHom N M g p ⟨x, hx⟩ ∧
        homOfTensorLinear N M g x = (u : (homPresentation N P).module.M) := by
  refine ⟨((homPresentation N P).homogeneousEquiv p).symm (pureHom N M g p ⟨x, hx⟩),
    LinearEquiv.apply_symm_apply _ _, ?_⟩
  exact homOfTensorLinear_apply N M g p x hx

/-- A linear map between right differential graded `A`-modules that commutes with the action of
homogeneous elements of `A` on homogeneous elements commutes with the whole action. -/
private theorem op_smul_of_homogeneous {X Y : DifferentialGradedModule A} (L : X.M →ₗ[R] Y.M)
    (h : ∀ (p m : ℤ) (x : X.M), x ∈ X.grading p → ∀ a : A.A, a ∈ A.grading m →
      L (MulOpposite.op a • x) = MulOpposite.op a • L x)
    (a : A.A) (x : X.M) : L (MulOpposite.op a • x) = MulOpposite.op a • L x := by
  induction x using DirectSum.Decomposition.inductionOn X.grading with
  | zero => simp
  | @homogeneous p x =>
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | @homogeneous m a => exact h p m (x : X.M) x.property (a : A.A) a.property
    | add a b hb hc =>
      simpa only [MulOpposite.op_add, add_smul, map_add] using congrArg₂ (· + ·) hb hc
  | add x y hx hy => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy

/-- The homomorphism attached to `g` respects the right `A`-action on homogeneous elements:
this is the `balance` field of the universal pure tensor against the `map_smul` field of the
presentation of the internal hom. -/
private theorem homOfTensorLinear_op_smul_homogeneous (N : Bimodule A B)
    (M : DifferentialGradedModule A) {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) (p m : ℤ)
    (x : M.M) (hx : x ∈ M.grading p) (a : A.A) (ha : a ∈ A.grading m) :
    homOfTensorLinear N M g (MulOpposite.op a • x) =
      MulOpposite.op a • homOfTensorLinear N M g x := by
  obtain ⟨u, hu, hxu⟩ := homOfTensor_exists_grading N M g p x hx
  have hsm : MulOpposite.op a • x ∈ M.grading (p + m) := M.smul_mem p m x a hx ha
  have hwmem : MulOpposite.op a • (u : (homPresentation N P).module.M) ∈
      (homPresentation N P).module.grading (p + m) :=
    (homPresentation N P).module.smul_mem p m _ a u.property ha
  have key : pureHom N M g (p + m) ⟨MulOpposite.op a • x, hsm⟩ =
      (homPresentation N P).homogeneousEquiv (p + m)
        ⟨MulOpposite.op a • (u : (homPresentation N P).module.M), hwmem⟩ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | @homogeneous q y =>
      have hbal : ((tensorDGFunctor N).pure M).toLinearMap (MulOpposite.op a • x)
            (y : N.rightModule.M) =
          ((tensorDGFunctor N).pure M).toLinearMap x
            ((show N.rightModule.grading (q + m) from
              (N.leftAction.1.action m ⟨a, ha⟩).v q (q + m) (by omega) y) :
                N.rightModule.M) :=
        ((tensorDGFunctor N).pure M).balance p q m ⟨x, hx⟩ y ⟨a, ha⟩
      have hms : ((homPresentation N P).homogeneousEquiv (p + m)
            ⟨MulOpposite.op a • (u : (homPresentation N P).module.M), hwmem⟩).1
              (y : N.rightModule.M) =
          ((homPresentation N P).homogeneousEquiv p u).1
            ((show N.rightModule.grading (q + m) from
              (N.leftAction.1.action m ⟨a, ha⟩).v q (q + m) (by omega) y) :
                N.rightModule.M) :=
        (homPresentation N P).map_smul p m q u ⟨a, ha⟩ y
      rw [pureHom_apply N M g (p + m) _ hsm, hbal, hms, hu, pureHom_apply N M g p x hx]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [homOfTensorLinear_apply N M g (p + m) _ hsm, key, LinearEquiv.symm_apply_apply, hxu]

/-- The homomorphism attached to `g` respects the differentials on homogeneous elements: this is
the `map_d` field of the universal pure tensor against the `map_d` field of the presentation of
the internal hom. -/
private theorem homOfTensorLinear_d_homogeneous (N : Bimodule A B)
    (M : DifferentialGradedModule A) {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) (p : ℤ)
    (x : M.M) (hx : x ∈ M.grading p) :
    homOfTensorLinear N M g (M.d x) =
      (homPresentation N P).module.d (homOfTensorLinear N M g x) := by
  obtain ⟨u, hu, hxu⟩ := homOfTensor_exists_grading N M g p x hx
  have hdmem : M.d x ∈ M.grading (p + 1) := M.d_mem p x hx
  have key : pureHom N M g (p + 1) ⟨M.d x, hdmem⟩ =
      (homPresentation N P).homogeneousEquiv (p + 1)
        ((homPresentation N P).module.gradedDifferential p u) := by
    rw [(homPresentation N P).map_d p u, hu]
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    have hpd : ((tensorDGFunctor N).functor.obj M).d
          (((tensorDGFunctor N).pure M).toLinearMap x y) =
        ((tensorDGFunctor N).pure M).toLinearMap (M.d x) y +
          (p.negOnePow : ℤ) • ((tensorDGFunctor N).pure M).toLinearMap x
            (N.rightModule.d y) :=
      ((tensorDGFunctor N).pure M).map_d p ⟨x, hx⟩ y
    have hgd : g.toFun (((tensorDGFunctor N).functor.obj M).d
          (((tensorDGFunctor N).pure M).toLinearMap x y)) =
        P.d (g.toFun (((tensorDGFunctor N).pure M).toLinearMap x y)) :=
      LinearMap.congr_fun g.map_d _
    rw [hpd, map_add, map_zsmul] at hgd
    rw [pureHom_apply N M g (p + 1) _ hdmem, homogeneousMapDifferential_val]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [pureHom_apply N M g p x hx, pureHom_apply N M g p x hx, ← hgd,
      ← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow]
    abel
  rw [homOfTensorLinear_apply N M g (p + 1) _ hdmem, key, LinearEquiv.symm_apply_apply,
    gradedDifferential_apply, hxu]

/-- The homomorphism `M ⟶ Hom^•_B(N, P)` attached to a homomorphism `M ⊗_A N ⟶ P`: send `x` to
the map `y ↦ g (x ⊗ y)`. -/
private def homOfTensor (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) :
    M ⟶ (homPresentation N P).module where
  toFun := homOfTensorLinear N M g
  map_smul x a :=
    op_smul_of_homogeneous _ (homOfTensorLinear_op_smul_homogeneous N M g) a x
  map_grading n x hx := by
    have h : homOfTensorLinear N M g x =
        (((homPresentation N P).homogeneousEquiv n).symm (pureHom N M g n ⟨x, hx⟩) :
          (homPresentation N P).module.M) := homOfTensorLinear_apply N M g n x hx
    rw [h]
    exact (((homPresentation N P).homogeneousEquiv n).symm (pureHom N M g n ⟨x, hx⟩)).property
  map_d := by
    apply LinearMap.ext
    intro x
    change homOfTensorLinear N M g (M.d x) =
      (homPresentation N P).module.d (homOfTensorLinear N M g x)
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | @homogeneous p x =>
      exact homOfTensorLinear_d_homogeneous N M g p (x : M.M) x.property
    | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The two directions are mutually inverse -/

/-- The homomorphism `M ⊗_A N ⟶ P` attached to a homomorphism `M ⟶ Hom^•_B(N, P)`, by the
universal property of the relative tensor product. -/
private def tensorOfHom (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (φ : M ⟶ (homPresentation N P).module) :
    DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P :=
  ((tensorDGFunctor N).universal M P (balancedOfHom N M φ)).choose

/-- The homomorphism attached to `φ` by the universal property evaluates on pure tensors as
`x ⊗ y ↦ (φ x)(y)`. -/
private theorem tensorOfHom_pure (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (φ : M ⟶ (homPresentation N P).module)
    (x : M.M) (y : N.rightModule.M) :
    (tensorOfHom N M φ).toFun (((tensorDGFunctor N).pure M).toLinearMap x y) =
      homEval N P (φ.toFun x) y :=
  ((tensorDGFunctor N).universal M P (balancedOfHom N M φ)).choose_spec.1 x y

/-- A homogeneous map between presentations of the internal hom, transported along an equality
of degrees, has the same underlying values. -/
private theorem homogeneousMap_cast_val {X Y : DifferentialGradedModule B} {i j : ℤ}
    (hij : i = j) (f : HomogeneousMap B X Y i) (y : X.M) :
    (hij ▸ f : HomogeneousMap B X Y j).1 y = f.1 y := by
  cases hij; rfl

/-- Reading a homogeneous map back into a presentation of the internal hom does not depend on
which of two equal degrees is used. -/
private theorem homogeneousEquiv_symm_cast (N : Bimodule A B) (P : DifferentialGradedModule B)
    {i j : ℤ} (hij : i = j) (f : HomogeneousMap B N.rightModule P i) :
    (((homPresentation N P).homogeneousEquiv i).symm f : (homPresentation N P).module.M) =
      (((homPresentation N P).homogeneousEquiv j).symm (hij ▸ f) :
        (homPresentation N P).module.M) := by
  cases hij; rfl

/-- The internal hom functor acts by postcomposition, read through the chosen presentations. -/
private theorem homModuleFunctor_map_apply (N : Bimodule A B)
    {Y Y' : DifferentialGradedModule B} (h : Y ⟶ Y') (p : ℤ)
    (v : (homPresentation N Y).module.grading p) :
    ((homModuleFunctor A B N.rightModule N.leftAction).map h).toFun
        (v : (homPresentation N Y).module.M) =
      (((homPresentation N Y').homogeneousEquiv (0 + p)).symm
        (homogeneousMapComp B (rfl : (0 : ℤ) + p = 0 + p) (cocycleOfHom B h).1
          ((homPresentation N Y).homogeneousEquiv p v)) :
            (homPresentation N Y').module.M) :=
  homPostcompHomogeneousMap_apply A B N.rightModule N.leftAction
    (homPresentation N Y) (homPresentation N Y') 0 p (cocycleOfHom B h).1 v

/-- **The tensor–Hom bijection.** Homomorphisms `M ⊗_A N ⟶ P` of right differential graded
`B`-modules correspond to homomorphisms `M ⟶ Hom^•_B(N, P)` of right differential graded
`A`-modules. -/
private def tensorHomEquivAux (N : Bimodule A B) (M : DifferentialGradedModule A)
    (P : DifferentialGradedModule B) :
    DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P ≃
      (M ⟶ (homPresentation N P).module) where
  toFun := homOfTensor N M
  invFun := tensorOfHom N M
  left_inv g := by
    apply tensorObj_hom_ext N M
    intro x y
    rw [tensorOfHom_pure]
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | @homogeneous p x =>
      obtain ⟨u, hu, hxu⟩ := homOfTensor_exists_grading N M g p (x : M.M) x.property
      have h1 : (homOfTensor N M g).toFun (x : M.M) =
        (u : (homPresentation N P).module.M) := hxu
      rw [h1, homEval_apply' N P p u, hu, pureHom_apply N M g p (x : M.M) x.property]
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  right_inv φ := by
    apply DifferentialGradedModule.Hom.ext_of_grading
    intro p x
    have hvmem : φ.toFun (x : M.M) ∈ (homPresentation N P).module.grading p :=
      φ.map_grading p (x : M.M) x.property
    have key : pureHom N M (tensorOfHom N M φ) p ⟨(x : M.M), x.property⟩ =
        (homPresentation N P).homogeneousEquiv p ⟨φ.toFun (x : M.M), hvmem⟩ := by
      apply Subtype.ext
      apply LinearMap.ext
      intro y
      rw [pureHom_apply, tensorOfHom_pure, homEval_apply N P p _ hvmem]
    have h := homOfTensorLinear_apply N M (tensorOfHom N M φ) p (x : M.M) x.property
    change homOfTensorLinear N M (tensorOfHom N M φ) (x : M.M) = φ.toFun (x : M.M)
    rw [h, key, LinearEquiv.symm_apply_apply]

/-! ### Naturality -/

/-- Naturality of the tensor–Hom bijection in the source module, on pure tensors. -/
private theorem tensorOfHom_comp (N : Bimodule A B) {X' X : DifferentialGradedModule A}
    {Y : DifferentialGradedModule B} (f : X' ⟶ X)
    (φ : X ⟶ (homPresentation N Y).module) (x : X'.M) (y : N.rightModule.M) :
    (tensorOfHom N X' (DifferentialGradedModule.Hom.comp φ f)).toFun
        (((tensorDGFunctor N).pure X').toLinearMap x y) =
      (tensorOfHom N X φ).toFun (((tensorCompFunctor N).map f).toFun
        (((tensorDGFunctor N).pure X').toLinearMap x y)) := by
  rw [tensorOfHom_pure, tensorCompFunctor_map_pure, tensorOfHom_pure]
  rfl

/-- Naturality of the tensor–Hom bijection in the target module, on homogeneous elements. -/
private theorem homOfTensorLinear_comp (N : Bimodule A B) (X : DifferentialGradedModule A)
    {Y Y' : DifferentialGradedModule B}
    (f : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj X) Y) (g : Y ⟶ Y')
    (p : ℤ) (x : X.M) (hx : x ∈ X.grading p) :
    homOfTensorLinear N X (DifferentialGradedModule.Hom.comp g f) x =
      ((homModuleFunctor A B N.rightModule N.leftAction).map g).toFun
        (homOfTensorLinear N X f x) := by
  obtain ⟨u, hu, hxu⟩ := homOfTensor_exists_grading N X f p x hx
  have hcast : (0 : ℤ) + p = p := by omega
  have key : pureHom N X (DifferentialGradedModule.Hom.comp g f) p ⟨x, hx⟩ =
      hcast ▸ (homogeneousMapComp B (rfl : (0 : ℤ) + p = 0 + p) (cocycleOfHom B g).1
        ((homPresentation N Y).homogeneousEquiv p u)) := by
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    rw [homogeneousMap_cast_val hcast,
      pureHom_apply N X (DifferentialGradedModule.Hom.comp g f) p x hx]
    show g.toFun (f.toFun (((tensorDGFunctor N).pure X).toLinearMap x y)) =
      (cocycleOfHom B g).1.1 (((homPresentation N Y).homogeneousEquiv p u).1 y)
    rw [cocycleOfHom_val, hu, pureHom_apply N X f p x hx]
  rw [homOfTensorLinear_apply N X (DifferentialGradedModule.Hom.comp g f) p x hx, key,
    ← homogeneousEquiv_symm_cast N Y' hcast, hxu, homModuleFunctor_map_apply N g p u]

/-! ### The adjunction -/

/-- **Stacks 09LN, the differential graded case.** Tensoring with a differential graded
`(A, B)`-bimodule `N` is left adjoint to the internal hom out of `N`, as functors between the
categories of differential graded modules:
`Hom_{Mod^{dg}_{(B,d)}}(M ⊗_A N, P) = Hom_{Mod^{dg}_{(A,d)}}(M, Hom^•_B(N, P))`,
naturally in `M` and `P`.

This is the degree-zero part of the source's isomorphism of Hom complexes — the bijection of the
morphism groups of the two categories of differential graded modules — which is why the tag is
part-qualified. -/
@[stacks 09LN "the differential graded case in degree zero", no_expose]
def tensorCompFunctor_adj_homModuleFunctor (N : Bimodule A B) :
    tensorCompFunctor N ⊣ homModuleFunctor A B N.rightModule N.leftAction :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M P => tensorHomEquivAux N M P
      homEquiv_naturality_left_symm := fun {_ _ _} f φ =>
        tensorObj_hom_ext N _ _ _ (fun x y => tensorOfHom_comp N f φ x y)
      homEquiv_naturality_right := fun {X _ _} f g =>
        DifferentialGradedModule.Hom.ext_of_grading
          (fun p x => homOfTensorLinear_comp N X f g p (x : X.M) x.property) }

/-- **Stacks 09LN, the differential graded case**, as the bijection of morphism groups
`Hom_{Mod^{dg}_{(B,d)}}(M ⊗_A N, P) = Hom_{Mod^{dg}_{(A,d)}}(M, Hom^•_B(N, P))`. It is natural
in `M` and `P`, being the hom-set bijection of
`DifferentialGraded.Bimodule.tensorCompFunctor_adj_homModuleFunctor`. -/
@[stacks 09LN "the differential graded case in degree zero, as a bijection"]
def tensorHomEquiv (N : Bimodule A B) (M : DifferentialGradedModule A)
    (P : DifferentialGradedModule B) :
    ((tensorCompFunctor N).obj M ⟶ P) ≃
      (M ⟶ (homModuleFunctor A B N.rightModule N.leftAction).obj P) :=
  (tensorCompFunctor_adj_homModuleFunctor N).homEquiv M P

/-! ### The adjunction on the homotopy categories -/

/-- **Stacks 09LN for differential graded modules, on the homotopy categories.** Tensoring with a
differential graded `(A, B)`-bimodule `N` is left adjoint to the internal hom out of `N` as
functors `K(A, d) ⥤ K(B, d)` and `K(B, d) ⥤ K(A, d)`.

This is the adjunction on the categories of differential graded modules, descended along the
passage to homotopy classes: both functors are compatible with it, by Tag 09LM
(`DifferentialGraded.Bimodule.tensorCompFunctor_quotient`) and Tag 0FQQ
(`DifferentialGradedModule.homHomotopyDescent`), and an adjunction descends to a quotient
category by `CategoryTheory.Quotient.adjunctionOfSquares`. -/
@[stacks 09LN "the differential graded case in degree zero, on the homotopy categories",
  sga "5 IIIB 5.2" "partial"]
def tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor (N : Bimodule A B) :
    tensorHomotopyFunctor N ⊣ homHomotopyCategoryFunctor A B N.rightModule N.leftAction :=
  CategoryTheory.Quotient.adjunctionOfSquares (homotopyRel A) (homotopyRel B)
    (tensorCompFunctor_adj_homModuleFunctor N) (tensorCompFunctor_quotient N)
    (homHomotopyDescent N.rightModule N.leftAction).symm

/-! ### The lift of a homomorphism into the internal hom -/

/-- **The homomorphism out of `M ⊗_A N` attached to a homomorphism into the internal hom.** A
homomorphism `φ : M ⟶ Hom^•_B(N, P)` of right differential graded `A`-modules gives, by the
universal property of the relative tensor product, a homomorphism `M ⊗_A N ⟶ P` of right
differential graded `B`-modules: on a pure tensor `x ⊗ y` with `x ∈ M^p` homogeneous it is the
value at `y` of the degree-`p` homogeneous map that `φ x` presents.

This is the inverse direction of `DifferentialGraded.Bimodule.tensorHomEquiv`, stated so that the
value on pure tensors — the only property of it a consumer needs — is available; it determines
the homomorphism, by `DifferentialGraded.Bimodule.tensorObj_hom_ext`. -/
theorem exists_tensorHomLift (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (φ : M ⟶ (homPresentation N P).module) :
    ∃ g : tensorObj N M ⟶ P, ∀ (p : ℤ) (x : M.grading p) (y : N.rightModule.M),
      g.toFun ((tensorPure N M).toLinearMap (x : M.M) y) =
        ((homPresentation N P).homogeneousEquiv p
          ⟨φ.toFun (x : M.M), φ.map_grading p (x : M.M) x.property⟩).1 y :=
  ⟨tensorOfHom N M φ, fun p x y => by
    rw [tensorOfHom_pure, homEval_apply N P p _ (φ.map_grading p (x : M.M) x.property)]⟩

/-- **The inverse of the tensor–Hom bijection on a pure tensor.** For `φ : M ⟶ Hom^•_B(N, P)` and
`x` homogeneous of degree `p`, the homomorphism `M ⊗_A N ⟶ P` attached to `φ` sends `x ⊗ y` to
the value at `y` of the degree-`p` homogeneous map that `φ x` presents. -/
theorem tensorHomEquiv_symm_pure (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (φ : M ⟶ (homPresentation N P).module) (p : ℤ)
    (x : M.grading p) (y : N.rightModule.M) :
    ((tensorHomEquiv N M P).symm φ).toFun ((tensorPure N M).toLinearMap (x : M.M) y) =
      ((homPresentation N P).homogeneousEquiv p
        ⟨φ.toFun (x : M.M), φ.map_grading p (x : M.M) x.property⟩).1 y := by
  have h : (tensorHomEquiv N M P).symm φ = tensorOfHom N M φ := by
    rw [tensorHomEquiv, tensorCompFunctor_adj_homModuleFunctor, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  rw [h]
  exact (tensorOfHom_pure N M φ (x : M.M) y).trans
    (congrArg (fun f => f y) (homEval_apply N P p _ (φ.map_grading p (x : M.M) x.property)))


/-! ### The isomorphism of Hom complexes: Stacks 09LN in every degree

The bijection above is the degree-zero part of the source's isomorphism of Hom complexes. The
all-degrees statement is the content of this section, and the two inputs it needs beyond the
degree-zero one are both available: the pure tensors *generate* `M ⊗_A N`
(`DifferentialGraded.Bimodule.tensorObj_linearMap_ext`), which is what makes a homogeneous — not
necessarily closed — map out of `M ⊗_A N` determined by its values on them; and the evaluation
`Hom^•_B(N, P) ⊗_A N ⟶ P` is a *closed* homomorphism, so it is produced by the degree-zero
universal property. A degree-`n` homogeneous map `M ⟶ Hom^•_B(N, P)` is then tensored with `N` by
the functoriality of Tag 09LM on homogeneous morphisms and composed with the evaluation, which
inverts the restriction to the pure tensors. No graded universal property of the relative tensor
product is assumed. -/

/-- Two homogeneous elements of the internal hom of the same degree whose associated homogeneous
maps agree are equal. -/
private theorem homEval_ext (N : Bimodule A B) (P : DifferentialGradedModule B) (m : ℤ)
    {z w : (homPresentation N P).module.M}
    (hz : z ∈ (homPresentation N P).module.grading m)
    (hw : w ∈ (homPresentation N P).module.grading m)
    (h : ∀ y : N.rightModule.M, homEval N P z y = homEval N P w y) : z = w := by
  have key : (homPresentation N P).homogeneousEquiv m ⟨z, hz⟩ =
      (homPresentation N P).homogeneousEquiv m ⟨w, hw⟩ :=
    Subtype.ext (LinearMap.ext fun y => by
      rw [← homEval_apply N P m z hz, ← homEval_apply N P m w hw]
      exact h y)
  exact congrArg Subtype.val
    (((homPresentation N P).homogeneousEquiv m).injective key)

/-- Two linear maps into the internal hom that send a homogeneous element of `M` of degree `p` to
degree `p + n` and have the same evaluations on it are equal. -/
private theorem linearMap_ext_of_homEval (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    {L L' : M.M →ₗ[R] (homPresentation N P).module.M}
    (hL : ∀ p x, x ∈ M.grading p → L x ∈ (homPresentation N P).module.grading (p + n))
    (hL' : ∀ p x, x ∈ M.grading p → L' x ∈ (homPresentation N P).module.grading (p + n))
    (h : ∀ p x, x ∈ M.grading p → ∀ y, homEval N P (L x) y = homEval N P (L' x) y) :
    L = L' := by
  refine LinearMap.ext fun x => ?_
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x z hx hz => simp only [map_add, hx, hz]
  | @homogeneous p x =>
    exact homEval_ext N P (p + n) (hL p _ x.property) (hL' p _ x.property) (h p _ x.property)

/-- Evaluation of the differential of a homogeneous element of the internal hom. -/
private theorem homEval_d (N : Bimodule A B) (P : DifferentialGradedModule B) (m : ℤ)
    (z : (homPresentation N P).module.M)
    (hz : z ∈ (homPresentation N P).module.grading m) (y : N.rightModule.M) :
    homEval N P ((homPresentation N P).module.d z) y =
      P.d (homEval N P z y) -
        DifferentialGraded.gradedSign R m • homEval N P z (N.rightModule.d y) := by
  have hd : (homPresentation N P).module.d z ∈ (homPresentation N P).module.grading (m + 1) :=
    (homPresentation N P).module.d_mem m z hz
  rw [homEval_apply N P (m + 1) _ hd, homEval_apply N P m z hz]
  have hge : (⟨(homPresentation N P).module.d z, hd⟩ :
        (homPresentation N P).module.grading (m + 1)) =
      (homPresentation N P).module.gradedDifferential m ⟨z, hz⟩ := rfl
  rw [hge, (homPresentation N P).map_d m ⟨z, hz⟩]
  rfl

/-! #### Restriction to the pure tensors, in every degree -/

/-- Restricting a degree-`n` homogeneous map out of `M ⊗_A N` to the pure tensors with a fixed
homogeneous `x ∈ M^p` gives a degree-`p + n` homogeneous right-`B`-linear map `N → P`. -/
private def pureHomogeneous (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p : ℤ) :
    M.grading p →ₗ[R] HomogeneousMap B N.rightModule P (p + n) where
  toFun x := ⟨ψ.1.comp (((tensorDGFunctor N).pure M).toLinearMap (x : M.M)), by
    constructor
    · intro i y hy
      change ψ.1 (((tensorDGFunctor N).pure M).toLinearMap (x : M.M) y) ∈
        P.grading (i + (p + n))
      simpa only [show p + i + n = i + (p + n) by ring] using
        ψ.2.1 (p + i) _ (((tensorDGFunctor N).pure M).map_grading p i x ⟨y, hy⟩)
    · intro b y
      change ψ.1 (((tensorDGFunctor N).pure M).toLinearMap (x : M.M)
          (MulOpposite.op b • y)) =
        MulOpposite.op b • ψ.1 (((tensorDGFunctor N).pure M).toLinearMap (x : M.M) y)
      rw [((tensorDGFunctor N).pure M).map_right (x : M.M) y b, ψ.2.2]⟩
  map_add' x y := Subtype.ext (LinearMap.ext fun z => by simp)
  map_smul' r x := Subtype.ext (LinearMap.ext fun z => by simp)

private theorem pureHomogeneous_apply (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p : ℤ) (x : M.M) (hx : x ∈ M.grading p)
    (y : N.rightModule.M) :
    (pureHomogeneous N M n ψ p ⟨x, hx⟩).1 y =
      ψ.1 (((tensorDGFunctor N).pure M).toLinearMap x y) := rfl

/-- The degree-`p` component of the degree-`n` homogeneous map `M ⟶ Hom^•_B(N, P)` attached to a
degree-`n` homogeneous map out of `M ⊗_A N`. -/
private def curryComponent (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p : ℤ) :
    M.grading p →ₗ[R] (homPresentation N P).module.M :=
  ((homPresentation N P).module.grading (p + n)).subtype.comp
    (((homPresentation N P).homogeneousEquiv (p + n)).symm.toLinearMap.comp
      (pureHomogeneous N M n ψ p))

/-- The underlying linear map of the degree-`n` homogeneous map `M ⟶ Hom^•_B(N, P)` attached to a
degree-`n` homogeneous map out of `M ⊗_A N`. -/
private def curryLinear (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) :
    M.M →ₗ[R] (homPresentation N P).module.M :=
  (DirectSum.toModule R ℤ _ (curryComponent N M n ψ)).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

private theorem curryLinear_apply (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p : ℤ) (x : M.M) (hx : x ∈ M.grading p) :
    curryLinear N M n ψ x =
      (((homPresentation N P).homogeneousEquiv (p + n)).symm
        (pureHomogeneous N M n ψ p ⟨x, hx⟩) : (homPresentation N P).module.M) :=
  toModule_decompose_apply M (curryComponent N M n ψ) p x hx

private theorem curryLinear_mem (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p : ℤ) (x : M.M) (hx : x ∈ M.grading p) :
    curryLinear N M n ψ x ∈ (homPresentation N P).module.grading (p + n) := by
  rw [curryLinear_apply N M n ψ p x hx]
  exact (((homPresentation N P).homogeneousEquiv (p + n)).symm
    (pureHomogeneous N M n ψ p ⟨x, hx⟩)).property

/-- Evaluating the attached map at a homogeneous element returns the restriction of `ψ` to the
pure tensors with that element in front. -/
private theorem homEval_curryLinear (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p : ℤ) (x : M.M) (hx : x ∈ M.grading p)
    (y : N.rightModule.M) :
    homEval N P (curryLinear N M n ψ x) y =
      ψ.1 (((tensorDGFunctor N).pure M).toLinearMap x y) := by
  rw [homEval_apply N P (p + n) _ (curryLinear_mem N M n ψ p x hx)]
  have h : (⟨curryLinear N M n ψ x, curryLinear_mem N M n ψ p x hx⟩ :
        (homPresentation N P).module.grading (p + n)) =
      ((homPresentation N P).homogeneousEquiv (p + n)).symm
        (pureHomogeneous N M n ψ p ⟨x, hx⟩) :=
    Subtype.ext (curryLinear_apply N M n ψ p x hx)
  rw [h, LinearEquiv.apply_symm_apply]
  rfl

/-- The attached map respects the right `A`-action on homogeneous elements. -/
private theorem curryLinear_op_smul_homogeneous (N : Bimodule A B)
    (M : DifferentialGradedModule A) {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p m : ℤ) (x : M.M) (hx : x ∈ M.grading p)
    (a : A.A) (ha : a ∈ A.grading m) :
    curryLinear N M n ψ (MulOpposite.op a • x) =
      MulOpposite.op a • curryLinear N M n ψ x := by
  have hsm : MulOpposite.op a • x ∈ M.grading (p + m) := M.smul_mem p m x a hx ha
  have hwmem : MulOpposite.op a • curryLinear N M n ψ x ∈
      (homPresentation N P).module.grading (p + n + m) :=
    (homPresentation N P).module.smul_mem (p + n) m _ a (curryLinear_mem N M n ψ p x hx) ha
  have hlmem : curryLinear N M n ψ (MulOpposite.op a • x) ∈
      (homPresentation N P).module.grading (p + n + m) := by
    have h := curryLinear_mem N M n ψ (p + m) _ hsm
    rwa [show p + m + n = p + n + m by ring] at h
  refine homEval_ext N P (p + n + m) hlmem hwmem fun y => ?_
  induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | @homogeneous q y =>
    have hbal : ((tensorDGFunctor N).pure M).toLinearMap (MulOpposite.op a • x)
          (y : N.rightModule.M) =
        ((tensorDGFunctor N).pure M).toLinearMap x
          ((show N.rightModule.grading (q + m) from
            (N.leftAction.1.action m ⟨a, ha⟩).v q (q + m) (by omega) y) :
              N.rightModule.M) :=
      ((tensorDGFunctor N).pure M).balance p q m ⟨x, hx⟩ y ⟨a, ha⟩
    have hms : homEval N P (MulOpposite.op a • curryLinear N M n ψ x)
          (y : N.rightModule.M) =
        homEval N P (curryLinear N M n ψ x)
          ((show N.rightModule.grading (q + m) from
            (N.leftAction.1.action m ⟨a, ha⟩).v q (q + m) (by omega) y) :
              N.rightModule.M) := by
      rw [homEval_apply N P (p + n + m) _ hwmem,
        homEval_apply N P (p + n) _ (curryLinear_mem N M n ψ p x hx)]
      exact (homPresentation N P).map_smul (p + n) m q
        ⟨curryLinear N M n ψ x, curryLinear_mem N M n ψ p x hx⟩ ⟨a, ha⟩ y
    rw [homEval_curryLinear N M n ψ (p + m) _ hsm, hbal, hms,
      homEval_curryLinear N M n ψ p x hx]

/-- **The restriction of a degree-`n` homogeneous map out of `M ⊗_A N` to the pure tensors**, as a
degree-`n` homogeneous right-`A`-linear map `M ⟶ Hom^•_B(N, P)`. -/
private def tensorHomCurry (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) :
    HomogeneousMap A M (homPresentation N P).module n :=
  ⟨curryLinear N M n ψ, by
    constructor
    · intro i x hx
      exact curryLinear_mem N M n ψ i x hx
    · intro a x
      exact op_smul_of_homogeneous _ (curryLinear_op_smul_homogeneous N M n ψ) a x⟩

private theorem homEval_tensorHomCurry (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (p : ℤ) (x : M.M) (hx : x ∈ M.grading p)
    (y : N.rightModule.M) :
    homEval N P ((tensorHomCurry N M n ψ).1 x) y =
      ψ.1 (((tensorDGFunctor N).pure M).toLinearMap x y) :=
  homEval_curryLinear N M n ψ p x hx y

private theorem curryLinear_add (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ φ : HomogeneousMap B (tensorObj N M) P n) :
    curryLinear N M n (ψ + φ) = curryLinear N M n ψ + curryLinear N M n φ :=
  linearMap_ext_of_homEval N M n (curryLinear_mem N M n (ψ + φ))
    (fun p x hx => Submodule.add_mem _ (curryLinear_mem N M n ψ p x hx)
      (curryLinear_mem N M n φ p x hx))
    fun p x hx y => by
      rw [homEval_curryLinear N M n (ψ + φ) p x hx, LinearMap.add_apply, map_add,
        LinearMap.add_apply, homEval_curryLinear N M n ψ p x hx,
        homEval_curryLinear N M n φ p x hx]
      rfl

private theorem curryLinear_smul (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ) (r : R)
    (ψ : HomogeneousMap B (tensorObj N M) P n) :
    curryLinear N M n (r • ψ) = r • curryLinear N M n ψ :=
  linearMap_ext_of_homEval N M n (curryLinear_mem N M n (r • ψ))
    (fun p x hx => Submodule.smul_mem _ r (curryLinear_mem N M n ψ p x hx))
    fun p x hx y => by
      rw [homEval_curryLinear N M n (r • ψ) p x hx, LinearMap.smul_apply, map_smul,
        LinearMap.smul_apply, homEval_curryLinear N M n ψ p x hx]
      rfl

/-! #### The evaluation, and the inverse direction -/

/-- The evaluation `Hom^•_B(N, P) ⊗_A N ⟶ P`, a closed degree-zero homomorphism: it is the lift
of the identity of the internal hom. -/
private def evalHom (N : Bimodule A B) (P : DifferentialGradedModule B) :
    tensorObj N (homPresentation N P).module ⟶ P :=
  tensorOfHom N (homPresentation N P).module (𝟙 (homPresentation N P).module)

private theorem evalHom_pure (N : Bimodule A B) (P : DifferentialGradedModule B)
    (z : (homPresentation N P).module.M) (y : N.rightModule.M) :
    (evalHom N P).toFun
        (((tensorDGFunctor N).pure (homPresentation N P).module).toLinearMap z y) =
      homEval N P z y :=
  tensorOfHom_pure N (homPresentation N P).module (𝟙 (homPresentation N P).module) z y

/-- The evaluation, as a closed degree-zero homogeneous map. -/
private def evalHomogeneous (N : Bimodule A B) (P : DifferentialGradedModule B) :
    HomogeneousMap B (tensorObj N (homPresentation N P).module) P 0 :=
  (cocycleOfHom B (evalHom N P)).1

/-- **A degree-`n` homogeneous map `M ⟶ Hom^•_B(N, P)`, tensored with `N` and evaluated**: the
inverse of the restriction to the pure tensors. -/
private def tensorHomUncurry (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (f : HomogeneousMap A M (homPresentation N P).module n) :
    HomogeneousMap B (tensorObj N M) P n :=
  homogeneousMapComp B (zero_add n) (evalHomogeneous N P) ((tensorDGFunctor N).functor.map f)

private theorem tensorHomUncurry_pure (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (f : HomogeneousMap A M (homPresentation N P).module n) (x : M.M)
    (y : N.rightModule.M) :
    (tensorHomUncurry N M n f).1 (((tensorDGFunctor N).pure M).toLinearMap x y) =
      homEval N P (f.1 x) y := by
  show (evalHomogeneous N P).1 (((tensorDGFunctor N).functor.map f).1
    (((tensorDGFunctor N).pure M).toLinearMap x y)) = _
  rw [(tensorDGFunctor N).map_pure f x y]
  exact evalHom_pure N P (f.1 x) y

/-! #### The two directions are mutually inverse -/

private theorem curryLinear_uncurry (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (f : HomogeneousMap A M (homPresentation N P).module n) :
    curryLinear N M n (tensorHomUncurry N M n f) = f.1 := by
  refine linearMap_ext_of_homEval N M n (curryLinear_mem N M n _) f.2.1 fun p x hx y => ?_
  rw [homEval_curryLinear N M n (tensorHomUncurry N M n f) p x hx y,
    tensorHomUncurry_pure N M n f x y]

private theorem tensorHomCurry_uncurry (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (f : HomogeneousMap A M (homPresentation N P).module n) :
    tensorHomCurry N M n (tensorHomUncurry N M n f) = f :=
  Subtype.ext (curryLinear_uncurry N M n f)

private theorem tensorHomUncurry_curry (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) :
    tensorHomUncurry N M n (tensorHomCurry N M n ψ) = ψ := by
  refine Subtype.ext (tensorObj_linearMap_ext N M _ _ fun x y => ?_)
  rw [tensorHomUncurry_pure N M n (tensorHomCurry N M n ψ) x y]
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | @homogeneous p x => exact homEval_tensorHomCurry N M n ψ p (x : M.M) x.property y

/-! #### Compatibility with the differentials of the Hom complexes -/

private theorem curryLinear_differential (N : Bimodule A B)
    (M : DifferentialGradedModule A) {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) :
    curryLinear N M (n + 1) (homogeneousMapDifferential B ψ) =
      (homPresentation N P).module.d.comp (curryLinear N M n ψ) -
        DifferentialGraded.gradedSign R n • ((curryLinear N M n ψ).comp M.d) := by
  have hR1 : ∀ p x, x ∈ M.grading p → (homPresentation N P).module.d (curryLinear N M n ψ x) ∈
      (homPresentation N P).module.grading (p + n + 1) := fun p x hx =>
    (homPresentation N P).module.d_mem (p + n) _ (curryLinear_mem N M n ψ p x hx)
  have hR2 : ∀ p x, x ∈ M.grading p → curryLinear N M n ψ (M.d x) ∈
      (homPresentation N P).module.grading (p + n + 1) := fun p x hx => by
    rw [← add_right_comm]
    exact curryLinear_mem N M n ψ (p + 1) _ (M.d_mem p x hx)
  refine linearMap_ext_of_homEval N M (n + 1) (curryLinear_mem N M _ _)
    (fun p x hx => ?_) fun p x hx y => ?_
  · rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      ← add_assoc]
    exact Submodule.sub_mem _ (hR1 p x hx) (Submodule.smul_mem _ _ (hR2 p x hx))
  · have hpd := ((tensorDGFunctor N).pure M).map_d p ⟨x, hx⟩ y
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      homEval_d N P (p + n) _ (curryLinear_mem N M n ψ p x hx) y,
      homEval_curryLinear N M n ψ p x hx y, homEval_curryLinear N M n ψ p x hx (N.rightModule.d y),
      homEval_curryLinear N M n ψ (p + 1) _ (M.d_mem p x hx) y,
      homEval_curryLinear N M (n + 1) _ p x hx y]
    change P.d _ - DifferentialGraded.gradedSign R n • ψ.1 ((tensorObj N M).d _) = _
    rw [hpd, map_add, map_zsmul, ← Int.cast_smul_eq_zsmul R,
      DifferentialGraded.intCast_negOnePow, smul_add, smul_smul,
      DifferentialGraded.gradedSign_add p n,
      mul_comm (DifferentialGraded.gradedSign R p) (DifferentialGraded.gradedSign R n)]
    abel

private theorem tensorHomCurry_differential (N : Bimodule A B)
    (M : DifferentialGradedModule A) {P : DifferentialGradedModule B} (n : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) :
    tensorHomCurry N M (n + 1) (homogeneousMapDifferential B ψ) =
      homogeneousMapDifferential A (tensorHomCurry N M n ψ) :=
  Subtype.ext (curryLinear_differential N M n ψ)

/-- The characterizing property of the restriction to the pure tensors, read through the
presentation of the internal hom. -/
private theorem homogeneousEquiv_tensorHomCurry (N : Bimodule A B)
    (M : DifferentialGradedModule A) {P : DifferentialGradedModule B} (n p : ℤ)
    (ψ : HomogeneousMap B (tensorObj N M) P n) (x : M.M) (hx : x ∈ M.grading p)
    (y : N.rightModule.M) :
    ((homPresentation N P).homogeneousEquiv (p + n)
        ⟨(tensorHomCurry N M n ψ).1 x, (tensorHomCurry N M n ψ).2.1 p x hx⟩).1 y =
      ψ.1 (((tensorDGFunctor N).pure M).toLinearMap x y) := by
  have h := homEval_apply N P (p + n) ((tensorHomCurry N M n ψ).1 x)
    ((tensorHomCurry N M n ψ).2.1 p x hx)
  exact (LinearMap.congr_fun h y).symm.trans (homEval_tensorHomCurry N M n ψ p x hx y)

/-! #### Stacks 09LN in every degree -/

/-- **Stacks 09LN, in every degree.** For a right differential graded `A`-module `M`, a
differential graded `(A, B)`-bimodule `N` and a right differential graded `B`-module `P` the two
Hom complexes

`Hom^•_{Mod^{dg}_{(B, d)}}(M ⊗_A N, P)`  and  `Hom^•_{Mod^{dg}_{(A, d)}}(M, Hom^•_B(N, P))`

are isomorphic as complexes of `R`-modules: in each degree `n` the homogeneous right-`B`-linear
maps `M ⊗_A N → P` of degree `n` correspond `R`-linearly to the homogeneous right-`A`-linear maps
`M → Hom^•_B(N, P)` of degree `n`, by restriction to the pure tensors, and the correspondence
commutes with the differentials of the two Hom complexes.

The correspondence is pinned by its value on pure tensors, which is what the first displayed
property says: the homogeneous map that the image of `ψ` at a homogeneous `x` presents sends `y`
to `ψ (x ⊗ y)`. That property determines it, since the pure tensors generate `M ⊗_A N`.

The degree-zero part is `DifferentialGraded.Bimodule.tensorHomEquiv`, which is the bijection of
morphism groups of the two categories of differential graded modules; the statement here is the
isomorphism of Hom complexes that the source asserts, of which that bijection is the part given
by the closed elements of degree zero. -/
@[stacks 09LN "the differential graded case in every degree, as an isomorphism of Hom complexes"]
theorem exists_tensorHomComplexIso (N : Bimodule A B) (M : DifferentialGradedModule A)
    (P : DifferentialGradedModule B) :
    ∃ e : ∀ n : ℤ, HomogeneousMap B (tensorObj N M) P n ≃ₗ[R]
        HomogeneousMap A M (homPresentation N P).module n,
      (∀ (n p : ℤ) (ψ : HomogeneousMap B (tensorObj N M) P n) (x : M.M)
          (hx : x ∈ M.grading p) (y : N.rightModule.M),
        ((homPresentation N P).homogeneousEquiv (p + n)
            ⟨(e n ψ).1 x, (e n ψ).2.1 p x hx⟩).1 y =
          ψ.1 (((tensorDGFunctor N).pure M).toLinearMap x y)) ∧
        ∀ (n : ℤ) (ψ : HomogeneousMap B (tensorObj N M) P n),
          e (n + 1) (homogeneousMapDifferential B ψ) =
            homogeneousMapDifferential A (e n ψ) := by
  refine ⟨fun n =>
    { toFun := tensorHomCurry N M n
      map_add' := fun ψ φ => Subtype.ext (curryLinear_add N M n ψ φ)
      map_smul' := fun r ψ => Subtype.ext (curryLinear_smul N M n r ψ)
      invFun := tensorHomUncurry N M n
      left_inv := tensorHomUncurry_curry N M n
      right_inv := tensorHomCurry_uncurry N M n },
    fun n p ψ x hx y => homogeneousEquiv_tensorHomCurry N M n p ψ x hx y,
    fun n ψ => tensorHomCurry_differential N M n ψ⟩

end DifferentialGraded.Bimodule

end

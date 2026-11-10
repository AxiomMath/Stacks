module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionFunctor

/-!
# The comparison `N ⊗_B S ⟶ Hom_B(T, N)`

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, let `T` be
a differential graded `(A, B)`-bimodule, and let `S = Hom^•_B(T, B)` carry the differential graded
`(B, A)`-bimodule structure of `DifferentialGraded.Bimodule.homDualBimodule` (the first assertion
of [Stacks, Tag 0BZ0]). For every right differential graded `B`-module `N` there is a
homomorphism of right differential graded `A`-modules

`c_N : N ⊗_B S ⟶ Hom^•_B(T, N)`,  `y ⊗ f ↦ (t ↦ y · f t)`,

natural in `N`. This is the map the proof of Tag 0BZ0 calls `c_N`: it is the composition pairing
of Tag 09LC, `N = Hom_B(B, N)` with `Hom_B(T, B)` into `Hom_B(T, N)`.

The construction is the honest one. The pairing is assembled from its homogeneous pieces: on
`y ∈ N^q` and `f ∈ S^p` it is the composite of `b ↦ y · b` with the homogeneous map `T → B` that
`f` is, which is `DifferentialGraded.Bimodule.evalPair`; this is bilinear, adds degrees, is
balanced over `B`, is right `A`-linear, and satisfies the graded Leibniz rule
(`DifferentialGraded.Bimodule.evalBalanced`), so it factors through the relative tensor product by
the universal property of Tag 09LM.

## Main definitions

* `DifferentialGraded.Bimodule.evalPair`: the homogeneous map `t ↦ y · f t`.
* `DifferentialGraded.Bimodule.evalTotal`: the pairing `N × S → Hom^•_B(T, N)`, `R`-bilinear.
* `DifferentialGraded.Bimodule.evalBalanced`: it as a balanced bilinear chain map.
* `DifferentialGraded.Bimodule.evalHom`: `c_N : N ⊗_B S ⟶ Hom^•_B(T, N)`.
* `DifferentialGraded.Bimodule.evalModuleNatTrans`: `c` as a natural transformation of the
  functors of Tag 09LM and Tag 0FQQ on differential graded modules.
* `DifferentialGraded.Bimodule.evalHomotopyNatTrans`: the same on the homotopy categories.
* `DifferentialGraded.Bimodule.evalToDerivedCategoryNatTrans`: the same with the target
  localized, i.e. a transformation of the two functors that Tag 09LS and Tag 09LI derive.

## Main results

* `DifferentialGraded.Bimodule.evalTotal_apply`: the pairing on homogeneous elements.
* `DifferentialGraded.Bimodule.evalHom_pure`: `c_N` on a pure tensor.
* `DifferentialGraded.Bimodule.homModuleFunctor_map_evalTotal`: the internal hom functor acts on
  the pairing by postcomposition, which is the naturality of `c`.

## Implementation notes

*What is not proved here, and where it is.* The second assertion of Tag 0BZ0 is that the induced
map `N ⊗_B^𝐋 S ⟶ R\Hom(T, N)` is an isomorphism of functors on `D(B, d)`. Neither that map nor
the isomorphism is constructed below, and no `@[stacks 0BZ0]` attribute is attached to anything
in this file; what this file supplies is the composition pairing out of which the map is
assembled. The tag's two assertions are carried by
`DifferentialGraded.Bimodule.homDualBimodule` and by
`DifferentialGraded.Bimodule.derivedTensorHomDualFunctorIso` in
`StacksFrontier/Algebra/DifferentialGraded/Module/InternalHomTensorIso.lean`.

The map cannot be read off a universal property. `- ⊗_B^𝐋 S` is the *right* Kan
extension of `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory` along the localization
(Tag 09LS), and `R\Hom(T, -)` is the *left* Kan extension of
`DifferentialGradedModule.homToDerivedCategory` along the same localization (Tag 09LI). Both
universal properties therefore produce transformations `R\Hom(T, -) ⟶ - ⊗_B^𝐋 S`, and neither
produces one in the direction Tag 0BZ0 asserts. The source constructs the map by hand from
resolutions — choose `P → N → I` with `P` of property (P) and `I` of property (I), and take
`P ⊗_B S → Hom_B(T, P) → Hom_B(T, I)` — so formalizing it needs the pointwise descriptions of
the two derived functors at those resolutions, together with an argument that the resulting map is
natural. `DifferentialGraded.Bimodule.evalToDerivedCategoryNatTrans` below is the input of that
construction, which is carried out as `DifferentialGraded.Bimodule.derivedEvalNatTrans`.

The proof that the map is an isomorphism has all of its inputs in the library:
the dévissage of `D(B, d)` from the shifts of `B` is
`DifferentialGradedModule.property_of_coproducts_of_two_out_of_three_of_shifts` (Tag 0FQE),
commutation of `R\Hom(T, -)` with direct sums under the compactness hypothesis (1) of Tag 0BZ0 is
`DifferentialGraded.Bimodule.preservesColimitsOfShape_discrete_derivedHomFunctor`, and the unit
`B ⊗_B^𝐋 S ≅ S` is `DifferentialGraded.Bimodule.derivedTensorRegularIso`; hypothesis (2) of
Tag 0BZ0 is the invertibility of the comparison of
`DifferentialGradedModule.DerivedHomData.comparison` at the regular module.

*Why the pairing is assembled by hand.* The internal hom has no canonical underlying module: its
graded pieces are only identified with homogeneous maps through a chosen
`DifferentialGradedModule.HomModuleData`. A map *into* it therefore has to be given on graded
pieces and assembled with `DirectSum.toModule`, which is what `evalRowFun` and `evalTotal` do; the
four conditions making it a `DifferentialGraded.Bimodule.BalancedBilinearMap` are then checked on
homogeneous elements and extended by the direct-sum decomposition.

## References

* [Stacks Project, Tag 0BZ0](https://stacks.math.columbia.edu/tag/0BZ0); the composition pairing
  is [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the tensor functor
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the internal hom functor
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ), and the two derived functors
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) and
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI).
-/
@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex DifferentialGradedModule

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- For a homogeneous `y ∈ N^q` and a homogeneous `f ∈ S^p`, where `S = Hom^•_B(T, B)`, the
degree-`q + p` homogeneous right-`B`-linear map `T → N` given by `t ↦ y · f t`. -/
def evalPair (T : Bimodule A B) {N : DifferentialGradedModule.{u, u, u} B} {q p : ℤ}
    (y : N.grading q) (f : (homDualModule T).grading p) :
    HomogeneousMap B T.rightModule N (q + p) :=
  homogeneousMapComp B (rfl : q + p = q + p) (regularHomogeneousMapₗ N q y)
    ((homDualPresentation T).homogeneousEquiv p f)

/-- `DifferentialGraded.Bimodule.evalPair` sends `t` to `y · f t`. -/
theorem evalPair_apply (T : Bimodule A B) {N : DifferentialGradedModule.{u, u, u} B} {q p : ℤ}
    (y : N.grading q) (f : (homDualModule T).grading p) (t : T.rightModule.M) :
    (evalPair T y f).1 t =
      MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) • (y : N.M) := rfl

/-- `DifferentialGraded.Bimodule.evalPair` is additive in the element of `S`. -/
theorem evalPair_add_right (T : Bimodule A B) {N : DifferentialGradedModule.{u, u, u} B}
    {q p : ℤ} (y : N.grading q) (f g : (homDualModule T).grading p) :
    evalPair T y (f + g) = evalPair T y f + evalPair T y g := by
  have ht : ∀ t : T.rightModule.M,
      ((((homDualPresentation T).homogeneousEquiv p) (f + g)).1 t : B.A) =
        (((homDualPresentation T).homogeneousEquiv p) f).1 t +
          (((homDualPresentation T).homogeneousEquiv p) g).1 t := fun t =>
    congrArg (fun z : HomogeneousMap B T.rightModule (regularModule B) p => z.1 t)
      (((homDualPresentation T).homogeneousEquiv p).map_add f g)
  refine Subtype.ext (LinearMap.ext fun t => ?_)
  change MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) (f + g)).1 t) •
      (y : N.M) =
    MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) • (y : N.M) +
      MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) g).1 t) • (y : N.M)
  rw [ht t, MulOpposite.op_add, add_smul]

/-- `DifferentialGraded.Bimodule.evalPair` is `R`-linear in the element of `S`. -/
theorem evalPair_smul_right (T : Bimodule A B) {N : DifferentialGradedModule.{u, u, u} B}
    {q p : ℤ} (r : R) (y : N.grading q) (f : (homDualModule T).grading p) :
    evalPair T y (r • f) = r • evalPair T y f := by
  have ht : ∀ t : T.rightModule.M,
      ((((homDualPresentation T).homogeneousEquiv p) (r • f)).1 t : B.A) =
        r • (((homDualPresentation T).homogeneousEquiv p) f).1 t := fun t =>
    congrArg (fun z : HomogeneousMap B T.rightModule (regularModule B) p => z.1 t)
      (((homDualPresentation T).homogeneousEquiv p).map_smul r f)
  refine Subtype.ext (LinearMap.ext fun t => ?_)
  change MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) (r • f)).1 t) •
      (y : N.M) =
    r • MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) • (y : N.M)
  rw [ht t, MulOpposite.op_smul, smul_assoc]

/-- `DifferentialGraded.Bimodule.evalPair` is additive in the element of `N`. -/
theorem evalPair_add_left (T : Bimodule A B) {N : DifferentialGradedModule.{u, u, u} B}
    {q p : ℤ} (y z : N.grading q) (f : (homDualModule T).grading p) :
    evalPair T (y + z) f = evalPair T y f + evalPair T z f := by
  refine Subtype.ext (LinearMap.ext fun t => ?_)
  change MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) •
      ((y : N.M) + (z : N.M)) =
    MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) • (y : N.M) +
      MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) • (z : N.M)
  rw [smul_add]

/-- `DifferentialGraded.Bimodule.evalPair` is `R`-linear in the element of `N`. -/
theorem evalPair_smul_left (T : Bimodule A B) {N : DifferentialGradedModule.{u, u, u} B}
    {q p : ℤ} (r : R) (y : N.grading q) (f : (homDualModule T).grading p) :
    evalPair T (r • y) f = r • evalPair T y f := by
  refine Subtype.ext (LinearMap.ext fun t => ?_)
  change MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) •
      (r • (y : N.M)) =
    r • MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) • (y : N.M)
  exact smul_comm _ r _

/-- The comparison on a pair of homogeneous pieces, as an `R`-bilinear map. -/
def evalPieceₗ (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) (q p : ℤ) :
    N.grading q →ₗ[R] (homDualModule T).grading p →ₗ[R] (homPresentation T N).module.M where
  toFun y :=
    { toFun := fun f =>
        ((((homPresentation T N).homogeneousEquiv (q + p)).symm (evalPair T y f)) :
          (homPresentation T N).module.M)
      map_add' := fun f g => by
        rw [evalPair_add_right, map_add]
        rfl
      map_smul' := fun r f => by
        rw [RingHom.id_apply, evalPair_smul_right, map_smul]
        rfl }
  map_add' y z := by
    refine LinearMap.ext fun f => ?_
    change ((((homPresentation T N).homogeneousEquiv (q + p)).symm (evalPair T (y + z) f)) :
      (homPresentation T N).module.M) = _
    rw [evalPair_add_left, map_add]
    rfl
  map_smul' r y := by
    refine LinearMap.ext fun f => ?_
    change ((((homPresentation T N).homogeneousEquiv (q + p)).symm (evalPair T (r • y) f)) :
      (homPresentation T N).module.M) = _
    rw [evalPair_smul_left, map_smul]
    rfl

/-- The comparison out of the whole of `S = Hom^•_B(T, B)`, for a homogeneous element of `N`. -/
def evalRowFun (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) {q : ℤ}
    (y : N.grading q) : (homDualModule T).M →ₗ[R] (homPresentation T N).module.M :=
  (DirectSum.toModule R ℤ (homPresentation T N).module.M
    fun p => evalPieceₗ T N q p y).comp
    (DirectSum.decomposeLinearEquiv (homDualModule T).grading).toLinearMap

/-- `DifferentialGraded.Bimodule.evalRowFun` on a homogeneous element of `S` is the comparison
on that pair of homogeneous pieces. -/
theorem evalRowFun_apply (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B)
    {q p : ℤ} (y : N.grading q) (f : (homDualModule T).grading p) :
    evalRowFun T N y (f : (homDualModule T).M) = evalPieceₗ T N q p y f := by
  change (DirectSum.toModule R ℤ (homPresentation T N).module.M
      fun i => evalPieceₗ T N q i y)
      ((DirectSum.decomposeLinearEquiv (homDualModule T).grading) (f : (homDualModule T).M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]

/-- `DifferentialGraded.Bimodule.evalRowFun`, as an `R`-linear map in the element of `N`. -/
def evalRowₗ (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) (q : ℤ) :
    N.grading q →ₗ[R] ((homDualModule T).M →ₗ[R] (homPresentation T N).module.M) where
  toFun y := evalRowFun T N y
  map_add' y z := by
    refine LinearMap.ext fun w => ?_
    induction w using DirectSum.Decomposition.inductionOn (homDualModule T).grading with
    | zero => simp
    | @homogeneous p f =>
      rw [LinearMap.add_apply, evalRowFun_apply, evalRowFun_apply, evalRowFun_apply,
        (evalPieceₗ T N q p).map_add y z, LinearMap.add_apply]
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add, h₁, h₂]
      simp only [LinearMap.add_apply, map_add]
  map_smul' r y := by
    refine LinearMap.ext fun w => ?_
    induction w using DirectSum.Decomposition.inductionOn (homDualModule T).grading with
    | zero => simp
    | @homogeneous p f =>
      rw [LinearMap.smul_apply, RingHom.id_apply, evalRowFun_apply, evalRowFun_apply,
        (evalPieceₗ T N q p).map_smul r y, LinearMap.smul_apply]
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add, h₁, h₂]
      simp only [LinearMap.smul_apply, RingHom.id_apply, map_add]

/-- `DifferentialGraded.Bimodule.evalRowₗ` on a homogeneous element of `S` is the element of
`Hom^•_B(T, N)` corresponding to `DifferentialGraded.Bimodule.evalPair`. -/
theorem evalRowₗ_apply (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) (q p : ℤ)
    (y : N.grading q) (f : (homDualModule T).grading p) :
    evalRowₗ T N q y (f : (homDualModule T).M) =
      ((((homPresentation T N).homogeneousEquiv (q + p)).symm (evalPair T y f)) :
        (homPresentation T N).module.M) :=
  evalRowFun_apply T N y f

/-- The comparison `N ⊗_B S → Hom^•_B(T, N)`, as an `R`-bilinear map `N × S → Hom^•_B(T, N)`:
on homogeneous elements it is `(y, f) ↦ (t ↦ y · f t)`. -/
def evalTotal (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) :
    N.M →ₗ[R] (homDualModule T).M →ₗ[R] (homPresentation T N).module.M :=
  (DirectSum.toModule R ℤ ((homDualModule T).M →ₗ[R] (homPresentation T N).module.M)
    fun q => evalRowₗ T N q).comp
    (DirectSum.decomposeLinearEquiv N.grading).toLinearMap

/-- The pairing on homogeneous `y ∈ N^q` and `f ∈ S^p` is the element of `Hom^•_B(T, N)` of
degree `q + p` corresponding to `t ↦ y · f t`. -/
theorem evalTotal_apply (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) (q p : ℤ)
    (y : N.grading q) (f : (homDualModule T).grading p) :
    evalTotal T N (y : N.M) (f : (homDualModule T).M) =
      ((((homPresentation T N).homogeneousEquiv (q + p)).symm (evalPair T y f)) :
        (homPresentation T N).module.M) := by
  have h : evalTotal T N (y : N.M) = evalRowₗ T N q y := by
    change (DirectSum.toModule R ℤ _ fun i => evalRowₗ T N i)
      ((DirectSum.decomposeLinearEquiv N.grading) (y : N.M)) = _
    rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  rw [h, evalRowₗ_apply]


/-! ### Extensionality for the internal hom module -/

/-- Two homogeneous elements of `Hom^•_B(T, N)` of equal degrees whose associated homogeneous
maps take the same values on homogeneous elements of `T` have the same underlying element. -/
theorem homModule_val_ext (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B)
    {i j : ℤ} (hij : i = j) (u : (homPresentation T N).module.grading i)
    (v : (homPresentation T N).module.grading j)
    (h : ∀ (k : ℤ) (t : T.rightModule.grading k),
      ((((homPresentation T N).homogeneousEquiv i) u).1 (t : T.rightModule.M) : N.M) =
        ((((homPresentation T N).homogeneousEquiv j) v).1 (t : T.rightModule.M) : N.M)) :
    (u : (homPresentation T N).module.M) = (v : (homPresentation T N).module.M) := by
  subst hij
  rw [((homPresentation T N).homogeneousEquiv i).injective
    (homogeneousMap_ext fun k t => h k t)]

/-! ### The comparison is a balanced bilinear map -/

/-- The value of the comparison on homogeneous elements, as an element of a graded piece. -/
def evalGraded (T : Bimodule A B) {N : DifferentialGradedModule.{u, u, u} B} {q p : ℤ}
    (y : N.grading q) (f : (homDualModule T).grading p) :
    (homPresentation T N).module.grading (q + p) :=
  ((homPresentation T N).homogeneousEquiv (q + p)).symm (evalPair T y f)

/-- The pairing on homogeneous elements is the underlying element of
`DifferentialGraded.Bimodule.evalGraded`. -/
theorem evalTotal_eq_evalGraded (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B)
    {q p : ℤ} (y : N.grading q) (f : (homDualModule T).grading p) :
    evalTotal T N (y : N.M) (f : (homDualModule T).M) =
      (evalGraded T y f : (homPresentation T N).module.M) :=
  evalTotal_apply T N q p y f

/-- The homogeneous map associated with `DifferentialGraded.Bimodule.evalGraded` is
`DifferentialGraded.Bimodule.evalPair`. -/
theorem homogeneousEquiv_evalGraded (T : Bimodule A B)
    {N : DifferentialGradedModule.{u, u, u} B} {q p : ℤ} (y : N.grading q)
    (f : (homDualModule T).grading p) :
    ((homPresentation T N).homogeneousEquiv (q + p)) (evalGraded T y f) = evalPair T y f :=
  LinearEquiv.apply_symm_apply _ _

/-- The homogeneous map associated with `DifferentialGraded.Bimodule.evalGraded` sends `t` to
`y · f t`. -/
private theorem homogeneousEquiv_evalGraded_apply (T : Bimodule A B)
    {N : DifferentialGradedModule.{u, u, u} B} {q p : ℤ} (y : N.grading q)
    (f : (homDualModule T).grading p) (t : T.rightModule.M) :
    ((((homPresentation T N).homogeneousEquiv (q + p)) (evalGraded T y f)).1 t : N.M) =
      MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1 t) • (y : N.M) :=
  (congrArg (fun z : HomogeneousMap B T.rightModule N (q + p) => z.1 t)
    (homogeneousEquiv_evalGraded T y f)).trans (evalPair_apply T y f t)

/-- **The comparison adds degrees.** -/
theorem evalTotal_mem (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) (q p : ℤ)
    (y : N.grading q) (f : (homDualModule T).grading p) :
    evalTotal T N (y : N.M) (f : (homDualModule T).M) ∈
      (homPresentation T N).module.grading (q + p) := by
  rw [evalTotal_eq_evalGraded]
  exact (evalGraded T y f).property

/-- **The comparison is right `A`-linear in the second variable**, on homogeneous elements. -/
theorem evalTotal_op_smul_graded (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B)
    (q p m : ℤ) (y : N.grading q) (f : (homDualModule T).grading p) (a : A.grading m) :
    evalTotal T N (y : N.M) (MulOpposite.op (a : A.A) • (f : (homDualModule T).M)) =
      MulOpposite.op (a : A.A) • evalTotal T N (y : N.M) (f : (homDualModule T).M) := by
  rw [evalTotal_eq_evalGraded T N y
      (⟨MulOpposite.op (a : A.A) • (f : (homDualModule T).M),
        (homDualModule T).smul_mem p m (f : (homDualModule T).M) (a : A.A)
          f.property a.property⟩ : (homDualModule T).grading (p + m)),
    evalTotal_eq_evalGraded]
  refine homModule_val_ext T N (show q + (p + m) = q + p + m by omega) _
    (⟨MulOpposite.op (a : A.A) • (evalGraded T y f : (homPresentation T N).module.M),
      (homPresentation T N).module.smul_mem (q + p) m
        (evalGraded T y f : (homPresentation T N).module.M) (a : A.A)
        (evalGraded T y f).property a.property⟩ :
      (homPresentation T N).module.grading (q + p + m)) ?_
  intro k t
  refine Eq.trans ?_ ((homPresentation T N).map_smul (q + p) m k (evalGraded T y f) a t).symm
  rw [homogeneousEquiv_evalGraded_apply, homogeneousEquiv_evalGraded_apply]
  exact congrArg (fun c : B.A => MulOpposite.op c • (y : N.M))
    ((homDualPresentation T).map_smul p m k f a t)

/-- **The comparison is balanced over `B`**, on homogeneous elements: moving a homogeneous
`b ∈ B^n` from the right action on `N` to the left action on `S` does not change the value. -/
theorem evalTotal_balance_graded (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B)
    (q p n : ℤ) (y : N.grading q) (f : (homDualModule T).grading p) (b : B.grading n) :
    evalTotal T N (MulOpposite.op (b : B.A) • (y : N.M)) (f : (homDualModule T).M) =
      evalTotal T N (y : N.M) ((homDualSmul T b f : (homDualModule T).M)) := by
  rw [evalTotal_eq_evalGraded T N
      (⟨MulOpposite.op (b : B.A) • (y : N.M),
        N.smul_mem q n (y : N.M) (b : B.A) y.property b.property⟩ : N.grading (q + n)) f,
    evalTotal_eq_evalGraded T N y (homDualSmul T b f)]
  refine homModule_val_ext T N (show q + n + p = q + (p + n) by omega) _ _ ?_
  intro k t
  rw [homogeneousEquiv_evalGraded_apply, homogeneousEquiv_evalGraded_apply,
    homDualBimodule_action_apply T n p k b f t]
  change MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1
      (t : T.rightModule.M)) • (MulOpposite.op (b : B.A) • (y : N.M)) = _
  rw [smul_smul, ← MulOpposite.op_mul]

-- Membership transported along an equality of degrees is
-- `DifferentialGradedModule.mem_grading_congr`, StacksFrontier/Algebra/DGA/Abelian.lean:188.

/-- **The comparison satisfies the graded Leibniz rule**, on homogeneous elements. -/
theorem evalTotal_d_graded (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B)
    (q p : ℤ) (x : N.grading q) (f : (homDualModule T).grading p) :
    (homPresentation T N).module.d (evalTotal T N (x : N.M) (f : (homDualModule T).M)) =
      evalTotal T N (N.d (x : N.M)) (f : (homDualModule T).M) +
        (q.negOnePow : ℤ) •
          evalTotal T N (x : N.M) ((homDualModule T).d (f : (homDualModule T).M)) := by
  have hmem1 : (evalGraded T (N.gradedDifferential q x) f : (homPresentation T N).module.M) ∈
      (homPresentation T N).module.grading (q + p + 1) :=
    mem_grading_congr (show q + 1 + p = q + p + 1 by omega)
      (evalGraded T (N.gradedDifferential q x) f).property
  have hmem2 : (evalGraded T x ((homDualModule T).gradedDifferential p f) :
      (homPresentation T N).module.M) ∈ (homPresentation T N).module.grading (q + p + 1) :=
    mem_grading_congr (show q + (p + 1) = q + p + 1 by omega)
      (evalGraded T x ((homDualModule T).gradedDifferential p f)).property
  have hd1 : evalTotal T N (N.d (x : N.M)) (f : (homDualModule T).M) =
      (evalGraded T (N.gradedDifferential q x) f : (homPresentation T N).module.M) :=
    evalTotal_eq_evalGraded T N (N.gradedDifferential q x) f
  have hd2 : evalTotal T N (x : N.M) ((homDualModule T).d (f : (homDualModule T).M)) =
      (evalGraded T x ((homDualModule T).gradedDifferential p f) :
        (homPresentation T N).module.M) :=
    evalTotal_eq_evalGraded T N x ((homDualModule T).gradedDifferential p f)
  rw [evalTotal_eq_evalGraded T N x f, hd1, hd2]
  have key : (homPresentation T N).module.gradedDifferential (q + p) (evalGraded T x f) =
      (⟨_, hmem1⟩ : (homPresentation T N).module.grading (q + p + 1)) +
        (q.negOnePow : ℤ) •
          (⟨_, hmem2⟩ : (homPresentation T N).module.grading (q + p + 1)) := by
    refine ((homPresentation T N).homogeneousEquiv (q + p + 1)).injective
      (homogeneousMap_ext fun k t => ?_)
    have hL : ((((homPresentation T N).homogeneousEquiv (q + p + 1))
          ((homPresentation T N).module.gradedDifferential (q + p) (evalGraded T x f))).1
          (t : T.rightModule.M) : N.M) =
        N.d (MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1
            (t : T.rightModule.M)) • (x : N.M)) -
          DifferentialGraded.gradedSign R (q + p) •
            (MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1
              (T.rightModule.d (t : T.rightModule.M))) • (x : N.M)) := by
      rw [(homPresentation T N).map_d (q + p) (evalGraded T x f), homogeneousEquiv_evalGraded]
      rfl
    have hW1 : ((((homPresentation T N).homogeneousEquiv (q + p + 1))
          (⟨_, hmem1⟩ : (homPresentation T N).module.grading (q + p + 1))).1
          (t : T.rightModule.M) : N.M) =
        MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1
          (t : T.rightModule.M)) • N.d (x : N.M) := by
      refine (homogeneousEquiv_val_apply_congr (homPresentation T N)
        (show q + p + 1 = q + 1 + p by omega) _
        (evalGraded T (N.gradedDifferential q x) f) rfl t).trans
        (homogeneousEquiv_evalGraded_apply T (N.gradedDifferential q x) f t)
    have hW2 : ((((homPresentation T N).homogeneousEquiv (q + p + 1))
          (⟨_, hmem2⟩ : (homPresentation T N).module.grading (q + p + 1))).1
          (t : T.rightModule.M) : N.M) =
        MulOpposite.op (B.d ((((homDualPresentation T).homogeneousEquiv p) f).1
              (t : T.rightModule.M)) -
            DifferentialGraded.gradedSign R p •
              ((((homDualPresentation T).homogeneousEquiv p) f).1
                (T.rightModule.d (t : T.rightModule.M)) : B.A)) • (x : N.M) := by
      refine (homogeneousEquiv_val_apply_congr (homPresentation T N)
        (show q + p + 1 = q + (p + 1) by omega) _
        (evalGraded T x ((homDualModule T).gradedDifferential p f)) rfl t).trans ?_
      rw [homogeneousEquiv_evalGraded, evalPair_apply]
      exact congrArg (fun c : B.A => MulOpposite.op c • (x : N.M))
        (congrArg (fun z : HomogeneousMap B T.rightModule (regularModule B) (p + 1) =>
          z.1 (t : T.rightModule.M)) ((homDualPresentation T).map_d p f))
    rw [hL]
    have hRsum : ((((homPresentation T N).homogeneousEquiv (q + p + 1))
          ((⟨_, hmem1⟩ : (homPresentation T N).module.grading (q + p + 1)) +
            (q.negOnePow : ℤ) •
              (⟨_, hmem2⟩ : (homPresentation T N).module.grading (q + p + 1)))).1
          (t : T.rightModule.M) : N.M) =
        ((((homPresentation T N).homogeneousEquiv (q + p + 1))
            (⟨_, hmem1⟩ : (homPresentation T N).module.grading (q + p + 1))).1
            (t : T.rightModule.M) : N.M) +
          (q.negOnePow : ℤ) • ((((homPresentation T N).homogeneousEquiv (q + p + 1))
            (⟨_, hmem2⟩ : (homPresentation T N).module.grading (q + p + 1))).1
            (t : T.rightModule.M) : N.M) := by
      rw [map_add, map_zsmul]
      rfl
    rw [hRsum, hW1, hW2, N.leibniz_apply q (x : N.M) x.property
      ((((homDualPresentation T).homogeneousEquiv p) f).1 (t : T.rightModule.M)),
      MulOpposite.op_sub, sub_smul, smul_sub, MulOpposite.op_smul, smul_assoc]
    simp only [← Int.cast_smul_eq_zsmul R (q.negOnePow : ℤ),
      DifferentialGraded.intCast_negOnePow]
    rw [smul_smul, DifferentialGraded.gradedSign_add]
    abel
  calc (homPresentation T N).module.d (evalGraded T x f : (homPresentation T N).module.M)
      = (((homPresentation T N).module.gradedDifferential (q + p) (evalGraded T x f)) :
          (homPresentation T N).module.M) := rfl
    _ = _ := by rw [key]; rfl

/-! ### The comparison as a balanced bilinear map -/

/-- **The graded Leibniz rule**, for an arbitrary element of `S`. -/
theorem evalTotal_d (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) (q : ℤ)
    (x : N.grading q) (y : (homDualModule T).M) :
    (homPresentation T N).module.d (evalTotal T N (x : N.M) y) =
      evalTotal T N (N.d (x : N.M)) y +
        (q.negOnePow : ℤ) • evalTotal T N (x : N.M) ((homDualModule T).d y) := by
  induction y using DirectSum.Decomposition.inductionOn (homDualModule T).grading with
  | zero => simp
  | @homogeneous p f => exact evalTotal_d_graded T N q p x f
  | add y z hy hz =>
    simp only [map_add, hy, hz, smul_add]
    abel

/-- **The comparison is right `A`-linear in the second variable.** -/
theorem evalTotal_op_smul (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B)
    (x : N.M) (y : (homDualModule T).M) (a : A.A) :
    evalTotal T N x (MulOpposite.op a • y) = MulOpposite.op a • evalTotal T N x y := by
  induction x using DirectSum.Decomposition.inductionOn N.grading with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, smul_add]
  | @homogeneous q x =>
    induction y using DirectSum.Decomposition.inductionOn (homDualModule T).grading with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]
    | @homogeneous p f =>
      induction a using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | add a b ha hb => simp only [MulOpposite.op_add, add_smul, map_add, ha, hb]
      | @homogeneous m a => exact evalTotal_op_smul_graded T N q p m x f a

/-- **The comparison `N ⊗_B S → Hom^•_B(T, N)`, as a balanced bilinear chain map.** On
homogeneous elements it is `(y, f) ↦ (t ↦ y · f t)`. -/
def evalBalanced (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) :
    BalancedBilinearMap N (homDualBimodule T) (homPresentation T N).module where
  toLinearMap := evalTotal T N
  map_grading p q x y := evalTotal_mem T N p q x y
  map_d p x y := evalTotal_d T N p x y
  balance p q n x y b := evalTotal_balance_graded T N p q n x y b
  map_right x y a := evalTotal_op_smul T N x y a

/-! ### The comparison as a homomorphism out of the tensor product -/

/-- **The comparison `c_N : N ⊗_B S ⟶ Hom^•_B(T, N)`** of right differential graded `A`-modules,
the lift of `DifferentialGraded.Bimodule.evalBalanced` through the universal property of the
relative tensor product. -/
def evalHom (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) :
    DifferentialGradedModule.Hom
      ((tensorDGFunctor (homDualBimodule T)).functor.obj N) (homPresentation T N).module :=
  ((tensorDGFunctor (homDualBimodule T)).universal N (homPresentation T N).module
    (evalBalanced T N)).choose

/-- `c_N` sends the pure tensor `y ⊗ f` to `t ↦ y · f t`. -/
theorem evalHom_pure (T : Bimodule A B) (N : DifferentialGradedModule.{u, u, u} B) (y : N.M)
    (f : (homDualModule T).M) :
    (evalHom T N).toFun
        (((tensorDGFunctor (homDualBimodule T)).pure N).toLinearMap y f) =
      evalTotal T N y f :=
  ((tensorDGFunctor (homDualBimodule T)).universal N (homPresentation T N).module
    (evalBalanced T N)).choose_spec.1 y f

/-! ### Naturality -/

/-- The internal hom functor acts on the comparison by postcomposition, on homogeneous
elements. -/
theorem homModuleFunctor_map_evalTotal_graded (T : Bimodule A B)
    {L M : DifferentialGradedModule.{u, u, u} B} (h : L ⟶ M) (q p : ℤ) (y : L.grading q)
    (f : (homDualModule T).grading p) :
    ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun
        (evalTotal T L (y : L.M) (f : (homDualModule T).M)) =
      evalTotal T M (h.toFun (y : L.M)) (f : (homDualModule T).M) := by
  have hmem : ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun
      (evalGraded T y f : (homPresentation T L).module.M) ∈
      (homPresentation T M).module.grading (q + p) :=
    ((homModuleFunctor A B T.rightModule T.leftAction).map h).map_grading (q + p) _
      (evalGraded T y f).property
  have hR : evalTotal T M (h.toFun (y : L.M)) (f : (homDualModule T).M) =
      (evalGraded T (h.gradedMap q y) f : (homPresentation T M).module.M) :=
    evalTotal_eq_evalGraded T M (h.gradedMap q y) f
  rw [evalTotal_eq_evalGraded T L y f, hR]
  refine homModule_val_ext T M (rfl : q + p = q + p)
    (⟨_, hmem⟩ : (homPresentation T M).module.grading (q + p)) _ ?_
  intro k t
  have hpost := homModuleFunctor_map_homogeneousEquiv_apply A B T.rightModule T.leftAction h
    (q + p) (evalGraded T y f) t
  refine hpost.trans ((congrArg h.toFun (homogeneousEquiv_evalGraded_apply T y f t)).trans ?_)
  refine Eq.trans ?_ (homogeneousEquiv_evalGraded_apply T (h.gradedMap q y) f t).symm
  exact h.map_smul (y : L.M) ((((homDualPresentation T).homogeneousEquiv p) f).1
    (t : T.rightModule.M))

/-- The internal hom functor acts on the comparison by postcomposition. -/
theorem homModuleFunctor_map_evalTotal (T : Bimodule A B)
    {L M : DifferentialGradedModule.{u, u, u} B} (h : L ⟶ M) (y : L.M)
    (f : (homDualModule T).M) :
    ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun (evalTotal T L y f) =
      evalTotal T M (h.toFun y) f := by
  have hzero : ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun
      (0 : (homPresentation T L).module.M) = 0 := map_zero _
  have hadd : ∀ u v : (homPresentation T L).module.M,
      ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun (u + v) =
        ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun u +
          ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun v :=
    fun u v => map_add _ u v
  induction y using DirectSum.Decomposition.inductionOn L.grading with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply]
    exact hzero
  | add y₁ y₂ hy₁ hy₂ =>
    simp only [map_add, LinearMap.add_apply]
    rw [hadd, hy₁, hy₂]
    rfl
  | @homogeneous q y =>
    induction f using DirectSum.Decomposition.inductionOn (homDualModule T).grading with
    | zero =>
      simp only [map_zero]
      exact hzero
    | add f₁ f₂ hf₁ hf₂ =>
      simp only [map_add]
      rw [hadd, hf₁, hf₂]
      rfl
    | @homogeneous p f => exact homModuleFunctor_map_evalTotal_graded T h q p y f

/-- **The comparison, naturally in `N`.** The maps `c_N : N ⊗_B S ⟶ Hom^•_B(T, N)` form a
natural transformation of the ordinary tensor functor of Tag 09LM with the bimodule
`S = Hom^•_B(T, B)` into the internal hom functor of Tag 0FQQ out of `T`.

Naturality is an identity between two homomorphisms out of a tensor product, so it is checked on
pure tensors, where both sides send `y ⊗ f` to `t ↦ h(y) · f t`. -/
def evalModuleNatTrans (T : Bimodule A B) :
    tensorCompFunctor (homDualBimodule T) ⟶
      homModuleFunctor A B T.rightModule T.leftAction where
  app N := evalHom T N
  naturality L M h := by
    refine tensorObj_hom_ext' (homDualBimodule T) L _ _ fun y f => ?_
    change (evalHom T M).toFun
        (((tensorCompFunctor (homDualBimodule T)).map h).toFun
          (((tensorDGFunctor (homDualBimodule T)).pure L).toLinearMap y f)) =
      ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun
        ((evalHom T L).toFun
          (((tensorDGFunctor (homDualBimodule T)).pure L).toLinearMap y f))
    refine Eq.trans ?_ (congrArg (fun z : (homPresentation T L).module.M =>
      ((homModuleFunctor A B T.rightModule T.leftAction).map h).toFun z)
        (evalHom_pure T L y f)).symm
    refine Eq.trans ?_ (homModuleFunctor_map_evalTotal T h y f).symm
    rw [tensorCompFunctor_map_pure']
    exact evalHom_pure T M (h.toFun y) f

/-! ### The comparison on the homotopy categories -/

/-- The comparison on the homotopy categories, before descending along the quotient by
homotopy. -/
def evalHomotopyNatTransAux (T : Bimodule A B) :
    toHomotopyCategory B ⋙ tensorHomotopyFunctor (homDualBimodule T) ⟶
      toHomotopyCategory B ⋙ homHomotopyCategoryFunctor A B T.rightModule T.leftAction :=
  (tensorCompFunctor_quotient (homDualBimodule T)).inv ≫
    Functor.whiskerRight (evalModuleNatTrans T) (toHomotopyCategory A) ≫
      (homHomotopyDescent T.rightModule T.leftAction).inv

/-- **The comparison on the homotopy categories.** The maps `c_N : N ⊗_B S ⟶ Hom^•_B(T, N)`
descend to a natural transformation `- ⊗_B S ⟶ Hom_B(T, -)` of the functors
`K(B, d) ⥤ K(A, d)` of Tag 09LM and Tag 0FQQ.

The descent is available because `K(B, d)` is the quotient of the category of differential graded
`B`-modules by homotopy, so a transformation of the underlying functors that is compatible with
the quotient lifts; compatibility is Tag 09LM's `tensorCompFunctor_quotient` on the source and
Tag 0FQQ's `homHomotopyDescent` on the target. -/
def evalHomotopyNatTrans (T : Bimodule A B) :
    tensorHomotopyFunctor (homDualBimodule T) ⟶
      homHomotopyCategoryFunctor A B T.rightModule T.leftAction :=
  CategoryTheory.Quotient.natTransLift (homotopyRel B) (evalHomotopyNatTransAux T)

/-- The component of the comparison on the homotopy categories at the class of a differential
graded module, through the two compatibilities with the quotient. -/
theorem evalHomotopyNatTrans_app (T : Bimodule A B)
    (N : DifferentialGradedModule.{u, u, u} B) :
    (evalHomotopyNatTrans T).app ((toHomotopyCategory B).obj N) =
      (tensorCompFunctor_quotient (homDualBimodule T)).inv.app N ≫
        (toHomotopyCategory A).map ((evalModuleNatTrans T).app N) ≫
          (homHomotopyDescent T.rightModule T.leftAction).inv.app N := by
  change (evalHomotopyNatTransAux T).app N = _
  rfl

/-- **The comparison between the two functors that Tag 09LS and Tag 09LI derive.** The
transformation on the homotopy categories, with the target localized at the quasi-isomorphisms of
differential graded `A`-modules.

This is the transformation `γ` out of which the comparison
`N ⊗_B^𝐋 S ⟶ R\Hom(T, N)` of Tag 0BZ0 is built; see the implementation notes for what remains. -/
def evalToDerivedCategoryNatTrans (T : Bimodule A B) :
    tensorFunctorToDerivedCategory (homDualBimodule T) ⟶
      homToDerivedCategory A B T.rightModule T.leftAction :=
  Functor.whiskerRight (evalHomotopyNatTrans T) (quasiIsomorphisms' A).Q

/-- The component of the localized comparison is the image under the localization of the
component on the homotopy categories. -/
theorem evalToDerivedCategoryNatTrans_app (T : Bimodule A B) (X : HomotopyCategory B) :
    (evalToDerivedCategoryNatTrans T).app X =
      (quasiIsomorphisms' A).Q.map ((evalHomotopyNatTrans T).app X) := rfl

end DifferentialGraded.Bimodule

end

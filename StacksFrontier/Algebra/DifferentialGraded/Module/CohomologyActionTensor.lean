module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.CohomologyEndomorphism
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents

/-!
# Tensoring the action of a cocycle with a bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. A degree-`k` cocycle `a` of `A` acts in two places: by
left multiplication `A ⟶ A[k]` on the regular module
(`DifferentialGradedModule.regularCocycleHom`), and by left multiplication `N ⟶ N[k]` on the
bimodule (`DifferentialGraded.Bimodule.cocycleAction`). This file proves that the second is the
first tensored with `N`: the pure tensor `b ⊗ y` of `A ⊗_A N` is carried by `1 ⊗ (a·)` to
`(ab) ⊗ y`, which the unit isomorphism `A ⊗_A N ≅ N` reads as `a (b y)`.

Passing to `D(B, d)`, the derived tensor product `- ⊗_A^𝐋 N` therefore carries the canonical map
$$H^k(A) \longrightarrow \Hom_{D(A, d)}(A, A[k])$$
to the canonical map
$$H^k(A) \longrightarrow \Hom_{D(B, d)}(N, N[k]),$$
whose bijectivity is hypothesis (2) of [Stacks, Tag 09R9]. Since the first map is a bijection
(`DifferentialGradedModule.cohomologyToDerivedCategory_bijective`), that hypothesis says exactly
that `- ⊗_A^𝐋 N` is bijective on the morphisms from the regular module to its `k`-th shift.

## Main definitions

* `DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal`: for a right differential graded
  `A`-module `M` whose class in `K(A, d)` is orthogonal on the left to the acyclic modules, the
  isomorphism `M ⊗_A^𝐋 N ≅ M ⊗_A N` of `D(B, d)`, composed with a chosen differential graded
  model of `M ⊗_A N`.

## Main results

* `DifferentialGraded.Bimodule.tensorCompFunctor_map_regularCocycleHom`: the differential graded
  computation. Tensoring left multiplication by `a` on the regular module with `N` is left
  multiplication by `a` on `N`, modulo the unit isomorphisms `A ⊗_A N ≅ N` and
  `A[k] ⊗_A N ≅ N[k]`.
* `DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal_hom_naturality`: a commuting
  square of differential graded modules whose left-hand vertical is tensoring with `N` descends to
  a commuting square of `D(B, d)` whose left-hand vertical is the derived tensor product.
* `DifferentialGraded.Bimodule.derivedTensorFunctor_map_regularCocycleHom` and
  `DifferentialGraded.Bimodule.derivedTensorFunctor_map_cohomologyToDerivedCategory`: the derived
  form of the computation, on a single cocycle and on a cohomology class.
* `DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_iff` and
  `DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_iff_shift`: the map of
  hypothesis (2) of Tag 09R9 is bijective in degree `k` exactly when `- ⊗_A^𝐋 N` is bijective on
  `Hom_{D(A, d)}(A, A[k])`, with `A[k]` read first as the image of the shifted differential graded
  module and then as the `k`-th translate in the triangulated structure.

## Implementation notes

*The computation is carried out with the differential graded shift.* The shift in every
statement but the last is `DifferentialGradedModule.shift`, the shift of the category of
differential graded modules, and not the translation of the triangulated structure on `D(B, d)`.
That is what keeps the computation elementary: the comparison `A[k] ⊗_A N ≅ (A ⊗_A N)[k]` it needs
is the sign-free one of Tag 0FQN, already packaged in
`DifferentialGraded.Bimodule.tensorShiftRegularIso`. No commutation of an internal Hom functor
with the translation is used, and neither the unit of the adjunction of Tag 09LT nor the
comparison of Tag 0CS5 appears. Only the final criterion is restated for the translation of
`D(A, d)`, by composing with `DifferentialGradedModule.regularShiftCompare`, which compares the
two shifts on the image of the regular module.

*Why the comparison isomorphism is rebuilt here.*
`DifferentialGraded.Bimodule.derivedTensorRegularIso` is the special case of
`DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal` at the regular module with the
unit isomorphism, but it carries `no_expose`, so outside its own module it is an opaque
isomorphism and no identity relating it to the comparison of Tag 09LS can be proved. The general
construction below is stated for an arbitrary left-orthogonal module and an arbitrary
differential graded model of the ordinary tensor product, and is accompanied by
`DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal_hom`, which is the identity that
makes it computable.

*The differential graded square is checked on pure tensors.* Both sides are homomorphisms out of
`A ⊗_A N`, which the universal property of Tag 09LM characterizes by its pure tensors, so
`DifferentialGraded.Bimodule.tensorObj_hom_ext'` reduces the identity to the statement
`a (b y) = (ab) y`. That is the associativity of the left action, which
`DifferentialGraded.leftActionAlgHom` supplies as the multiplicativity of an algebra
homomorphism; the passage between the two names the left action carries —
`DifferentialGraded.Bimodule.leftMultiplication` on homogeneous elements and
`DifferentialGraded.leftActionTotal` on all of `A` — is
`DifferentialGraded.Bimodule.leftMultiplication_eq_leftActionTotal`.

*Universes.* As throughout this chapter's tensor interface, the base ring, the two algebras and
the modules all live in a single universe `u`; the narrowing comes down the chain from
`DifferentialGraded.Bimodule.TensorDGFunctorData` and is not decided here.

*No tag.* Hypothesis (2) of Tag 09R9 is a hypothesis, not a statement of the source, and the
tagged statement of Tag 09R9 is the full faithfulness of the derived tensor functor, which is not
proved here; Tag 09LM supplies the universal property used, and is already carried by
`DifferentialGraded.Bimodule.tensorDGFunctor`. So nothing below carries a `stacks` attribute.

## References

* [Stacks Project, Tag 09R9](https://stacks.math.columbia.edu/tag/09R9) for the hypothesis being
  computed, [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) for the relative tensor product
  and its universal property, [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) for the
  derived tensor product, and [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the left
  orthogonality of the regular module and its shifts.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- The total left action is associative: acting by a product is acting by the two factors in
turn. This is the multiplicativity of `DifferentialGraded.leftActionAlgHom`, read pointwise. -/
theorem leftActionTotal_mul_apply (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) (a b : A.A) (x : M.M) :
    leftActionTotal A B M L (a * b) x =
      leftActionTotal A B M L a (leftActionTotal A B M L b x) :=
  congrArg (fun f : Module.End R M.M => f x) (map_mul (leftActionAlgHom A B M L) a b)

namespace Bimodule

/-! ### Left multiplication through the total left action -/

/-- Left multiplication by a homogeneous element of `A` on a differential graded `(A, B)`-bimodule
is the total left action at that element. The two are the same map under different names: the
first is the homogeneous right `B`-linear map induced by a component of the left action cochain,
the second is the assembly of all those components along the grading. -/
theorem leftMultiplication_eq_leftActionTotal (N : Bimodule A B) (k : ℤ) (a : A.grading k)
    (x : N.rightModule.M) :
    (N.leftMultiplication k a).1 x =
      leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) x := by
  induction x using DirectSum.Decomposition.inductionOn N.rightModule.grading with
  | zero => simp
  | @homogeneous p x =>
    rw [leftMultiplication_apply, leftActionTotal_apply A B N.rightModule N.leftAction.1 k a,
      totalizeCochain_apply B N.rightModule k p (N.leftAction.1.action k a) x]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The differential graded computation -/

/-- **Left multiplication by a cocycle, tensored with `N`, is left multiplication by that
cocycle.** Let `a` be a degree-`k` cocycle of `A`. Tensoring the homomorphism `A ⟶ A[k]` of left
multiplication by `a` with the bimodule `N` gives a homomorphism `A ⊗_A N ⟶ A[k] ⊗_A N`; read
through the unit isomorphisms `A ⊗_A N ≅ N` and `A[k] ⊗_A N ≅ N[k]`, it is the homomorphism
`N ⟶ N[k]` by which `a` acts on `N`.

On a pure tensor `b ⊗ y` both sides are `a (b y)`: the left-hand side sends `b ⊗ y` to
`(ab) ⊗ y` and then to `(ab) y`, the right-hand side to `b y` and then to `a (b y)`. -/
theorem tensorCompFunctor_map_regularCocycleHom (N : Bimodule A B) (k : ℤ) (a : A.Cocycle k) :
    (tensorCompFunctor N).map (regularCocycleHom A k a) ≫ (tensorShiftRegularIso N k).hom =
      (tensorRegularIso N).1.hom ≫ N.cocycleAction k a := by
  refine tensorObj_hom_ext' N (regularModule A) _ _ fun x y => ?_
  have h : (tensorShiftRegularIso N k).hom.toFun
        (((tensorCompFunctor N).map (regularCocycleHom A k a)).toFun
          (((tensorDGFunctor N).pure (regularModule A)).toLinearMap x y)) =
      (N.cocycleAction k a).toFun ((tensorRegularIso N).1.hom.toFun
        (((tensorDGFunctor N).pure (regularModule A)).toLinearMap x y)) := by
    rw [tensorCompFunctor_map_pure', tensorShiftRegularIso_hom_pure, (tensorRegularIso N).2,
      regularCocycleHom_toFun, cocycleAction_toFun, regularHomogeneousMul_val_apply,
      leftMultiplication_eq_leftActionTotal, leftActionTotal_mul_apply]
  exact h

/-! ### The derived comparison at a left-orthogonal module -/

/-- **The derived tensor product at a left-orthogonal module.** If the class in `K(A, d)` of a
right differential graded `A`-module `M` is orthogonal on the left to the acyclic modules, the
comparison `M ⊗_A^𝐋 N → M ⊗_A N` of Tag 09LS is invertible, so the derived tensor product is
computed by the ordinary one. The ordinary one is read through a chosen isomorphism `M ⊗_A N ≅ P`
of differential graded modules, which is how the unit isomorphisms of
`DifferentialGraded.Bimodule.tensorRegularIso` and
`DifferentialGraded.Bimodule.tensorShiftRegularIso` enter. -/
def derivedTensorIsoOfLeftOrthogonal (N : Bimodule A B) (M : DifferentialGradedModule A)
    (hM : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M))
    {P : DifferentialGradedModule B} (e : (tensorCompFunctor N).obj M ≅ P) :
    (derivedTensorFunctor N).obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj M) ≅
      (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj P :=
  haveI := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N
    ((toHomotopyCategory A).obj M) hM
  asIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M)) ≪≫
    (quasiIsomorphisms' B).Q.mapIso
      ((Iso.app (tensorCompFunctor_quotient N) M).symm ≪≫ (toHomotopyCategory B).mapIso e)

/-- The comparison of `DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal` is the
comparison of Tag 09LS followed by the compatibility of Tag 09LM with the passage to homotopy
classes and the chosen model. This identity is what makes the isomorphism computable. -/
theorem derivedTensorIsoOfLeftOrthogonal_hom (N : Bimodule A B) (M : DifferentialGradedModule A)
    (hM : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M))
    {P : DifferentialGradedModule B} (e : (tensorCompFunctor N).obj M ≅ P) :
    (derivedTensorIsoOfLeftOrthogonal N M hM e).hom =
      (derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M) ≫
        (quasiIsomorphisms' B).Q.map ((tensorCompFunctor_quotient N).inv.app M ≫
          (toHomotopyCategory B).map e.hom) :=
  rfl

/-- **A differential graded square descends to the derived tensor product.** Let `φ : M ⟶ M'` be a
homomorphism of right differential graded `A`-modules whose two sources are orthogonal on the left
to the acyclic modules, let `e : M ⊗_A N ≅ P` and `e' : M' ⊗_A N ≅ P'` be differential graded
models of the ordinary tensor products, and let `ψ : P ⟶ P'` be the homomorphism that tensoring
`φ` with `N` becomes in those models. Then `φ ⊗^𝐋 1` is `ψ`, modulo the comparisons of
`DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal`.

The square is the naturality of the comparison of Tag 09LS, followed by the naturality of the
compatibility of Tag 09LM with the passage to homotopy classes. -/
theorem derivedTensorIsoOfLeftOrthogonal_hom_naturality (N : Bimodule A B)
    {M M' : DifferentialGradedModule A} (φ : M ⟶ M')
    (hM : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M))
    (hM' : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M'))
    {P P' : DifferentialGradedModule B} (e : (tensorCompFunctor N).obj M ≅ P)
    (e' : (tensorCompFunctor N).obj M' ≅ P') (ψ : P ⟶ P')
    (hψ : (tensorCompFunctor N).map φ ≫ e'.hom = e.hom ≫ ψ) :
    (derivedTensorFunctor N).map ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map φ) ≫
        (derivedTensorIsoOfLeftOrthogonal N M' hM' e').hom =
      (derivedTensorIsoOfLeftOrthogonal N M hM e).hom ≫
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).map ψ := by
  have hcounit : (derivedTensorFunctor N).map
          ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map φ)) ≫
        (derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M') =
      (derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M) ≫
        (quasiIsomorphisms' B).Q.map
          ((tensorHomotopyFunctor N).map ((toHomotopyCategory A).map φ)) :=
    (derivedTensorFunctorCounit N).naturality ((toHomotopyCategory A).map φ)
  have hquot : (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map φ) ≫
        (tensorCompFunctor_quotient N).inv.app M' =
      (tensorCompFunctor_quotient N).inv.app M ≫
        (toHomotopyCategory B).map ((tensorCompFunctor N).map φ) :=
    (tensorCompFunctor_quotient N).inv.naturality φ
  have hmid : (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map φ) ≫
        ((tensorCompFunctor_quotient N).inv.app M' ≫ (toHomotopyCategory B).map e'.hom) =
      (tensorCompFunctor_quotient N).inv.app M ≫
        ((toHomotopyCategory B).map e.hom ≫ (toHomotopyCategory B).map ψ) := by
    rw [← Category.assoc, hquot, Category.assoc, ← Functor.map_comp, hψ, Functor.map_comp]
  rw [derivedTensorIsoOfLeftOrthogonal_hom, derivedTensorIsoOfLeftOrthogonal_hom]
  simp only [Functor.comp_map]
  rw [← Category.assoc, hcounit, Category.assoc, ← Functor.map_comp, hmid]
  simp only [Functor.map_comp, Category.assoc]

/-! ### The derived form of the computation -/

/-- **The derived form of the computation.** In `D(B, d)` the derived tensor product with `N` of
left multiplication by a degree-`k` cocycle `a` on the regular module is left multiplication by
`a` on the bimodule, modulo the derived unit isomorphisms `A ⊗_A^𝐋 N ≅ N` and
`A[k] ⊗_A^𝐋 N ≅ N[k]`.

This is the differential graded computation of
`DifferentialGraded.Bimodule.tensorCompFunctor_map_regularCocycleHom` carried along
`DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal_hom_naturality`; the regular module
and its shifts are orthogonal on the left to the acyclic modules by Tag 09K1, which is what makes
the derived tensor product computable at them. -/
theorem derivedTensorFunctor_map_regularCocycleHom (N : Bimodule A B) (k : ℤ) (a : A.Cocycle k) :
    (derivedTensorFunctor N).map
          ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (regularCocycleHom A k a)) ≫
        (derivedTensorIsoOfLeftOrthogonal N ((regularModule A).shift k)
          (leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A k)
          (tensorShiftRegularIso N k)).hom =
      (derivedTensorIsoOfLeftOrthogonal N (regularModule A)
          (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A)
          (tensorRegularIso N).1).hom ≫
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).map (N.cocycleAction k a) :=
  derivedTensorIsoOfLeftOrthogonal_hom_naturality N (regularCocycleHom A k a) _ _ _ _ _
    (tensorCompFunctor_map_regularCocycleHom N k a)

/-- **The derived tensor functor computes the comparison of hypothesis (2) of Tag 09R9.** The
canonical map `H^k(A) → Hom_{D(A, d)}(A, A[k])` of
`DifferentialGradedModule.cohomologyToDerivedCategory`, followed by `- ⊗_A^𝐋 N`, is the canonical
map `H^k(A) → Hom_{D(B, d)}(N, N[k])` of
`DifferentialGraded.Bimodule.cohomologyEndomorphismComparison`, modulo the derived unit
isomorphisms. -/
theorem derivedTensorFunctor_map_cohomologyToDerivedCategory (N : Bimodule A B) (k : ℤ)
    (x : A.Cohomology k) :
    (derivedTensorFunctor N).map (cohomologyToDerivedCategory A k x) ≫
        (derivedTensorIsoOfLeftOrthogonal N ((regularModule A).shift k)
          (leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A k)
          (tensorShiftRegularIso N k)).hom =
      (derivedTensorIsoOfLeftOrthogonal N (regularModule A)
          (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A)
          (tensorRegularIso N).1).hom ≫ N.cohomologyEndomorphismComparison k x := by
  induction x using Quotient.inductionOn with
  | h a => exact derivedTensorFunctor_map_regularCocycleHom N k a

/-- A map that is `g` composed with equivalences on both sides is bijective iff `g` is. -/
private theorem bijective_iff_of_eq_equiv_comp {α β γ δ : Type*} (f : α → δ) (g : β → γ)
    (e : γ ≃ δ) (e' : α ≃ β) (h : f = e ∘ g ∘ e') :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [h, Equiv.comp_bijective, Equiv.bijective_comp]

/-- **Hypothesis (2) of Tag 09R9 is a full faithfulness of `- ⊗_A^𝐋 N` on the regular module.**
The canonical map `H^k(A) → Hom_{D(B, d)}(N, N[k])` is bijective exactly when `- ⊗_A^𝐋 N` is
bijective from `Hom_{D(A, d)}(A, A[k])` onto `Hom_{D(B, d)}(A ⊗_A^𝐋 N, A[k] ⊗_A^𝐋 N)`.

The canonical map `H^k(A) → Hom_{D(A, d)}(A, A[k])` is a bijection
(`DifferentialGradedModule.cohomologyToDerivedCategory_bijective`), and composing with an
isomorphism of `D(B, d)` on either side is a bijection, so the two statements differ by
bijections only. -/
theorem bijective_cohomologyEndomorphismComparison_iff (N : Bimodule A B) (k : ℤ) :
    Function.Bijective (N.cohomologyEndomorphismComparison k) ↔
      Function.Bijective ((derivedTensorFunctor N).map :
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶
            (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj ((regularModule A).shift k)) →
          _) := by
  refine bijective_iff_of_eq_equiv_comp _ _
    (Iso.homCongr
        (derivedTensorIsoOfLeftOrthogonal N (regularModule A)
          (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A) (tensorRegularIso N).1)
        (derivedTensorIsoOfLeftOrthogonal N ((regularModule A).shift k)
          (leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A k)
          (tensorShiftRegularIso N k))) (cohomologyEquivDerivedHom A k) ?_
  funext x
  rw [Function.comp_apply, Function.comp_apply, Iso.homCongr_apply,
    cohomologyEquivDerivedHom_apply, derivedTensorFunctor_map_cohomologyToDerivedCategory,
    Iso.inv_hom_id_assoc]

/-- **Hypothesis (2) of Tag 09R9, with the shift taken in the triangulated structure.** The
criterion of `DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_iff` with
`A[k]` read as the `k`-th translate of the class of the regular module in `D(A, d)`, which is the
form a dévissage over the shifts of that class consumes.

The two shifts are compared by `DifferentialGradedModule.regularShiftCompare`; composing with it
and with its image under `- ⊗_A^𝐋 N`, both isomorphisms, turns one criterion into the other. -/
theorem bijective_cohomologyEndomorphismComparison_iff_shift (N : Bimodule A B) (k : ℤ) :
    Function.Bijective (N.cohomologyEndomorphismComparison k) ↔
      Function.Bijective ((derivedTensorFunctor N).map :
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶
            ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧) →
          _) := by
  rw [bijective_cohomologyEndomorphismComparison_iff]
  refine (bijective_iff_of_eq_equiv_comp _ _
    (Iso.homCongr
      ((derivedTensorFunctor N).mapIso (Iso.refl
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))))
      ((derivedTensorFunctor N).mapIso (regularShiftCompare A k)))
    (Iso.homCongr (Iso.refl ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
      (regularModule A))) (regularShiftCompare A k)).symm ?_).symm
  funext f
  rw [Function.comp_apply, Function.comp_apply, ← Functor.map_homCongr, Equiv.apply_symm_apply]

end Bimodule

end DifferentialGraded

end

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.EffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Defs
import all StacksFrontier.AlgebraicGeometry.Descent.Modules.EffectiveDescent

/-!
# Effective descent for algebras along a universally injective ring map

This is the affine case of Stacks 0245 — effective descent for schemes affine over the base —
in its ring-theoretic form.  Let `R → A` be a universally injective ring map (for instance a
faithfully flat one), let `B` be an `A`-algebra, and let
`θ : B ⊗[R] A ≃ₐ[R] A ⊗[R] B` be an isomorphism over `A ⊗[R] A` satisfying the cocycle
condition.  Then the invariants of `θ` form an `R`-subalgebra `C ⊆ B` whose base change along
`R → A` is `B`, compatibly with `θ`.

## Main definitions

* `Stacks.AlgebraDescent.cocycle01`, `...cocycle12`, `...cocycle02` are the three pullbacks of a
  transition map to the triple tensor product, in which the cocycle condition is stated.
* `Stacks.AlgebraDescent.moduleDescentDatum` is the module descent datum of Tag 023G underlying
  an algebra transition.
* `Stacks.AlgebraDescent.invariantSubalgebra` is the `R`-subalgebra of elements of `B` fixed by
  the transition.

## Main results

* `Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv`: the invariant subalgebra `C` satisfies
  `A ⊗[R] C ≃ₐ[A] B`, with the isomorphism given on pure tensors by `a ⊗ c ↦ a • c` and
  compatible with the transition, in the sense that `θ ((a • c) ⊗ b) = a ⊗ (b • c)`.
* `Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv_of_faithfullyFlat`: the same with the
  hypothesis `Module.FaithfullyFlat R A`, which is the form an fpqc covering supplies.
* `Stacks.AlgebraDescent.universallyInjective_of_faithfullyFlat`: a faithfully flat ring map is
  universally injective, in the same-universe form `Algebra.UniversallyInjective` uses.

## Implementation notes

The proof is the one in Tag 0245: the algebra transition is an isomorphism of the underlying
module descent data, so Tag 08XA (`ModuleCat.isEffectiveDescentMorphismForModules_iff_`
`universallyInjective`, through the counit isomorphism of its essential-surjectivity half)
already produces an `R`-module whose base change is `B`, namely the invariants
`ModuleCat.invariantSubmodule`.  Because `θ` is multiplicative the invariants are closed under
multiplication and contain the image of `R`, so they form a subalgebra, and the module
isomorphism `A ⊗[R] C → B` is the algebra map `Algebra.TensorProduct.lift` — the two agree on
pure tensors, where both send `a ⊗ c` to `a • c`.

Two spellings of the `R`-module structure on `B` have to be reconciled.  The descent-datum API
of `ModuleCat.DescentData` uses `ModuleCat.restrictModule R A (ModuleCat.of A B)`, whose scalar
action is `r • b = algebraMap R A r • b`, while the statements here use the `Algebra R B`
instance.  The two carriers are the same type and the two actions agree by
`IsScalarTower.algebraMap_smul`, so `restrictEquiv` is the identity map and the transports
`srcEquiv`, `tgtEquiv`, `tripleEquiv` are the identity on pure tensors; every lemma crossing
between the two spellings is proved by reducing to pure tensors.

`A ⊗[R] A`-linearity of the transition is *not* a separate hypothesis: it follows from
multiplicativity together with the two hypotheses `hleft` and `hright` saying that `θ` is a
morphism over `A ⊗[R] A`, because on either side the action of `a ⊗ b` is multiplication by
`a ⊗ 1` and by `1 ⊗ b` (`srcEquiv_smul`, `tgtEquiv_smul`).

The three rings share one universe.  This comes from `Algebra.UniversallyInjective`, which
quantifies over test modules in the universe of its source ring.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 08XA](https://stacks.math.columbia.edu/tag/08XA)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

noncomputable section

namespace Stacks.AlgebraDescent

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-! ### Transporting between `B` and its restricted-scalars spelling -/

/-- `B`, viewed as an `R`-module through `A`, identified with `B` itself. -/
def restrictEquiv :
    ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)) ≃ₗ[R] B where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change (algebraMap R A r) • (show B from x) = r • (show B from x)
    exact IsScalarTower.algebraMap_smul A r (show B from x)

/-- `restrictEquiv` is the identity on underlying elements. -/
@[simp] lemma restrictEquiv_apply
    (x : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) :
    restrictEquiv R A B x = x := rfl

/-- The inverse of `restrictEquiv` is the identity on underlying elements. -/
@[simp] lemma restrictEquiv_symm_apply (x : B) :
    (restrictEquiv R A B).symm x = x := rfl

/-- `restrictEquiv` carries the restricted-scalars action of `a : A` to `a • _` on `B`. -/
lemma restrictEquiv_action (a : A)
    (x : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) :
    restrictEquiv R A B (ModuleCat.restrictedScalarAction R A (ModuleCat.of A B) a x)
      = a • restrictEquiv R A B x := rfl

/-- The transport on the source of a transition map. -/
def srcEquiv :
    (↑(ModuleCat.restrictModule R A (ModuleCat.of A B)) ⊗[R] A) ≃ₗ[R] (B ⊗[R] A) :=
  TensorProduct.congr (restrictEquiv R A B) (LinearEquiv.refl R A)

/-- The transport on the target of a transition map. -/
def tgtEquiv :
    (A ⊗[R] ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) ≃ₗ[R] (A ⊗[R] B) :=
  TensorProduct.congr (LinearEquiv.refl R A) (restrictEquiv R A B)

/-- The transport on the triple tensor product. -/
def tripleEquiv :
    ((A ⊗[R] A) ⊗[R] ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) ≃ₗ[R]
      ((A ⊗[R] A) ⊗[R] B) :=
  TensorProduct.congr (LinearEquiv.refl R (A ⊗[R] A)) (restrictEquiv R A B)

/-- `srcEquiv` on a pure tensor `x ⊗ₜ a` is `restrictEquiv x ⊗ₜ a`. -/
@[simp] lemma srcEquiv_tmul (x : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)))
    (a : A) :
    srcEquiv R A B (x ⊗ₜ[R] a) = restrictEquiv R A B x ⊗ₜ[R] a :=
  TensorProduct.congr_tmul _ _ _ _

/-- The inverse of `srcEquiv` on a pure tensor `x ⊗ₜ a`. -/
@[simp] lemma srcEquiv_symm_tmul (x : B) (a : A) :
    (srcEquiv R A B).symm (x ⊗ₜ[R] a) = (restrictEquiv R A B).symm x ⊗ₜ[R] a := rfl

/-- `tgtEquiv` on a pure tensor `a ⊗ₜ x` is `a ⊗ₜ restrictEquiv x`. -/
@[simp] lemma tgtEquiv_tmul (a : A)
    (x : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) :
    tgtEquiv R A B (a ⊗ₜ[R] x) = a ⊗ₜ[R] restrictEquiv R A B x :=
  TensorProduct.congr_tmul _ _ _ _

/-- The inverse of `tgtEquiv` on a pure tensor `a ⊗ₜ x`. -/
@[simp] lemma tgtEquiv_symm_tmul (a : A) (x : B) :
    (tgtEquiv R A B).symm (a ⊗ₜ[R] x) = a ⊗ₜ[R] (restrictEquiv R A B).symm x := rfl

/-- The inverse of `tripleEquiv` on a pure tensor `s ⊗ₜ x`. -/
@[simp] lemma tripleEquiv_symm_tmul (s : A ⊗[R] A) (x : B) :
    (tripleEquiv R A B).symm (s ⊗ₜ[R] x) = s ⊗ₜ[R] (restrictEquiv R A B).symm x := rfl

/-- Multiplying a pure tensor of `B ⊗[R] A` by `algebraMap a ⊗ 1` and `1 ⊗ b`. -/
private theorem algebraMap_tmul_mul_tmul_mul_tmul
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] (a b c : A) (x : B) :
    (algebraMap A B a ⊗ₜ[R] (1 : A)) * (x ⊗ₜ[R] c) * ((1 : B) ⊗ₜ[R] b) =
      (a • x) ⊗ₜ[R] (c * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.smul_def, mul_one, one_mul]

/-- Multiplying a pure tensor of `A ⊗[R] B` by `a ⊗ 1` and `1 ⊗ algebraMap b`. -/
private theorem tmul_mul_tmul_mul_tmul_algebraMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] (a b c : A) (x : B) :
    (a ⊗ₜ[R] (1 : B)) * (c ⊗ₜ[R] x) * ((1 : A) ⊗ₜ[R] algebraMap A B b) =
      (a * c) ⊗ₜ[R] (b • x) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.smul_def, mul_one, one_mul, mul_comm (algebraMap A B b)]

/-- The `A ⊗[R] A`-action on the source of a transition map, written multiplicatively. -/
lemma srcEquiv_smul (a b : A)
    (z : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)) ⊗[R] A) :
    srcEquiv R A B ((a ⊗ₜ[R] b) • z) =
      (algebraMap A B a ⊗ₜ[R] (1 : A)) * srcEquiv R A B z * ((1 : B) ⊗ₜ[R] b) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [smul_add, map_add, map_add, hz, hw, mul_add, add_mul]
  | tmul x c =>
    rw [ModuleCat.sourceTensor_smul_tmul, srcEquiv_tmul, srcEquiv_tmul,
      restrictEquiv_action, algebraMap_tmul_mul_tmul_mul_tmul, mul_comm b c]

/-- The `A ⊗[R] A`-action on the target of a transition map, written multiplicatively. -/
lemma tgtEquiv_smul (a b : A)
    (w : A ⊗[R] ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) :
    tgtEquiv R A B ((a ⊗ₜ[R] b) • w) =
      (a ⊗ₜ[R] (1 : B)) * tgtEquiv R A B w * ((1 : A) ⊗ₜ[R] algebraMap A B b) := by
  induction w using TensorProduct.inductionOn with
  | add z w hz hw => rw [smul_add, map_add, map_add, hz, hw, mul_add, add_mul]
  | tmul c x =>
    rw [ModuleCat.targetTensor_smul_tmul, tgtEquiv_tmul, tgtEquiv_tmul,
      restrictEquiv_action, tmul_mul_tmul_mul_tmul_algebraMap]

/-! ### The module descent datum attached to an algebra transition -/

/-- An algebra transition isomorphism, transported to the restricted-scalars spelling. -/
def transitionLinearEquiv (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B)) :
    (↑(ModuleCat.restrictModule R A (ModuleCat.of A B)) ⊗[R] A) ≃ₗ[R]
      (A ⊗[R] ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) :=
  (srcEquiv R A B) ≪≫ₗ θ.toLinearEquiv ≪≫ₗ (tgtEquiv R A B).symm

/-- `transitionLinearEquiv θ` is `tgtEquiv.symm ∘ θ ∘ srcEquiv`. -/
@[simp] lemma transitionLinearEquiv_apply (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    (z : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)) ⊗[R] A) :
    transitionLinearEquiv R A B θ z = (tgtEquiv R A B).symm (θ (srcEquiv R A B z)) := rfl

/-- If `θ` is compatible with the two `A`-algebra structures, then `transitionLinearEquiv θ` is
`A ⊗[R] A`-linear. -/
lemma transitionLinearEquiv_smul (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
    (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)
    (s : A ⊗[R] A)
    (z : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)) ⊗[R] A) :
    transitionLinearEquiv R A B θ (s • z) = s • transitionLinearEquiv R A B θ z := by
  induction s using TensorProduct.inductionOn with
  | add s t hs ht => rw [add_smul, map_add, hs, ht, add_smul]
  | tmul a b =>
    apply (tgtEquiv R A B).injective
    rw [transitionLinearEquiv_apply, LinearEquiv.apply_symm_apply, srcEquiv_smul, map_mul, map_mul,
      hleft, hright, tgtEquiv_smul, transitionLinearEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The transition map of the module descent datum built from an algebra transition. -/
def moduleTransition (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
    (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a) :
    (↑(ModuleCat.restrictModule R A (ModuleCat.of A B)) ⊗[R] A) ≃ₗ[A ⊗[R] A]
      (A ⊗[R] ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) where
  toFun := transitionLinearEquiv R A B θ
  invFun := (transitionLinearEquiv R A B θ).symm
  map_add' := map_add _
  map_smul' := transitionLinearEquiv_smul R A B θ hleft hright
  left_inv := (transitionLinearEquiv R A B θ).left_inv
  right_inv := (transitionLinearEquiv R A B θ).right_inv

/-- Restricting the scalars of `moduleTransition` to `R` gives `transitionLinearEquiv`. -/
lemma moduleTransition_restrictScalars (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
    (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a) :
    ((moduleTransition R A B θ hleft hright).toLinearMap.restrictScalars R) =
      (transitionLinearEquiv R A B θ).toLinearMap := rfl

/-! ### The cocycle condition -/

/-- A transition map applied to tensor slots `0, 1` of `(B ⊗[R] A) ⊗[R] A`. -/
def cocycle01 (θ : (B ⊗[R] A) →ₗ[R] (A ⊗[R] B)) :
    ((B ⊗[R] A) ⊗[R] A) →ₗ[R] ((A ⊗[R] B) ⊗[R] A) := θ.rTensor A

/-- A transition map applied to tensor slots `1, 2` of `(A ⊗[R] B) ⊗[R] A`. -/
def cocycle12 (θ : (B ⊗[R] A) →ₗ[R] (A ⊗[R] B)) :
    ((A ⊗[R] B) ⊗[R] A) →ₗ[R] ((A ⊗[R] A) ⊗[R] B) :=
  (TensorProduct.assoc R A A B).symm.toLinearMap ∘ₗ θ.lTensor A ∘ₗ
    (TensorProduct.assoc R A B A).toLinearMap

/-- A transition map applied to tensor slots `0, 2` of `(B ⊗[R] A) ⊗[R] A`. -/
def cocycle02 (θ : (B ⊗[R] A) →ₗ[R] (A ⊗[R] B)) :
    ((B ⊗[R] A) ⊗[R] A) →ₗ[R] ((A ⊗[R] A) ⊗[R] B) :=
  (TensorProduct.rightComm R A B A).toLinearMap ∘ₗ θ.rTensor A ∘ₗ
    (TensorProduct.rightComm R B A A).toLinearMap

/-- `TensorProduct.rightComm` commutes with the transports `tgtEquiv` and `tripleEquiv`. -/
lemma rightComm_tgtEquiv (v : A ⊗[R] B) (b : A) :
    (TensorProduct.rightComm R A
        (↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) A)
      (((tgtEquiv R A B).symm v) ⊗ₜ[R] b) =
      (tripleEquiv R A B).symm ((TensorProduct.rightComm R A B A) (v ⊗ₜ[R] b)) := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw =>
    rw [map_add, add_tmul, map_add, hv, hw, add_tmul, map_add, map_add]
  | tmul a y => rfl

/-- The inverse associator commutes with the transports `tgtEquiv` and `tripleEquiv`. -/
lemma assoc_tgtEquiv (a : A) (v : A ⊗[R] B) :
    (TensorProduct.assoc R A A
        (↑(ModuleCat.restrictModule R A (ModuleCat.of A B)))).symm
      (a ⊗ₜ[R] ((tgtEquiv R A B).symm v)) =
      (tripleEquiv R A B).symm
        ((TensorProduct.assoc R A A B).symm (a ⊗ₜ[R] v)) := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw =>
    rw [map_add, tmul_add, map_add, hv, hw, tmul_add, map_add, map_add]
  | tmul a' y => rfl

variable (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
  (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
  (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)

include hleft hright in
/-- `ModuleCat.transition12` of `moduleTransition` is `cocycle12` up to the transports. -/
lemma transition12_apply (v : A ⊗[R] B) (c : A) :
    ModuleCat.transition12 R A (ModuleCat.of A B)
        (moduleTransition R A B θ hleft hright) (((tgtEquiv R A B).symm v) ⊗ₜ[R] c) =
      (tripleEquiv R A B).symm (cocycle12 R A B θ.toLinearMap (v ⊗ₜ[R] c)) := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw =>
    rw [map_add, add_tmul, map_add, hv, hw, add_tmul, map_add, map_add]
  | tmul a y =>
    rw [ModuleCat.transition12, cocycle12]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tgtEquiv_symm_tmul,
      TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, moduleTransition_restrictScalars,
      AlgEquiv.toLinearMap_apply]
    exact assoc_tgtEquiv R A B a (θ (y ⊗ₜ[R] c))

include hleft hright in
/-- `ModuleCat.transition02` of `moduleTransition` is `cocycle02` up to the transports. -/
lemma transition02_apply (x : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)))
    (b c : A) :
    ModuleCat.transition02 R A (ModuleCat.of A B)
        (moduleTransition R A B θ hleft hright) ((x ⊗ₜ[R] b) ⊗ₜ[R] c) =
      (tripleEquiv R A B).symm (cocycle02 R A B θ.toLinearMap
        ((restrictEquiv R A B x ⊗ₜ[R] b) ⊗ₜ[R] c)) := by
  rw [ModuleCat.transition02, cocycle02]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.rightComm_tmul,
    LinearMap.rTensor_tmul, moduleTransition_restrictScalars,
    transitionLinearEquiv_apply, srcEquiv_tmul, AlgEquiv.toLinearMap_apply]
  exact rightComm_tgtEquiv R A B (θ (restrictEquiv R A B x ⊗ₜ[R] c)) b

include hleft hright in
/-- `ModuleCat.transition01` of `moduleTransition` on a pure tensor `(x ⊗ₜ b) ⊗ₜ c`. -/
lemma transition01_apply (x : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)))
    (b c : A) :
    ModuleCat.transition01 R A (ModuleCat.of A B)
        (moduleTransition R A B θ hleft hright) ((x ⊗ₜ[R] b) ⊗ₜ[R] c) =
      ((tgtEquiv R A B).symm (θ (restrictEquiv R A B x ⊗ₜ[R] b))) ⊗ₜ[R] c := by
  rw [ModuleCat.transition01]
  simp only [LinearMap.rTensor_tmul, moduleTransition_restrictScalars]
  rfl

/-- The module descent datum of Tag 023G underlying an algebra transition. -/
def moduleDescentDatum
    (hcoc : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap) :
    ModuleCat.DescentData.{u, u, u} R A where
  module := ModuleCat.of A B
  transition := moduleTransition R A B θ hleft hright
  cocycle := by
    apply TensorProduct.ext'
    intro p c
    induction p using TensorProduct.inductionOn with
    | add p q hp hq => rw [add_tmul, map_add, map_add, hp, hq]
    | tmul x b =>
      rw [LinearMap.comp_apply, transition01_apply R A B θ hleft hright,
        transition12_apply R A B θ hleft hright,
        transition02_apply R A B θ hleft hright]
      congr 1
      conv_rhs => rw [← hcoc]
      rw [LinearMap.comp_apply, cocycle01, LinearMap.rTensor_tmul,
        AlgEquiv.toLinearMap_apply]

/-- The underlying module of `moduleDescentDatum` is `B`. -/
@[simp] lemma moduleDescentDatum_module
    (hcoc : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap) :
    (moduleDescentDatum R A B θ hleft hright hcoc).module = ModuleCat.of A B := rfl

/-! ### The invariant subalgebra -/

include hleft in
/-- The `R`-subalgebra of elements of `B` fixed by the transition isomorphism. -/
def invariantSubalgebra : Subalgebra R B where
  carrier := {b : B | θ (b ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] b}
  mul_mem' := by
    intro x y hx hy
    change θ ((x * y) ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] (x * y)
    change θ (x ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] x at hx
    change θ (y ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] y at hy
    rw [show (x * y) ⊗ₜ[R] (1 : A) = (x ⊗ₜ[R] (1 : A)) * (y ⊗ₜ[R] (1 : A)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], map_mul, hx, hy,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  one_mem' := by
    change θ ((1 : B) ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] (1 : B)
    rw [show (1 : B) ⊗ₜ[R] (1 : A) = 1 from rfl, map_one]
    rfl
  add_mem' := by
    intro x y hx hy
    change θ ((x + y) ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] (x + y)
    change θ (x ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] x at hx
    change θ (y ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] y at hy
    rw [add_tmul, map_add, hx, hy, tmul_add]
  zero_mem' := by
    change θ ((0 : B) ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] (0 : B)
    rw [zero_tmul, map_zero, tmul_zero]
  algebraMap_mem' := by
    intro r
    change θ ((algebraMap R B r) ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] (algebraMap R B r)
    have h1 : (algebraMap R B r) ⊗ₜ[R] (1 : A)
        = (algebraMap A B (algebraMap R A r)) ⊗ₜ[R] (1 : A) := by
      rw [← IsScalarTower.algebraMap_apply]
    rw [h1, hleft, Algebra.algebraMap_eq_smul_one (R := R) (A := A) r,
      TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

omit [IsScalarTower R A B] in
include hleft hright in
/-- An invariant element is compatible with the transition in the form required by
`ModuleCat.DescentData.IsEffective`: `θ ((a • c) ⊗ b) = a ⊗ (b • c)`. -/
lemma transition_smul_tmul_of_mem {c : B}
    (hc : θ (c ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] c) (a b : A) :
    θ ((a • c) ⊗ₜ[R] b) = a ⊗ₜ[R] (b • c) := by
  have hsrc : (a • c) ⊗ₜ[R] b =
      (algebraMap A B a ⊗ₜ[R] (1 : A)) * (c ⊗ₜ[R] (1 : A)) * ((1 : B) ⊗ₜ[R] b) := by
    rw [algebraMap_tmul_mul_tmul_mul_tmul, one_mul]
  rw [hsrc, map_mul, map_mul, hleft, hc, hright,
    tmul_mul_tmul_mul_tmul_algebraMap, mul_one]

include hleft in
/-- `b` lies in `invariantSubalgebra` if and only if `θ (b ⊗ₜ 1) = 1 ⊗ₜ b`. -/
lemma mem_invariantSubalgebra (b : B) :
    b ∈ invariantSubalgebra R A B θ hleft ↔
      θ (b ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] b := Iff.rfl

include hleft hright in
/-- An element lies in the invariant submodule of `moduleDescentDatum` if and only if its image
under `restrictEquiv` lies in `invariantSubalgebra`. -/
lemma mem_invariantSubmodule_iff
    (hcoc : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap)
    (x : ↑(ModuleCat.restrictModule R A (ModuleCat.of A B))) :
    x ∈ ModuleCat.invariantSubmodule R A (moduleDescentDatum R A B θ hleft hright hcoc) ↔
      restrictEquiv R A B x ∈ invariantSubalgebra R A B θ hleft := by
  rw [mem_invariantSubalgebra]
  change (moduleDescentDatum R A B θ hleft hright hcoc).transitionRestrictScalars R A
      (x ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] x ↔ _
  rw [show (moduleDescentDatum R A B θ hleft hright hcoc).transitionRestrictScalars R A
      (x ⊗ₜ[R] (1 : A)) = (tgtEquiv R A B).symm (θ (restrictEquiv R A B x ⊗ₜ[R] (1 : A)))
      from rfl,
    show ((1 : A) ⊗ₜ[R] x :
        A ⊗[R] ↑(ModuleCat.restrictModule R A (ModuleCat.of A B)))
      = (tgtEquiv R A B).symm ((1 : A) ⊗ₜ[R] restrictEquiv R A B x) from rfl]
  exact (tgtEquiv R A B).symm.injective.eq_iff

/-! ### Effective descent -/

include hleft hright in
/-- **The affine case of Stacks 0245.** Let `R → A` be a universally injective ring map and
let `B` be an `A`-algebra carrying a descent datum `θ` relative to `R → A`.  Then the invariants of
`θ` form an `R`-subalgebra `C` of `B` whose base change to `A` is `B`. -/
theorem exists_subalgebra_tensorEquiv
    (h : Algebra.UniversallyInjective R A)
    (hcoc : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap) :
    ∃ C : Subalgebra R B,
      (∀ b : B, b ∈ C ↔ θ (b ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] b) ∧
      ∃ e : (A ⊗[R] C) ≃ₐ[A] B,
        (∀ (a : A) (c : C), e (a ⊗ₜ[R] c) = a • (c : B)) ∧
        ∀ (a b : A) (c : C),
          θ ((e (a ⊗ₜ[R] c)) ⊗ₜ[R] b) = a ⊗ₜ[R] (e (b ⊗ₜ[R] c)) := by
  refine ⟨invariantSubalgebra R A B θ hleft, fun b ↦ Iff.rfl, ?_⟩
  have hmem := mem_invariantSubmodule_iff R A B θ hleft hright hcoc
  let sub : ↥(invariantSubalgebra R A B θ hleft) ≃ₗ[R]
      ↥(ModuleCat.invariantSubmodule R A (moduleDescentDatum R A B θ hleft hright hcoc)) :=
    { toFun := fun x ↦ ⟨x.1, (hmem x.1).mpr x.2⟩
      invFun := fun y ↦ ⟨y.1, (hmem y.1).mp y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ Subtype.ext (IsScalarTower.algebraMap_smul A r (x.1 : B)).symm }
  let full : (A ⊗[R] ↥(invariantSubalgebra R A B θ hleft)) ≃ₗ[R]
      (A ⊗[R] ↥(ModuleCat.invariantSubmodule R A (moduleDescentDatum R A B θ hleft hright hcoc))) :=
    TensorProduct.congr (LinearEquiv.refl R A) sub
  let counit := ModuleCat.descentCounitLinearEquiv R A h
    (moduleDescentDatum R A B θ hleft hright hcoc)
  let g : (A ⊗[R] ↥(invariantSubalgebra R A B θ hleft)) →ₐ[A] B :=
    Algebra.TensorProduct.lift (Algebra.ofId A B)
      (invariantSubalgebra R A B θ hleft).val (fun _ _ ↦ Commute.all _ _)
  have hgtmul : ∀ (a : A) (c : ↥(invariantSubalgebra R A B θ hleft)),
      g (a ⊗ₜ[R] c) = a • (c : B) := fun a c ↦ by
    rw [Algebra.smul_def]
    exact Algebra.TensorProduct.lift_tmul _ _ _ a c
  have hg : ∀ z, g z = counit (full z) := fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]; rfl
    | tmul a c =>
      rw [hgtmul, show full (a ⊗ₜ[R] c) = a ⊗ₜ[R] sub c from
        TensorProduct.congr_tmul _ _ _ _]
      exact (ModuleCat.descentCounitLinearEquiv_tmul R A h
        (moduleDescentDatum R A B θ hleft hright hcoc) a (sub c)).symm
  have hbij : Function.Bijective g := funext hg ▸
    (counit.bijective.comp full.bijective : Function.Bijective (fun z ↦ counit (full z)))
  refine ⟨AlgEquiv.ofBijective g hbij, hgtmul, fun a b c ↦ ?_⟩
  change θ (g (a ⊗ₜ[R] c) ⊗ₜ[R] b) = a ⊗ₜ[R] g (b ⊗ₜ[R] c)
  rw [hgtmul, hgtmul]
  exact transition_smul_tmul_of_mem R A B θ hleft hright c.2 a b

/-- A faithfully flat ring map is universally injective: the special case of Tag 05CK that
`Algebra.UniversallyInjective` is phrased in. -/
theorem universallyInjective_of_faithfullyFlat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] :
    Algebra.UniversallyInjective R A := by
  intro Q _ _
  rw [← LinearMap.exact_zero_iff_injective PUnit.{1}]
  refine Module.FaithfullyFlat.lTensor_reflects_exact R A 0 _ ?_
  rw [LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective]
  exact lTensor_rTensor_algebraMap_injective

include hleft hright in
/-- **The affine case of Stacks 0245 along a faithfully flat ring map.**  This is the form in
which an fpqc covering by a single affine supplies the hypothesis. -/
theorem exists_subalgebra_tensorEquiv_of_faithfullyFlat [Module.FaithfullyFlat R A]
    (hcoc : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap) :
    ∃ C : Subalgebra R B,
      (∀ b : B, b ∈ C ↔ θ (b ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] b) ∧
      ∃ e : (A ⊗[R] C) ≃ₐ[A] B,
        (∀ (a : A) (c : C), e (a ⊗ₜ[R] c) = a • (c : B)) ∧
        ∀ (a b : A) (c : C),
          θ ((e (a ⊗ₜ[R] c)) ⊗ₜ[R] b) = a ⊗ₜ[R] (e (b ⊗ₜ[R] c)) :=
  exists_subalgebra_tensorEquiv R A B θ hleft hright
    universallyInjective_of_faithfullyFlat hcoc

end Stacks.AlgebraDescent

end

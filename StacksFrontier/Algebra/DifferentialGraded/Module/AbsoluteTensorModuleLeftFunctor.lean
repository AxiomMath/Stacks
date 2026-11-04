module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModule

/-!
# The absolute tensor product is a functor in its left variable

Let `R` be a commutative ring, let `(A, d)` and `(B, d)` be differential graded `R`-algebras and
let `N` be a right differential graded `B`-module. Tensoring over the base ring with `N` on the
right,

`L ↦ DifferentialGradedModule.absoluteTensorModule L N`,

is a functor `Mod_(A, d) ⥤ Mod_(B, d)`: a homomorphism `φ : L ⟶ L'` of right differential graded
`A`-modules induces `φ ⊗ 1 : L ⊗_R N ⟶ L' ⊗_R N`.

Nothing about the left factor beyond its grading and its differential is used, exactly as for the
object `DifferentialGradedModule.absoluteTensorModule` itself. A homomorphism of differential
graded modules has degree zero, so no Koszul sign enters: `φ ⊗ 1` commutes with
`d_L ⊗ 1 + (-1)^deg ⊗ d_N` because `φ` commutes with `d_L` and preserves the grading, so it
commutes with the sign operator `DifferentialGradedModule.absKoszulSign` as well.

## Main definitions

* `DifferentialGradedModule.absModLeftMap`: **the action on morphisms**, `φ ⊗ 1`.
* `DifferentialGradedModule.absoluteTensorLeftFunctor`: **the absolute tensor product with `N` as
  a functor in its left variable**, `Mod_(A, d) ⥤ Mod_(B, d)`.

## Main results

* `DifferentialGradedModule.absModLeftMap_tmul`: the induced map on a pure tensor.
* `DifferentialGradedModule.absKoszulSign_comp`: a degree-preserving map commutes with the Koszul
  sign operator.

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) is the notion of a
  differential graded module and of a homomorphism of such, and
  [Tag 065W](https://stacks.math.columbia.edu/tag/065W) the signed tensor differential.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedModule

attribute [local instance] absModRightModule absModRightScalarTower absModDecomposition

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The Koszul sign is natural -/

/-- A homomorphism of differential graded modules has degree zero, so it commutes with the
operator that multiplies the degree-`p` part by `(-1)^p`. -/
theorem absKoszulSign_comp {L L' : DifferentialGradedModule.{u, u, u} A} (φ : L ⟶ L') :
    φ.toFun ∘ₗ absKoszulSign L = absKoszulSign L' ∘ₗ φ.toFun := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn L.grading with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]
  | @homogeneous p x =>
    have hx : φ.toFun (x : L.M) ∈ L'.grading p := φ.map_grading p x x.property
    have hL' : absKoszulSign L' (φ.toFun (x : L.M)) =
        (p.negOnePow : ℤ) • φ.toFun (x : L.M) :=
      absKoszulSign_apply_coe L' p ⟨φ.toFun (x : L.M), hx⟩
    simp only [LinearMap.comp_apply, absKoszulSign_apply_coe, hL', map_zsmul]

/-! ### The action on morphisms -/

/-- **The absolute tensor product on morphisms in the left variable**: a homomorphism
`φ : L ⟶ L'` of right differential graded `A`-modules induces `φ ⊗ 1 : L ⊗_R N ⟶ L' ⊗_R N`. -/
def absModLeftMap {L L' : DifferentialGradedModule.{u, u, u} A} (φ : L ⟶ L')
    (N : DifferentialGradedModule.{u, u, u} B) :
    absoluteTensorModule L N ⟶ absoluteTensorModule L' N where
  toFun := TensorProduct.map φ.toFun LinearMap.id
  map_smul z b := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [smul_add, map_add, hu, hv]
    | tmul u v =>
      rw [absMod_smul_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply, absMod_smul_tmul]
  map_grading n z hz := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, q, u, v, hu, hv, rfl, rfl⟩ := hz
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
      exact absModTmul_mem L' N p q _ _ (φ.map_grading p u hu) hv
    | zero => simp
    | add u v hu hv ihu ihv => simpa only [map_add] using Submodule.add_mem _ ihu ihv
    | smul r u hu ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
  map_d := by
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.map φ.toFun LinearMap.id (absModDifferential L N (x ⊗ₜ[R] y)) =
      absModDifferential L' N (TensorProduct.map φ.toFun LinearMap.id (x ⊗ₜ[R] y))
    induction x using DirectSum.Decomposition.inductionOn L.grading with
    | zero => simp
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
    | @homogeneous p x =>
      have hx : φ.toFun (x : L.M) ∈ L'.grading p := φ.map_grading p x x.property
      have hd : φ.toFun (L.d (x : L.M)) = L'.d (φ.toFun (x : L.M)) :=
        LinearMap.congr_fun φ.map_d (x : L.M)
      have key : absModDifferential L' N (φ.toFun (x : L.M) ⊗ₜ[R] y) =
          (L'.d (φ.toFun (x : L.M)) ⊗ₜ[R] y : L'.M ⊗[R] N.M) +
            (p.negOnePow : ℤ) • (φ.toFun (x : L.M) ⊗ₜ[R] N.d y) :=
        absModDifferential_tmul L' N p ⟨φ.toFun (x : L.M), hx⟩ y
      rw [absModDifferential_tmul]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, map_add, map_zsmul, key, hd]

/-- The map `φ ⊗ 1` sends a pure tensor `x ⊗ y` to `φ x ⊗ y`. -/
@[simp]
theorem absModLeftMap_tmul {L L' : DifferentialGradedModule.{u, u, u} A} (φ : L ⟶ L')
    (N : DifferentialGradedModule.{u, u, u} B) (x : L.M) (y : N.M) :
    (absModLeftMap φ N).toFun (x ⊗ₜ[R] y) = φ.toFun x ⊗ₜ[R] y := by
  rw [show (absModLeftMap φ N).toFun = TensorProduct.map φ.toFun LinearMap.id from rfl,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- Two homomorphisms out of `L ⊗_R N` agree if they agree on pure tensors. -/
private theorem absoluteTensorModule_hom_ext {L : DifferentialGradedModule.{u, u, u} A}
    {N M : DifferentialGradedModule.{u, u, u} B} {f g : absoluteTensorModule L N ⟶ M}
    (h : ∀ (x : L.M) (y : N.M), f.toFun (x ⊗ₜ[R] y) = g.toFun (x ⊗ₜ[R] y)) : f = g :=
  DifferentialGradedModule.Hom.ext (TensorProduct.ext' h)

/-- The identity of `L` induces the identity of `L ⊗_R N`. -/
theorem absModLeftMap_id (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) :
    absModLeftMap (𝟙 L) N = 𝟙 (absoluteTensorModule L N) := by
  exact absoluteTensorModule_hom_ext fun x y => by simp; rfl

/-- The map induced by a composite is the composite of the induced maps:
`(φ ≫ ψ) ⊗ 1 = (φ ⊗ 1) ≫ (ψ ⊗ 1)`. -/
theorem absModLeftMap_comp {L L' L'' : DifferentialGradedModule.{u, u, u} A} (φ : L ⟶ L')
    (ψ : L' ⟶ L'') (N : DifferentialGradedModule.{u, u, u} B) :
    absModLeftMap (φ ≫ ψ) N = absModLeftMap φ N ≫ absModLeftMap ψ N := by
  exact absoluteTensorModule_hom_ext fun x y => by simp; rfl

/-! ### The functor -/

/-- **The absolute tensor product with `N` is a functor in its left variable.** The right
differential graded `B`-module `L ⊗_R N`, with `B` acting on the second factor and with the
signed tensor differential, depends functorially on the right differential graded `A`-module
`L`. -/
def absoluteTensorLeftFunctor (N : DifferentialGradedModule.{u, u, u} B) :
    DifferentialGradedModule.{u, u, u} A ⥤ DifferentialGradedModule.{u, u, u} B where
  obj L := absoluteTensorModule L N
  map φ := absModLeftMap φ N
  map_id L := absModLeftMap_id L N
  map_comp φ ψ := absModLeftMap_comp φ ψ N

/-- The functor `absoluteTensorLeftFunctor N` sends `L` to `L ⊗_R N`. -/
@[simp]
theorem absoluteTensorLeftFunctor_obj (N : DifferentialGradedModule.{u, u, u} B)
    (L : DifferentialGradedModule.{u, u, u} A) :
    (absoluteTensorLeftFunctor (A := A) N).obj L = absoluteTensorModule L N := rfl

/-- The functor `absoluteTensorLeftFunctor N` sends a homomorphism `φ` to `φ ⊗ 1`. -/
@[simp]
theorem absoluteTensorLeftFunctor_map {L L' : DifferentialGradedModule.{u, u, u} A} (φ : L ⟶ L')
    (N : DifferentialGradedModule.{u, u, u} B) :
    (absoluteTensorLeftFunctor N).map φ = absModLeftMap φ N := rfl

end DifferentialGradedModule

end

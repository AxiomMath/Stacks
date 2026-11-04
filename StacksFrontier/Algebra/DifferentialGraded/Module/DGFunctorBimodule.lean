module

public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismBimodule
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Evaluation

/-!
# The bimodule a functor of differential graded categories attaches to an object

Let `C` be a differential graded category over a commutative ring `R`, let `x` be an object of
`C` with endomorphism differential graded algebra `A = End(x)` (Tag 09LE), and let
`G : C ⥤ Mod^dg_(B, d)` be a functor of differential graded categories into the right
differential graded modules over a differential graded `R`-algebra `B`. Then `G(x)` is a
differential graded `(A, B)`-bimodule: a homogeneous `a ∈ A^n` is a degree-`n` endomorphism of
`x`, and it acts on `G(x)` through the degree-`n` homogeneous right `B`-linear map `G(a)`.

The case of interest is `G = Hom_C(y, -)`, the representable functor of a second object `y`
with `B = End(y)`: then `G(x) = Hom_C(y, x)` with `A` acting by postcomposition and `B` by
precomposition.

## Main definitions

* `DGCategory.DGFunctor.mapₗ`: the action of a functor on a Hom module, as an `R`-linear map.
* `DifferentialGradedModule.dgFunctorLeftAction`: the left action of `End(x)` on `G(x)`.
* `DifferentialGraded.Bimodule.ofDGFunctor`: `G(x)` as a differential graded
  `(End(x), B)`-bimodule.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
* [Stacks Project, Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v w

namespace DGCategory

variable {R : Type*} [CommRing R]

/-- The action of a functor of differential graded categories on a Hom module, as an `R`-linear
map. -/
def DGFunctor.mapₗ {A B : DGCategory R} (F : DGFunctor A B) (x y : A.Obj) (n : ℤ) :
    A.Hom x y n →ₗ[R] B.Hom (F.obj x) (F.obj y) n where
  toFun := F.map
  map_add' := F.map_add
  map_smul' := F.map_smul

/-- The linear map `F.mapₗ x y n` sends a morphism `f` to `F.map f`. -/
@[simp] theorem DGFunctor.mapₗ_apply {A B : DGCategory R} (F : DGFunctor A B) {x y : A.Obj}
    {n : ℤ} (f : A.Hom x y n) : F.mapₗ x y n f = F.map f := rfl

end DGCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {C : DGCategory.{u, v, u} R} {x : C.Obj}
  (Rx : DGCategory.HomRepresentation C x) {B : DifferentialGradedAlgebra.{u, u} R}
  (G : DGCategory.DGFunctor C (dgCategory.{u, u, u} B))

/-- **The left action of `End(x)` on `G(x)`.** A degree-`n` element of the endomorphism algebra
of `x` is a degree-`n` endomorphism of `x`; it acts on the complex underlying `G(x)` through the
cochain of the homogeneous map `G(a)`. -/
def dgFunctorLeftAction : Rx.algebra.LeftAction (G.obj x).toCochainComplex where
  action n := (homogeneousMapToCochainₗ B (G.obj x) (G.obj x) n).comp
    ((G.mapₗ x x n).comp (Rx.algebraHom n).toLinearMap)
  map_one := by
    obtain ⟨e, he, hid⟩ := Rx.algebra_one
    have he' : (⟨1, SetLike.one_mem_graded Rx.algebra.grading⟩ : Rx.algebra.grading 0) = e :=
      Subtype.ext he.symm
    change homogeneousMapToCochain B (G.map (Rx.algebraHom 0 _)) = _
    rw [he', hid, G.map_id]
    exact homogeneousMapToCochain_id B (G.obj x)
  map_mul n m a b := by
    obtain ⟨c, hc, hcomp⟩ := Rx.algebra_mul n m (n + m) rfl a b
    have hc' : (⟨(a : Rx.algebra.A) * (b : Rx.algebra.A),
        SetLike.mul_mem_graded a.property b.property⟩ : Rx.algebra.grading (n + m)) = c :=
      Subtype.ext hc.symm
    change homogeneousMapToCochain B (G.map (Rx.algebraHom (n + m) _)) = _
    rw [hc', hcomp, G.map_comp]
    exact homogeneousMapToCochain_comp B rfl _ _
  map_d n a := by
    change homogeneousMapToCochain B (G.map (Rx.algebraHom (n + 1) _)) = _
    rw [Rx.algebra_d n a, G.map_d]
    exact homogeneousMapToCochain_d B _

/-- A homogeneous `a ∈ End(x)^n` acts on `G(x)` through the cochain of the homogeneous map
`G(a)`. -/
theorem dgFunctorLeftAction_action (n : ℤ) (a : Rx.algebra.grading n) :
    (dgFunctorLeftAction Rx G).action n a =
      homogeneousMapToCochain B (G.map (Rx.algebraHom n a)) :=
  rfl

/-- The left action of `End(x)` on `G(x)` is by right `B`-linear cochains, so it is a
differential graded bimodule structure (Tag 0FQI). -/
def dgFunctorBimoduleStructure : BimoduleStructure Rx.algebra B (G.obj x) :=
  ⟨dgFunctorLeftAction Rx G, fun n a =>
    isRightLinearCochain_homogeneousMapToCochain B (G.obj x) (G.map (Rx.algebraHom n a))⟩

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {C : DGCategory.{u, v, u} R} {x : C.Obj}
  (Rx : DGCategory.HomRepresentation C x) {B : DifferentialGradedAlgebra.{u, u} R}
  (G : DGCategory.DGFunctor C (dgCategory.{u, u, u} B))

/-- **`G(x)` as a differential graded `(End(x), B)`-bimodule.** The right module is `G(x)` and a
homogeneous `a ∈ End(x)^n` acts on the left through `G(a)`. -/
@[implicit_reducible]
def ofDGFunctor : Bimodule Rx.algebra B where
  rightModule := G.obj x
  leftAction := dgFunctorBimoduleStructure Rx G

/-- The right module underlying `ofDGFunctor Rx G` is `G(x)`. -/
@[simp] theorem ofDGFunctor_rightModule : (ofDGFunctor Rx G).rightModule = G.obj x := rfl

/-- Left multiplication by a homogeneous `a ∈ End(x)^n` on `G(x)` is `G(a)`, on a homogeneous
element. -/
theorem ofDGFunctor_action_v (n p : ℤ) (a : Rx.algebra.grading n) (y : (G.obj x).grading p) :
    ((show (G.obj x).grading (p + n) from
        ((ofDGFunctor Rx G).leftAction.1.action n a).v p (p + n) rfl y) : (G.obj x).M) =
      (G.map (Rx.algebraHom n a)).1 y :=
  rfl

end DifferentialGraded.Bimodule

end

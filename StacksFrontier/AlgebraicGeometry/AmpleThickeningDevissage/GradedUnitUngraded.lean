module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPullCommutative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPullUnital
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedFunctorial

/-!
# The ungraded realization of `A ⟶ v_* v^* A`

Let `v : V ⟶ X` be a morphism of schemes and `A` a sheaf of graded `𝒪_X`-algebras whose
homogeneous multiplication commutes in every pair of degrees. The canonical homomorphism of
sheaves of graded algebras `A ⟶ v_* v^* A` is the unit of
`Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction`
(`Stacks.PushforwardGradedAlgebra.gradedUnit`), and it is the surjection
`⨁_m A_m ⟶ ⨁_m v_* v^* A_m` of the graded arguments of [Stacks, Tag 09MS].

This file assembles its **ungraded** realization: a morphism of sheaves of commutative
`𝒪_X`-algebras between the ungraded realizations of the two sheaves of graded algebras. Two
things were needed and both are now available.

* `Stacks.RelativeSpec.ungradedAlgebraSheafMap` takes a
  `SheafOfModules.GradedAlgebra.UnitalHom`, and the graded unit is a
  `SheafOfModules.GradedAlgebra.Hom`, which does not carry the unit law. The upgrade is
  `Stacks.PushforwardGradedAlgebra.gradedUnitUnitalHom`.
* It also takes the commutativity of homogeneous multiplication *of the target*, since the
  ungraded realization is a sheaf of commutative rings. That is
  `Stacks.PushforwardGradedAlgebra.pushforwardPullback_mul_comm`.

At `A = Sym(L)` for an invertible `L` the source is the algebra sheaf of the line bundle,
`Stacks.LineBundle.Situation.algebraSheaf`, whose relative spectrum is the total space, and the
pieces of `A` are the tensor powers `L^{⊗ m}`; so the morphism below is the ungraded form of
`⨁_m L^{⊗ m} ⟶ ⨁_m v_* v^* L^{⊗ m}`.

## Main definitions

* `Stacks.AmpleThickeningDevissage.pushforwardPullbackGradedAlgebra`: `v_* v^* A` as a sheaf of
  graded `𝒪_X`-algebras, for a morphism of schemes.
* `Stacks.AmpleThickeningDevissage.ungradedGradedUnitMap`: **the ungraded realization of
  `A ⟶ v_* v^* A`, as a morphism of sheaves of commutative `𝒪_X`-algebras.**
* `Stacks.AmpleThickeningDevissage.Situation.ungradedGradedUnitMap`: the same at `A = Sym(L)`,
  with the algebra sheaf of the line bundle as its source.

## Main results

* `Stacks.AmpleThickeningDevissage.pushforwardPullbackGradedAlgebra_mul_comm`: homogeneous
  multiplication in `v_* v^* A` commutes in every pair of degrees whenever it does in `A`.
* `Stacks.AmpleThickeningDevissage.ungradedGradedUnitMap_incl`: **the ungraded realization
  carries a homogeneous local section of degree `n` to the image of that section under the
  degree-`n` component of the graded unit**, which is what ties it to everything known about the
  graded unit degreewise — in particular to its kernel
  `Stacks.AmpleThickeningDevissage.kernelSubmodule_gradedUnit_app` and to its local
  surjectivity (`Stacks.AmpleThickeningDevissage.epi_gradedUnit_app_of_isClosedImmersion` for a
  closed immersion, `Stacks.PushforwardGradedAlgebra.epi_gradedUnit_app_of_generatingSections`
  under global generation of the piece).

## Scope

**No `stacks` attribute is attached.** What is here is the push–pull graded algebra `v_* v^* A`,
the commutativity of its multiplication, and the graded unit `A ⟶ v_* v^* A`. The twisted Čech
argument of `StacksFrontier/AlgebraicGeometry/TwistedThickeningLift/` uses the degreewise unit,
through the sections over affine opens (`GradedUnitClosedSurjective.lean`) and through its
multiplicativity on homogeneous sections.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 0B8S](https://stacks.math.columbia.edu/tag/0B8S)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe u

namespace Stacks.AmpleThickeningDevissage

/-! ### `v_* v^* A` for a morphism of schemes -/

variable {V X : Scheme.{u}} (v : V ⟶ X)
  (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

/-- **`v_* v^* A` as a sheaf of graded `𝒪_X`-algebras**, for a morphism of schemes: the
pushforward along `v` of the pullback along `v`, both taken at the underlying morphism of ringed
spaces, which is the target of `Stacks.PushforwardGradedAlgebra.gradedUnit`. -/
def pushforwardPullbackGradedAlgebra : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra v.toLRSHom.toShHom
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra v.toLRSHom.toShHom A
      (structureSheafRing _).property)

/-- The homogeneous pieces of `v_* v^* A` are the direct images of the pullbacks of those of
`A`. -/
theorem pushforwardPullbackGradedAlgebra_piece (n : ℤ) :
    (pushforwardPullbackGradedAlgebra v A).piece n =
      (pushforwardFunctor v.toLRSHom.toShHom).obj
        ((pullbackFunctor v.toLRSHom.toShHom).obj (A.piece n)) :=
  rfl

/-- **Homogeneous multiplication in `v_* v^* A` commutes in every pair of degrees** whenever it
does in `A`. This is the hypothesis the ungraded realization as a sheaf of *commutative* rings
takes of the target of the graded unit. -/
theorem pushforwardPullbackGradedAlgebra_mul_comm
    (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
    (i j : ℤ) (U : (Opens X)ᵒᵖ)
    (x : ((pushforwardPullbackGradedAlgebra v A).piece i).val.obj U)
    (y : ((pushforwardPullbackGradedAlgebra v A).piece j).val.obj U) :
    HEq (((pushforwardPullbackGradedAlgebra v A).mul i j).app U x y)
      (((pushforwardPullbackGradedAlgebra v A).mul j i).app U y x) :=
  Stacks.PushforwardGradedAlgebra.pushforwardPullback_mul_comm v.toLRSHom.toShHom A hA i j U x y

/-! ### The ungraded realization of the graded unit -/

variable (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U)
  (y : (A.piece j).val.obj U), HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))

/-- **The ungraded realization of `A ⟶ v_* v^* A`, as a morphism of sheaves of commutative
`𝒪_X`-algebras.** Its source is the ungraded realization of `A`, whose relative spectrum is the
total space in the case `A = Sym(L)`. -/
def ungradedGradedUnitMap :
    Stacks.RelativeSpec.ungradedAlgebraSheaf X A hA ⟶
      Stacks.RelativeSpec.ungradedAlgebraSheaf X (pushforwardPullbackGradedAlgebra v A)
        (pushforwardPullbackGradedAlgebra_mul_comm v A hA) :=
  Stacks.RelativeSpec.ungradedAlgebraSheafMap X A (pushforwardPullbackGradedAlgebra v A) hA
    (pushforwardPullbackGradedAlgebra_mul_comm v A hA)
    (Stacks.PushforwardGradedAlgebra.gradedUnitUnitalHom v.toLRSHom.toShHom A)

/-- **The ungraded realization of the graded unit carries a homogeneous local section of degree
`n` to the image of that section under the degree-`n` component of the graded unit.** This
characterizes it, and it is what makes everything known about
`Stacks.PushforwardGradedAlgebra.gradedUnit` degreewise — its kernel
(`Stacks.AmpleThickeningDevissage.kernelSubmodule_gradedUnit_app`) and its local surjectivity
(`Stacks.PushforwardGradedAlgebra.epi_gradedUnit_app_of_generatingSections`) — a statement about
this morphism. -/
theorem ungradedGradedUnitMap_incl (n : ℤ) (U : X.Opens) (x : (A.piece n).val.obj (op U)) :
    ((ungradedGradedUnitMap v A hA).right.hom.app (op U)).hom
        (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X A hA n U x) =
      Stacks.RelativeSpec.ungradedAlgebraSheafIncl X (pushforwardPullbackGradedAlgebra v A)
        (pushforwardPullbackGradedAlgebra_mul_comm v A hA) n U
        (((Stacks.PushforwardGradedAlgebra.gradedUnit v.toLRSHom.toShHom A).app n).val.app
          (op U) x) :=
  Stacks.RelativeSpec.ungradedAlgebraSheafMap_incl X A (pushforwardPullbackGradedAlgebra v A) hA
    (pushforwardPullbackGradedAlgebra_mul_comm v A hA)
    (Stacks.PushforwardGradedAlgebra.gradedUnitUnitalHom v.toLRSHom.toShHom A) n U x

/-! ### The case of the symmetric algebra of a line bundle -/

namespace Situation

variable (D : Stacks.LineBundle.Situation.{u}) {W : Scheme.{u}} (w : W ⟶ D.X)

/-- **The ungraded realization of `Sym(L) ⟶ w_* w^* Sym(L)`**, whose source is the algebra sheaf
of the line bundle. In degree `m` the graded unit is the module-level unit at `L^{⊗ m}`, so this
is the ungraded form of `⨁_m L^{⊗ m} ⟶ ⨁_m w_* w^* L^{⊗ m}` — the surjection of the graded
square-zero extension of [Stacks, Tag 09MS]. -/
def ungradedGradedUnitMap :
    D.algebraSheaf ⟶
      Stacks.RelativeSpec.ungradedAlgebraSheaf D.X
        (pushforwardPullbackGradedAlgebra w D.symmetricAlgebra)
        (pushforwardPullbackGradedAlgebra_mul_comm w D.symmetricAlgebra
          D.symmetricAlgebra_mul_comm) :=
  Stacks.AmpleThickeningDevissage.ungradedGradedUnitMap w D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm

/-- The ungraded realization of `Sym(L) ⟶ w_* w^* Sym(L)` on a homogeneous local section of
degree `m`. -/
theorem ungradedGradedUnitMap_incl (m : ℤ) (U : D.X.Opens)
    (x : (D.symmetricAlgebra.piece m).val.obj (op U)) :
    ((Situation.ungradedGradedUnitMap D w).right.hom.app (op U)).hom (D.algebraSheafIncl m U x) =
      Stacks.RelativeSpec.ungradedAlgebraSheafIncl D.X
        (pushforwardPullbackGradedAlgebra w D.symmetricAlgebra)
        (pushforwardPullbackGradedAlgebra_mul_comm w D.symmetricAlgebra
          D.symmetricAlgebra_mul_comm) m U
        (((Stacks.PushforwardGradedAlgebra.gradedUnit w.toLRSHom.toShHom
          D.symmetricAlgebra).app m).val.app (op U) x) :=
  Stacks.AmpleThickeningDevissage.ungradedGradedUnitMap_incl w D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm m U x

end Situation

end Stacks.AmpleThickeningDevissage

end

module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge

/-!
# The direct image of a sheaf of graded algebras along a morphism of schemes

For a morphism of schemes `p : X ⟶ S` and a sheaf `A` of graded `𝒪_X`-algebras, this file
constructs the direct image `p_*A` as a sheaf of graded `𝒪_S`-algebras, with homogeneous pieces
the direct images `p_*(A_n)`.

## Main definitions

* `Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardMul`: the multiplication of
  `p_*A`, as an `𝒪_S`-bilinear map of the direct images.
* `Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardOne`: the unit of `p_*A`.
* `Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra`: `p_*A` as a
  `SheafOfModules.GradedAlgebra S.ringCatSheaf`.
* `Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardSheafGradedAlgebra`: `p_*A` as
  sheaf-level graded algebra data on `S` in the sense of Situation 01NN, given commutativity,
  concentration in nonnegative degrees and quasi-coherence of the direct images.

## Main results

* `pushforwardGradedAlgebra_piece`, `pushforwardGradedAlgebra_mul_app` and
  `pushforwardGradedAlgebra_one_eval`: the pieces, the multiplication and the unit of `p_*A` are
  those of `A` over the inverse-image opens.
* `isCommutative_pushforwardGradedAlgebra` and
  `vanishesInNegativeDegrees_pushforwardGradedAlgebra`: commutativity and concentration in
  nonnegative degrees are inherited by the direct image.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

namespace Stacks.AlgebraicGeometry.PushforwardGradedAlgebra

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S)
  (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

/-! ### The multiplication and the unit of the direct image -/

/-- **The multiplication of `p_*A`**: over an open `U` of `S` it is the multiplication of `A`
over `p ⁻¹ᵁ U`. -/
def pushforwardMul (i j : ℤ) :
    SheafOfModules.BilinearMap.{u, u, u, u, u}
      ((Scheme.Modules.pushforward p).obj (A.piece i))
      ((Scheme.Modules.pushforward p).obj (A.piece j))
      ((Scheme.Modules.pushforward p).obj (A.piece (i + j))) where
  app U := (A.mul i j).app (op (p ⁻¹ᵁ U.unop))
  map_smul_left U _ x y := (A.mul i j).map_smul_left (op (p ⁻¹ᵁ U.unop)) _ x y
  map_smul_right U _ x y := (A.mul i j).map_smul_right (op (p ⁻¹ᵁ U.unop)) _ x y
  naturality f x y := (A.mul i j).naturality ((Opens.map p.base).op.map f) x y

/-- **The unit of `p_*A`**: the unit of `A`, read over the inverse images of the opens of `S`. -/
def pushforwardOne :
    ((Scheme.Modules.pushforward p).obj (A.piece 0)).sections :=
  PresheafOfModules.sectionsMk (fun U ↦ A.one.eval (op (p ⁻¹ᵁ U.unop)))
    (fun {_ _} f ↦ PresheafOfModules.sections_property A.one ((Opens.map p.base).op.map f))

/-! ### The direct image as a sheaf of graded algebras -/

/-- **The direct image `p_*A` of a sheaf of graded algebras along a morphism of schemes**, with
homogeneous pieces the direct images `p_*(A_n)`. -/
def pushforwardGradedAlgebra : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf where
  piece n := (Scheme.Modules.pushforward p).obj (A.piece n)
  mul i j := pushforwardMul p A i j
  one := pushforwardOne p A
  mul_assoc i j k U x y z := A.mul_assoc i j k (op (p ⁻¹ᵁ U.unop)) x y z
  one_mul i U x := A.one_mul i (op (p ⁻¹ᵁ U.unop)) x
  mul_one i U x := A.mul_one i (op (p ⁻¹ᵁ U.unop)) x

/-- The pieces of `p_*A` are the direct images of the pieces of `A`. -/
theorem pushforwardGradedAlgebra_piece (n : ℤ) :
    (pushforwardGradedAlgebra p A).piece n = (Scheme.Modules.pushforward p).obj (A.piece n) :=
  rfl

/-- The multiplication of `p_*A` over an open of `S` is the multiplication of `A` over its
inverse image. -/
theorem pushforwardGradedAlgebra_mul_app (i j : ℤ) (U : (S.Opens)ᵒᵖ) :
    ((pushforwardGradedAlgebra p A).mul i j).app U = (A.mul i j).app (op (p ⁻¹ᵁ U.unop)) :=
  rfl

/-- The unit of `p_*A` over an open of `S` is the unit of `A` over its inverse image. -/
theorem pushforwardGradedAlgebra_one_eval (U : (S.Opens)ᵒᵖ) :
    (pushforwardGradedAlgebra p A).one.eval U = A.one.eval (op (p ⁻¹ᵁ U.unop)) :=
  rfl

/-! ### Commutativity and concentration in nonnegative degrees -/

/-- **Commutativity is inherited by the direct image.** -/
theorem isCommutative_pushforwardGradedAlgebra (hcomm : IsCommutative A) :
    IsCommutative (pushforwardGradedAlgebra p A) :=
  fun i j U a b ↦ hcomm i j (op (p ⁻¹ᵁ U.unop)) a b

/-- **Concentration in nonnegative degrees is inherited by the direct image.** -/
theorem vanishesInNegativeDegrees_pushforwardGradedAlgebra
    (hneg : VanishesInNegativeDegrees A) :
    VanishesInNegativeDegrees (pushforwardGradedAlgebra p A) :=
  fun n hn U x ↦ hneg n hn (op (p ⁻¹ᵁ U.unop)) x

/-- **`p_*A` as sheaf-level graded algebra data on `S`** in the sense of Situation 01NN, for `A`
commutative and concentrated in nonnegative degrees, with quasi-coherent direct images
`p_*(A_n)`. -/
def pushforwardSheafGradedAlgebra (hcomm : IsCommutative A)
    (hneg : VanishesInNegativeDegrees A)
    (hqc : ∀ n : ℤ,
      (((Scheme.Modules.pushforward p).obj (A.piece n) : S.Modules)).IsQuasicoherent) :
    SheafGradedAlgebra S :=
  toSheafGradedAlgebra (pushforwardGradedAlgebra p A)
    (isCommutative_pushforwardGradedAlgebra p A hcomm)
    (vanishesInNegativeDegrees_pushforwardGradedAlgebra p A hneg) hqc

/-- The pieces of `pushforwardSheafGradedAlgebra` are the direct images `p_*(A_n)`. -/
theorem pushforwardSheafGradedAlgebra_piece (hcomm : IsCommutative A)
    (hneg : VanishesInNegativeDegrees A)
    (hqc : ∀ n : ℤ, (((Scheme.Modules.pushforward p).obj (A.piece n) : S.Modules)).IsQuasicoherent)
    (n : ℤ) :
    (pushforwardSheafGradedAlgebra p A hcomm hneg hqc).piece n =
      (Scheme.Modules.pushforward p).obj (A.piece n) :=
  rfl

end Stacks.AlgebraicGeometry.PushforwardGradedAlgebra

end

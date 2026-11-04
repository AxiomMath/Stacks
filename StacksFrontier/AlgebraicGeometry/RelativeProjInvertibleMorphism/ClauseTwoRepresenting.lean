module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjRepresents

/-!
# The morphism the relative homogeneous spectrum attaches to a quadruple

The morphism `W ⟶ Proj_S(𝒜)` that the representation of the functor `F` of [Stacks, Tag 01NX]
attaches to a point of `F(W)`, and its value on a quadruple of one degree.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

variable {S W : Scheme.{u}} (A : SheafGradedAlgebra.{u} S)

/-- **The point of the extended functor of the display 01NX attached to a point of `F(W)`**: at a
morphism `g : W' ⟶ W` out of a quasi-compact scheme, the pullback of the point. -/
def F.toLim (ξ : F (situationAlgebra A) W) : (F.limFunctor (situationAlgebra A)).obj (op W) where
  val _ _ g := F.pullback g ξ
  compat _ _ _ _ h g := (F.pullback_comp g h ξ).symm

/-- **The morphism `W ⟶ Proj_S(𝒜)` which the construction of the relative homogeneous spectrum
attaches to a point of `F(W)`**: the representing bijection of [Stacks, Tag 01NZ] applied to it. -/
def F.classifyingMorphism (ξ : F (situationAlgebra A) W) : W ⟶ (relativeProj A).scheme :=
  (relativeProjRepresentableByFunctorUnconditional A).homEquiv.symm (F.toLim A ξ)

/-- **On a point of one degree `k`, the morphism is the one into the degree-`k` open** of the
relative homogeneous spectrum given by the chart-wise representation of [Stacks, Tag 01NU],
followed by the canonical identification of [Stacks, Tag 01NZ]. -/
theorem F.classifyingMorphism_mk {g : W ⟶ S} {k : ℕ} (hk : 0 < k)
    (Q : Quadruple g (situationAlgebra A) (k : ℤ)) :
    F.classifyingMorphism A (F.mk g (by exact_mod_cast hk) Q)
      = Fd.homDegreeOpen A (relativeProj A) hk (Fd.mk g Q)
          ≫ ((relativeProj A).degreeOpen k).ι ≫ (canonicalIso A (relativeProj A)).inv := by
  show (F.representableByRelativeProjOfCharts A (relativeProj A)).homEquiv.symm
        (F.toLim A (F.mk g (by exact_mod_cast hk) Q)) ≫ (canonicalIso A (relativeProj A)).inv = _
  rw [← Category.assoc]
  congr 1
  refine (Scheme.QcClassifying.eq_toHom _ _ _ fun V hV => ?_).symm
  show V.ι ≫ Fd.homDegreeOpen A (relativeProj A) hk (Fd.mk g Q) ≫ _
      = Fd.homDegreeOpen A (relativeProj A) hk (Fd.pullback V.ι (Fd.mk g Q)) ≫ _
  rw [Fd.homDegreeOpen_pullback']
  exact (Category.assoc _ _ _).symm

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end

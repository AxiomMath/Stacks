module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Pullback of a sheaf of graded algebras along a morphism of schemes

`Stacks.RingedSpace.pullbackGradedAlgebra` pulls a sheaf of `ℤ`-graded algebras back along a
morphism of ringed spaces. This file reads that construction in the vocabulary of schemes,
where `Scheme.Modules.pullback` and `Stacks.RingedSpace.pullbackFunctor` are the same functor,
and proves that the pieces stay quasi-coherent ([Stacks, Tag 01BG]) and that vanishing pieces
stay vanishing.

## Main definitions

* `Stacks.Conormal.gradedPullback`: the pullback of a sheaf of graded algebras along a morphism
  of schemes.

## Main results

* `Stacks.Conormal.gradedPullback_mul_pullbackSection` and
  `Stacks.Conormal.gradedPullback_one_eval`: **the identification of the pulled-back algebra.**
  The product of the pullbacks of two homogeneous sections is the pullback of their product,
  and the unit is the pullback of the unit.
* `Stacks.Conormal.gradedPullback_isQuasicoherent` and
  `Stacks.Conormal.gradedPullback_negative_isZero`: the pieces of the pullback are
  quasi-coherent, and are zero wherever the pieces of the source are.

## Implementation notes

`Scheme.Modules.pullback g` and `Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom` are
equal by `rfl`, as are `X.ringCatSheaf` and
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`, the unit of the two adjunctions, and
`g ⁻¹ᵁ U` and `(RingedSpaceModuleAdjunction.opensMap g.toLRSHom.toShHom).obj U`.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (g : Z ⟶ X)

/-- Over the whole preimage of an open the pullback of a section is the image of the section
under the unit of `g^* ⊣ g_*`. -/
lemma pullbackSection_self (M : X.Modules) (U : X.Opens) (a : M.val.obj (op U)) :
    Scheme.Modules.pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) a := by
  unfold Scheme.Modules.pullbackSection
  have hid : (homOfLE (le_refl (g ⁻¹ᵁ U))).op = 𝟙 (op (g ⁻¹ᵁ U)) := Subsingleton.elim _ _
  rw [hid]
  simp
  rfl

variable (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

/-- **The pullback of a sheaf of graded algebras along a morphism of schemes.** -/
noncomputable def gradedPullback : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf :=
  Stacks.RingedSpace.pullbackGradedAlgebra g.toLRSHom.toShHom A

/-- The degree-`n` piece of the pullback is the pullback of the degree-`n` piece. -/
@[simp] lemma gradedPullback_piece (n : ℤ) :
    (gradedPullback g A).piece n = (Scheme.Modules.pullback g).obj (A.piece n) := rfl

/-- The pieces of the pullback are quasi-coherent as soon as the pieces are. This is
[Stacks, Tag 01BG]. -/
lemma gradedPullback_isQuasicoherent (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherent) (n : ℤ) :
    ((gradedPullback g A).piece n).IsQuasicoherent :=
  have := hA n
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g (A.piece n)

/-- A piece of the pullback is zero wherever the corresponding piece is. -/
lemma gradedPullback_isZero {n : ℤ} (hn : Limits.IsZero (A.piece n)) :
    Limits.IsZero ((gradedPullback g A).piece n) :=
  (Scheme.Modules.pullback g).map_isZero hn

/-- The pullback of a nonnegatively graded algebra is nonnegatively graded. -/
lemma gradedPullback_negative_isZero (hA : ∀ (n : ℤ), n < 0 → Limits.IsZero (A.piece n))
    (n : ℤ) (hn : n < 0) : Limits.IsZero ((gradedPullback g A).piece n) :=
  gradedPullback_isZero g A (hA n hn)

/-- **The pulled-back multiplication on pulled-back sections.** The product of the pullbacks of
two homogeneous sections over an open `U` of the target is the pullback of their product. -/
lemma gradedPullback_mul_pullbackSection (i j : ℤ) (U : X.Opens)
    (a : (A.piece i).val.obj (op U)) (b : (A.piece j).val.obj (op U)) :
    ((gradedPullback g A).mul i j).app (op (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackSection g (A.piece i) U (g ⁻¹ᵁ U) le_rfl a)
        (Scheme.Modules.pullbackSection g (A.piece j) U (g ⁻¹ᵁ U) le_rfl b) =
      Scheme.Modules.pullbackSection g (A.piece (i + j)) U (g ⁻¹ᵁ U) le_rfl
        ((A.mul i j).app (op U) a b) := by
  rw [pullbackSection_self g (A.piece i) U a, pullbackSection_self g (A.piece j) U b,
    pullbackSection_self g (A.piece (i + j)) U ((A.mul i j).app (op U) a b)]
  exact Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit g.toLRSHom.toShHom A i j U a b

/-- **The homogeneous multiplication of the pullback is commutative as soon as the homogeneous
multiplication of `A` is.** -/
lemma gradedPullback_mul_comm
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (i j : ℤ) (W : (Opens ↥Z)ᵒᵖ)
    (a : ((gradedPullback g A).piece i).val.obj W)
    (b : ((gradedPullback g A).piece j).val.obj W) :
    HEq (((gradedPullback g A).mul i j).app W a b)
      (((gradedPullback g A).mul j i).app W b a) :=
  Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc i j W a b

/-- **The unit of the pulled-back algebra is the pullback of the unit.** -/
lemma gradedPullback_one_eval (U : X.Opens) :
    (gradedPullback g A).one.eval (op (g ⁻¹ᵁ U)) =
      Scheme.Modules.pullbackSection g (A.piece 0) U (g ⁻¹ᵁ U) le_rfl (A.one.eval (op U)) := by
  rw [pullbackSection_self g (A.piece 0) U (A.one.eval (op U))]
  exact Stacks.RingedSpace.pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom A U

end Stacks.Conormal

end

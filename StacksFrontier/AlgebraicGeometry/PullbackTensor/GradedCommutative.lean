module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra

/-!
# Commutativity of the pulled-back multiplication

Let `f : X ⟶ Y` be a morphism of ringed spaces and `A` a sheaf of `ℤ`-graded `𝒪_Y`-algebras in
the sense of [Stacks, Tag 0FQW]. `Stacks.RingedSpace.pullbackGradedAlgebra` makes `f^*A` a sheaf
of graded `𝒪_X`-algebras, and proves the three laws a `SheafOfModules.GradedAlgebra` asks for —
associativity and the two unit laws. **Commutativity is not one of those laws**, because
`SheafOfModules.GradedAlgebra` does not ask for it; it is an extra property, and this file proves
that `f^*A` has it whenever `A` does.

That is the one thing missing before a commutative, nonnegatively graded, quasi-coherent algebra
on `Y` can be pulled back to one on `X`: the other two properties the sheaf-level data of
Situation 01NN asks for are already available for a pullback, as
`Stacks.Conormal.gradedPullback_negative_isZero` and `gradedPullback_isQuasicoherent`.

## Main results

* `Stacks.RingedSpace.pullbackMul_comm`: **the pulled-back multiplication is commutative as soon
  as the multiplication of `A` is.**
* `Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm`: the same, written with the multiplication
  of `Stacks.RingedSpace.pullbackGradedAlgebra`.

## Implementation notes

The proof is the two-variable instance of the argument that
`StacksFrontier/AlgebraicGeometry/PullbackTensor/GradedAlgebra.lean` runs in three variables for
associativity, and it uses that file's public inputs unchanged: a section of a sheaf is
determined by its germs (`Stacks.RingedSpace.heq_of_sheafCast_grpGerm`), the germ of a product is
the product of the germs (`Stacks.RingedSpace.stalkMul_grpGerm`), and the stalk of `f^*G` is
generated over the local ring by the germs of pullback-unit images
(`Stacks.RingedSpace.pullbackStalk_linearMap_ext`). The generation argument is run one variable at
a time — two steps — and on germs of pullback-unit images commutativity is the hypothesis `hcomm`
on `A`.

Two of the steps the associativity proof factors through private helpers of that file are inlined
here as local `have`s rather than restated as declarations: the germ of a pulled-back product of
two pullback-unit images, and the transport of such a germ along an equality of the pieces.

The statement is heterogeneous because the two sides live in the pieces of the degrees `i + j`
and `j + i`, which agree only propositionally. It is reduced to a plain equality by
`heq_of_sheafCast_grpGerm`, exactly as the three laws are.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

section PullbackCommutative

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))
  (hcomm : ∀ (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj U)
    (b : (A.piece j).val.obj U), HEq ((A.mul i j).app U a b) ((A.mul j i).app U b a))

include hcomm

/-- Commutativity of the pulled-back multiplication, on germs of pullback-unit images of two
sections over one common open. -/
private lemma comm_stalk_common (i j : ℤ) (p : X.carrier) (V : Opens Y.carrier)
    (hx : f.hom.base p ∈ V) (a : (A.piece i).val.obj (op V)) (b : (A.piece j).val.obj (op V)) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj V) hx
            (pullbackUnit f (A.piece i) (op V) a))
          (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj V) hx
            (pullbackUnit f (A.piece j) (op V) b))) =
      stalkMul (pullbackBilinear f (A.mul j i)) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj V) hx
          (pullbackUnit f (A.piece j) (op V) b))
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj V) hx
          (pullbackUnit f (A.piece i) (op V) a)) := by
  have key : ∀ {M N P : SheafOfModules.{u} (structureRingSheaf Y)}
      (β : SheafOfModules.BilinearMap M N P) (c : M.val.obj (op V)) (d : N.val.obj (op V)),
      stalkMul (pullbackBilinear f β) p
          (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
            (pullbackUnit f M (op V) c))
          (grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj V) hx
            (pullbackUnit f N (op V) d)) =
        grpGerm X ((pullbackFunctor f).obj P).val p ((opensMap f).obj V) hx
          (pullbackUnit f P (op V) (β.app (op V) c d)) := fun β c d =>
    (stalkMul_grpGerm (pullbackBilinear f β) p ((opensMap f).obj V) hx _ _).trans
      (congrArg _ (pullbackBilinear_pullbackUnit f β (op V) c d))
  have cast_germ : ∀ {M N : SheafOfModules.{u} (structureRingSheaf Y)} (hMN : M = N)
      (c : M.val.obj (op V)) (d : N.val.obj (op V)), HEq c d →
      sheafCast (congrArg (pullbackFunctor f).obj hMN) p
          (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
            (pullbackUnit f M (op V) c)) =
        grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj V) hx
          (pullbackUnit f N (op V) d) := by
    intro M N hMN c d hcd
    subst hMN
    obtain rfl := eq_of_heq hcd
    rfl
  rw [key (A.mul i j) a b, key (A.mul j i) b a]
  exact cast_germ (congrArg A.piece (add_comm i j)) _ _ (hcomm i j (op V) a b)

/-- Commutativity of the pulled-back multiplication, on germs of pullback-unit images of two
sections over two possibly different opens. -/
private lemma comm_stalk_gen (i j : ℤ) (p : X.carrier) (Va Vb : Opens Y.carrier)
    (ha : f.hom.base p ∈ Va) (hb : f.hom.base p ∈ Vb) (a : (A.piece i).val.obj (op Va))
    (b : (A.piece j).val.obj (op Vb)) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
            (pullbackUnit f (A.piece i) (op Va) a))
          (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
            (pullbackUnit f (A.piece j) (op Vb) b))) =
      stalkMul (pullbackBilinear f (A.mul j i)) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
          (pullbackUnit f (A.piece j) (op Vb) b))
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
          (pullbackUnit f (A.piece i) (op Va) a)) := by
  have hxW : f.hom.base p ∈ Va ⊓ Vb := ⟨ha, hb⟩
  rw [← grpGerm_pullbackUnit_restrict f (A.piece i) p (inf_le_left : Va ⊓ Vb ≤ Va) hxW a,
    ← grpGerm_pullbackUnit_restrict f (A.piece j) p (inf_le_right : Va ⊓ Vb ≤ Vb) hxW b]
  exact comm_stalk_common f A hcomm i j p (Va ⊓ Vb) hxW _ _

/-- Commutativity of the pulled-back multiplication on stalks, in the second variable
arbitrary. -/
private lemma comm_stalk_y (i j : ℤ) (p : X.carrier) (Va : Opens Y.carrier)
    (ha : f.hom.base p ∈ Va) (a : (A.piece i).val.obj (op Va))
    (gy : grpStalk X ((pullbackFunctor f).obj (A.piece j)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
            (pullbackUnit f (A.piece i) (op Va) a)) gy) =
      stalkMul (pullbackBilinear f (A.mul j i)) p gy
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
          (pullbackUnit f (A.piece i) (op Va) a)) := by
  set gx := grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
    (pullbackUnit f (A.piece i) (op Va) a) with hgx
  exact LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f (A.piece j) p
      (((sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n))
          (add_comm i j)) p).toLinearMap).comp
        (stalkMulLeft (pullbackBilinear f (A.mul i j)) p gx))
      (stalkMulRight (pullbackBilinear f (A.mul j i)) p gx)
      (fun Vb hb b => by
        rw [hgx]
        exact comm_stalk_gen f A hcomm i j p Va Vb ha hb a b)) gy

/-- **Commutativity of the pulled-back multiplication on stalks.** -/
private lemma comm_stalk (i j : ℤ) (p : X.carrier)
    (gx : grpStalk X ((pullbackFunctor f).obj (A.piece i)).val p)
    (gy : grpStalk X ((pullbackFunctor f).obj (A.piece j)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p gx gy) =
      stalkMul (pullbackBilinear f (A.mul j i)) p gy gx :=
  LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f (A.piece i) p
      (((sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n))
          (add_comm i j)) p).toLinearMap).comp
        (stalkMulRight (pullbackBilinear f (A.mul i j)) p gy))
      (stalkMulLeft (pullbackBilinear f (A.mul j i)) p gy)
      (fun Va ha a => comm_stalk_y f A hcomm i j p Va ha a gy)) gx

/-- **The pulled-back multiplication is commutative as soon as the multiplication of `A` is.**

The two sides live in the pieces of the degrees `i + j` and `j + i`, which agree only
propositionally, so the equality is heterogeneous — as in the three laws of
`Stacks.RingedSpace.pullbackGradedAlgebra`. -/
theorem pullbackMul_comm (i j : ℤ) (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U))
    (y : ((pullbackFunctor f).obj (A.piece j)).val.obj (op U)) :
    HEq ((pullbackBilinear f (A.mul i j)).app (op U) x y)
      ((pullbackBilinear f (A.mul j i)).app (op U) y x) := by
  refine heq_of_sheafCast_grpGerm
    (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) U _ _
    fun p hp => ?_
  rw [← stalkMul_grpGerm (pullbackBilinear f (A.mul i j)) p U hp x y,
    ← stalkMul_grpGerm (pullbackBilinear f (A.mul j i)) p U hp y x]
  exact comm_stalk f A hcomm i j p _ _

/-- **The pullback of a commutative sheaf of graded algebras is commutative**, written with the
multiplication of `Stacks.RingedSpace.pullbackGradedAlgebra`. -/
theorem pullbackGradedAlgebra_mul_comm_of_comm (i j : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((pullbackGradedAlgebra f A).piece i).val.obj U)
    (y : ((pullbackGradedAlgebra f A).piece j).val.obj U) :
    HEq (((pullbackGradedAlgebra f A).mul i j).app U x y)
      (((pullbackGradedAlgebra f A).mul j i).app U y x) := by
  obtain ⟨U⟩ := U
  exact pullbackMul_comm f A hcomm i j U x y

end PullbackCommutative

end Stacks.RingedSpace

end

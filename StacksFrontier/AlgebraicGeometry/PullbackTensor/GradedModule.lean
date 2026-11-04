module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.LeftGradedModule
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.BilinearExt

/-!
# Pullback of a right graded module along a morphism of ringed spaces

Let `f : X ⟶ Y` be a morphism of ringed spaces, `A` a sheaf of `ℤ`-graded `𝒪_Y`-algebras and
`M` a **right** graded `A`-module in the sense of [Stacks, Tag 0FQZ]. Then `f^*M` is a right
graded module over the pulled-back algebra `f^*A` of
`Stacks.RingedSpace.pullbackGradedAlgebra`: the pieces are the pullbacks of the pieces and the
action is the pullback of the action, through [Stacks, Tag 01CD].

## Main definitions

* `Stacks.RingedSpace.smulBilinearRight`: the action of a right graded module, in one pair of
  degrees, as a bilinear map of sheaves of modules.
* `Stacks.RingedSpace.pullbackGradedModule`: **the pullback of a right graded module.**

## Main results

* `Stacks.RingedSpace.pullbackBilinear_flip`: **pulling back a bilinear map commutes with
  interchanging its two variables.**
* `Stacks.RingedSpace.pullbackBilinear_one_right`: a unit law for the *second* variable of a
  bilinear map pulls back.
* `Stacks.RingedSpace.pullbackGradedModule_smul_pullbackUnit`: on pullback-unit images the
  pulled-back action is the pullback-unit image of the action.

## Implementation notes

The associativity and unit laws of the pulled-back action follow from
`Stacks.RingedSpace.pullbackBilinear_assoc` and `Stacks.RingedSpace.pullbackBilinear_one`. Since
the unit of a right module acts in the second variable, the unit law is transported through
`Stacks.RingedSpace.pullbackBilinear_flip`: pulling back a bilinear map commutes with
interchanging its two variables.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite

universe u

namespace Stacks.RingedSpace
open RingedSpaceModuleAdjunction

section Flip

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {A B D : SheafOfModules.{u} (structureRingSheaf Y)}

/-- **Pulling back a bilinear map of sheaves of modules commutes with interchanging its two
variables.** Both sides are bilinear maps `f^*B × f^*A ⟶ f^*D`, and on a pair of pullback-unit
images both are the pullback-unit image of the original value, so
`Stacks.RingedSpace.pullbackBilinear_ext` applies. -/
theorem pullbackBilinear_flip (β : SheafOfModules.BilinearMap A B D) :
    pullbackBilinear f β.flip = (pullbackBilinear f β).flip := by
  refine Stacks.BilinearMap.ext fun V y x => ?_
  obtain ⟨V⟩ := V
  refine pullbackBilinear_ext f (pullbackBilinear f β.flip) (pullbackBilinear f β).flip
    (fun W b a => ?_) V y x
  exact (pullbackBilinear_pullbackUnit f β.flip (op W) b a).trans
    (pullbackBilinear_pullbackUnit f β (op W) a b).symm

end Flip

section UnitRight

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {M₀ N Q : SheafOfModules.{u} (structureRingSheaf Y)} (t : M₀.sections)
  (β : SheafOfModules.BilinearMap N M₀ Q) (hQ : Q = N)
  (hone : ∀ (V : Opens Y.carrier) (a : N.val.obj (op V)),
    HEq (β.app (op V) a (t.eval (op V))) a)

include hQ hone in
/-- **A unit law for the second variable of a bilinear map of sheaves of modules pulls back**,
the unit being the global section of the pullback attached to a global section. This is
`Stacks.RingedSpace.pullbackBilinear_one` for the interchanged map, read back through
`Stacks.RingedSpace.pullbackBilinear_flip`. -/
theorem pullbackBilinear_one_right (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj N).val.obj (op U)) :
    HEq ((pullbackBilinear f β).app (op U) x ((pullbackSectionsUnit f M₀ t).eval (op U))) x := by
  have hflip : (pullbackBilinear f β).app (op U) x ((pullbackSectionsUnit f M₀ t).eval (op U)) =
      (pullbackBilinear f β.flip).app (op U) ((pullbackSectionsUnit f M₀ t).eval (op U)) x := by
    rw [pullbackBilinear_flip f β]
    rfl
  exact (heq_of_eq hflip).trans (pullbackBilinear_one f t β.flip hQ hone U x)

end UnitRight

section Module

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))

/-- The action of a right graded module in the degrees `(n, i)`, as a bilinear map of sheaves of
modules. -/
def smulBilinearRight (M : SheafOfModules.GradedModule.{u, u, u} A) (n i : ℤ) :
    SheafOfModules.BilinearMap (M.piece n) (A.piece i) (M.piece (n + i)) where
  app U := M.smul n i U
  map_smul_left U r x y := M.smul_smul_left n i U r x y
  map_smul_right U r x y := M.smul_smul_right n i U r x y
  naturality g x y := M.smul_naturality n i g x y

/-- **The pullback of a right graded module along a morphism of ringed spaces**, a right graded
module over the pulled-back graded algebra. The pieces are the pullbacks of the pieces and the
action is the pullback of the action. -/
noncomputable def pullbackGradedModule (M : SheafOfModules.GradedModule.{u, u, u} A) :
    SheafOfModules.GradedModule.{u, u, u} (pullbackGradedAlgebra f A) where
  piece n := (pullbackFunctor f).obj (M.piece n)
  smul n i U := (pullbackBilinear f (smulBilinearRight A M n i)).app U
  smul_smul_left n i U r x y :=
    (pullbackBilinear f (smulBilinearRight A M n i)).map_smul_left U r x y
  smul_smul_right n i U r x y :=
    (pullbackBilinear f (smulBilinearRight A M n i)).map_smul_right U r x y
  smul_naturality n i _ _ g x y :=
    (pullbackBilinear f (smulBilinearRight A M n i)).naturality g x y
  smul_mul n i j U x y z := by
    obtain ⟨U⟩ := U
    exact pullbackBilinear_assoc f (smulBilinearRight A M n i) (A.mul i j)
      (smulBilinearRight A M (n + i) j) (smulBilinearRight A M n (i + j))
      (congrArg M.piece (add_assoc n i j)) (fun V x y z => M.smul_mul n i j (op V) x y z) U x y z
  smul_one n U x := by
    obtain ⟨U⟩ := U
    exact pullbackBilinear_one_right f A.one (smulBilinearRight A M n 0)
      (congrArg M.piece (add_zero n)) (fun V x => M.smul_one n (op V) x) U x

/-- The degree `n` piece of the pullback of a graded module is the pullback of its degree `n`
piece. -/
@[simp] lemma pullbackGradedModule_piece (M : SheafOfModules.GradedModule.{u, u, u} A) (n : ℤ) :
    (pullbackGradedModule f A M).piece n = (pullbackFunctor f).obj (M.piece n) := rfl

/-- **The pulled-back action on pullback-unit images** is the pullback-unit image of the
action. -/
lemma pullbackGradedModule_smul_pullbackUnit (M : SheafOfModules.GradedModule.{u, u, u} A)
    (n i : ℤ) (V : Opens Y.carrier) (x : (M.piece n).val.obj (op V))
    (a : (A.piece i).val.obj (op V)) :
    (pullbackGradedModule f A M).smul n i (op ((opensMap f).obj V))
        (pullbackUnit f (M.piece n) (op V) x) (pullbackUnit f (A.piece i) (op V) a) =
      pullbackUnit f (M.piece (n + i)) (op V) (M.smul n i (op V) x a) :=
  pullbackBilinear_pullbackUnit f (smulBilinearRight A M n i) (op V) x a

end Module

end Stacks.RingedSpace

end

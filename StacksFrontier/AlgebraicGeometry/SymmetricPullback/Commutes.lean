module

public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.BilinearExt
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge

/-!
# The pulled-back degree-one generator of a symmetric algebra pairwise commutes

Let `f : X ⟶ Y` be a morphism of ringed spaces, `A` a sheaf of graded `𝒪_Y`-algebras and
`ι : F ⟶ A.piece 1` a degree-one generator. `Stacks.RingedSpace.pullbackGradedAlgebra` makes
`f^*A` a sheaf of graded `𝒪_X`-algebras, and `(f^*ι)` is a degree-one generator of it. This
file proves the side condition that the universal property of the *symmetric* algebra attaches
to a generator — `SheafOfModules.GradedAlgebra.PairwiseCommutes` — transfers along `f^*`, and
along the pushforward.

## Main results

* `Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackGen`: the product of two pullback-unit
  images under the pulled-back generator is the pullback-unit image of their product.
* `Stacks.RingedSpace.pairwiseCommutes_pullbackGen`: `PairwiseCommutes` transfers along the
  pullback.
* `SheafOfModules.GradedAlgebra.pairwiseCommutes_pushforwardGenerator`: `PairwiseCommutes`
  transfers along the pushforward.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
  SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))
  {F : SheafOfModules.{u} (structureRingSheaf Y)}

/-- The degree-one generator of the pulled-back graded algebra obtained from a degree-one
generator of `A`: the pullback of `ι`, whose target is the degree-one piece of
`Stacks.RingedSpace.pullbackGradedAlgebra` on the nose. -/
noncomputable abbrev pullbackGen (ι : F ⟶ A.piece 1) :
    (pullbackFunctor f).obj F ⟶ (pullbackGradedAlgebra f A).piece 1 :=
  (pullbackFunctor f).map ι

/-- The product, in the pulled-back algebra, of the images under the pulled-back generator of
two pullback-unit sections is the pullback-unit image of the product in `A`. -/
lemma pullbackGradedAlgebra_mul_pullbackGen (ι : F ⟶ A.piece 1) (V : Opens Y.carrier)
    (s u : F.val.obj (op V)) :
    ((pullbackGradedAlgebra f A).mul 1 1).app (op ((opensMap f).obj V))
        ((pullbackGen f A ι).val.app (op ((opensMap f).obj V)) (pullbackUnit f F (op V) s))
        ((pullbackGen f A ι).val.app (op ((opensMap f).obj V)) (pullbackUnit f F (op V) u)) =
      pullbackUnit f (A.piece (1 + 1)) (op V)
        ((A.mul 1 1).app (op V) (ι.val.app (op V) s) (ι.val.app (op V) u)) := by
  have hs : (pullbackGen f A ι).val.app (op ((opensMap f).obj V))
        (pullbackUnit f F (op V) s) =
      pullbackUnit f (A.piece 1) (op V) (ι.val.app (op V) s) :=
    pullbackUnit_naturality f ι (op V) s
  have hu : (pullbackGen f A ι).val.app (op ((opensMap f).obj V))
        (pullbackUnit f F (op V) u) =
      pullbackUnit f (A.piece 1) (op V) (ι.val.app (op V) u) :=
    pullbackUnit_naturality f ι (op V) u
  rw [hs, hu]
  exact pullbackGradedAlgebra_mul_pullbackUnit f A 1 1 V _ _

/-- **`PairwiseCommutes` transfers along the pullback.** If any two local sections of `F` have
commuting images under a degree-one generator `ι` of `A`, then any two local sections of
`f^*F` — not only the pulled-back ones — have commuting images under `f^*ι` in the pulled-back
graded algebra. -/
theorem pairwiseCommutes_pullbackGen {ι : F ⟶ A.piece 1} (hι : PairwiseCommutes ι) :
    PairwiseCommutes (pullbackGen f A ι) := by
  intro U s u
  obtain ⟨U⟩ := U
  refine pullbackBilinear_ext f
    ((((pullbackGradedAlgebra f A).mul 1 1).compLeft (pullbackGen f A ι).val).compRight
      (pullbackGen f A ι).val)
    (((((pullbackGradedAlgebra f A).mul 1 1).compLeft (pullbackGen f A ι).val).compRight
      (pullbackGen f A ι).val).flip)
    (fun V a b => ?_) U s u
  change ((pullbackGradedAlgebra f A).mul 1 1).app (op ((opensMap f).obj V))
      ((pullbackGen f A ι).val.app (op ((opensMap f).obj V)) (pullbackUnit f F (op V) a))
      ((pullbackGen f A ι).val.app (op ((opensMap f).obj V)) (pullbackUnit f F (op V) b)) =
    ((pullbackGradedAlgebra f A).mul 1 1).app (op ((opensMap f).obj V))
      ((pullbackGen f A ι).val.app (op ((opensMap f).obj V)) (pullbackUnit f F (op V) b))
      ((pullbackGen f A ι).val.app (op ((opensMap f).obj V)) (pullbackUnit f F (op V) a))
  rw [pullbackGradedAlgebra_mul_pullbackGen, pullbackGradedAlgebra_mul_pullbackGen]
  exact congrArg _ (hι (op V) a b)

end Stacks.RingedSpace

namespace SheafOfModules.GradedAlgebra

open AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {F : SheafOfModules.{u} (structureSheafRing Y)}
  {B : GradedAlgebra.{u, u} (structureSheafRing X)}
  {κ : (modulePullback f).obj F ⟶ B.piece 1}

/-- A degree-one generator with pairwise commuting image pushes forward to one with pairwise
commuting image: the condition on the pushforward over `U` is the condition on `B` over the
preimage of `U`. -/
theorem pairwiseCommutes_pushforwardGenerator (hκ : PairwiseCommutes κ) :
    PairwiseCommutes (pushforwardGenerator f κ) := by
  intro U s u
  rw [pushforwardGenerator_val_app, pushforwardGenerator_val_app]
  exact hκ ((opensMap f).op.obj U) _ _

end SheafOfModules.GradedAlgebra


end

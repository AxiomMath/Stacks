module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra

/-!
# A bilinear map out of pullbacks is determined by its values on pullback-unit sections

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `M`, `N` be sheaves of `𝒪_Y`-modules.
`RingedSpaceModuleAdjunction.modulePullback` is defined as `(modulePushforward f).leftAdjoint`
and so has no description of its sections: the only local sections of `f^*M` that can be named
are the pullback-unit images `Stacks.RingedSpace.pullbackUnit` of local sections of `M`, and
those do not exhaust the sections over an open of `X`. This file proves that they nevertheless
*determine* a bilinear map out of `f^*M × f^*N`:

`Stacks.RingedSpace.pullbackBilinear_ext` — two bilinear maps
`f^*M × f^*N ⟶ Q` agreeing on pairs of pullback-unit images are equal on all pairs of local
sections.

The proof is the one `StacksFrontier/AlgebraicGeometry/PullbackTensor/GradedAlgebra.lean` runs
inline for each of the three graded-algebra laws, extracted once and for all: a section of a
sheaf is determined by its germs (`Stacks.RingedSpace.section_ext_grpGerm`), the germ of a
product is a function of the germs of the factors (`Stacks.RingedSpace.stalkMul_grpGerm`), and
the stalk of `f^*M` at `p` is generated over `𝒪_{X,p}` by the germs of pullback-unit images
(`Stacks.RingedSpace.pullbackStalk_linearMap_ext`, which is [Stacks, Tag 0098]). The two
variables are reduced one at a time, and the two resulting sections — over two possibly
different opens of `Y` — are restricted to the intersection.

## Main results

* `Stacks.RingedSpace.grpGerm_pullbackUnit_restrict`: the germ of a pullback-unit image is
  unchanged by restricting the section to a smaller open.
* `Stacks.RingedSpace.pullbackBilinear_ext`: **bilinear extensionality for pullbacks.**
* `Stacks.RingedSpace.pullbackBilinear_heq_ext`: the same with the two targets allowed to differ
  by a propositional equality and the two variables interchanged, which is the shape a
  commutation law of a graded algebra takes.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

section BilinearExt

variable {M N : SheafOfModules.{u} (structureRingSheaf Y)}
  {Q : SheafOfModules.{u} (structureRingSheaf X)}
  (β γ : SheafOfModules.BilinearMap ((pullbackFunctor f).obj M)
    ((pullbackFunctor f).obj N) Q)

/-- The germs of two bilinear maps agree at `p` on germs of pullback-unit images of sections
over two possibly different opens, as soon as the maps agree on pullback-unit images of
sections over a common open. -/
private lemma stalkMul_eq_of_pullbackUnit
    (h : ∀ (V : Opens Y.carrier) (a : M.val.obj (op V)) (b : N.val.obj (op V)),
      β.app (op ((opensMap f).obj V)) (pullbackUnit f M (op V) a)
          (pullbackUnit f N (op V) b) =
        γ.app (op ((opensMap f).obj V)) (pullbackUnit f M (op V) a)
          (pullbackUnit f N (op V) b))
    (p : X.carrier) (V : Opens Y.carrier) (hxV : f.hom.base p ∈ V) (a : M.val.obj (op V))
    (W : Opens Y.carrier) (hxW : f.hom.base p ∈ W) (b : N.val.obj (op W)) :
    stalkMul β p
        (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hxV
          (pullbackUnit f M (op V) a))
        (grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj W) hxW
          (pullbackUnit f N (op W) b)) =
      stalkMul γ p
        (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hxV
          (pullbackUnit f M (op V) a))
        (grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj W) hxW
          (pullbackUnit f N (op W) b)) := by
  have hxVW : f.hom.base p ∈ V ⊓ W := ⟨hxV, hxW⟩
  rw [← grpGerm_pullbackUnit_restrict f M p (inf_le_left : V ⊓ W ≤ V) hxVW a,
    ← grpGerm_pullbackUnit_restrict f N p (inf_le_right : V ⊓ W ≤ W) hxVW b,
    stalkMul_grpGerm β p ((opensMap f).obj (V ⊓ W)) hxVW _ _,
    stalkMul_grpGerm γ p ((opensMap f).obj (V ⊓ W)) hxVW _ _]
  exact congrArg _ (h (V ⊓ W) _ _)

/-- **Bilinear extensionality for pullbacks.** Two bilinear maps `f^*M × f^*N ⟶ Q` which agree
on pairs of pullback-unit images of local sections of `M` and `N` over a common open of `Y`
agree on every pair of local sections of `f^*M` and `f^*N` over every open of `X`.

The pullback-unit images do not exhaust the sections of a pullback — `modulePullback` is an
abstract left adjoint — but their germs generate every stalk, by [Stacks, Tag 0098]. -/
theorem pullbackBilinear_ext
    (h : ∀ (V : Opens Y.carrier) (a : M.val.obj (op V)) (b : N.val.obj (op V)),
      β.app (op ((opensMap f).obj V)) (pullbackUnit f M (op V) a)
          (pullbackUnit f N (op V) b) =
        γ.app (op ((opensMap f).obj V)) (pullbackUnit f M (op V) a)
          (pullbackUnit f N (op V) b))
    (U : Opens X.carrier) (x : ((pullbackFunctor f).obj M).val.obj (op U))
    (y : ((pullbackFunctor f).obj N).val.obj (op U)) :
    β.app (op U) x y = γ.app (op U) x y := by
  refine section_ext_grpGerm Q U _ _ fun p hp => ?_
  rw [← stalkMul_grpGerm β p U hp x y, ← stalkMul_grpGerm γ p U hp x y]
  have hy : ∀ (V : Opens Y.carrier) (hxV : f.hom.base p ∈ V) (a : M.val.obj (op V))
      (gy : grpStalk X ((pullbackFunctor f).obj N).val p),
      stalkMul β p
          (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hxV
            (pullbackUnit f M (op V) a)) gy =
        stalkMul γ p
          (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hxV
            (pullbackUnit f M (op V) a)) gy := by
    intro V hxV a gy
    exact LinearMap.congr_fun
      (pullbackStalk_linearMap_ext f N p
        (stalkMulLeft β p (grpGerm X ((pullbackFunctor f).obj M).val p
          ((opensMap f).obj V) hxV (pullbackUnit f M (op V) a)))
        (stalkMulLeft γ p (grpGerm X ((pullbackFunctor f).obj M).val p
          ((opensMap f).obj V) hxV (pullbackUnit f M (op V) a)))
        (fun W hxW b => stalkMul_eq_of_pullbackUnit f β γ h p V hxV a W hxW b)) gy
  exact LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f M p
      (stalkMulRight β p (grpGerm X ((pullbackFunctor f).obj N).val p U hp y))
      (stalkMulRight γ p (grpGerm X ((pullbackFunctor f).obj N).val p U hp y))
      (fun V hxV a => hy V hxV a _))
    (grpGerm X ((pullbackFunctor f).obj M).val p U hp x)

end BilinearExt

section HeqBilinearExt

variable {M N : SheafOfModules.{u} (structureRingSheaf Y)}
  {Q Q' : SheafOfModules.{u} (structureRingSheaf X)}

/-- **Heterogeneous bilinear extensionality for pullbacks, in the commuted form.** Let `β` and
`γ` be bilinear maps out of `f^*M × f^*N` and `f^*N × f^*M` whose targets are *equal* sheaves
of modules. If `β` and `γ` take heterogeneously equal values on the pullback-unit images of
local sections of `M` and `N`, with the two variables interchanged, then they do so on every
pair of local sections of `f^*M` and `f^*N`.

This is `Stacks.RingedSpace.pullbackBilinear_ext` with the two targets allowed to differ by a
propositional equality, which is the shape a commutation law of a graded algebra takes: the two
sides of `HEq (mul i j a b) (mul j i b a)` live in the degree-`i + j` and the degree-`j + i`
piece. The equality of targets is `subst`ed away before the homogeneous statement is used, so
no cast on a section survives into the proof. -/
theorem pullbackBilinear_heq_ext (hQ : Q = Q')
    (β : SheafOfModules.BilinearMap ((pullbackFunctor f).obj M)
      ((pullbackFunctor f).obj N) Q)
    (γ : SheafOfModules.BilinearMap ((pullbackFunctor f).obj N)
      ((pullbackFunctor f).obj M) Q')
    (h : ∀ (V : Opens Y.carrier) (a : M.val.obj (op V)) (b : N.val.obj (op V)),
      HEq (β.app (op ((opensMap f).obj V)) (pullbackUnit f M (op V) a)
          (pullbackUnit f N (op V) b))
        (γ.app (op ((opensMap f).obj V)) (pullbackUnit f N (op V) b)
          (pullbackUnit f M (op V) a)))
    (U : Opens X.carrier) (x : ((pullbackFunctor f).obj M).val.obj (op U))
    (y : ((pullbackFunctor f).obj N).val.obj (op U)) :
    HEq (β.app (op U) x y) (γ.app (op U) y x) := by
  subst hQ
  exact heq_of_eq
    (pullbackBilinear_ext f β γ.flip (fun V a b => eq_of_heq (h V a b)) U x y)

end HeqBilinearExt

end Stacks.RingedSpace


end

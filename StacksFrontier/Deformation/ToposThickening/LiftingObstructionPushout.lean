module

public import StacksFrontier.Deformation.ToposThickening.LiftingObstructionFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# Step 3 of the proof of Stacks 08UG/08U8: the algebra map `a` is locally surjective

Step 1 (`StacksFrontier/Deformation/ToposThickening/LiftingObstructionPresentation.lean`) attaches
to a `Deformation.ToposThickening.FirstOrderLiftDiagram` the presentation
`α : 𝒪_{B'₁}[ℰ] ⟶ 𝒪_{X₁}` with thickened coefficients and the algebra map
`a : 𝒪_{B'₁}[ℰ] ⟶ 𝒪_{X'₁}` over it. Step 3 of the source reads a factorization of `ξ` as an
algebra map out of `𝒪_{B'₁}[ℰ]` and descends it along `a`; the source phrases this as `𝒪_{X'₁}`
being the pushout of `ℐ' → 𝒪_{B'₁}[ℰ]` along `a|_{ℐ'} : ℐ' → 𝒢₁`. What the descent actually
consumes is that `a` is locally surjective, which is proved here, together with the agreement of
the two maps on `ℐ'`, which is
`Deformation.ToposThickening.FirstOrderLiftDiagram.twist_backAlgebra_thickIdeal`
(`StacksFrontier/Deformation/ToposThickening/LiftingObstructionSufficiency.lean`).

## Main results

* `Deformation.ToposThickening.FirstOrderLiftDiagram.isLocallySurjective_pairFst`:
  the first projection `ℰ ⟶ 𝒪_{X'₁}` is locally surjective, hence so is `a`
  (`isLocallySurjective_frontAlgebra`).

## Implementation notes

**Local surjectivity of `a`.** `a` is `pairFst` on the variables, so
`Stacks.Sites.FreeAlgebra.isLocallySurjective_freeAlgebraSheafDesc` reduces the claim to local
surjectivity of `pairFst : ℰ ⟶ 𝒪_{X'₁}`. That holds for the same reason
`isLocallySurjective_pairAlpha` does, with one refinement instead of two: a local section `x` of
`𝒪_{X'₁}` has `g(x̄)` lifting locally to a section `y` of `𝒪_{X'₂}` because the reduction of the
back layer is locally surjective, and `(x, y)` is then a section of `ℰ` over `x`.

The identification of `𝒪_{X'₁}` with the square-zero pushout
`Stacks.Sites.SqZeroPushout.pushoutSheaf` is not stated: that construction is made for a small
site with sections in its own universe, whereas a `FirstOrderLiftDiagram` lives on an arbitrary
site with sections in `max u v w`, and the descent along `a` does not need the pushout object.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.FreeAlgebra
open Stacks.Sites.Conormal

universe v u w

namespace Deformation.ToposThickening.FirstOrderLiftDiagram

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)

/-! ### `a : 𝒪_{B'₁}[ℰ] ⟶ 𝒪_{X'₁}` is locally surjective -/

/-- **The first projection `ℰ ⟶ 𝒪_{X'₁}` is locally surjective.** A local section `x` of
`𝒪_{X'₁}` has `g(x̄)` lifting, locally, to a section `y` of `𝒪_{X'₂}`, because the reduction of
the back layer is locally surjective; `(x, y)` is then a section of the fibre product `ℰ` lying
over `x`. -/
instance isLocallySurjective_pairFst : Presheaf.IsLocallySurjective J (pairFst D) where
  imageSieve_mem {U} x := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J D.back.reduction.hom
      (D.g.hom.app (op U) (D.front.reduction.hom.app (op U) x)))
    rintro V f ⟨y, hy⟩
    refine ⟨⟨(D.front.O'.obj.map f.op x, y), ?_⟩, rfl⟩
    change D.g.hom.app (op V) (D.front.reduction.hom.app (op V) (D.front.O'.obj.map f.op x)) =
      D.back.reduction.hom.app (op V) y
    rw [sheafHom_naturality_apply, sheafHom_naturality_apply, hy]

/-- **The algebra map `a : 𝒪_{B'₁}[ℰ] ⟶ 𝒪_{X'₁}` is locally surjective**, because it is the
first projection on the variables and that is locally surjective. -/
instance isLocallySurjective_frontAlgebra :
    Presheaf.IsLocallySurjective J (frontAlgebra D).hom :=
  isLocallySurjective_freeAlgebraSheafDesc J D.front.OB' D.front.O' (pairPresheaf D)
    D.front.f' (pairFst D)

end Deformation.ToposThickening.FirstOrderLiftDiagram

end

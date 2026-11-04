module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.Sections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffinePullbackSections

/-!
# The projection-formula map on global sections of a morphism of affine schemes

For a ring map `φ : R ⟶ A`, a sheaf of modules `G` on `Spec A` and an `R`-module `N`, this file
reads `Stacks.ProjectionFormula.projectionFormulaMap_app_top` in the vocabulary of the affine
dictionary: the projection-formula map of `Spec φ` carries the global section attached to a
pair `(a, n)` --- a global section `a` of `G`, which is a global section of `(Spec φ)_*G`, and
the canonical section of `Ñ` attached to `n` --- to the global section of
`G ⊗_{𝒪_{Spec A}} (Spec φ)^*Ñ` attached to `a` and `AlgebraicGeometry.pullbackTildeΓUnit n`.

Since `pullbackTildeΓUnit n` is the section that `AlgebraicGeometry.pullbackTildeΓEquiv` sends
to `1 ⊗ n`, on global sections the projection-formula map is `m ⊗ n ↦ m ⊗ (1 ⊗ n)`, which is
`TensorProduct.AlgebraTensorModule.cancelBaseChange` read backwards.

No quasi-coherence and no finiteness is assumed; `G` is an arbitrary sheaf of modules on
`Spec A`.

## Main results

* `Stacks.ProjectionFormula.unit_topSec`: the unit of `(Spec φ)^* ⊣ (Spec φ)_*` carries the
  canonical global section of `Ñ` attached to `n` to `AlgebraicGeometry.pullbackTildeΓUnit n`.
* `Stacks.ProjectionFormula.projectionFormulaMap_gammaTmul`: the identification above.

## Implementation notes

`AlgebraicGeometry.TildeTensor.gammaTmul` is the global section of a tensor product attached to
a pair of global sections, so the statement is an equation between two of those, one over
`Spec R` and one over `Spec A`.  A global section of `(Spec φ)_*G` *is* a global section of `G`
(`AlgebraicGeometry.Scheme.Modules.pushforward` reindexes, and the preimage of `⊤` is `⊤`), and
the `R`-action it carries is the `A`-action restricted along `φ`, which is
`AlgebraicGeometry.pushforwardΓLinearEquiv`; neither fact is needed to *state* the equation, and
no transport appears in it.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace Stacks.ProjectionFormula

open RingedSpaceModuleAdjunction AlgebraicGeometry.TildeTensor
open Stacks.AlgebraicGeometry.ProjectionFormula

universe u

variable {R A : CommRingCat.{u}} (φ : R ⟶ A) (G : (Spec A).Modules) (N : ModuleCat.{u} R)

/-- **The unit of `(Spec φ)^* ⊣ (Spec φ)_*` on a canonical global section.**  It carries the
global section of `Ñ` attached to `n` to `AlgebraicGeometry.pullbackTildeΓUnit n`, which is the
section that `AlgebraicGeometry.pullbackTildeΓEquiv` sends to the pure tensor `1 ⊗ n`. -/
theorem unit_topSec (n : N) :
    ((((modulePullbackPushforwardAdjunction (Spec.map φ).toLRSHom.toShHom).unit.app
        (tilde N)).val.app (op ⊤)).hom (topSec N n))
      = pullbackTildeΓUnit R A φ N n := rfl

/-- **The projection-formula map of a morphism of affine schemes, on global sections.**  It
carries the global section of `(Spec φ)_*G ⊗_{𝒪_{Spec R}} Ñ` attached to a global section `a`
of `G` and the canonical section of `Ñ` attached to `n`, to the global section of
`G ⊗_{𝒪_{Spec A}} (Spec φ)^*Ñ` attached to `a` and `AlgebraicGeometry.pullbackTildeΓUnit n`.

Since `AlgebraicGeometry.pullbackTildeΓEquiv` sends `pullbackTildeΓUnit n` to `1 ⊗ n`, this
says that on global sections the projection-formula map is `a ⊗ n ↦ a ⊗ (1 ⊗ n)`, the map
`M ⊗_R N ⟶ M ⊗_A (A ⊗_R N)` that
`TensorProduct.AlgebraTensorModule.cancelBaseChange` inverts.

There is no hypothesis: `G` is an arbitrary sheaf of modules on `Spec A`. -/
theorem projectionFormulaMap_gammaTmul
    (a : Γ((Scheme.Modules.pushforward (Spec.map φ)).obj G, ⊤)) (n : N) :
    ((projectionFormulaMap (Spec.map φ) G (tilde N)).val.app (op ⊤)).hom
        (gammaTmul ((Scheme.Modules.pushforward (Spec.map φ)).obj G) (tilde N) a
          (topSec N n))
      = gammaTmul G ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde N)) a
          (pullbackTildeΓUnit R A φ N n) :=
  projectionFormulaMap_app_top (Spec.map φ) G (tilde N) a (topSec N n)

end Stacks.ProjectionFormula

end

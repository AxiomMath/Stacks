module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
import all StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidalUnitors
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparison
public import StacksFrontier.CategoryTheory.Monoidal.FunctorTensorIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackKFlatMonoidal

/-!
# Derived pullback and the quasi-coherent derived tensor product

For a morphism of schemes `f : X ⟶ Y`, the derived pullback `Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`
is strong monoidal for the derived tensor products, with tensor comparison
`Lf^*(K₂ ⊗ᴸ K₁) ≅ Lf^*K₂ ⊗ᴸ Lf^*K₁`.

## Main definitions

* `monoidal_quasiCoherentDerivedPullback`: the strong monoidal structure on `Lf^*` on `D_QCoh`.
* `quasiCoherentDerivedPullbackTensorIso`: the natural isomorphism
  `Lf^*(K₂ ⊗ᴸ K₁) ≅ Lf^*K₂ ⊗ᴸ Lf^*K₁`.

## Main results

* `quasiCoherentDerivedPullbackTensorIso_hom_app`: the components of
  `quasiCoherentDerivedPullbackTensorIso` are the oplax tensorator of `Lf^*`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Derived pullback is a strong monoidal functor `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`** for the
derived tensor products ([Stacks, Tag 079U]), at the locally small model. It is the restriction,
by [Stacks, Tag 08DW] part (1), of the monoidal structure
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal` of
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` to the full monoidal subcategories `D_QCoh`. -/
instance monoidal_quasiCoherentDerivedPullback : (quasiCoherentDerivedPullback' f).Monoidal :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := Scheme.Modules.canonicalDerivedMonoidal Y
  letI : (derivedPullback f).Monoidal :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f.toLRSHom.toShHom
  ObjectProperty.liftMonoidal _ _ _

/-- **The tensor comparison of derived pullback on `D_QCoh`** ([Stacks, Tag 079U]),
`Lf^*(K₂ ⊗ᴸ_{𝒪_Y} K₁) ≅ Lf^*K₂ ⊗ᴸ_{𝒪_X} Lf^*K₁`, natural in `(K₁, K₂)`: the oplax tensorator of
`Stacks.Duality.monoidal_quasiCoherentDerivedPullback`, read on the bifunctors
`Stacks.Duality.quasiCoherentDerivedTensorSwap` through
`Stacks.Duality.quasiCoherentDerivedTensorIsoCurriedTensor`. -/
def quasiCoherentDerivedPullbackTensorIso :
    quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ≅
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X :=
  Functor.Monoidal.swapTensorIso (quasiCoherentDerivedPullback' f)
    (quasiCoherentDerivedTensorIsoCurriedTensor Y) (quasiCoherentDerivedTensorIsoCurriedTensor X)

/-- The components of `Stacks.Duality.quasiCoherentDerivedPullbackTensorIso` are the oplax
tensorator `δ` of `Lf^*`, conjugated by `Stacks.Duality.quasiCoherentDerivedTensorIsoCurriedTensor`
on `Y` and on `X`. -/
theorem quasiCoherentDerivedPullbackTensorIso_hom_app (P Q : quasiCoherentDerivedCategory Y) :
    (quasiCoherentDerivedPullbackTensorIso f).hom.app (P, Q) =
      (quasiCoherentDerivedPullback' f).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P) ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) Q P ≫
          ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
            ((quasiCoherentDerivedPullback' f).obj Q)).app
              ((quasiCoherentDerivedPullback' f).obj P) :=
  rfl

end Stacks.Duality

end

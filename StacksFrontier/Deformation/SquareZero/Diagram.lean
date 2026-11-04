module

public import StacksFrontier.Deformation.SquareZero.Problem

/-!
# Compatible square-zero deformation diagrams

We package two square-zero extension problems and chosen solutions, together with the
compatible maps between all terms except for the map between the two extension rings.  We
also record what it means for a ring map between those extension rings to fill the diagram.

## Main definitions

* `Stacks.Deformation.CompatibleSquareZeroDeformationDiagram` is the standing deformation
  diagram with its middle arrow omitted.
* `Stacks.Deformation.CompatibleSquareZeroDeformationDiagram.FittingMap` is a ring map which
  supplies the omitted arrow and makes every square commute.

## Main results

There are no propositional results in this file.

## Implementation notes

The vertical maps of rings are represented by algebra structures.  The displayed map
`I₁ → I₂` is therefore the restriction of `A'₁ → A'₂` to the two specified kernel ideals.
The explicitly bundled `B₁`-module structure on `N₂`, together with its scalar-tower
condition, says that it is obtained by restriction along `B₁ → B₂`.

## References

* [Stacks Project, Tag 08S5](https://stacks.math.columbia.edu/tag/08S5)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂

namespace Stacks.Deformation
/-- The standing diagram of two compatible square-zero extension problems and solutions,
with the map between the two solution rings not yet supplied. -/
public structure CompatibleSquareZeroDeformationDiagram where
  /-- The first square-zero extension problem. -/
  S₁ : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}
  /-- The second square-zero extension problem. -/
  S₂ : SquareZeroExtensionProblem.{v₁, v₂, v₃, v₄}
  /-- The chosen solution over the first problem. -/
  X₁ : S₁.CompatibleExtension.{w₁}
  /-- The chosen solution over the second problem. -/
  X₂ : S₂.CompatibleExtension.{w₂}
  /-- The vertical map `A'₁ → A'₂`. -/
  [algebraA'₁A'₂ : Algebra S₁.A' S₂.A']
  /-- The vertical map `A₁ → A₂`. -/
  [algebraA₁A₂ : Algebra S₁.A S₂.A]
  /-- The vertical map `B₁ → B₂`. -/
  [algebraB₁B₂ : Algebra S₁.B S₂.B]
  /-- The two maps from `A'₁` to `A₂` agree. -/
  toA_comm :
    (algebraMap S₂.A' S₂.A).comp (algebraMap S₁.A' S₂.A') =
      (algebraMap S₁.A S₂.A).comp (algebraMap S₁.A' S₁.A)
  /-- The two maps from `A₁` to `B₂` agree. -/
  toB_comm :
    (algebraMap S₂.A S₂.B).comp (algebraMap S₁.A S₂.A) =
      (algebraMap S₁.B S₂.B).comp (algebraMap S₁.A S₁.B)
  /-- The `B₁`-module structure on `N₂` obtained by restricting scalars from `B₂`. -/
  [moduleB₁N₂ : Module S₁.B S₂.N]
  /-- The restricted action is induced by the displayed map `B₁ → B₂`. -/
  [isScalarTowerB₁B₂N₂ : IsScalarTower S₁.B S₂.B S₂.N]
  /-- The vertical map `N₁ → N₂`. -/
  mapN : S₁.N →ₗ[S₁.B] S₂.N
  /-- The map `A'₁ → A'₂` carries `I₁` into `I₂`. -/
  map_I : ∀ i : S₁.I, algebraMap S₁.A' S₂.A' i ∈ S₂.I
  /-- The left square, involving the prescribed maps from the ideals to the modules,
  commutes. -/
  map_c : ∀ i : S₁.I,
    mapN (S₁.c i) = S₂.c ⟨algebraMap S₁.A' S₂.A' i, map_I i⟩

attribute [instance]
  CompatibleSquareZeroDeformationDiagram.algebraA'₁A'₂
  CompatibleSquareZeroDeformationDiagram.algebraA₁A₂
  CompatibleSquareZeroDeformationDiagram.algebraB₁B₂
  CompatibleSquareZeroDeformationDiagram.moduleB₁N₂
  CompatibleSquareZeroDeformationDiagram.isScalarTowerB₁B₂N₂

namespace CompatibleSquareZeroDeformationDiagram

/-- A ring map between the chosen extension rings which fills the omitted arrow in a
compatible square-zero deformation diagram. -/
public structure FittingMap (D : CompatibleSquareZeroDeformationDiagram) where
  /-- The map `B'₁ → B'₂`. -/
  toRingHom : D.X₁.B' →+* D.X₂.B'
  /-- The map is compatible with the vertical map `A'₁ → A'₂`. -/
  toA'_comm :
    toRingHom.comp (algebraMap D.S₁.A' D.X₁.B') =
      (algebraMap D.S₂.A' D.X₂.B').comp (algebraMap D.S₁.A' D.S₂.A')
  /-- The map induces the displayed map `B₁ → B₂` on the quotients. -/
  toB_comm :
    D.X₂.toB.toRingHom.comp toRingHom =
      (algebraMap D.S₁.B D.S₂.B).comp D.X₁.toB.toRingHom
  /-- On the square-zero kernels, the map induces the displayed map `N₁ → N₂`. -/
  kernel_comm : ∀ n : D.S₁.N,
    toRingHom ((D.X₁.kernelEquiv n : RingHom.ker D.X₁.toB.toRingHom) : D.X₁.B') =
      ((D.X₂.kernelEquiv (D.mapN n) : RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')

end CompatibleSquareZeroDeformationDiagram

end Stacks.Deformation
end

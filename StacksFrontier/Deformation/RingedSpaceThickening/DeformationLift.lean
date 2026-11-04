module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationDiagram

/-!
# The morphisms fitting into the diagram of Stacks 08U9 compatibly with `ν`

Let `D` be the diagram of the four ideal rows of **Stacks 08UA**, attached to a commutative cube
of ringed spaces of **Stacks 08U9** whose horizontal arrows are first order thickenings
(`AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram`). **Stacks 08U8** is about
the morphisms of ringed spaces `φ : X'₂ ⟶ X'₁` *fitting into (08U9) compatibly with `ν`*:

* `φ` fills the two faces of the cube that the data leave open, `i₂ ≫ φ = g ≫ i₁` and
  `φ ≫ f'₁ = f'₂ ≫ h'` (`DeformationCube.IsCompatibleLift`);
* the map of ideals `g^*𝒢₁ ⟶ 𝒢₂` that `φ` induces is `ν`.

The second condition is stated through the canonical first order ideal map of the square of
thickenings `(i₂, i₁, g, φ)` of **Stacks 08KZ**,
`MorphismOfThickenings.firstOrderIdealMap : i₂ₓ g^* i₁^* Ker(i₁^♯) ⟶ Ker(i₂^♯)`, read through
the identifications `Ker(i_j^♯) ≅ i_{j,*}𝒢_j` of the diagram. This is the same formulation as
the compatibility `DeformationIdealDiagram.front_isSolution` with which the diagram identifies
the ideal of each layer with its module.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.frontIdealToModule`: the map
  `i₁^* Ker(i₁^♯) ⟶ 𝒢₁` adjoint to the identification `Ker(i₁^♯) ≅ i₁,* 𝒢₁`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.liftSquare`: the square of
  thickenings `(i₂, i₁, g, φ)` attached to a morphism `φ` filling the upper face.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.IsLift`: **the morphisms
  fitting into (08U9) compatibly with `ν`**.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08U9](https://stacks.math.columbia.edu/tag/08U9)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

namespace DeformationIdealDiagram

variable (D : DeformationIdealDiagram.{u})

/-- The map `i₁^* Ker(i₁^♯) ⟶ 𝒢₁` on `X₁` adjoint to the identification
`Ker(i₁^♯) ≅ i₁,* 𝒢₁` of the diagram. -/
def frontIdealToModule :
    (modulePullback D.cube.i₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.i₁) ⟶
      D.G₁ :=
  ((modulePullbackPushforwardAdjunction D.cube.i₁).homEquiv _ _).symm D.kernelIso₁.hom

/-- The square of thickenings of **Stacks 08KZ** formed by `i₂` over `i₁`, with `g` on the
reduced spaces and a morphism `φ : X'₂ ⟶ X'₁` filling the upper face of the cube on the
thickened ones. -/
def liftSquare (φ : D.cube.X₂' ⟶ D.cube.X₁') (hφ : D.cube.i₂ ≫ φ = D.cube.g ≫ D.cube.i₁) :
    MorphismOfThickenings.{u} where
  X := D.cube.X₂
  X' := D.cube.X₂'
  S := D.cube.X₁
  S' := D.cube.X₁'
  i := D.cube.i₂
  t := D.cube.i₁
  f := D.cube.g
  f' := φ
  i_isThickening := D.i₂_firstOrder.1
  t_isThickening := D.i₁_firstOrder.1
  comm := hφ

/-- **The morphisms `X'₂ ⟶ X'₁` fitting into the diagram (08U9) compatibly with `ν`**, as in
**Stacks 08U8**: `φ` fills the two missing faces of the cube, and the map on ideals it induces —
the canonical first order ideal map `g^*𝒢₁ ⟶ 𝒢₂` of the square of thickenings
`(i₂, i₁, g, φ)`, read through the identifications of the ideals with `𝒢₁` and `𝒢₂` — is `ν`. -/
def IsLift (φ : D.cube.X₂' ⟶ D.cube.X₁') : Prop :=
  ∃ h : D.cube.IsCompatibleLift φ,
    ((D.liftSquare φ h.1).firstOrderIdealMap D.i₂_firstOrder D.i₁_firstOrder).1 ≫
        D.kernelIso₂.hom =
      (modulePushforward D.cube.i₂).map
        ((modulePullback D.cube.g).map D.frontIdealToModule ≫ D.nu)

/-- The set of morphisms `X'₂ ⟶ X'₁` fitting into the diagram (08U9) compatibly with `ν`. -/
abbrev Lifts : Type u := {φ : D.cube.X₂' ⟶ D.cube.X₁' // D.IsLift φ}

end DeformationIdealDiagram

end AlgebraicGeometry.RingedSpaceThickening

end

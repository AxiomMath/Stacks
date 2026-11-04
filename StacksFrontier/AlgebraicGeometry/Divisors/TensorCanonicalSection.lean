module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkNaturality

/-!
# Multiplication by the canonical section of a divisor twist

Let `X` be a scheme and `D ⊆ X` a closed subscheme with sheaf `𝒪_X(D)` and canonical section
`1_D ∈ Γ(X, 𝒪_X(D))`. Multiplication by `1_D` turns any `𝒪_X`-module `F` into its twist:

`F ≅ F ⊗_{𝒪_X} 𝒪_X ⟶ F ⊗_{𝒪_X} 𝒪_X(D)`.

When `D` is an effective Cartier divisor this is the map induced by the inclusion
`𝒪_X ⊆ 𝒪_X(D)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorLeftMap`: tensoring a morphism of `𝒪_X`-modules on the
  left by a fixed module, the companion of
  `AlgebraicGeometry.Scheme.Modules.tensorRightMap`.
* `AlgebraicGeometry.Scheme.Modules.tensorRightUnitor`: the right unit constraint
  `F ⊗_{𝒪_X} 𝒪_X ≅ F` of the sheaf tensor product on a scheme.
* `Stacks.Divisors.canonicalSectionHom`: the canonical section `1_D` of `𝒪_X(D)` read as a
  morphism `𝒪_X ⟶ 𝒪_X(D)`.
* `Stacks.Divisors.tensorCanonicalSection`: multiplication by `1_D`, as a morphism
  `F ⟶ F ⊗_{𝒪_X} 𝒪_X(D)`.

## Implementation notes

A global section of a sheaf of modules is the same thing as a morphism out of the structure
sheaf (`SheafOfModules.unitHomEquiv`), so the canonical section of `𝒪_X(D)` becomes a morphism
`𝒪_X ⟶ 𝒪_X(D)` with no choices; tensoring it on the left with `F` and undoing the right unitor
is then multiplication by the section.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Tensoring a morphism `g : A ⟶ B` of `𝒪_X`-modules on the left by `F`, as a morphism
`F ⊗_{𝒪_X} A ⟶ F ⊗_{𝒪_X} B`. -/
def Scheme.Modules.tensorLeftMap (F : X.Modules) {A B : X.Modules} (g : A ⟶ B) :
    Scheme.Modules.tensorObj F A ⟶ Scheme.Modules.tensorObj F B :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(X).presheaf, (X).IsSheaf⟩).obj F).map g

/-- Tensoring the identity of `A` on the left by `F` gives the identity of `F ⊗_{𝒪_X} A`. -/
@[simp]
theorem Scheme.Modules.tensorLeftMap_id (F A : X.Modules) :
    Scheme.Modules.tensorLeftMap F (𝟙 A) = 𝟙 (Scheme.Modules.tensorObj F A) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(X).presheaf, (X).IsSheaf⟩).obj F).map_id A

/-- The right unit constraint `F ⊗_{𝒪_X} 𝒪_X ≅ F` of the sheaf tensor product on a scheme. -/
abbrev Scheme.Modules.tensorRightUnitor (F : X.Modules) :
    Scheme.Modules.tensorObj F (SheafOfModules.unit X.ringCatSheaf) ≅ F :=
  Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.sheaf.obj X.ringCatSheaf.property F

end AlgebraicGeometry

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- The canonical section `1_D` of `𝒪_X(D)`, read as a morphism `𝒪_X ⟶ 𝒪_X(D)` of
`𝒪_X`-modules. -/
noncomputable def canonicalSectionHom (D : X.IdealSheafData) :
    SheafOfModules.unit X.ringCatSheaf ⟶ invertibleSheaf' D :=
  (invertibleSheaf' D).unitHomEquiv.symm (canonicalSection' D)

/-- **Multiplication by the canonical section of `𝒪_X(D)`.** For `D` an effective Cartier
divisor this is the map `F ⟶ F ⊗_{𝒪_X} 𝒪_X(D)` induced by the inclusion `𝒪_X ⊆ 𝒪_X(D)`. -/
noncomputable def tensorCanonicalSection (D : X.IdealSheafData) (F : X.Modules) :
    F ⟶ Scheme.Modules.tensorObj F (invertibleSheaf' D) :=
  (Scheme.Modules.tensorRightUnitor F).inv ≫
    Scheme.Modules.tensorLeftMap F (canonicalSectionHom D)

/-- Multiplication by the canonical section commutes with tensoring a morphism of modules by
`𝒪_X(D)`: both sides are the image under the tensor bifunctor of the one morphism of pairs
`(f, 1_D)`. -/
theorem tensorLeftMap_canonicalSectionHom_comp_tensorRightMap (D : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) :
    Scheme.Modules.tensorLeftMap F (canonicalSectionHom D) ≫
        Scheme.Modules.tensorRightMap f (invertibleSheaf' D) =
      Scheme.Modules.tensorRightMap f (SheafOfModules.unit X.ringCatSheaf) ≫
        Scheme.Modules.tensorLeftMap G (canonicalSectionHom D) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(X).presheaf, (X).IsSheaf⟩).map f).naturality (canonicalSectionHom D)

end Stacks.Divisors

end

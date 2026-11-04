module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalsInQuasicoherentModules

/-!
# Restriction of scalars does not change the image of a morphism out of a tensor product

Let `ρ : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on a space and let `F`, `G` be
sheaves of `ℬ`-modules. The tensor product does not commute with restriction of scalars, but the
lax comparison

`(F|_𝒜) ⊗_𝒜 (G|_𝒜) ⟶ (F ⊗_ℬ G)|_𝒜`

of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsLax` is an epimorphism
(`Stacks.SheafOfModules.TensorRestrictScalars.epi_laxComparison`), and precomposition with an
epimorphism does not change an image subobject. So a morphism defined on `F ⊗_ℬ G` and a morphism
defined on the `𝒜`-linear tensor product of the restrictions have the *same image*, even though
their sources differ.

This is the mechanism by which a filtration of a sheaf of `ℬ`-modules by images of morphisms out
of tensor products over `ℬ` can be recognised as a filtration by images of morphisms out of
tensor products over `𝒜`: the two descriptions of a step agree on the nose, with no comparison of
the sources.

## Main results

* `Stacks.SheafOfModules.TensorRestrictScalars.imageSubobject_laxComparison_comp`: the image of
  a morphism out of `(F ⊗_ℬ G)|_𝒜` is the image of its precomposition with the lax comparison.
* `Stacks.SheafOfModules.TensorRestrictScalars.imageSubobject_laxComparison_comp_map`: the same
  for a morphism restricted from one defined over `ℬ`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open PresheafOfModules (ringedSpaceOfSheaf)

noncomputable section

universe u

namespace Stacks.SheafOfModules.TensorRestrictScalars

variable {Y : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})
  (ρ : A ⟶ B) (F G : SheafOfModules.{u} (Tensor.ringSheaf B))

/-- Sheaves of modules over the smaller ring sheaf form an abelian category, which is what gives
the image subobjects below. The instance is supplied explicitly: finding it at these binders
exceeds the default instance-synthesis budget, exactly as in
`StacksFrontier/AlgebraicGeometry/DeRham/ExteriorPowerFiltration.lean`. -/
local instance abelianBaseSheaves :
    Abelian (_root_.SheafOfModules.{u} (Tensor.ringSheaf A)) :=
  _root_.SheafOfModules.instAbelian _

/-- **The image of a morphism out of `(F ⊗_ℬ G)|_𝒜` is the image of its precomposition with the
lax comparison `(F|_𝒜) ⊗_𝒜 (G|_𝒜) ⟶ (F ⊗_ℬ G)|_𝒜`.** The comparison is an epimorphism, and
precomposing with an epimorphism does not change an image. -/
theorem imageSubobject_laxComparison_comp
    {Q : _root_.SheafOfModules.{u} (Tensor.ringSheaf A)}
    (g : (restrictScalarsSheaf A B ρ).obj (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).obj G) ⟶
        Q) :
    imageSubobject (laxComparison A B ρ F G ≫ g) = imageSubobject g :=
  Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp _ (epi_laxComparison A B ρ F G) g

/-- **A morphism of sheaves of `ℬ`-modules out of `F ⊗_ℬ G` and the `𝒜`-linear morphism it
induces on `(F|_𝒜) ⊗_𝒜 (G|_𝒜)` have the same image.** This is
`Stacks.SheafOfModules.TensorRestrictScalars.imageSubobject_laxComparison_comp` for a restricted
morphism, which is the form a filtration by images of wedge products consumes. -/
theorem imageSubobject_laxComparison_comp_map
    {P : _root_.SheafOfModules.{u} (Tensor.ringSheaf B)}
    (g : ((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).obj G ⟶ P) :
    imageSubobject (laxComparison A B ρ F G ≫ (restrictScalarsSheaf A B ρ).map g) =
      imageSubobject ((restrictScalarsSheaf A B ρ).map g) :=
  imageSubobject_laxComparison_comp A B ρ F G _

end Stacks.SheafOfModules.TensorRestrictScalars

end

end

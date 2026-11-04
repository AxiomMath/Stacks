module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# The degenerate projection formula `h_*𝒪_T ⊗_{𝒪_S} H ≅ h_*(h^*H)`

Let `h : T ⟶ S` be an affine morphism of schemes and `H` a quasi-coherent `𝒪_S`-module. Stacks
Tag 0FZE (`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap`, proved in
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal`) gives, for every quasi-coherent
`𝒪_T`-module `G`, an isomorphism `h_*G ⊗_{𝒪_S} H ≅ h_*(G ⊗_{𝒪_T} h^*H)`. This file specializes
`G` to the structure sheaf `𝒪_T`, viewed as a module over itself, and cancels the resulting
`𝒪_T ⊗_{𝒪_T} -` factor on the right with the left unitor of the tensor product sheaf, to obtain
`h_*𝒪_T ⊗_{𝒪_S} H ≅ h_*(h^*H)`. This is the computation underlying Stacks Tag 01Z0.

## Main results

* `Stacks.AlgebraicGeometry.ProjectionFormula.pushforwardUnitTensorIso`: for an affine morphism
  `h : T ⟶ S` and a quasi-coherent `𝒪_S`-module `H`, the isomorphism
  `h_*𝒪_T ⊗_{𝒪_S} H ≅ h_*(h^*H)`.

## Implementation notes

The structure sheaf of `T`, viewed as a module over itself, is `AlgebraicGeometry.Scheme.unitModule
T`, and its quasi-coherence is already an instance (`StacksDraft.AlgebraicGeometry.Descent.
PullbackSectionsSheaf.UnitComparison`), so specializing the first argument `G` of
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent` to it needs no
new quasi-coherence argument. The left unitor canceling the `𝒪_T ⊗_{𝒪_T} -` factor is
`Stacks.RingedSpace.tensorSheafUnitLeftIso` from `StacksDraft.Algebra.Category.ModuleCat.Sheaf.
TensorUnitSections`, typed exactly over the uncurried tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` that `projectionFormulaIsoOfQuasicoherent` itself is
stated against, so no transport between spellings of the tensor product sheaf is needed either.

## References

* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.ProjectionFormula

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-- **The degenerate projection formula at the structure sheaf of the source.** For an affine
morphism `h : T ⟶ S` and a quasi-coherent `𝒪_S`-module `H`, the direct image of the structure
sheaf `𝒪_T` tensored with `H` is isomorphic to the direct image of the pullback of `H`:
`h_*𝒪_T ⊗_{𝒪_S} H ≅ h_*(h^*H)`.

Obtained from the projection-formula isomorphism of Stacks Tag 0FZE at `G := 𝒪_T`, followed by
the left unitor canceling the resulting `𝒪_T ⊗_{𝒪_T} h^*H` factor. -/
def pushforwardUnitTensorIso [IsAffineHom h] (H : S.Modules) (hH : H.IsQuasicoherent) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pushforward h).obj (Scheme.unitModule T), H) ≅
      (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj H) :=
  projectionFormulaIsoOfQuasicoherent h (Scheme.unitModule T) H inferInstance hH ≪≫
    (Scheme.Modules.pushforward h).mapIso
      (Stacks.RingedSpace.tensorSheafUnitLeftIso T.toRingedSpace
        ((Scheme.Modules.pullback h).obj H))

end Stacks.AlgebraicGeometry.ProjectionFormula

end

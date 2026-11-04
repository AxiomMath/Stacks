module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne

/-!
# Pullback of modules on algebraic spaces and tensor products

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  The pullback `f^*` of modules on the small
étale sites commutes with the tensor product sheaf in which the tensor powers of Stacks 01CU are
formed (Stacks 03EL), and it carries the structure sheaf to the structure sheaf; hence the
pullback of an invertible `𝒪_Y`-module is invertible (Stacks 0B8L).  The comparison
`f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` of integer tensor powers built from these is
`AlgebraicGeometry.Space.modulePullbackInvertibleTensorPowerIso`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackSheafTensorIso`: `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`, for the
  tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` in which the tensor powers of
  Stacks 01CU are formed.

## Main results

* `AlgebraicGeometry.Space.isInvertible_modulePullback`: the pullback of an invertible module is
  invertible.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03EL for algebraic spaces**: `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`. -/
def modulePullbackSheafTensorIso (f : X ⟶ Y) (M N : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj
        ((modulePullback B S hS f).obj M)).obj ((modulePullback B S hS f).obj N) :=
  (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS f)).app (M, N)

/-- **The pullback of an invertible module along a morphism of algebraic spaces is invertible**
(Stacks 0B8L): if `L ⊗ N ≅ 𝒪_Y` then `f^*L ⊗ f^*N ≅ f^*(L ⊗ N) ≅ f^*𝒪_Y ≅ 𝒪_X`. -/
theorem isInvertible_modulePullback (f : X ⟶ Y) (L : Modules.{u, u} B S hS Y.1 Y.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property L] :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
      ((modulePullback B S hS f).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (C := (smallEtaleRingedSite B S hS Y.1 Y.2).C) (J := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
    L).mp hL
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (C := (smallEtaleRingedSite B S hS X.1 X.2).C) (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
    (O := structurePresheaf B S hS X.1) _).mpr ⟨(modulePullback B S hS f).obj N,
      ⟨(modulePullbackSheafTensorIso B S hS f L N).symm ≪≫
        (modulePullback B S hS f).mapIso e ≪≫ modulePullbackUnitIso B S hS f⟩⟩

end AlgebraicGeometry.Space

end

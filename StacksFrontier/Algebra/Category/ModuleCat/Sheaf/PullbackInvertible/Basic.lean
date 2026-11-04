module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of an invertible module is invertible

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `L` be an invertible
sheaf of `𝒪_Y`-modules, that is, one whose left tensor functor is an equivalence
(`Stacks.SheafOfModules.IsInvertible`, Tag 01CS).  This file proves that `f^*L` is an
invertible sheaf of `𝒪_X`-modules.

The argument is the one in the Stacks Project.  Invertibility is equivalent to the existence
of a tensor inverse (`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`, Tag
0B8K), so choose `N` with `L ⊗_{𝒪_Y} N ≅ 𝒪_Y`.  Pullback commutes with the tensor product
(`Stacks.RingedSpace.comparisonBifunctorIso`, Tag 01CD) and carries the unit to the unit
(`SheafOfModules.pullbackObjUnitToUnit`, which is invertible because `f^*` is computed by a
final functor on opens), so

`f^*L ⊗_{𝒪_X} f^*N ≅ f^*(L ⊗_{𝒪_Y} N) ≅ f^*𝒪_Y ≅ 𝒪_X`,

and Tag 0B8K applies again, on `X` this time.

## Main results

* `Stacks.RingedSpace.modulePullback_isInvertible` — **Stacks 0B8L**, the pullback of an
  invertible sheaf of modules along a morphism of ringed spaces is invertible.  It is an
  instance, so invertibility of a pullback is found by instance search.
* `Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry` — the same statement for
  the library's other formalisation of invertibility,
  `AlgebraicGeometry.SheafOfModules.IsInvertible`.

## References

* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction

/-- **Stacks Project, Tag 0B8L.** The pullback of an invertible module along a
morphism of ringed spaces is invertible. -/
@[stacks 0B8L, instance]
theorem modulePullback_isInvertible {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y))
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf) L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
      ((modulePullback f).obj L) := by
  let hX := Presheaf.isSheaf_comp_of_isSheaf
    (Opens.grothendieckTopology X.carrier) X.presheaf
    (forget₂ CommRingCat RingCat) X.IsSheaf
  apply (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (hO := hX) ((modulePullback f).obj L)).mpr
  let hY := Presheaf.isSheaf_comp_of_isSheaf
    (Opens.grothendieckTopology Y.carrier) Y.presheaf
    (forget₂ CommRingCat RingCat) Y.IsSheaf
  obtain ⟨N, ⟨e⟩⟩ :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit (hO := hY) L).mp inferInstance
  let : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  have : (opensMap f).Final := final_of_representablyFlat _
  have e₂ : (modulePullback f).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
          (forget₂ CommRingCat RingCat) hY⟩).obj L).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) hX⟩).obj ((modulePullback f).obj L)).obj
        ((modulePullback f).obj N) :=
    (comparisonBifunctorIso f).app (L, N)
  let e₃ := asIso (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f))
  exact ⟨(modulePullback f).obj N, ⟨e₂.symm ≪≫ (modulePullback f).mapIso e ≪≫ e₃⟩⟩

/-- **Stacks Project, Tag 0B8L**, restated for `AlgebraicGeometry.SheafOfModules.IsInvertible`.
The library carries two formalisations of invertibility of a sheaf of modules — this one and
`Stacks.SheafOfModules.IsInvertible` — which agree by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` but are deliberately not bridged by
instances.  Consumers stated against this spelling, such as the Gysin operations of chapter 42,
use this form.  It is not an instance for the same reason the bridge is not. -/
theorem modulePullback_isInvertible_algebraicGeometry {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y))
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf) L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
      ((modulePullback f).obj L) :=
  have : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ h
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (modulePullback_isInvertible f L)

end Stacks.RingedSpace

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Flat pullback of a torsion-free module

The pullback of a torsion-free quasi-coherent module along a flat morphism of integral schemes is
torsion free.

Torsion freeness of a quasi-coherent module on an integral scheme is detected on stalks, so the
statement reduces to the following algebra: if `R → S` is a flat local homomorphism and `M` is a
torsion-free `R`-module, then `S ⊗[R] M` is a torsion-free `S`-module. The stalk of the pullback
is identified with that base change by the stalk formula for the pullback of modules on ringed
spaces.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_modulePullback`: flat pullback
  preserves torsion freeness.

## Implementation notes

The conclusion is stated with the quasi-coherence of the pullback supplied inside the statement
by a `letI`, because `Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree` is only defined for
a quasi-coherent module and that instance is not found by synthesis from quasi-coherence of the
source.

## References

* [Stacks Project, Tag 0AXV](https://stacks.math.columbia.edu/tag/0AXV)
* [Stacks Project, Tag 0AXW](https://stacks.math.columbia.edu/tag/0AXW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- The stalk of the flat pullback of a torsion-free quasi-coherent module is torsion free over
the local ring of the source: it is the base change of the stalk along a flat homomorphism. -/
private theorem isTorsionFree_stalk_modulePullback {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (G : Y.Modules) [G.IsQuasicoherent] (hG : IsTorsionFree G) (x : X) :
    letI : Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        ((Scheme.Modules.pullback f).obj G).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) ((Scheme.Modules.pullback f).obj G).val x
    Module.IsTorsionFree (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        ((Scheme.Modules.pullback f).obj G).val.presheaf x) := by
  let g := f.toLRSHom.toShHom
  let y := g.hom.base x
  let R := Y.presheaf.stalk y
  let S := X.presheaf.stalk x
  let M := ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) G.val.presheaf y)
  let : Algebra R S := (g.hom.stalkMap x).hom.toAlgebra
  let : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val y
  let : Module.IsTorsionFree R M :=
    (AlgebraicGeometry.isTorsionFree_iff_forall_stalk G).mp hG y
  let : Module.Flat R S := by
    change (f.stalkMap x).hom.Flat
    exact (Flat.iff_flat_stalkMap f).mp inferInstance x
  let : Module.IsTorsionFree S (TensorProduct R S M) :=
    isTorsionFree_baseChange_of_flat
  obtain ⟨hstalk, -⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv g G x
  have hIso :
      ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        ((Scheme.Modules.pullback f).obj G).val.presheaf x) ≃ₗ[S]
        TensorProduct R S M := hstalk
  exact hIso.injective.moduleIsTorsionFree hIso (fun r m => hIso.map_smul r m)

/-- **Stacks Project, Tag 0AXV.** The flat pullback of a torsion-free quasi-coherent module on an
integral scheme is torsion free. -/
@[stacks 0AXV, ega "IV 9.4.9" "partial"]
theorem isTorsionFree_modulePullback {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (G : Y.Modules) [G.IsQuasicoherent] (hG : IsTorsionFree G) :
    letI : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent :=
      @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent X.toRingedSpace
        Y.toRingedSpace f.toLRSHom.toShHom G ‹G.IsQuasicoherent›
    IsTorsionFree ((Scheme.Modules.pullback f).obj G) := by
  let : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent X.toRingedSpace
      Y.toRingedSpace f.toLRSHom.toShHom G ‹G.IsQuasicoherent›
  exact (AlgebraicGeometry.isTorsionFree_iff_forall_stalk
    ((Scheme.Modules.pullback f).obj G)).2 fun x => isTorsionFree_stalk_modulePullback f G hG x

end Stacks.AlgebraicGeometry.ReflexiveModules

end

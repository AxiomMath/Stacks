module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness descends along an fpqc covering

A quasi-coherent module on a scheme is finite locally free as soon as its pullback to every
member of an fpqc covering is finite locally free.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover`: Stacks Tag 05B2.

## Implementation notes

This is the proof in the source. Finite local freeness of a sheaf of modules on a scheme is
flatness together with finite presentation, which is the equivalence of entries (1) and (4) of
Tag 05P2, available as
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation`. Each
of the two properties on the right descends along an fpqc covering: flatness by Tag 05B1
(`AlgebraicGeometry.isFlat_of_pullback_fpqc`) and finite presentation by Tag 05B0
(`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`). So the hypothesis is pushed
through the equivalence on each member of the covering, the two halves are descended
separately, and the conclusion is read off the equivalence on the base.

The flatness input is stated for a covering family presented as membership of its presieve in
the fpqc precoverage, and for the pullback functor
`RingedSpaceModuleAdjunction.modulePullback` of sheaves of modules over ringed spaces; the
covering here is an `AlgebraicGeometry.Scheme.Cover` for the fpqc precoverage, whose `mem₀`
field is exactly that membership, and the two pullback functors agree on a morphism of schemes.

## References

* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
-/

@[expose] public section

open CategoryTheory RingedSpaceModuleAdjunction

universe u v

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05B2.** Let `M` be a quasi-coherent module on a scheme `X` and let
`𝒰` be an fpqc covering of `X`. If the pullback of `M` to every member of `𝒰` is finite locally
free, then `M` is finite locally free. -/
@[stacks 05B2, sga "1 VIII 1.10" "finite locally free"]
public theorem isFiniteLocallyFree_of_pullback_fpqcCover {X : Scheme.{u}} (M : X.Modules)
    [hqc : M.IsQuasicoherent] (𝒰 : X.Cover.{v} Scheme.fpqcPrecoverage)
    (h : ∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj M)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  have hlocal (i) := (SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation
    ((Scheme.Modules.pullback (𝒰.f i)).obj M)).mp (h i)
  have hfp : M.IsFinitePresentation :=
    isFinitePresentation_of_pullback_fpqcCover M 𝒰 fun i => (hlocal i).2
  -- Tag 05B1 reads the structure sheaf as that of the underlying ringed space, which is the
  -- same sheaf of rings but not the spelling instance synthesis sees.
  let : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) M := hqc
  exact (SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation M).mpr
    ⟨isFlat_of_pullback_fpqc 𝒰.f 𝒰.mem₀ M fun i => (hlocal i).1, hfp⟩

end AlgebraicGeometry

end

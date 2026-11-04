module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Tag 01R2: the conormal sheaf of an immersion is quasi-coherent

Let `i : Z ⟶ X` be an immersion of schemes.  It factors canonically as a closed immersion
`i.liftCoborder : Z ⟶ i.coborderRange` followed by the open immersion
`i.coborderRange.ι : i.coborderRange ⟶ X`.  Writing `ℐ` for the ideal sheaf of
`i.liftCoborder`, the **conormal sheaf** of `i` is `i.liftCoborder^* ℐ`; on an affine chart
over which `i` is a closed immersion cut out by an ideal `I` this is `I/I²`, which is the
form in which [Stacks, Tag 01R2] states the definition.

The sheaf itself is `Stacks.Conormal.conormalSheaf`, which this file re-exports from
`StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison`; what is proved here
is the quasi-coherence half of the definition.

## Main results

* `Stacks.Conormal.conormalSheaf_isQuasicoherent`: **Tag 01R2**, the conormal sheaf is
  quasi-coherent, which is part of the assertion of the definition.

## Implementation notes

`Stacks.Conormal.conormalSheaf` is an `abbrev` so that the declarations which were stated
before it existed against the written-out pullback — `Stacks.Conormal.affineConormalIsoCotangent`
(Tag 01R3 (2)) and `Stacks.Divisors.normalSheaf` — are statements about `conormalSheaf` at
reducible transparency, with nothing to transport.

Quasi-coherence is the composite of two facts already in the development: the ideal sheaf of a
closed immersion of schemes is quasi-coherent
(`Stacks.Conormal.isQuasicoherent_idealSheaf`, which is Tag 01R8 (1) for a closed immersion),
and the pullback of a quasi-coherent module along a morphism of ringed spaces is quasi-coherent
(`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent`, Tag 01BG).  Nothing
affine-local is needed.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction Opposite

universe u

namespace Stacks.Conormal

/-- **Stacks Project, Tag 01R2.**  The conormal sheaf of an immersion is quasi-coherent. -/
@[stacks 01R2 "quasi-coherence"]
instance conormalSheaf_isQuasicoherent {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    (conormalSheaf i).IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    i.liftCoborder.toLRSHom.toShHom
    (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)
    (isQuasicoherent_idealSheaf i.liftCoborder)

end Stacks.Conormal

end

module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the Fourier-Mukai kernel of a relative equivalence, unconditionally

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes and let `K` be the Fourier-Mukai kernel
of a relative equivalence from `X` to `Y` over `S` ([Stacks, Tag 0G0I]). For any morphism
`s : S₁ ⟶ S`, with `X₁ = X ×_S S₁` and `Y₁ = Y ×_S S₁`, the pullback
`K₁ = L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^* K` is the Fourier-Mukai kernel of a relative equivalence from
`X₁` to `Y₁` over `S₁`. This is [Stacks, Tag 0G0K].

`AlgebraicGeometry.isRelativeEquivalenceKernel_derivedPullback` proves this from the
proposition `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent`, which is
[Stacks, Tag 08IB]. That proposition is proved by
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`; this module composes the two. It
cannot be done in the file of the former without changing its imports and its registration,
which stay as they are.

## Main results

* `AlgebraicGeometry.isRelativeEquivalenceKernel_baseChange` — **[Stacks, Tag 0G0K]**.

## Implementation notes

*The hypotheses on `f` and `g`.* The source's Section 0G0F fixes `X ⟶ S` and `Y ⟶ S` smooth and
proper. The statement here asks only that `f` and `g` be flat, separated, quasi-compact and
quasi-separated, all of which smooth proper morphisms are, so it is more general than the
source's. The morphism `s : S₁ ⟶ S` is arbitrary, as in the source.

*Which side of the fibre product.* The source writes `X₁ = S₁ ×_S X`; here `X₁` is the chosen
pullback `X ×_S S₁` with structure morphism `pullback.snd f s`. The two differ by the symmetry of
the fibre product.

## References

* [Stacks Project, Tag 0G0K](https://stacks.math.columbia.edu/tag/0G0K)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0G0K]: a relative equivalence is stable under base change.** Let `f : X ⟶ S`
and `g : Y ⟶ S` be flat, separated, quasi-compact and quasi-separated (for instance smooth and
proper, as in the source), and let `K` be the Fourier-Mukai kernel of a relative equivalence
from `X` to `Y` over `S` ([Stacks, Tag 0G0I]). Let `s : S₁ ⟶ S` be any morphism of schemes, and
write `X₁ = X ×_S S₁` and `Y₁ = Y ×_S S₁` with their projections to `S₁`. Then

`K₁ = L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^* K`

is the Fourier-Mukai kernel of a relative equivalence from `X₁` to `Y₁` over `S₁`.

This is `AlgebraicGeometry.isRelativeEquivalenceKernel_derivedPullback` at
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`, which is [Stacks, Tag 08IB]. -/
@[stacks 0G0K "the whole lemma, for an arbitrary base change S1 -> S; f and g need only be \
flat, separated and qcqs, all implied by the source's smooth proper hypotheses. Tag 08IB enters \
through AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent, which proves it"]
theorem isRelativeEquivalenceKernel_baseChange
    {S X Y S₁ : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : S₁ ⟶ S)
    [IsSeparated f] [IsSeparated g] [Flat f] [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    {K : DerivedCategory (pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) :
    IsRelativeEquivalenceKernel (pullback.snd f s) (pullback.snd g s)
      ((derivedPullback (fourierMukaiBaseChangeMap f g s).toLRSHom.toShHom).obj K) :=
  isRelativeEquivalenceKernel_derivedPullback derivedBaseChangeIsIsoOnQuasicoherent f g s hK

end AlgebraicGeometry

end

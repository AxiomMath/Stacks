module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Topology
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies

/-!
# Syntomic coverings of the big crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  A family of morphisms
`{(Uᵢ, Tᵢ, δᵢ) ⟶ (U, T, δ)}` in the big crystalline category `CRIS(X/S)` is a *syntomic
covering* when `Uᵢ = U ×_T Tᵢ` for every `i` and `{Tᵢ ⟶ T}` is a syntomic covering of schemes,
that is a jointly surjective family of syntomic morphisms.  Together with the Zariski, étale,
smooth and fppf coverings of `StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Topology` this is
part (1) of [Stacks, Tag 07IB].

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.IsSyntomicCovering` — a syntomic covering
  family of divided power thickenings, [Stacks, Tag 07IB].

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.IsSyntomicCovering.isFppfCovering` — a
  syntomic covering family of divided power thickenings is an fppf covering family.

## References

* [Stacks Project, Tag 07IB](https://stacks.math.columbia.edu/tag/07IB)
* [Stacks Project, Tag 021N](https://stacks.math.columbia.edu/tag/021N)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-- **Stacks Project, Tag 07IB.**  A syntomic covering family of divided power thickenings of
`X/S`: every `Uᵢ` is `U ×_T Tᵢ` and `{Tᵢ ⟶ T}` is a syntomic covering of schemes. -/
@[stacks 07IB "(1), syntomic coverings"]
abbrev IsSyntomicCovering {B : Thickening S} (E : PreZeroHypercover.{u + 1} B) : Prop :=
  IsCovering (Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u})) E

/-- A syntomic covering family of divided power thickenings is an fppf covering family, since a
syntomic covering of schemes is an fppf covering, [Stacks, Tag 021N]. -/
theorem IsSyntomicCovering.isFppfCovering {B : Thickening S}
    {E : PreZeroHypercover.{u + 1} B} (hE : IsSyntomicCovering E) : IsFppfCovering E :=
  ⟨hE.1, Scheme.syntomicPrecoverage_le_fppfPrecoverage _ hE.2⟩

end Crystalline.GlobalCrystallineSituation.Thickening

end

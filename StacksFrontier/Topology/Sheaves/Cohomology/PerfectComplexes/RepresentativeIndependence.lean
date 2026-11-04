module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalCriterion
import StacksFrontier.Algebra.Homology.QuasiIsoRoof
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Perfectness is independent of the representative

An object `K` of the derived category of `𝒪_X`-modules is perfect when *some* complex
representing it is a perfect complex. This file shows that *every* complex representing a perfect
object is then perfect, so that the two conditions — "this complex is perfect" and "the object it
represents is perfect" — agree for every representative.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_isPerfect_representation`: any complex
  representing a perfect object of the derived category is itself a perfect complex. This is
  [Stacks, Tag 08CN].

## Implementation notes

Two complexes representing the same object of the derived category are joined by a roof of
quasi-isomorphisms (`CochainComplex.quasiIsoRoof_iff_nonempty_iso`), and perfectness of complexes
is invariant under such roofs
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_iff_of_quasiIsoRoof`). The argument therefore
takes place at the level of complexes and uses no derived category of an open subspace; the
derived category of `X`, in which `K` lives, is any model. All universes of the ringed space
coincide, as they must for `StrictlyPerfect.OXMod` to exist.

## References

* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- **Stacks 08CN.** Every complex representing a perfect object of the derived category of
`𝒪_X`-modules is itself a perfect complex.

Perfectness of `K` provides one perfect representative `E`. The isomorphism `Q(E) ≅ Q(F)` with
the complex `F` at hand is a roof of quasi-isomorphisms between `E` and `F`, and perfectness of
complexes is invariant under roofs. -/
@[stacks 08CN "representative_independence"]
theorem isPerfectComplex_of_isPerfect_representation
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {K : DerivedCategory (OXMod.{u, u} X)} (hK : IsPerfect K)
    {F : CochainComplex (OXMod.{u, u} X) ℤ}
    (hF : Nonempty (DerivedCategory.Q.obj F ≅ K)) :
    IsPerfectComplex F := by
  obtain ⟨E, hE, ⟨eEK⟩⟩ := hK
  obtain ⟨eFK⟩ := hF
  exact (isPerfectComplex_iff_of_quasiIsoRoof
    ((CochainComplex.quasiIsoRoof_iff_nonempty_iso E F).2 ⟨eEK ≪≫ eFK.symm⟩)).1 hE

end AlgebraicGeometry.RingedSpace

end

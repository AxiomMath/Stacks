module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQuasiCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula on `D_QCoh`

We prove `AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent`: for a quasi-compact
quasi-separated morphism of schemes and complexes with quasi-coherent cohomology, the
projection-formula morphism of [Stacks, Tag 0B53] is an isomorphism, that is,
[Stacks, Tag 08EU]. The Fourier–Mukai development of [Stacks, Tag 0FYS] takes this proposition
as a hypothesis.

## Main results

* `AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`: **[Stacks, Tag 08EU]**, the
  projection-formula morphism is an isomorphism on complexes with quasi-coherent cohomology.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08EU].** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes. For `E` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)` the projection-formula morphism of
[Stacks, Tag 0B53]

`R f_* E ⊗^𝐋_{𝒪_Y} K ⟶ R f_*(E ⊗^𝐋_{𝒪_X} L f^* K)`

is an isomorphism; that is, `AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent` holds. -/
@[stacks 08EU "the whole tag, in the shape of the proposition \
AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent, which this proves"]
theorem projectionFormulaIsIsoOnQuasicoherent :
    ProjectionFormulaIsIsoOnQuasicoherent.{u} := by
  intro V W p hqc hqs E A hE hA
  have := hqc
  have := hqs
  exact Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent
    p E hE A hA

end AlgebraicGeometry

end

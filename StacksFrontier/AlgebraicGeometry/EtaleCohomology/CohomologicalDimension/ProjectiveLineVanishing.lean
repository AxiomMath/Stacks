module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ProjectiveLineCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of the higher direct images along the projective line above degree two

For a ring `A` let `g : ℙ¹_A ⟶ Spec A` be the projective line. Then `R^q g_* 𝒢 = 0` for every
torsion abelian sheaf `𝒢` on the small étale site of `ℙ¹_A` and every `q > 2`. This is the case
of `Stacks.EtaleCohomology.properDirectImageVanishingStatement` for the proper morphism `g`, all of
whose fibres have dimension at most one
(`AlgebraicGeometry.topologicalKrullDim_fiber_projectiveLine_le_one`).

## Main results

* `AlgebraicGeometry.isZero_rightDerived_etaleAbelianDirectImage_projectiveLine`: the vanishing
  above.

## References

* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- For every ring `A`, every torsion abelian sheaf `𝒢` on the small étale site of `ℙ¹_A` and
every `q > 2`, the higher direct image `R^q g_* 𝒢` along the structure morphism
`g : ℙ¹_A ⟶ Spec A` is zero. -/
@[sga "4 XII 5.3" "special case"]
public theorem isZero_rightDerived_etaleAbelianDirectImage_projectiveLine (A : Type u)
    [CommRing A] (G : Sheaf (projectiveLine A).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty (projectiveLine A).smallEtaleTopology G)
    (q : ℕ) (hq : 2 < q) :
    IsZero (((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0}
      (projectiveLine A ↘ Spec (.of A))).rightDerived q).obj G) :=
  Stacks.EtaleCohomology.properDirectImageVanishingStatement (projectiveLine A ↘ Spec (.of A)) 1
    (topologicalKrullDim_fiber_projectiveLine_le_one A) G hG q
    (by exact_mod_cast (show 2 * 1 < q by lia))

end AlgebraicGeometry

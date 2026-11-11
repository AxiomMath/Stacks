module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent

/-!
# The étale sheaf condition from quasi-coherence (Stacks 06WK, clause (1))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of Stacks 06TV. Stacks 06WK says that `F` is quasi-coherent in
the sense of Stacks 06WG exactly when

1. `F` is locally quasi-coherent (Stacks 06WJ), and
2. for every arrow `φ : x ⟶ y` of `𝒳` lying over a morphism of schemes `f : U ⟶ V` the
   comparison map `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of Stacks 06WC is an isomorphism.

Local quasi-coherence is a conjunction: the étale sheaf condition, and quasi-coherence of the
restriction to the small étale site of the scheme below each object. This file proves the
forward direction of its first conjunct, which is the first step of the source's proof: a
quasi-coherent module is a sheaf for the inherited fppf topology, and the inherited étale
topology is coarser, so it is a sheaf for that as well.

## Main results

* `AlgebraicGeometry.Stack.associatedTopology_mono`: the site of Stacks 06TP is monotone in the
  topology chosen on the underlying category of schemes.
* `AlgebraicGeometry.Stack.isSheaf_etale_of_isQuasicoherent`: the étale sheaf condition of
  clause (1) of Stacks 06WK, in the forward direction, at every module universe.

## Where Stacks 06WK is

The whole biconditional of Stacks 06WK, both directions and both clauses, is
`Stack.isQuasicoherentFppf_iff_isLocallyQuasicoherent_and_isIso_sheafifiedRestrictComparison`
in `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIffComparisonIso`, which
carries the tag. The result here is the first step of its proof, kept because it holds at every
module universe `m`, while the biconditional is stated at the universe `u` of the schemes, where
the pullback of Stacks 06WC exists. The hypothesis below is quasi-coherence in the sense of
Stacks 06WG: `AlgebraicGeometry.FibredSite.ringStructureSheafCore_fppf_eq_stack` identifies the
coefficient sheaf of rings used here with the one that Stacks 06WG is stated over.

## References

* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The site of Stacks 06TP is monotone in the topology chosen on the underlying category of
schemes: a coarser topology on the schemes localizes to a coarser topology over `S`, and the
topology inherited along `p` is monotone in the topology it is inherited from. -/
theorem associatedTopology_mono {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    {τ σ : GrothendieckTopology B.Schemes} (h : τ ≤ σ) :
    associatedTopology B S hS p τ ≤ associatedTopology B S hS p σ := by
  have hover : τ.over (B.obj hS) ≤ σ.over (B.obj hS) := by
    intro X R hR
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    exact h _ hR
  exact Precoverage.toGrothendieck_mono fun _ _ hR =>
    ⟨hR.1, GrothendieckTopology.toPrecoverage_monotone hover _ hR.2⟩

/-- **A quasi-coherent module on a category fibred in groupoids is a sheaf for the inherited
étale topology.**

This is the first conjunct of clause (1) of Stacks 06WK in the forward direction, local
quasi-coherence being the étale sheaf condition together with quasi-coherence of the restrictions
to the small étale sites, and it is the first step of the source's proof: quasi-coherence of `F`
in the sense of Stacks 06WG asserts in particular that `F` is a sheaf for the inherited fppf
topology, and the inherited étale topology is coarser. Stacks 06WK itself is
`Stack.isQuasicoherentFppf_iff_isLocallyQuasicoherent_and_isIso_sheafifiedRestrictComparison`. -/
theorem isSheaf_etale_of_isQuasicoherent {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : ∃ h : Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf,
      SheafOfModules.IsQuasicoherentOnSite
        (⟨F, h⟩ : SheafOfModules.{m}
          (ringStructureSheafCore B S hS p hp B.topology le_rfl))) :
    Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf :=
  hF.elim fun h _ =>
    h.of_le (associatedTopology_mono B S hS p (etaleTopology_le_topology B))

end AlgebraicGeometry.Stack

end

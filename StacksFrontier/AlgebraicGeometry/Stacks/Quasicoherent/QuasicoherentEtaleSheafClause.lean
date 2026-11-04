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
* `AlgebraicGeometry.Stack.isSheaf_etale_of_isQuasicoherent`: **Stacks 06WK**, the étale sheaf
  condition of clause (1) in the forward direction.

## The rest of Stacks 06WK, and why it is not here

The biconditional splits into four separable pieces, of which this file delivers one. The
hypothesis below is quasi-coherence in the sense of Stacks 06WG:
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_fppf_eq_stack` identifies the coefficient
sheaf of rings used here with the one that Stacks 06WG is stated over.

* (⟹) clause (1), first conjunct — the étale sheaf condition. This is
  `AlgebraicGeometry.Stack.isSheaf_etale_of_isQuasicoherent`, proved below with no further
  input.
* (⟹) clause (1), second conjunct — for every object `x` the restriction `x^*F|_{U_ét}` is
  quasi-coherent on the small étale site of `U`. Quasi-coherence of `F` is quasi-coherence for
  the *inherited fppf* topology, so a global presentation is only available on an fppf covering
  of `x`, while the conclusion asks for one on an étale covering of each object of the small
  étale site. The passage is quasi-coherence from the inherited fppf topology to a coarser one,
  which is `AlgebraicGeometry.FibredSite.QuasicoherentOnSiteOfLeFppf` at `τ = .etale`, one of
  the two inputs of Stacks 0EM8; it is **no longer a hypothesis**, being proved at the module
  universe `u` of the schemes by
  `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_siteKind` in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine`, so this conjunct is
  available in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentOnSiteCoarserFromFppf` as
  `AlgebraicGeometry.Stack.forallQuasicoherentIsLocallyQuasicoherent` and is not restated here.
  The opposite direction is
  `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_of_siteRestriction`. The
  clause (2) of Descent, Proposition 03DX at `τ = étale` which this library does prove, namely
  `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`, does not supply it:
  that takes a module already quasi-coherent *on the small étale site* and produces the
  `𝒪_U`-module, which is the conclusion sought here and not the hypothesis available.
* (⟹) clause (2) — the comparison maps are isomorphisms. The source reads `𝒳/y` as
  `(Sch/V)_{fppf}` and identifies `y^*F` with the module associated to a quasi-coherent module
  on the scheme `V`, by the essential-surjectivity half of Descent, Proposition 03DX *at the
  big site*, which is a theorem of this library at every base,
  `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`;
  what is not built is the assembly of the comparison maps into that isomorphism, described
  under (⟸) below.
* (⟸) clauses (1) and (2) together imply quasi-coherence. Its sheaf half is Stacks 076T, which
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromFlatBaseChange` carries over
  `AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`. Its quasi-coherence half is *not*
  blocked by a missing prerequisite: Stacks 06WI, available as
  `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImage`, reduces
  it to quasi-coherence of `y^*F` on `(Sch/V)_{fppf}`; clause (1) makes `F|_{V_ét}`
  quasi-coherent, so clause (2) of Descent, Proposition 03DX at `τ = étale` applies and
  produces the quasi-coherent `𝒪_V`-module `𝓕_V`; and Descent, Lemma 03DV, available as
  `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`,
  makes `𝓕_V^a` quasi-coherent on `(Sch/V)_{fppf}`. What is missing is only the step the source
  states as "condition (2) now signifies": an isomorphism `y^*F ≅ 𝓕_V^a` of sheaves of modules
  on `(Sch/V)_{fppf}`, assembled from the comparison maps `c_φ` of clause (2), which supply its
  value at each object but not yet its compatibility with the arrows. That assembly is not
  built here.

None of the three is stated here, with or without those inputs as hypotheses.

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

/-- **Stacks 06WK.** A quasi-coherent module on a category fibred in groupoids is a sheaf for the
inherited étale topology.

This is the first conjunct of clause (1) of the source, local quasi-coherence being the étale
sheaf condition together with quasi-coherence of the restrictions to the small étale sites, and
it is the first step of the source's proof: quasi-coherence of `F` in the sense of Stacks 06WG
asserts in particular that `F` is a sheaf for the inherited fppf topology, and the inherited
étale topology is coarser. -/
@[stacks 06WK "the étale sheaf condition, which is the first conjunct of clause (1), in the \
forward direction"]
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

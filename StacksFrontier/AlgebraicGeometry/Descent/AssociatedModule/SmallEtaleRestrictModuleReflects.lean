module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit

/-!
# Restriction to the small Zariski site reflects isomorphisms of quasi-coherent modules

Let `S` be a scheme contained in a big étale site and let `𝒢`, `𝒢'` be quasi-coherent
`𝒪`-modules on the small étale site of `S`.  If their restrictions along the inclusion of the
small Zariski site are isomorphic, then `𝒢` and `𝒢'` are isomorphic.

The counit of the associated-module adjunction is an isomorphism at a quasi-coherent module —
`AlgebraicGeometry.SmallEtale.isIso_counit`, the key step of Descent, Proposition 03DX (2) at
`τ = étale` — so each module is recovered from its restriction as `(𝒢|_{S_Zar})^a`, and the
associated-module functor carries the given isomorphism of restrictions to one of the modules.

## Main results

* `AlgebraicGeometry.SmallEtale.nonempty_iso_of_iso_restrictModule`: **restriction to the small
  Zariski site reflects isomorphisms between quasi-coherent modules on the small étale site.**

## Implementation notes

The quasi-coherence hypothesis that `AlgebraicGeometry.SmallEtale.isIso_counit` also carries,
that the restriction of the module is quasi-coherent on the Zariski site, is not an added
hypothesis: it is `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, which holds
unconditionally.

The conclusion is `Nonempty` rather than a constructed isomorphism because the isomorphism
produced depends on the given one, which is an argument; a `def` would be equally available, and
the consumers of this statement work inside a proof.

No `stacks` attribute is attached: this is a formal consequence of clause (2) of Stacks 03DX at
`τ = étale`, which is already registered where it is proved.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Restriction along the inclusion of the small Zariski site reflects isomorphisms between
quasi-coherent modules on the small étale site.**  Each module is the associated module of its
restriction, by the counit of Descent, Proposition 03DX (2) at `τ = étale`, so an isomorphism of
the restrictions becomes one of the modules. -/
theorem nonempty_iso_of_iso_restrictModule
    (G G' : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : G.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite)
    (e : (restrictModule B S hS).obj G ≅ (restrictModule B S hS).obj G') :
    Nonempty (G ≅ G') := by
  have := isIso_counit B S hS G hG (isQuasicoherent_restrictModule B S hS G hG)
  have := isIso_counit B S hS G' hG' (isQuasicoherent_restrictModule B S hS G' hG')
  exact ⟨(asIso ((associatedModuleAdjunction B S hS).counit.app G)).symm ≪≫
    (associatedModule B S hS).mapIso e ≪≫
    asIso ((associatedModuleAdjunction B S hS).counit.app G')⟩

end AlgebraicGeometry.SmallEtale

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections under a flat quasi-compact morphism with geometrically connected fibres

Let `f : T ⟶ S` be a flat quasi-compact morphism of schemes whose geometric fibres are
connected, and let `F` be a sheaf of sets on the small étale site of `S`.  Then the canonical map
`Γ(S, F) ⟶ Γ(T, f⁻¹F)` is bijective, naturally in `F` [Stacks, Tag 0A3H].

The proof is the source's.  A flat quasi-compact morphism with geometrically connected fibres is
universally submersive (`Stacks.EtaleCohomology.universally_isQuotientMap_of_flat_quasiCompact`),
and for a universally submersive morphism with geometrically connected fibres the canonical
comparison of global sections is an isomorphism [Stacks, Tag 0EZK]
(`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage`).

## Main results

* `Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage_of_flat_quasiCompact`: the
  canonical comparison from global sections downstairs to global sections of the inverse image
  upstairs is an isomorphism.
* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso_of_flat_of_quasiCompact`: the
  resulting natural isomorphism of global-sections functors.

## Implementation notes

`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso_of_flat_quasiCompact` states the
same isomorphism with Tag 0EZK as a hypothesis; Tag 0EZK being proved, the isomorphism here
assumes nothing beyond the source.  Unlike Tag 0EZK, this tag needs no erratum: flatness and
quasi-compactness are stable under base change, so they give universal submersivity outright,
and the étale base change at which plain submersivity fails for 0EZK does not arise here.

## References

* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Tag 0A3H.** For `f : T ⟶ S` flat and quasi-compact with geometrically
connected fibres, the *canonical* comparison `Γ(S, F) ⟶ Γ(T, f⁻¹F)` is an isomorphism for every
sheaf of sets `F` on the small étale site of `S`, naturally in `F`. This is the form in which
the source asserts the tag — it writes `Γ(S, F) = Γ(T, f⁻¹F)` for the canonical map, and proves
that map injective and surjective — and it is stronger than the bare existence of an isomorphism
of global-sections functors, which would not say that the isomorphism is restriction of
sections. -/
@[stacks 0A3H "the form the source asserts: the canonical comparison on global sections, rather \
than a bare isomorphism of global-sections functors"]
public theorem isIso_globalSectionsSmallEtaleInverseImage_of_flat_quasiCompact
    {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f] :
    IsIso (globalSectionsSmallEtaleInverseImage.{u, v} f) :=
  isIso_globalSectionsSmallEtaleInverseImage.{u, v} f
    (universally_isQuotientMap_of_flat_quasiCompact f)

/-- **Stacks Project, Tag 0A3H.** Pullback along a flat quasi-compact morphism with
geometrically connected fibres preserves global sections of every sheaf of sets on the small
étale site, naturally in the sheaf. The isomorphism is the canonical comparison, which
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage_of_flat_quasiCompact`
inverts. -/
@[stacks 0A3H "the natural isomorphism of global-sections functors, with no hypothesis beyond \
the source's"]
public def globalSectionsSmallEtaleInverseImageIso_of_flat_of_quasiCompact
    {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f] :
    Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ≅
      smallEtaleInverseImage.{u, v} f ⋙
        Sheaf.Γ (smallEtaleTopology T) (Type (max (u + 1) v)) :=
  globalSectionsSmallEtaleInverseImageIso.{u, v} f
    (universally_isQuotientMap_of_flat_quasiCompact f)

end Stacks.EtaleCohomology

end

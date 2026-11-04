module

public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product
public import StacksFrontier.AlgebraicGeometry.ClopenLift.ClopenSection
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.ModuleValued
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Quasi-coherence of the generic-point product of a quasi-coherent module

The generic-point decomposition of Stacks Tags 02OW and 0EMH has two halves: one for the sheaf
of meromorphic functions and one for the sheaf of meromorphic sections of a quasi-coherent
module `F`. For the functions, quasi-coherence of the product is
`Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_piGenericPointStalkModule`.
This file proves the same statement for the module-valued contributions
`Stacks.AlgebraicGeometry.GenericPointDecomposition.genericPointStalkModuleOf`, which is the
remaining input to quasi-coherence of the sheaf of meromorphic sections.

## Main results

* `MeromorphicSectionsQcoh.subsingleton_genericPointStalkModuleOf_sections`: that contribution has
  no sections on an open set missing the generic point.
* `MeromorphicSectionsQcoh.isQuasicoherent_piGenericPointStalkModuleOf`: the generic-point product
  of a quasi-coherent module is quasi-coherent.
* `MeromorphicSectionsQcoh.isQuasicoherent_of_isoProduct`: consequently a module isomorphic to that
  product — which is what parts (2) of Tags 02OW and 0EMH assert of the sheaf of meromorphic
  sections — is quasi-coherent.

## Implementation notes

Each of the three ingredients of the functions case generalises, and the two that carry content do
so for a different reason from the structure-sheaf case:

* Quasi-coherence of the contribution of one generic point is
  `AlgebraicGeometry.isQuasicoherent_genericPointStalkModuleOf`: the morphism
  `Spec 𝒪_{X, η} ⟶ X` is affine at a generic point
  (`Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isAffineHom_fromSpecStalk`), and the pullback
  of a quasi-coherent module is quasi-coherent (`Stacks.Modules.isQuasicoherent_pullback`), so the
  direct image is quasi-coherent by Stacks Tag 01SB for affine morphisms. The functions case is the
  special case `F = 𝒪_X`, where the pullback is the structure sheaf of the local scheme.
* The vanishing of the sections away from `η` holds for an arbitrary module on the local scheme,
  not just for its structure sheaf: the preimage of an open set missing `η` is empty, and the
  sections of any sheaf of modules over the empty open set form a subsingleton
  (`Stacks.Tag0B5PClopenLift.subsingleton_sections_bot`). The structure-sheaf case instead reads
  off a subsingleton instance for the ring of sections, which is unavailable for a general module.

The local finiteness argument itself is reused verbatim: `isIso_restrictPiLift` and
`isQuasicoherent_pi` are already stated for an arbitrary family of modules over an arbitrary index
type, so only the two inputs above had to be supplied.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicSectionsQcoh

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointGluing
open Stacks.AlgebraicGeometry.MeromorphicQuasicoherent

variable {X : Scheme.{u}}

/-! ### The contribution of one generic point -/

/-- The contribution of a generic point to the meromorphic sections of a module has no sections on
an open set missing that point: the preimage of such an open set in the local scheme is empty, and
the sections of a sheaf of modules over the empty open set form a subsingleton. -/
theorem subsingleton_genericPointStalkModuleOf_sections (F : X.Modules)
    {η : genericPoints X} {U : X.Opens} (hη : (η : X) ∉ U) :
    Subsingleton Γ(genericPointStalkModuleOf X F η, U) := by
  have h : (X.fromSpecStalk η.1) ⁻¹ᵁ U = ⊥ :=
    GenericPointGluing.fromSpecStalk_preimage_eq_bot η.2 hη
  show Subsingleton
    Γ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F, (X.fromSpecStalk η.1) ⁻¹ᵁ U)
  exact Stacks.Tag0B5PClopenLift.subsingleton_sections_bot _ h

/-! ### The generic-point product -/

/-- **The generic-point product of a quasi-coherent module is quasi-coherent.** On an affine open
only the finitely many generic points lying in that open have sections, so the restriction of the
product there is a finite product of quasi-coherent modules, and quasi-coherence is local on the
base. Only the local finiteness of the irreducible components is needed; no hypothesis on the
weakly associated points, and no hypothesis relating `F` to the generic points. -/
theorem isQuasicoherent_piGenericPointStalkModuleOf (F : X.Modules) [F.IsQuasicoherent]
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents (V : Set X)).Finite) :
    (∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η).IsQuasicoherent := by
  refine QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _ fun V ↦ ?_
  have hsub : ∀ η : genericPoints X, ¬ ((η : X) ∈ (V : X.Opens)) →
      ∀ W : (V : X.Opens).toScheme.Opens,
        Subsingleton Γ(genericPointStalkModuleOf X F η, (V : X.Opens).ι ''ᵁ W) := fun η hη W ↦
    subsingleton_genericPointStalkModuleOf_sections F
      fun h ↦ hη (Scheme.Opens.ι_image_le (V : X.Opens) W h)
  have hiso : IsIso (restrictPiLift (V : X.Opens)
      (fun η : genericPoints X ↦ genericPointStalkModuleOf X F η)
      fun η ↦ (η : X) ∈ (V : X.Opens)) :=
    isIso_restrictPiLift _ _ _ hsub
  have hfinite : Finite {η : genericPoints X // (η : X) ∈ (V : X.Opens)} :=
    finite_genericPoints_subtype X (hfin (V : X.Opens) V.2.isCompact)
  exact (SheafOfModules.isQuasicoherent (V : X.Opens).toScheme.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ _ hiso).symm
    (@isQuasicoherent_pi _ _ hfinite _ fun i ↦
      Scheme.Modules.isQuasicoherent_restrictFunctor (V : X.Opens).ι
        (genericPointStalkModuleOf X F i.1))

/-- Any module isomorphic to the generic-point product of a quasi-coherent module is
quasi-coherent. Parts (2) of Stacks Tags 02OW and 0EMH assert such an isomorphism for the sheaf
of meromorphic sections, so this is the remaining step from either of them to the quasi-coherence
clause of the same tag. -/
theorem isQuasicoherent_of_isoProduct (F : X.Modules) [F.IsQuasicoherent]
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents (V : Set X)).Finite)
    {M : X.Modules} (e : M ≅ ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :
    M.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
    (isQuasicoherent_piGenericPointStalkModuleOf F hfin)

end Stacks.AlgebraicGeometry.MeromorphicSectionsQcoh

end

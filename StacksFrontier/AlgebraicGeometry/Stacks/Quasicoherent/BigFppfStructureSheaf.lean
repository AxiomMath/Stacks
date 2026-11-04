module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf of the big fppf site of a scheme

The presheaf `T ↦ Γ(T, 𝒪_T)` on the big fppf category of schemes over `S` is a sheaf of
rings.  This is fppf descent of functions, the structure-sheaf case of faithfully flat
descent for quasi-coherent modules.

The proof has the same three steps as the small étale case of the same tag.  Global functions
are an fpqc sheaf of types on the category of all schemes.  The canonical functor from the big
fppf category over `S` to all schemes is compatible-preserving, because that category has
fibre products and the functor preserves them.  And every covering sieve of the localized fppf
topology has an fpqc covering image, because the selected covering families of a big fppf site
are fppf coverings of schemes and the fppf precoverage is contained in the fpqc one.

## Main results

* `AlgebraicGeometry.BigFppfOver.compatiblePreserving_toScheme`: the canonical functor to all
  schemes is compatible-preserving for the fpqc topology.
* `AlgebraicGeometry.BigFppfOver.coverPreserving_toScheme`: it is cover preserving from the
  localized fppf topology to the fpqc topology.
* `AlgebraicGeometry.BigFppfOver.isSheaf_globalSections`: the presheaf of global functions on
  the big fppf category over `S` is a sheaf of types.

## Implementation notes

The ring-valued conclusion of the tag, `AlgebraicGeometry.BigFppfOver.structure_isSheaf`, and
the structure sheaf `AlgebraicGeometry.BigFppfOver.structureSheaf` that packages it, are stated
in `StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf`, which this file imports and
re-exports.  They are the same two statements in either place — the sheaf condition on
`Stacks.Sites.structurePresheaf S (Over.post B.inclusion)` for the localized topology — so they
are stated once, there, where they carry the tag.  The descent route of this file reaches them
in one step from `isSheaf_globalSections` above, by
`Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget`: the restriction maps are jointly injective on
a covering sieve, so the ring-valued sheaf condition follows from the type-valued one.  The
imported proof takes the other road and does not use descent at all — global functions are
represented by the affine line, which is an object of every big fppf site, and a big fppf site
is subcanonical.

Cover preservation is proved in two stages because the localized topology is a localization
of a generated topology, and only the generated topology has generators to induct over:
`coverPreserving_of_generators` handles the inclusion of the chosen category of schemes into
all schemes, and `GrothendieckTopology.mem_over_iff` together with
`Sieve.functorPushforward_comp` transports the result along the slice projection.

The single-sieve form `Stacks.Sites.isSheafFor_op_comp` is used rather than
`Functor.isContinuous_of_coverPreserving`, so no sheafification instance on the big fppf site
is needed and the sheaf condition is established directly from the definition.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfSite

variable (B : BigFppfSite.{u})

/-- The inclusion of the chosen category of schemes into all schemes is cover preserving from
the fppf topology of the big site to the fpqc topology, because each selected covering family
is an fppf covering of schemes and fppf coverings are fpqc coverings. -/
public theorem coverPreserving_inclusion :
    CoverPreserving B.topology Scheme.fpqcTopology.{u} B.inclusion := by
  refine coverPreserving_of_generators B.inclusion B.precoverage _ ?_
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [← Sieve.generate_map_eq_functorPushforward]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ (B.isFppfCovering_of_isCovering hE))

end AlgebraicGeometry.BigFppfSite

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical functor from the big fppf category over `S` to all schemes preserves fibre
products: the slice projection does, and the inclusion of the chosen category of schemes
creates them. -/
public instance preservesPullbacks_toScheme :
    PreservesLimitsOfShape WalkingCospan (toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

/-- The canonical functor from the big fppf category over `S` to all schemes is
compatible-preserving: a cospan of the slice is completed by its fibre product there, and the
fibre product of its image is the image of that fibre product. -/
public theorem compatiblePreserving_toScheme :
    CompatiblePreserving.{u} Scheme.fpqcTopology.{u} (toScheme B S hS) := by
  refine Stacks.Sites.compatiblePreserving_of_lift _ _ ?_
  intro Y₁ Y₂ Z g₁ g₂ T f₁ f₂ e
  have h : IsPullback ((toScheme B S hS).map (pullback.fst g₁ g₂))
      ((toScheme B S hS).map (pullback.snd g₁ g₂)) ((toScheme B S hS).map g₁)
      ((toScheme B S hS).map g₂) :=
    (IsPullback.of_hasPullback g₁ g₂).map (toScheme B S hS)
  exact ⟨pullback g₁ g₂, pullback.fst g₁ g₂, pullback.snd g₁ g₂, h.lift f₁ f₂ e,
    pullback.condition, h.lift_fst f₁ f₂ e, h.lift_snd f₁ f₂ e⟩

/-- The canonical functor from the big fppf category over `S` to all schemes is cover
preserving from the localized fppf topology to the fpqc topology. -/
public theorem coverPreserving_toScheme :
    CoverPreserving (topology B S hS) Scheme.fpqcTopology.{u} (toScheme B S hS) := by
  refine ⟨fun {X R} hR => ?_⟩
  rw [GrothendieckTopology.mem_over_iff] at hR
  have key : R.functorPushforward (toScheme B S hS) =
      (Sieve.overEquiv X R).functorPushforward B.inclusion :=
    Sieve.functorPushforward_comp (forget B S hS) B.inclusion R
  rw [key]
  exact B.coverPreserving_inclusion.cover_preserve hR

/-- Global functions on the big fppf category over `S` form a sheaf of types. -/
public theorem isSheaf_globalSections :
    Presieve.IsSheaf (topology B S hS)
      ((toScheme B S hS).op ⋙ Stacks.Sites.globalSectionsSheaf.{u}.obj) := by
  intro X R hR
  exact Stacks.Sites.isSheafFor_op_comp (compatiblePreserving_toScheme B S hS) _ R
    ((coverPreserving_toScheme B S hS).cover_preserve hR)

end AlgebraicGeometry.BigFppfOver

end

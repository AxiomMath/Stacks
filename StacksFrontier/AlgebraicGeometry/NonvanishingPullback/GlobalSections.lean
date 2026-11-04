module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing

/-!
# Tag 0H78 at the `pullbackGlobalSections` spelling

`Stacks.NonvanishingPullback.preimage_nonvanishingLocus` is [Stacks, Tag 0H78] stated with
`Stacks.NonvanishingPullback.pullbackGlobalSection`, the image of a global section under the unit
of the module-pullback adjunction with no restriction map interposed. Everything that *carries* a
pulled-back global section around — the coherent triples of [Stacks, Tag 0F27] in particular,
through `Stacks.Algebraization.globalSectionsMap` — uses
`AlgebraicGeometry.pullbackGlobalSections`, which composes that unit with the restriction along
`f ⁻¹ᵁ ⊤ = ⊤`. The two agree, the restriction being along an identity, and this file records the
tag at the second spelling so that a consumer holding one does not have to rediscover the
comparison.

This had been rediscovered twice already, and neither copy was usable.
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionConstruction.lean` proves
both statements, at lines 129 and 140, as `private` theorems; and
`Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections`
(`StacksFrontier/AlgebraicGeometry/TwistPullbackRatio/Comparison.lean`) is public but states only
the implication from the image to the point, which is the half a consumer that has to read a
nonvanishing locus *back* along the morphism cannot use. Both should be replaced by the
declarations below rather than a fourth copy being written.

## Main results

* `Stacks.NonvanishingPullback.pullbackGlobalSections_eq_pullbackGlobalSection`: the two
  spellings of the pullback of a global section agree.
* `Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections`: **[Stacks,
  Tag 0H78]** at the `AlgebraicGeometry.pullbackGlobalSections` spelling.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.NonvanishingPullback

variable {X Y : Scheme.{u}} (i : X ⟶ Y) (M : Y.Modules)

/-- **The two spellings of the pullback of a global section agree**: the one built from the unit
of `i^* ⊣ i_*` alone, and the one that composes it with the restriction along `i ⁻¹ᵁ ⊤ = ⊤`. That
restriction is along an identity, so the comparison is `Functor.map_id_apply`. -/
theorem pullbackGlobalSections_eq_pullbackGlobalSection (s : Γ(M, ⊤)) :
    pullbackGlobalSections i M s = pullbackGlobalSection i M s := by
  show ((Scheme.Modules.pullback i).obj M).presheaf.map
      (eqToHom (show i ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (pullbackGlobalSection i M s) = _
  exact Functor.map_id_apply _ _ _

/-- **[Stacks, Tag 0H78] at the `AlgebraicGeometry.pullbackGlobalSections` spelling**: the inverse
image of the nonvanishing locus of a global section is the nonvanishing locus of its pullback. -/
theorem preimage_nonvanishingLocus_pullbackGlobalSections (s : Γ(M, ⊤)) :
    i.base ⁻¹' Stacks.Ample.nonvanishingLocus M s =
      Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback i).obj M)
        (pullbackGlobalSections i M s) := by
  rw [pullbackGlobalSections_eq_pullbackGlobalSection]
  exact preimage_nonvanishingLocus i M s

end Stacks.NonvanishingPullback

end

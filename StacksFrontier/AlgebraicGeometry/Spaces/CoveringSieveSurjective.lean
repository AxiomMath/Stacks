module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# A covering sieve of the big fppf site over `S` is jointly surjective on points

Every covering sieve of `AlgebraicGeometry.BigFppfOver.topology` contains, for each point of the
underlying scheme of its base, an arrow whose image contains that point. Consequently a relatively
representable, locally surjective morphism of presheaves on the big fppf site over `S` has
surjective represented base changes.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_mem_range_of_mem_topology`: a covering sieve of the big
  fppf site over `S` is jointly surjective on the points of the underlying schemes.
* `AlgebraicGeometry.Space.presheaf_surjective_of_isLocallySurjective`: a relatively
  representable morphism of presheaves which is locally surjective for the big fppf topology
  satisfies the presheaf relativization of `AlgebraicGeometry.Surjective`.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A covering sieve of the big fppf site over `S` is jointly surjective on points: given a
point of the scheme underlying the base of a covering sieve, some arrow of the sieve has that
point in the image of its underlying morphism of schemes. -/
theorem exists_mem_range_of_mem_topology {U : BigFppfOver B S hS} {R : Sieve U}
    (hR : R ∈ topology B S hS U) (y : (toScheme B S hS).obj U) :
    ∃ (V : BigFppfOver B S hS) (f : V ⟶ U), R f ∧
      y ∈ Set.range ((toScheme B S hS).map f).base := by
  obtain ⟨E, hE, hle⟩ :=
    AlgebraicGeometry.Space.exists_covering_refining_sieve B
      ((B.topology.mem_over_iff R).1 hR)
  have hfppf := B.isFppfCovering_of_isCovering hE
  rw [IsFppfCovering, Precoverage.mem_comap_iff, Presieve.map_ofArrows, Scheme.fppfPrecoverage,
    Scheme.ofArrows_mem_precoverage_iff] at hfppf
  obtain ⟨i, z, hz⟩ := hfppf.1 y
  exact ⟨Over.mk (E.f i ≫ U.hom), Over.homMk (E.f i),
    (Sieve.overEquiv_iff _ _).1 (hle _ _ (E.presieve₀_f i)), z, hz⟩

end BigFppfOver

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A relatively representable morphism of presheaves on the big fppf site over `S` which is
locally surjective for the big fppf topology is surjective after every representable base
change. -/
theorem presheaf_surjective_of_isLocallySurjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : G ⟶ F}
    (hrep : yoneda.relativelyRepresentable f)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f := by
  let _ := hsurj
  let _ : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hrep fun V ξ => ?_
  change _root_.AlgebraicGeometry.Surjective
    ((BigFppfOver.toScheme B S hS).map (hrep.snd ξ))
  refine (surjective_iff _).2 fun y => ?_
  obtain ⟨W, h, ⟨t, ht⟩, z, hz⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) f (yonedaEquiv ξ)) y
  have hcomm : yonedaEquiv.symm t ≫ f = yoneda.map h ≫ ξ := yonedaEquiv.injective <| by
    rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality]
  refine ⟨((BigFppfOver.toScheme B S hS).map
    (hrep.lift (yonedaEquiv.symm t) h hcomm)).base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp,
    Functor.relativelyRepresentable.lift_snd]
  exact hz

end Space

end AlgebraicGeometry

end

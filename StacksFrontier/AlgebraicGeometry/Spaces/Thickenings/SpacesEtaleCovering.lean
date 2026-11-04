module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization

/-!
# The spaces-étale sites of a thickening and of its ambient space have the same coverings

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, that is a closed subspace
whose inclusion is surjective on points. Base change along the inclusion is a functor from the
spaces-étale site of `X` to the spaces-étale site of `G`, and it identifies the two notions of
covering: a sieve of an object `U` of the spaces-étale site of `X` is a covering sieve exactly
when the sieve it generates on the base change of `U` is one.

The reason is that base change along the inclusion of a thickening changes nothing on points:
the cartesian projection from the base change of an object `V` of the spaces-étale site of `X`
back to `V` is a bijection on points, being a base change of the inclusion, which is itself a
bijection on points.

This is the identification of the *coverings* of the two sites. That the base-change functor
is an equivalence of the underlying categories — the other half of Stacks 05ZL — is
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsThickening` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEquivalence.lean`; together they
identify the two sites.

## Main results

* `AlgebraicGeometry.Space.bijective_pointsMap_spacesBaseChange_projection_of_isThickening`:
  the cartesian projection from the base change along the inclusion of a thickening is a
  bijection on points.
* `AlgebraicGeometry.Space.mem_spacesEtaleTopology_iff_functorPushforward_of_isThickening`:
  **Stacks 05ZL**, base change along the inclusion of a thickening both preserves and reflects
  covering sieves of the spaces-étale sites.

## Implementation notes

The covering sieves of a spaces-étale site are exactly the pointwise surjective ones,
`AlgebraicGeometry.Space.SpacesEtale.mem_topology_iff_sievePointwiseCover`, so after rewriting
with that characterization the statement is purely about the maps on points of Tag 03BU, and no
induction over the saturation of the presented precoverage is needed.

Bijectivity of the cartesian projection is the conjunction of two base-change statements.
Surjectivity is Stacks 03MH, `AlgebraicGeometry.Space.isSurjective_of_isPullback`, applied to
the surjectivity on points recorded by the definition of a thickening. Injectivity holds
because the projection is a base change of the inclusion, hence a monomorphism — the inclusion
of a subfunctor is one and monomorphisms are stable under base change — so Stacks 06RV,
`AlgebraicGeometry.Space.pointsMap_injective_of_mono`, applies.

With that in hand the two implications are asymmetric. Preserving a covering needs a point of
the base change of a member of the sieve lying over a given point of the base change of `U`,
which is Stacks 03H4, `AlgebraicGeometry.Space.exists_points_of_isPullback`, for the cartesian
square comparing the two base changes. Reflecting a covering needs only surjectivity of the
projection at `U` together with naturality of the projection, which transports the covering
point of the base change back down.

## References

* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace IsThickening

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- The closed subspace underlying a thickening `G ⊂ X`, read as an algebraic space over `S`:
the subfunctor `G`, which is an algebraic space by the definition of a closed subspace. -/
def space (hG : IsThickening B S hS X G) : AlgebraicSpaces B S hS := ⟨G.toFunctor, hG.1.1⟩

/-- The inclusion of the closed subspace underlying a thickening `G ⊂ X`, read as a morphism
of algebraic spaces over `S`. -/
def inclusion (hG : IsThickening B S hS X G) : space B S hS hG ⟶ X :=
  ObjectProperty.homMk G.ι

end IsThickening

/-- The cartesian projection from the base change along the inclusion of a thickening `G ⊂ X`
of an object `V` of the spaces-étale site of `X` is a bijection on points: it is a base change
of the inclusion, which is injective because it is a monomorphism and surjective by the
definition of a thickening. -/
theorem bijective_pointsMap_spacesBaseChange_projection_of_isThickening
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
    (V : SpacesEtale B S hS X) :
    Function.Bijective (pointsMap B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj V)).1
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app V).hom) := by
  have hsq := (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).isPullback V
  refine ⟨?_, isSurjective_of_isPullback B S hS hsq.flip hG.2⟩
  have : Mono ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app
      V).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms _)
      (AlgebraicSpaces.isPullback_hom B S hS hsq.flip)
      (show Mono (IsThickening.inclusion B S hS hG).hom from inferInstanceAs (Mono G.ι))
  exact pointsMap_injective_of_mono B S hS _

/-- **Stacks 05ZL.** Base change along the inclusion of a thickening `G ⊂ X` identifies the
covering sieves of the spaces-étale site of `X` with those of the spaces-étale site of `G`: a
sieve of an object `U` is covering exactly when the sieve it generates on the base change of
`U` is covering. -/
@[stacks 05ZL "identification of the covering sieves of the two spaces-étale sites"]
theorem mem_spacesEtaleTopology_iff_functorPushforward_of_isThickening
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
    (U : SpacesEtale B S hS X) (R : Sieve U) :
    R ∈ SpacesEtale.topology B S hS X U ↔
      R.functorPushforward
          (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor ∈
        SpacesEtale.topology B S hS (IsThickening.space B S hS hG)
          ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U) := by
  rw [SpacesEtale.mem_topology_iff_sievePointwiseCover,
    SpacesEtale.mem_topology_iff_sievePointwiseCover]
  constructor
  · intro hR x
    obtain ⟨V, f, hf, y, hy⟩ := hR (pointsMap B S hS _
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U).hom x)
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS
        (isPullback_overPullback_map (IsThickening.inclusion B S hS hG)
          ((SpacesEtale.inclusion B S hS X).map f)))
      x y hy.symm
    exact ⟨(spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj V,
      (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.map f,
      Sieve.image_mem_functorPushforward _ R hf, w, hw⟩
  · intro hR x
    obtain ⟨x', hx'⟩ :=
      (bijective_pointsMap_spacesBaseChange_projection_of_isThickening B S hS hG U).2 x
    obtain ⟨W, g, hg, y, hy⟩ := hR x'
    obtain ⟨V, f, k, hf, rfl⟩ := hg
    have hnat := pointsMap_apply_comm B S hS (congrArg (fun q ↦ q.hom)
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.naturality f))
      (pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS
        (IsThickening.space B S hS hG)).map k).hom y)
    have hk : pointsMap B S hS _
        (((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor ⋙
            SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map f).hom
        (pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS
          (IsThickening.space B S hS hG)).map k).hom y) = x' := by
      rwa [← pointsMap_comp_apply]
    have hU : pointsMap B S hS _
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U).hom
        (pointsMap B S hS _
          (((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor ⋙
            SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map f).hom
          (pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS
            (IsThickening.space B S hS hG)).map k).hom y)) = x := by
      rwa [hk]
    exact ⟨V, f, hf, pointsMap B S hS _
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app V).hom
      (pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS
        (IsThickening.space B S hS hG)).map k).hom y), hnat.symm.trans hU⟩

end AlgebraicGeometry.Space

end

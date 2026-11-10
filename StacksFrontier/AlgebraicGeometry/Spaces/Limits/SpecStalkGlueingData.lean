module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpensStalkAffineNhdsSiteLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StalkAffineNhdsSiteLimit

/-!
# Glueing data for the `2`-colimit identification at a point

Stacks 0E90 and Stacks 0E91 are stated from a cartesian square with vertices `N`, `U`, `M` and
the base, two diagrams `W Wn : I ⥤ BigFppfOver B S hS` over **one** index category, cones on them
with vertices `M` and `N`, the compatibilities of those cones with the square, and the point-set
data of `U` and of the stages. The `2`-colimit identifications `hloc` and `hoverlap` are only part
of what they take. This file supplies two pieces of the rest.

## The index transport

The two systems are built over different index categories: the affine open neighbourhoods of `s`
in `AlgebraicGeometry.affineOpenNhdsSiteDiagram`, and the neighbourhoods contained in a fixed one
in `AlgebraicGeometry.opensSpecStalkSiteDiagram`, because an open of a stage is only available
relative to a chosen stage. The glueing theorems bind a single index, so one system has to be
transported to the other's index, and it is the neighbourhoods that move: restricted along
`CategoryTheory.Over.forget`, which is an initial functor because the neighbourhoods are
cofiltered, so the restricted cone is still a limit.

## Main results

* `AlgebraicGeometry.restrictedSpecStalkSiteCone`: the cone with vertex `Spec 𝒪_{S, s}` over the
  affine open neighbourhoods of `s` contained in a fixed one.
* `AlgebraicGeometry.isLimitRestrictedSpecStalkSiteCone` and
  `AlgebraicGeometry.isLimitMapConeRestrictedSpecStalkSiteCone`: it is still a limit, in the site
  and on underlying schemes. The second is the hypothesis the size-free form of Stacks 07SK takes,
  so the clauses apply to the restricted system exactly as they do to the unrestricted one.
* `AlgebraicGeometry.BigFppfOver.isOpenImmersion_opensObj_hom` and
  `AlgebraicGeometry.BigFppfOver.range_opensObj_hom`: the point-set data of an open of `S` read as
  an object of the site — its structure morphism is an open immersion with range the open itself.
  For the complement of a closed point these are the `hUopen` and `hU` of the two tags.

## References

* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The point-set data of an open of `S` as an object of the site -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structure morphism of an open of `S`, read as an object of the big fppf category over
`S`, is an open immersion.** This is the `hUopen` hypothesis of Stacks 0E90 and Stacks 0E91. -/
theorem isOpenImmersion_opensObj_hom (P : S.Opens) :
    IsOpenImmersion (B.inclusion.map (opensObj B S hS P).hom) :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (X := S) P))

/-- **The range of the structure morphism of an open of `S`, read as an object of the big fppf
category over `S`, is that open.** With `P` the complement of a closed point this is the `hU`
hypothesis of Stacks 0E90 and Stacks 0E91. -/
theorem range_opensObj_hom (P : S.Opens) :
    Set.range (B.inclusion.map (opensObj B S hS P).hom) = (P : Set S) := by
  change Set.range ⇑(Scheme.Opens.ι (X := S) P) = _
  exact Scheme.Opens.range_ι P

/-- The range of the structure morphism of the complement of a point, read as an object of the
big fppf category over `S`, is that complement. -/
theorem range_opensObj_hom_eq_compl_singleton {s : S} (P : S.Opens)
    (hP : (P : Set S) = {s}ᶜ) :
    Set.range (B.inclusion.map (opensObj B S hS P).hom) = {s}ᶜ :=
  (range_opensObj_hom B S hS P).trans hP

end BigFppfOver

/-! ### The index transport -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : S)
  (W₀ : AffineOpenNhds S s)

/-- The affine open neighbourhoods of `s` contained in `W₀`, as a diagram in the big fppf category
over `S`: the diagram of all of them, restricted along `CategoryTheory.Over.forget`. This is the
index category on which the diagram of overlaps is available. -/
noncomputable abbrev restrictedAffineOpenNhdsSiteDiagram :
    Over W₀ ⥤ BigFppfOver B S hS :=
  Over.forget W₀ ⋙ affineOpenNhdsSiteDiagram B S hS s

/-- The cone with vertex `Spec 𝒪_{S, s}` over the affine open neighbourhoods of `s` contained in
`W₀`. -/
noncomputable abbrev restrictedSpecStalkSiteCone :
    Cone (restrictedAffineOpenNhdsSiteDiagram B S hS s W₀) :=
  (specStalkSiteCone B S hS s).whisker (Over.forget W₀)

/-- **`Spec 𝒪_{S, s}` is the limit of the affine open neighbourhoods of `s` contained in `W₀`.**
The neighbourhoods are cofiltered, so `CategoryTheory.Over.forget` is initial and restricting a
limit cone along it leaves a limit cone. -/
noncomputable def isLimitRestrictedSpecStalkSiteCone :
    IsLimit (restrictedSpecStalkSiteCone B S hS s W₀) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget W₀) (specStalkSiteCone B S hS s)).symm
    (isLimitSpecStalkSiteCone B S hS s)

/-- **The underlying schemes of the restricted cone form a limit of schemes.** This is the
hypothesis that the size-free form of Stacks 07SK takes, so its clauses apply to the restricted
system exactly as they do to the unrestricted one. -/
noncomputable def isLimitMapConeRestrictedSpecStalkSiteCone :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      (restrictedSpecStalkSiteCone B S hS s W₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget W₀)
      ((BigFppfOver.toScheme B S hS).mapCone (specStalkSiteCone B S hS s))).symm
    (isLimitMapConeSpecStalkSiteCone B S hS s)

/-- Every stage of the restricted diagram is affine. -/
instance isAffine_toScheme_restrictedAffineOpenNhdsSiteDiagram_obj (j : Over W₀) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).obj j)) :=
  isAffine_toScheme_affineOpenNhdsSiteDiagram_obj B S hS s j.left

/-- Every stage of the restricted diagram is an open subscheme of `S`. -/
theorem isOpenImmersion_restrictedAffineOpenNhdsSiteDiagram_obj_hom (j : Over W₀) :
    IsOpenImmersion (B.inclusion.map
      ((restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).obj j).hom) :=
  isOpenImmersion_affineOpenNhdsSiteDiagram_obj_hom B S hS s j.left

/-- Every stage of the restricted diagram contains the point `s`. -/
theorem mem_range_restrictedAffineOpenNhdsSiteDiagram_obj_hom (j : Over W₀) :
    s ∈ Set.range (B.inclusion.map
      ((restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).obj j).hom) :=
  mem_range_affineOpenNhdsSiteDiagram_obj_hom B S hS s j.left

/-- The transition morphisms of the restricted diagram are affine. -/
theorem isAffineHom_toScheme_map_restrictedAffineOpenNhdsSiteDiagram_map {j k : Over W₀}
    (e : j ⟶ k) :
    IsAffineHom ((BigFppfOver.toScheme B S hS).map
      ((restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).map e)) := by
  rw [show (restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).map e =
    (affineOpenNhdsSiteDiagram B S hS s).map e.left from rfl,
    toScheme_map_affineOpenNhdsSiteDiagram_map]
  exact isAffineHom_affineOpenNhdsDiagram_map S s e.left

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximationComplete
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperModificationOffClosedPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The scheme side of the situation of Artin's theorem on contractions

The situation of Stacks 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`) asks for an
algebraic space `X'` locally of finite type over `S`, and Stacks 0GIB
(`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_isSeparated`) asks in
addition that `X'` be separated over `S` and that the local rings of `S` at finite type points
be G-rings. This file supplies these hypotheses when `X'` is the sheaf represented by a scheme
`Z` over `S` and `S` is the spectrum of an algebra of finite type over a field.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_terminal_from_yoneda_of_structureMap`: the
  sheaf represented by a scheme locally of finite type over `S` is locally of finite type over
  `S`.
* `AlgebraicGeometry.Space.isSeparated_terminal_from_yoneda`: the sheaf represented by a scheme
  separated over `S` is separated over `S`.
* `AlgebraicGeometry.Space.isClosed_preimage_pointsToScheme` (already in the library) gives that
  the points over a closed subset of `Z` form a closed subset of `|Z|`.
* `AlgebraicGeometry.isGRing_stalk_spec_of_finiteType`: every local ring of the spectrum of an
  algebra of finite type over a field is a G-ring (Stacks 07PX and 07PV).

## Implementation notes

The structure morphism of a represented sheaf to the terminal sheaf is the image under the
Yoneda embedding of the morphism of the site to its terminal object, followed by the comparison
`AlgebraicGeometry.Space.yonedaTerminalIso`; the underlying morphism of schemes of the former is
the structure morphism to `S` up to `AlgebraicGeometry.Space.toSchemeTerminalIso`
(`AlgebraicGeometry.Space.toScheme_map_terminal_from`). Both properties respect isomorphisms,
so they may be read on schemes through
`AlgebraicGeometry.Space.isLocallyOfFiniteType_yoneda_map_iff` and
`AlgebraicGeometry.Space.isSeparated_yoneda_map_iff`.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure morphism of the sheaf represented by an object of the site is the Yoneda image
of the morphism to the terminal object of the site followed by the comparison of the represented
terminal object with the terminal sheaf. -/
theorem terminal_from_yoneda_obj_eq (Zo : BigFppfOver B S hS) :
    terminal.from (yoneda.obj Zo) =
      yoneda.map (terminal.from Zo) ≫ (yonedaTerminalIso B S hS).hom :=
  terminal.hom_ext _ _

/-- The underlying morphism of schemes of the morphism of the site to its terminal object is the
structure morphism to `S`, read through `AlgebraicGeometry.Space.toSchemeTerminalIso`. -/
theorem toScheme_map_terminal_from_eq (Zo : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (terminal.from Zo) =
      B.inclusion.map Zo.hom ≫ (toSchemeTerminalIso B S hS).inv := by
  rw [← toScheme_map_terminal_from, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A scheme locally of finite type over `S` is an algebraic space locally of finite type over
`S`.** The sheaf represented by an object of the big fppf site of `S` whose structure morphism
is locally of finite type is locally of finite type over `S`, its structure morphism being to
the terminal sheaf. -/
theorem isLocallyOfFiniteType_terminal_from_yoneda_of_structureMap
    (Zo : BigFppfOver B S hS)
    (hZ : LocallyOfFiniteType (B.inclusion.map Zo.hom)) :
    IsLocallyOfFiniteType B S hS (terminal.from (yoneda.obj Zo)) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsLocallyOfFiniteType B S hS f
  have _ : P.RespectsIso := isLocallyOfFiniteType_respectsIso B S hS
  rw [terminal_from_yoneda_obj_eq]
  refine (P.cancel_right_of_respectsIso (yoneda.map (terminal.from Zo))
    (yonedaTerminalIso B S hS).hom).2 ?_
  refine (isLocallyOfFiniteType_yoneda_map_iff B S hS _).2 ?_
  rw [toScheme_map_terminal_from_eq]
  infer_instance

/-- **A scheme separated over `S` is an algebraic space separated over `S`.** The sheaf
represented by an object of the big fppf site of `S` whose structure morphism is separated is
separated over `S`. -/
theorem isSeparated_terminal_from_yoneda (Zo : BigFppfOver B S hS)
    (hZ : AlgebraicGeometry.IsSeparated (B.inclusion.map Zo.hom)) :
    IsSeparated B S hS (terminal.from (yoneda.obj Zo)) := by
  have _ := isSeparated_respectsIso B S hS
  rw [terminal_from_yoneda_obj_eq]
  refine (MorphismProperty.cancel_right_of_respectsIso (@IsSeparated B S hS)
    (yoneda.map (terminal.from Zo)) (yonedaTerminalIso B S hS).hom).2 ?_
  refine (isSeparated_yoneda_map_iff B S hS _).2 ?_
  rw [toScheme_map_terminal_from_eq]
  infer_instance

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-- **The local rings of an algebra of finite type over a field are G-rings.** Let `R` be an
algebra of finite type over a field `k`. Then for every point `p` of `Spec R` the local ring
`𝒪_{Spec R, p}` is a G-ring: `k` is a G-ring and an algebra of finite type over a G-ring is one
(Stacks 07PX), and a localization of a G-ring is one (Stacks 07PV). -/
theorem isGRing_stalk_spec_of_finiteType (k : Type u) [Field k] (R : Type u) [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] (p : Spec (CommRingCat.of R)) :
    IsGRing ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
  StacksDraft.ArtinApproximation.isGRing_stalk_spec R
    (isGRing_basic_examples.{u, u}.2.2.2.2 k R (isGRing_basic_examples.{u, u}.1 k)) p

/-- The G-ring hypothesis of Stacks 0GIB for the spectrum of an algebra of finite type over a
field: the local ring at every finite type point is a G-ring (in fact at every point, by
`AlgebraicGeometry.isGRing_stalk_spec_of_finiteType`). -/
theorem isGRing_stalk_of_isFiniteTypePoint_spec (k : Type u) [Field k] (R : Type u)
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] :
    ∀ s : Spec (CommRingCat.of R), IsFiniteTypePoint s →
      IsGRing ((Spec (CommRingCat.of R)).presheaf.stalk s) :=
  fun s _ ↦ isGRing_stalk_spec_of_finiteType k R s

end AlgebraicGeometry

end

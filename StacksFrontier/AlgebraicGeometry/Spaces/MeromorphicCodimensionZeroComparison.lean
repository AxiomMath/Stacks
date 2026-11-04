module

public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroStalkMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# The direct image of the structure sheaf at a codimension-zero point

Let `X` be an algebraic space over a scheme `S` with a presentation `P` of its schematic locus
at the codimension-zero points, and let `η` be such a point.  The canonical morphism
`j_η : Spec(𝒪_{X, η}) ⟶ X` is representable, so the direct image `j_{η, *}𝒪_{X, η}` of the
structure sheaf is the restriction of the structure sheaf of `Spec(𝒪_{X, η})` along base change
of étale charts: its sections over an étale chart `U` of `X` are the regular functions on the
scheme `U ×_X Spec(𝒪_{X, η})`.

Every regular section of `𝒪_X` over a chart becomes a *unit* in that ring, because the base
change is flat, so the pullback of a regular section is regular, and `U ×_X Spec(𝒪_{X, η})` is
a scheme all of whose local rings have dimension zero, where regular sections are units.  The
universal property of the sheafified localization of Stacks 0EMC therefore produces the
canonical comparison

`𝒦_X ⟶ j_{η, *}𝒪_{X, η}`

extending the structure map `𝒪_X ⟶ j_{η, *}𝒪_{X, η}`.

All declarations below are in the namespace `AlgebraicGeometry.Space.CodimensionZeroPresentation`.

## Main definitions

* `genericPointStructureSheaf` is `j_{η, *}𝒪_{X, η}` and `genericPointSharp` is the structure
  map `𝒪_X ⟶ j_{η, *}𝒪_{X, η}`.
* `genericPointComparison` is the canonical comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}`.

## Main results

* `isUnit_genericPointSharp_app`: a regular section of `𝒪_X` over a chart has unit image in
  `j_{η, *}𝒪_{X, η}`.
* `toMeromorphicFunctionSheaf_comp_genericPointComparison`: the comparison extends the structure
  map, and `genericPointComparison_unique`: it is the only morphism of sheaves of rings that
  does.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) {x : points B S hS X.1}
    (hx : localRingDimension B S hS x = 0)

/-- The canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X` is representable, because the diagonal of
an algebraic space is. -/
theorem representable_genericMorphism :
    yoneda.relativelyRepresentable (P.genericMorphism hx X.2).hom :=
  Functor.relativelyRepresentable.of_diag X.2.diagonal_representable _

/-- **The direct image `j_{η, *}𝒪_{X, η}`** of the structure sheaf of `Spec(𝒪_{X, η})` along the
canonical morphism, as a sheaf of rings on the small étale site of `X`: its sections over an
étale chart `U` are the regular functions on `U ×_X Spec(𝒪_{X, η})`. -/
noncomputable def genericPointStructureSheaf :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  ((smallBaseChange B S hS (P.genericMorphism hx X.2)
        (P.representable_genericMorphism hx)).sheafPushforwardContinuous CommRingCat.{u}
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS (P.specStalkSpace hx).1)).obj
    (structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2)

/-- The structure map `𝒪_X ⟶ j_{η, *}𝒪_{X, η}`: on an étale chart `U` it is pullback of regular
functions along the cartesian projection `U ×_X Spec(𝒪_{X, η}) ⟶ U`. -/
noncomputable def genericPointSharp :
    structureSheaf B S hS X.1 X.2 ⟶ P.genericPointStructureSheaf hx :=
  smallBaseChangeSharpCommRingCat B S hS (P.genericMorphism hx X.2)
    (P.representable_genericMorphism hx)

/-- The base-changed chart of `Spec(𝒪_{X, η})` at an étale chart `U` of `X`. -/
noncomputable abbrev genericPointChart (U : SmallEtale B S hS X.1) :
    SmallEtale B S hS (P.specStalkSpace hx).1 :=
  (smallBaseChange B S hS (P.genericMorphism hx X.2)
    (P.representable_genericMorphism hx)).obj U

/-- The cartesian projection `U ×_X Spec(𝒪_{X, η}) ⟶ U` on the objects of the site. -/
noncomputable abbrev genericPointProjection (U : SmallEtale B S hS X.1) :
    (SmallEtale.toOver B S hS (P.specStalkSpace hx).1).obj (P.genericPointChart hx U) ⟶
      (SmallEtale.toOver B S hS X.1).obj U :=
  (P.representable_genericMorphism hx).snd U.1.hom

/-- The structure map is pullback along the cartesian projection. -/
theorem genericPointSharp_app (U : SmallEtale B S hS X.1)
    (s : (structurePresheaf B S hS X.1).obj (op U)) :
    ((P.genericPointSharp hx).hom.app (op U)).hom s =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (P.genericPointProjection hx U)).op).hom s :=
  rfl

/-- **The projection `U ×_X Spec(𝒪_{X, η}) ⟶ U` is flat.** -/
theorem flat_genericPointProjection (U : SmallEtale B S hS X.1) :
    Flat ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection hx U)) :=
  (P.flat_relative_fromSpecStalk hx).property U.1.hom _ _
    ((P.representable_genericMorphism hx).isPullback U.1.hom)

/-- **The projection `U ×_X Spec(𝒪_{X, η}) ⟶ U` is a preimmersion.** -/
theorem isPreimmersion_genericPointProjection (U : SmallEtale B S hS X.1) :
    IsPreimmersion ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection hx U)) :=
  (P.isPreimmersion_relative_fromSpecStalk hx).property U.1.hom _ _
    ((P.representable_genericMorphism hx).isPullback U.1.hom)

/-- **A regular section of `𝒪_X` over an étale chart has unit image in `j_{η, *}𝒪_{X, η}`.**
Its image is its pullback along the flat projection `U ×_X Spec(𝒪_{X, η}) ⟶ U`, hence a regular
section there, and the local rings of `U ×_X Spec(𝒪_{X, η})` have Krull dimension zero, so a
regular section of its structure sheaf is a unit. -/
theorem isUnit_genericPointSharp_app (U : SmallEtale B S hS X.1)
    (s : (structurePresheaf B S hS X.1).obj (op U)) (hs : IsRegularSection B S hS X.1 U s) :
    IsUnit (((P.genericPointSharp hx).hom.app (op U)).hom s) := by
  have := P.flat_genericPointProjection hx U
  set φ := (BigFppfOver.toScheme B S hS).map (P.genericPointProjection hx U) with hφ
  have hpull := pullbacksMeromorphicSections_of_flat φ ⊤ ⊤ (by simp) s hs
  have hmap : pullbackSection φ.toLRSHom ⊤ ⊤ (by simp) s = (Scheme.Γ.map φ.op).hom s := by
    simp [pullbackSection, Scheme.Hom.toLRSHom, Scheme.Hom.appTop]
    rfl
  rw [hmap] at hpull
  rw [P.genericPointSharp_app hx U s]
  exact isUnit_of_isRegularSectionOn_top_of_ringKrullDim_stalk_eq_zero _
    (P.ringKrullDim_stalk_specStalkChart hx X.2 (P.genericPointChart hx U)) _ hpull

/-- **The canonical comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}`**: the unique morphism of sheaves of
rings extending the structure map `𝒪_X ⟶ j_{η, *}𝒪_{X, η}` through `𝒪_X ⟶ 𝒦_X`.  It exists
because every regular section of `𝒪_X` has unit image. -/
noncomputable def genericPointComparison :
    meromorphicFunctionSheaf B S hS X.1 X.2 ⟶ P.genericPointStructureSheaf hx :=
  ((regularSectionsSubpresheaf B S hS X.1 X.2).existsUnique_lift_toLocalizationSheaf
    (P.genericPointStructureSheaf hx) (P.genericPointSharp hx)
    (fun U s => P.isUnit_genericPointSharp_app hx U.unop s.1 s.2)).choose

/-- Existence and uniqueness of the morphism of sheaves of rings extending the structure map. -/
private theorem existsUnique_toMeromorphicFunctionSheaf_comp :
    ∃! g : meromorphicFunctionSheaf B S hS X.1 X.2 ⟶ P.genericPointStructureSheaf hx,
      toMeromorphicFunctionSheaf B S hS X.1 X.2 ≫ g = P.genericPointSharp hx :=
  ((regularSectionsSubpresheaf B S hS X.1 X.2).existsUnique_lift_toLocalizationSheaf
    (P.genericPointStructureSheaf hx) (P.genericPointSharp hx)
    (fun U s => P.isUnit_genericPointSharp_app hx U.unop s.1 s.2))

/-- The comparison extends the structure map. -/
theorem toMeromorphicFunctionSheaf_comp_genericPointComparison :
    toMeromorphicFunctionSheaf B S hS X.1 X.2 ≫ P.genericPointComparison hx =
      P.genericPointSharp hx :=
  (P.existsUnique_toMeromorphicFunctionSheaf_comp hx).choose_spec.1

/-- The comparison is the only morphism of sheaves of rings extending the structure map. -/
theorem genericPointComparison_unique
    (g : meromorphicFunctionSheaf B S hS X.1 X.2 ⟶ P.genericPointStructureSheaf hx)
    (hg : toMeromorphicFunctionSheaf B S hS X.1 X.2 ≫ g = P.genericPointSharp hx) :
    g = P.genericPointComparison hx :=
  (P.existsUnique_toMeromorphicFunctionSheaf_comp hx).choose_spec.2 g hg

/-- The comparison on sections, over the image of a regular function. -/
theorem genericPointComparison_app_toMeromorphicFunctionSheaf (U : SmallEtale B S hS X.1)
    (s : (structurePresheaf B S hS X.1).obj (op U)) :
    ((P.genericPointComparison hx).hom.app (op U)).hom
        (((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom s) =
      ((P.genericPointSharp hx).hom.app (op U)).hom s :=
  congrArg (fun f : structureSheaf B S hS X.1 X.2 ⟶ P.genericPointStructureSheaf hx =>
    (f.hom.app (op U)).hom s) (P.toMeromorphicFunctionSheaf_comp_genericPointComparison hx)

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end

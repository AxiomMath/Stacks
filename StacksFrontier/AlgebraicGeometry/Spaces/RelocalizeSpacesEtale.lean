module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekOverMap
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.RelocalizationMorphism

/-!
# The spaces-étale site of an algebraic space viewed over a larger base

Let `g : T ⟶ S` be a morphism of a big fppf site. The lower-shriek extension `Λ` carries
algebraic spaces over `T` to algebraic spaces over `S`, and it preserves fibre products and
étale morphisms. So for an algebraic space `X` over `T` it induces a functor from the
spaces-étale site of `X` to that of `Λ X`, compatible with the comparison functors from the small
étale sites and with base change along a morphism of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSpacesFunctor`: `Λ` on algebraic spaces.
* `AlgebraicGeometry.Space.relocalizeSpacesEtale`: the functor
  `X_{spaces, étale} ⥤ (Λ X)_{spaces, étale}`.

## Main results

* `AlgebraicGeometry.Space.isEtale_relocalizeHom_iff`: `Λ φ` is étale if and only if `φ` is.
* `AlgebraicGeometry.Space.relocalizeComparisonIso`: the comparison functors of Stacks 03G1
  commute with relocalization, `e_X ⋙ cmp_{Λ X} ≅ cmp_X ⋙ Λ`.
* `AlgebraicGeometry.Space.relocalizeSpacesEtaleBaseChangeIso`: base change of spaces-étale
  sites commutes with relocalization, `f^{-1} ⋙ Λ ≅ Λ ⋙ (Λ f)^{-1}`.
* `AlgebraicGeometry.Space.relocalizeSpacesEtaleFullyFaithful`: the relocalization of
  spaces-étale sites is fully faithful.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- **The lower-shriek extension of algebraic spaces**, `Λ : Sp/T ⥤ Sp/S`. On objects and
morphisms it is `AlgebraicGeometry.Space.relocalizeSpace` and
`AlgebraicGeometry.Space.relocalizeHom`. -/
abbrev relocalizeSpacesFunctor : AlgebraicSpaces B T hT ⥤ AlgebraicSpaces B S hS :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ OverShriek.relocalizePresheafFunctor g)
    (fun Y => isAlgebraicSpace_relocalize' B hT hS g Y.1 Y.2)

/-- The lower-shriek extension of algebraic spaces preserves fibre products: they are computed
in presheaves, where `Λ` preserves connected limits. -/
instance relocalizeSpacesFunctor_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (relocalizeSpacesFunctor B hT hS g) := by
  have _ := relocalizePresheaf_preservesConnectedLimits (K := WalkingCospan) g
  have : PreservesLimitsOfShape WalkingCospan
      (relocalizeSpacesFunctor B hT hS g ⋙ ObjectProperty.ι _) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (ObjectProperty.ι _ ⋙ OverShriek.relocalizePresheafFunctor g))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (ObjectProperty.ι _)

/-- **The lower-shriek extension of a morphism of algebraic spaces is étale if and only if the
morphism is**: both are the every-étale-chart condition of Stacks 03XT, which `Λ` does not
change. -/
theorem isEtale_relocalizeHom_iff {Y Z : AlgebraicSpaces B T hT} (φ : Y ⟶ Z) :
    IsEtale B S hS (relocalizeHom B hT hS g φ).hom ↔ IsEtale B T hT φ.hom :=
  (isEtale_iff_holdsOnEveryEtaleChart B S hS (relocalizeSpace B hT hS g Y).2
      (relocalizeSpace B hT hS g Z).2 _).trans
    ((Space.holdsOnEveryEtaleChart_relocalizeMap_iff B T S hT hS g _ φ.hom).trans
      (isEtale_iff_holdsOnEveryEtaleChart B T hT Y.2 Z.2 φ.hom).symm)

variable (X : AlgebraicSpaces B T hT)

/-- **The spaces-étale site of `X` maps to that of `Λ X`**: an algebraic space étale over `X` is
sent to its lower-shriek extension, étale over `Λ X`. -/
def relocalizeSpacesEtale :
    SpacesEtale B T hT X ⥤ SpacesEtale B S hS (relocalizeSpace B hT hS g X) :=
  ObjectProperty.lift _
    (SpacesEtale.inclusion B T hT X ⋙ Over.post (relocalizeSpacesFunctor B hT hS g))
    (fun W => (isEtale_relocalizeHom_iff B hT hS g W.1.hom).2 W.2)

/-- The functor `relocalizeSpacesEtale` followed by the inclusion into the slice is `Λ` on the
slice. -/
def relocalizeSpacesEtaleCompInclusionIso :
    relocalizeSpacesEtale B hT hS g X ⋙
        SpacesEtale.inclusion B S hS (relocalizeSpace B hT hS g X) ≅
      SpacesEtale.inclusion B T hT X ⋙ Over.post (relocalizeSpacesFunctor B hT hS g) :=
  Iso.refl _

/-- On scheme charts, `Λ` of the chart of `X` attached to `A` is the chart of `Λ X` attached to
the relocalized chart: `Λ h_A ≅ h_{Λ A}` over `Λ X`. -/
def relocalizeChartFunctorIso :
    OverShriek.relocalizeChart g X.1 ⋙ chartFunctor B S hS (relocalizeSpace B hT hS g X) ≅
      chartFunctor B T hT X ⋙ Over.post (relocalizeSpacesFunctor B hT hS g) :=
  NatIso.ofComponents
    (fun A => Over.isoMk
      ((ObjectProperty.fullyFaithfulι _).preimageIso
        ((OverShriek.relocalizeYonedaIso g).app A.left).symm)
      (ObjectProperty.hom_ext _ (relocalizeChart_hom_eq B hT hS g X.1 A).symm))
    (fun {_ _} k => Over.OverMorphism.ext (ObjectProperty.hom_ext _
      ((OverShriek.relocalizeYonedaIso g).inv.naturality k.left)))

/-- **The comparison functors commute with relocalization**: a scheme chart of `X`, viewed as
an algebraic space étale over `X` and then relocalized, is the relocalized chart viewed as an
algebraic space étale over `Λ X`. -/
def relocalizeComparisonIso :
    (SmallEtale.relocalize B hT hS g X.1 X.2).functor ⋙
        comparisonFunctor B S hS (relocalizeSpace B hT hS g X) ≅
      comparisonFunctor B T hT X ⋙ relocalizeSpacesEtale B hT hS g X :=
  ((ObjectProperty.fullyFaithfulι
      (IsEtaleOver B S hS (relocalizeSpace B hT hS g X))).whiskeringRight
    (SmallEtale B T hT X.1)).preimageIso
    (Functor.isoWhiskerLeft (SmallEtale.inclusion B T hT X.1)
      (relocalizeChartFunctorIso B hT hS g X))

variable {X} in
/-- **Base change commutes with the lower-shriek extension** on spaces-étale sites: for
`f : X ⟶ Y`, base change along `f` followed by `Λ` is `Λ` followed by base change along `Λ f`.
This is the Beck–Chevalley isomorphism of `Λ`, which preserves fibre products. -/
def relocalizeSpacesEtaleBaseChangeIso {Y : AlgebraicSpaces B T hT} (f : X ⟶ Y) :
    (spacesBaseChange B T hT f).functor ⋙ relocalizeSpacesEtale B hT hS g X ≅
      relocalizeSpacesEtale B hT hS g Y ⋙
        (spacesBaseChange B S hS (relocalizeHom B hT hS g f)).functor :=
  ((ObjectProperty.fullyFaithfulι
      (IsEtaleOver B S hS (relocalizeSpace B hT hS g X))).whiskeringRight
    (SpacesEtale B T hT Y)).preimageIso
    (Functor.isoWhiskerLeft (SpacesEtale.inclusion B T hT Y)
      (Over.postPullbackIso (relocalizeSpacesFunctor B hT hS g) f))

/-! ### Full faithfulness -/

/-- `Λ` is fully faithful on presheaves over a fixed presheaf: under the equivalences of
Stacks 00Y1 it is `Over.map` on the slice over an object, an iterated slice. -/
def relocalizePresheafPostFullyFaithful (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    (Over.post (X := F) (OverShriek.relocalizePresheafFunctor g)).FullyFaithful :=
  have : (Over.post (X := F)
      (OverShriek.presheafEquivalence (U := B.obj hT)).functor).IsEquivalence := inferInstance
  have := (inferInstance : (Over.post
    (X := (Over.map (yoneda.map g)).obj
      ((OverShriek.presheafEquivalence (U := B.obj hT)).functor.obj F))
    (OverShriek.presheafEquivalence (U := B.obj hS)).inverse).IsEquivalence)
  have := Stacks.SheafOfModules.isEquivalence_overPost_overMap (yoneda.map g)
    ((OverShriek.presheafEquivalence (U := B.obj hT)).functor.obj F)
  ((Functor.FullyFaithful.ofFullyFaithful (Over.post (X := F)
      (OverShriek.presheafEquivalence (U := B.obj hT)).functor)).comp
    ((Functor.FullyFaithful.ofFullyFaithful (Over.post (Over.map (yoneda.map g)))).comp
      (Functor.FullyFaithful.ofFullyFaithful (Over.post (OverShriek.presheafEquivalence
        (U := B.obj hS)).inverse))))

/-- `Λ` is fully faithful on algebraic spaces over a fixed algebraic space. -/
def relocalizeSpacesPostFullyFaithful :
    (Over.post (X := X) (relocalizeSpacesFunctor B hT hS g)).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := Over.post (X := relocalizeSpace B hT hS g X)
      (ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    ((Functor.FullyFaithful.ofFullyFaithful (Over.post (X := X)
      (ObjectProperty.ι fun F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B T hT F))).comp
      (relocalizePresheafPostFullyFaithful B hT hS g X.1))

/-- **The relocalization of spaces-étale sites is fully faithful.** -/
def relocalizeSpacesEtaleFullyFaithful : (relocalizeSpacesEtale B hT hS g X).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := ObjectProperty.ι (IsEtaleOver B S hS (relocalizeSpace B hT hS g X)))
    ((ObjectProperty.fullyFaithfulι (IsEtaleOver B T hT X)).comp
      (relocalizeSpacesPostFullyFaithful B hT hS g X))

/-- The relocalization of spaces-étale sites is full. -/
instance : (relocalizeSpacesEtale B hT hS g X).Full :=
  (relocalizeSpacesEtaleFullyFaithful B hT hS g X).full

/-- The relocalization of spaces-étale sites is faithful. -/
instance : (relocalizeSpacesEtale B hT hS g X).Faithful :=
  (relocalizeSpacesEtaleFullyFaithful B hT hS g X).faithful

end AlgebraicGeometry.Space

end

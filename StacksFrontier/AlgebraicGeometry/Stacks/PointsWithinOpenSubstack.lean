module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeOpen
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget

/-!
# The open substack cut out by an open set of points

Let `𝒳` be an algebraic stack over `S` and let `Ω` be an open set of points of `|𝒳|`. The full
subcategory of `𝒳` cut out by the locus `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` is an
`AlgebraicGeometry.Stack.OpenSubstack` of `𝒳` whose set of points is `Ω`. So the rule `𝒰 ↦ |𝒰|`
from open substacks of `𝒳` to open subsets of `|𝒳|` is surjective.

## Main definitions

* `AlgebraicGeometry.Stack.pointsWithinOpenSubstack`: the open substack cut out by an open set of
  points.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_of_exists_representing`: one representing
  algebraic space suffices to test a relative property of a 1-morphism.
* `AlgebraicGeometry.Stack.isOpenImmersion_fullSubcategoryInclusion_pointsWithin`: the inclusion
  of the locus of an open set of points is an open immersion of algebraic stacks.
* `AlgebraicGeometry.Stack.pointSet_pointsWithinOpenSubstack`: its set of points is the open set
  one started from.
* `AlgebraicGeometry.Stack.exists_openSubstack_pointSet_eq`: every open subset of `|𝒳|` is the
  point set of an open substack.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two algebraic spaces over an object `U` of the big fppf site of `S` which are isomorphic as
presheaves have structural morphisms with the same properties, read as morphisms of algebraic
spaces over `S`. -/
theorem prop_algebraicSpaceMap_congr
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (U : BigFppfOver B S hS)
    {F F' : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hF' : IsAlgebraicSpace B U.left.1 U.left.2 F')
    (i : F ≅ F') :
    P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) ↔
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F', hF'⟩)) := by
  rw [prop_algebraicSpaceMap_iff B S hS P U F hF, prop_algebraicSpaceMap_iff B S hS P U F' hF']
  refine P.arrow_mk_iso_iff (Arrow.isoMk
    (ObjectProperty.isoMk _ ((OverShriek.relocalizePresheafFunctor U.hom).mapIso i))
    (Iso.refl _) ?_)
  apply ObjectProperty.hom_ext
  change (OverShriek.relocalizePresheafFunctor U.hom).map i.hom ≫
    OverShriek.relocalizeToYoneda U.hom F' = _ ≫ 𝟙 _
  exact (relocalizeToYoneda_naturality B U.left.1 S U.left.2 hS U.hom i.hom).trans
    (Category.comp_id _).symm

/-- **One representing algebraic space suffices to test a relative property.** A 1-morphism
representable by algebraic spaces has the relative property `P` as soon as, for every
scheme-valued point of the target, *some* algebraic space representing the base change has
structural morphism with `P`. -/
theorem hasRelativeProperty_of_exists_representing
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom),
      ∃ (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) ∧
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    HasRelativeProperty B S hS P f hf := by
  intro U y hy F' hF' he'
  obtain ⟨e'⟩ := he'
  obtain ⟨F, hF, ⟨e⟩, hP⟩ := h U y hy
  have hfib : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap U.hom 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f) 𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hy
      (CatFiberedInGroupoids.homFunctor_comp_p f)
  exact (prop_algebraicSpaceMap_congr B S hS P U hF hF'
    (representingIso B U.left.1 U.left.2
      (𝒲 := CatFiberedInGroupoids.mk (BasedCategory.ofFunctor _) hfib) F F' e e')).mp hP

/-- The inclusion of a subfunctor of `yoneda` of the terminal object of the big fppf site of `W`
is its structural morphism `AlgebraicGeometry.Space.toYonedaId`. -/
theorem subfunctor_ι_eq_toYonedaId (W : Scheme.{u}) (hW : B.Contains W)
    (G : Subfunctor (yoneda.obj (Over.mk (𝟙 (B.obj hW))) :
      (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)) :
    G.ι = Space.toYonedaId B W hW G.toFunctor := by
  ext Z x
  exact Over.mkIdTerminal.hom_ext _ _

/-- **An open subspace of the terminal object of the big fppf site of `U` has open immersion
structural morphism over `S`.** -/
theorem isOpenImmersion_algebraicSpaceMap_of_isOpenSubspace (U : BigFppfOver B S hS)
    (G : Subfunctor (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))) :
      (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u))
    (hG : Space.IsOpenSubspace B U.left.1 U.left.2 G) :
    Space.IsOpenImmersion B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
          ⟨G.toFunctor, hG.1⟩)).hom := by
  have := Space.openImmersion_isLocalAtTarget_fpqc.{u, u} B S hS
  refine (prop_algebraicSpaceMap_iff B S hS (Space.openImmersionProperty B S hS) U
    G.toFunctor hG.1).mpr ?_
  change Space.IsOpenImmersion B S hS (OverShriek.relocalizeToYoneda U.hom G.toFunctor)
  have _ := isIso_relocalizeToYoneda_yonedaId B U.left.1 S U.left.2 hS U.hom
  rw [← relocalizeToYoneda_eq_map_toYonedaId B U.left.1 S U.left.2 hS U.hom G.toFunctor]
  refine (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr ?_
  refine OverShriek.presheaf_map_relocalize U.hom (fun _ hm => hm) ?_
  rw [← subfunctor_ι_eq_toYonedaId B U.left.1 U.left.2 G]
  exact hG.2

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))

/-- **The inclusion of the locus of an open set of points of `|𝒳|` is an open immersion of
algebraic stacks.** -/
theorem isOpenImmersion_fullSubcategoryInclusion_pointsWithin
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    AlgebraicStacks.IsOpenImmersion B S hS
      (fullSubcategoryInclusion 𝒳 (pointsWithin 𝒳 Ω)
        (isAlgebraicStack_fullSubcategoryBased_pointsWithin.{u, w} B S hS 𝒳 Ω hΩ)) := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  have hrep := isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_pointsWithin
    B S hS 𝒳 Ω hΩ
  refine ⟨hrep, ?_⟩
  refine hasRelativeProperty_of_exists_representing B S hS
    (Space.openImmersionProperty B S hS)
    (fullSubcategoryInclusion 𝒳 (pointsWithin 𝒳 Ω)
      (isAlgebraicStack_fullSubcategoryBased_pointsWithin.{u, w} B S hS 𝒳 Ω hΩ)).hom
    hrep (fun U y hy => ?_)
  have hopen := isOpenSubspace_fullSubcategoryBaseChangeSubfunctor_pointsWithin B S hS 𝒳 y hy Ω hΩ
  exact ⟨_, hopen.1,
    nonempty_equivalenceOver_fullSubcategoryBaseChange_pointsWithin 𝒳 y Ω hy,
    isOpenImmersion_algebraicSpaceMap_of_isOpenSubspace B S hS U _ hopen⟩

/-- The open substack of `𝒳` cut out by an open set `Ω` of points of `|𝒳|`: the full subcategory
on `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`. -/
def pointsWithinOpenSubstack (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    OpenSubstack 𝒳 where
  property := pointsWithin 𝒳 Ω
  strictlyFull := ⟨fun e h => pointsWithin_of_hom 𝒳 Ω e.inv h⟩
  isAlgebraic := isAlgebraicStack_fullSubcategoryBased_pointsWithin.{u, w} B S hS 𝒳 Ω hΩ
  isOpenImmersion := isOpenImmersion_fullSubcategoryInclusion_pointsWithin B S hS 𝒳 Ω hΩ

/-- The defining property of `AlgebraicGeometry.Stack.pointsWithinOpenSubstack 𝒳 Ω` is the
locus `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`. -/
@[simp]
theorem pointsWithinOpenSubstack_property
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    (pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ).property = pointsWithin 𝒳 Ω :=
  rfl

/-- **The point set of the open substack cut out by `Ω` is `Ω`.** -/
theorem pointSet_pointsWithinOpenSubstack
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    (pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ).pointSet B S hS = Ω := by
  ext x
  rw [OpenSubstack.mem_pointSet_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp p (𝟙 p.obj)
  · intro hx
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    refine ⟨p, fun q φ => ?_, rfl⟩
    rw [(class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val 𝒳.val.property q p).2
      ⟨q, ⟨𝟙 q.obj⟩, ⟨φ⟩⟩]
    exact hx

/-- **The rule `𝒰 ↦ |𝒰|` is surjective.** Every open subset of the space of points of an algebraic
stack is the point set of an open substack, namely of the locus of that open set. -/
theorem exists_openSubstack_pointSet_eq
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    ∃ W : OpenSubstack 𝒳, W.pointSet B S hS = Ω :=
  ⟨pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ, pointSet_pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ⟩

end AlgebraicGeometry.Stack

end

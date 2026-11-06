module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.SmallAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# Spaces of finite type over a transported quasi-compact space descend

Let `B ⊆ B'` be big fppf sites and let `G = AlgebraicGeometry.changeBigSite B B' h S hS` be
the inverse image of Stacks 04W1. Let `X` be a quasi-compact algebraic space over `S` on `B`,
and let `p : Y' ⟶ G X` be a morphism of finite type of algebraic spaces on `B'`. Then `Y'` is
in the essential image of `G`.

## Main results

* `AlgebraicGeometry.Space.mem_essentialImage_changeBigSite_of_isFiniteType`: an algebraic
  space of finite type over the transport of a quasi-compact algebraic space descends.

## References

* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- Pullbacks of presheaves on a big fppf site, given directly: instance search for them times
out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ChangeOfBigSiteFiniteType
    (C : BigFppfSite.{u}) (T : Scheme.{u}) (hT : C.Contains T) :
    HasPullbacks ((BigFppfOver C T hT)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ChangeOfBigSiteFiniteType
    {C : BigFppfSite.{u}} {T : Scheme.{u}} {hT : C.Contains T}
    {X Y Z : (BigFppfOver C T hT)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_ChangeOfBigSiteFiniteType C T hT).has_limit _

/-- **An algebraic space of finite type over the transport of a quasi-compact algebraic space
descends to the smaller site.** -/
theorem mem_essentialImage_changeBigSite_of_isFiniteType {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.obj) (Y' : AlgebraicSpaces B' S (largerContains h hS))
    (p : Y'.obj ⟶ ((changeBigSite B B' h S hS).obj X).obj)
    (hp : IsFiniteType B' S (largerContains h hS) p) :
    ∃ Y : AlgebraicSpaces B S hS, Nonempty ((changeBigSite B B' h S hS).obj Y ≅ Y') := by
  let hS' : B'.Contains S := largerContains h hS
  let T' := BigFppfOver.toScheme B' S hS'
  have := inverseImage_isStableUnderComposition B' S hS' etale_isStableUnderComposition.{u}
  have := inverseImage_isStableUnderComposition B' S hS'
    AlgebraicGeometry.surjective_isStableUnderComposition.{u}
  obtain ⟨U, q, hUaff, hqS, hqE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ X.property).mp hX
  have hqE' : IsEtaleChart B S hS X.obj (CostructuredArrow.mk q) :=
    (isEtale_iff_presheaf_of_yoneda B S hS q).mp hqE
  let q' := (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk q)).hom
  letI : HasLimit (cospan q' p) := hasPullback_presheaf_ChangeOfBigSiteFiniteType q' p
  have hq'S := presheaf_surjective_changeBigSiteChart B B' h S hS X hqS hqE'
  have hq'E : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T') q' :=
    isEtaleChart_changeBigSiteChart B B' h S hS X hqE'
  have hP : IsAlgebraicSpace B' S hS' (pullback q' p) :=
    isAlgebraicSpace_pullback B' S hS' q' p (isAlgebraicSpace_yoneda B' S hS' _) Y'.property
      ((changeBigSite B B' h S hS).obj X).property
  have hPqc : IsQuasiCompactSpace B' S hS' (pullback q' p) :=
    hp.2 _ (isAlgebraicSpace_yoneda B' S hS' _)
      (isQuasiCompactSpace_yoneda_of_isAffine B' S hS' ((inclusionOver h S hS).obj U) hUaff) q'
  obtain ⟨W, w, hWaff, hwS, hwE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B' S hS' _ hP).mp hPqc
  have hwE' := (isEtale_iff_presheaf_of_yoneda B' S hS' w).mp hwE
  let a : yoneda.obj W ⟶ Y'.obj := w ≫ pullback.snd q' p
  have ha : ∀ {Q : MorphismProperty (BigFppfOver B' S hS')} [Q.IsStableUnderComposition],
      Q.presheaf w → Q.presheaf q' → Q.presheaf a := fun hw hq =>
    MorphismProperty.comp_mem _ _ _ hw
      (presheaf_of_isPullback B' S hS' (IsPullback.of_hasPullback q' p) hq)
  have haE := ha hwE' hq'E
  have haS := ha hwS hq'S
  let c : W ⟶ (inclusionOver h S hS).obj U := yoneda.preimage (w ≫ pullback.fst q' p)
  have hc : yoneda.map c ≫ q' = a ≫ p :=
    (congrArg (· ≫ q') (Functor.map_preimage yoneda _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (w ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))
  have hcft : LocallyOfFiniteType (T'.map c) := hp.1 _ _ a q' c haE hq'E hc
  have hcqc : QuasiCompact (T'.map c) :=
    @quasiCompact_of_compactSpace _ _ _ (@Scheme.compactSpace_of_isAffine _ hWaff)
      (@quasiSeparatedSpace_of_isAffine _ hUaff)
  have hWsize : (T'.obj W).size < B.cutoff :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (T'.map c)).trans_lt U.left.property
  let W₀ : BigFppfOver B S hS := BigFppfOver.mk B S hS hWsize (B'.inclusion.map W.hom)
  exact mem_essentialImage_changeBigSite_of_etale_surjective B B' h S hS Y' W₀ a haS haE

end AlgebraicGeometry.Space

end

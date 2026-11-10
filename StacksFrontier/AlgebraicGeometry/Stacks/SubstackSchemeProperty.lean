module

public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent
import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Substacks and subspaces cut out by a property of morphisms of schemes

Open, closed and locally closed subspaces of an algebraic space (Stacks 02YU) and open, closed
and locally closed substacks of an algebraic stack (Stacks 04YM) are the same notion read at three
properties `Q` of morphisms of schemes: the open immersions, the closed immersions and the
immersions. The subspace notion at an arbitrary `Q` is `AlgebraicGeometry.Space.IsSubspaceWith`
(in `StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage`); this file adds the substack notion
and the facts about the two which do not depend on which `Q` it is:

* a subfunctor is represented by morphisms with `Q` as soon as its inverse images along all
  morphisms from representable presheaves are;
* immersions and open immersions descend effectively along the covering sieves of the site
  (closed immersions do too:
  `AlgebraicGeometry.FormalSpace.isEffectiveDescentAlongCoveringSieve_isClosedImmersion`);
* the base change of the inclusion of a `Q`-substack along a scheme-valued point is a
  `Q`-subspace, and conversely a property inherited along morphisms all of whose such base
  changes are `Q`-subspaces cuts out a `Q`-substack.

## Main definitions

* `AlgebraicGeometry.Stack.HasBaseChangeProperty`: the Stacks 04XB condition at `Q` on a
  1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.IsSubstackWith`: a strictly full subcategory which is an algebraic
  stack and whose inclusion is representable by algebraic spaces and has the 04XB condition at
  `Q`.

## Main results

* `AlgebraicGeometry.Space.presheaf_ι_of_forall_preimage`.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_isImmersion` and
  `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_isOpenImmersion`.
* `AlgebraicGeometry.Stack.isSubspaceWith_fullSubcategoryBaseChangeSubfunctor` and
  `AlgebraicGeometry.Stack.isSubstackWith_of_forall_isSubspaceWith`.

## Implementation notes

At `Q` the closed immersions and the immersions of schemes,
`AlgebraicGeometry.Stack.IsSubstackWith` *is* `AlgebraicGeometry.Stack.IsClosedSubstack` and
`AlgebraicGeometry.Stack.IsLocallyClosedSubstack`, and at the open immersions it is the data of
`AlgebraicGeometry.Stack.OpenSubstack` beyond the property, by unfolding the abbreviations.
`AlgebraicGeometry.Stack.HasBaseChangeProperty` is the relative property of Stacks 03YK,
`AlgebraicGeometry.Stack.HasRelativeProperty`, without the two instance arguments that definition
carries, which nothing here uses.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Q : MorphismProperty Scheme.{u})

/-- Representability by morphisms with `Q` of the underlying morphism of presheaves, as a
property of morphisms of algebraic spaces over `S`. -/
abbrev propertyWith : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f.hom

/-- `AlgebraicGeometry.Space.propertyWith` is stable under base change. -/
instance : (propertyWith B S hS Q).IsStableUnderBaseChange where
  of_isPullback sq hf := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS sq) hf

/-- `AlgebraicGeometry.Space.propertyWith` respects isomorphisms. -/
instance : (propertyWith B S hS Q).RespectsIso :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

variable {B S hS Q}

/-- **A subfunctor is represented by morphisms with `Q` as soon as its inverse images along all
morphisms from representable presheaves are.** The inverse image along `g` is the base change of
the inclusion along `g` (`CategoryTheory.Subfunctor.isPullback_preimage`), so a represented base
change of the inverse image along the identity is one of the inclusion along `g`. -/
theorem presheaf_ι_of_forall_preimage [Q.RespectsIso] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z : Subfunctor F)
    (h : ∀ ⦃a : BigFppfOver B S hS⦄ (g : yoneda.obj a ⟶ F),
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (Z.preimage g).ι) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf Z.ι := by
  refine MorphismProperty.relative.of_exists fun a g => ?_
  obtain ⟨b, snd, fst, hpb⟩ := (h g).rep (𝟙 (yoneda.obj a))
  have hsq := hpb.paste_horiz (Subfunctor.isPullback_preimage g Z)
  rw [Category.id_comp] at hsq
  exact ⟨b, _, snd, hsq, (h g).property _ _ _ hpb⟩

/-- An immersion of schemes is a monomorphism locally of finite type. -/
theorem isImmersion_le_monomorphisms_inf_locallyOfFiniteType :
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType := by
  intro X Y f hf
  have _ : AlgebraicGeometry.IsImmersion f := hf
  exact ⟨inferInstanceAs (Mono f), inferInstance⟩

variable (B S hS) in
/-- **Immersions of schemes descend effectively along the covering sieves of the big fppf site
of `S`.** They are monomorphisms locally of finite type, which descend effectively by Stacks 02W8
(`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`), and being
an immersion is Zariski local on the target and descends along fppf coverings (Stacks 02YM). -/
theorem isEffectiveDescentAlongCoveringSieve_isImmersion :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
  have _ := Stacks.Descent.isImmersion_descendsAlong_fppf.{u}
  isEffectiveDescentAlongCoveringSieve_of_le
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)
    isImmersion_le_monomorphisms_inf_locallyOfFiniteType

variable (B S hS) in
/-- **Open immersions of schemes descend effectively along the covering sieves of the big fppf
site of `S`.** They are monomorphisms locally of finite type, which descend effectively by
Stacks 02W8, and being an open immersion is Zariski local on the target and descends along fpqc,
hence fppf, coverings. -/
@[sga "3 IV 6.4.1" "special case", sga "4 IV 8.5.5" "partial"]
theorem isEffectiveDescentAlongCoveringSieve_isOpenImmersion :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) :=
  have _ := descendsAlong_fppf_of_descendsAlong_fpqc
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
  isEffectiveDescentAlongCoveringSieve_of_le
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)
    (fun X Y f hf => by
      have _ : AlgebraicGeometry.IsOpenImmersion f := hf
      exact isImmersion_le_monomorphisms_inf_locallyOfFiniteType _ _ f inferInstance)

end Space

namespace Stack

section FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Q : MorphismProperty Scheme.{u})
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` *has the base
change property `Q`* when every algebraic space representing its base change along a
scheme-valued point of the target has structural morphism represented by morphisms with `Q`. This
is the condition of Stacks 04XB at `Q`; at the open immersions, the closed immersions and the
immersions it is `AlgebraicGeometry.Stack.IsOpenImmersion`,
`AlgebraicGeometry.Stack.IsClosedImmersion` and `AlgebraicGeometry.Stack.IsImmersion`. -/
abbrev HasBaseChangeProperty (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end FiberedInGroupoids

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Q : MorphismProperty Scheme.{u})

/-- A property of the objects of an algebraic stack `𝒳` over `S` cuts out a *`Q`-substack* when
it is closed under isomorphism, its full subcategory is an algebraic stack, and the inclusion of
that full subcategory is representable by algebraic spaces and has the base change property `Q`.
At the closed immersions and the immersions this is part (2) and part (3) of Stacks 04YM, and at
the open immersions it is the content of part (1). -/
abbrev IsSubstackWith (𝒳 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj) :
    Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
      IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryInclusion 𝒳 P hP).hom.hom ∧
        HasBaseChangeProperty B S hS Q (fullSubcategoryInclusion 𝒳 P hP).hom

variable {Q}

/-- **Membership of a `Q`-substack is inherited along morphisms**: its full subcategory is fibred
in groupoids and every morphism of `𝒳` is strongly cartesian. -/
theorem IsSubstackWith.prop_of_hom {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSubstackWith Q 𝒳 P)
    {a b : 𝒳.val.val.obj} (φ : a ⟶ b) (hb : P b) : P a := by
  have := hP.1
  exact prop_of_isHomLift B S hS hP.2.choose (𝒳.val.val.p.map φ) φ inferInstance hb

/-- The extension of a map to `yoneda W` has `Q` exactly when the structural morphism of the
lower-shriek extension of its source does. -/
private theorem presheaf_relocalizeToYoneda_iff_map {W : BigFppfOver B S hS}
    {X : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u}
    (k : X ⟶ yoneda.obj (Over.mk (𝟙 W.left))) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        ((OverShriek.relocalizePresheafFunctor W.hom).map k) ↔
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (OverShriek.relocalizeToYoneda W.hom X) := by
  let g := OverShriek.relocalizeToYoneda W.hom
    (yoneda.obj (Over.mk (𝟙 W.left)) : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
  have _ : IsIso g := isIso_relocalizeToYoneda_yonedaId B W.left.1 S W.left.2 hS W.hom
  rw [← relocalizeToYoneda_naturality B W.left.1 S W.left.2 hS W.hom k]
  exact (MorphismProperty.cancel_right_of_respectsIso
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf _ g).symm

variable [Q.RespectsIso]

/-- **The base change of the inclusion of a `Q`-substack along a scheme-valued point is a
`Q`-subspace.** Let `P` cut out a `Q`-substack of `𝒳` and let `z` be a scheme-valued point of
`𝒳` with values in `W`. The subfunctor of `yoneda W` whose sections over `T` are present exactly
when `P` holds at `z T` is a `Q`-subspace of `W`.

It is an algebraic space because it is isomorphic to any algebraic space representing the base
change of the inclusion along `z`, and its inclusion has `Q` because the lower-shriek extension
of that inclusion is, up to the isomorphism `AlgebraicGeometry.isIso_relocalizeToYoneda_yonedaId`,
the structural morphism that the base change property is about. -/
theorem isSubspaceWith_fullSubcategoryBaseChangeSubfunctor
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSubstackWith Q 𝒳 P)
    (W : BigFppfOver B S hS) (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map W.hom) :
    Space.IsSubspaceWith B W.left.1 W.left.2 Q
      (fullSubcategoryBaseChangeSubfunctor 𝒳 (fun φ hb => hP.prop_of_hom φ hb) z) := by
  have := hP.1
  obtain ⟨hPalg, hrep, hbc⟩ := hP.2
  set Z := fullSubcategoryBaseChangeSubfunctor 𝒳 (fun φ hb => hP.prop_of_hom φ hb) z
  obtain ⟨F, hF, ⟨e'⟩⟩ := hrep W z hz
  obtain ⟨e⟩ := nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳
    (fun φ hb => hP.prop_of_hom φ hb) z hz
  have hZalg : IsAlgebraicSpace B W.left.1 W.left.2 Z.toFunctor :=
    isAlgebraicSpace_of_iso B W.left.1 W.left.2 (PresheafOfCategories.isoOfEquivalenceOver e e') hF
  have h2 : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (OverShriek.relocalizeToYoneda W.hom Z.toFunctor) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.propertyWith B S hS Q) W _ hZalg).mp
      (hbc W z hz Z.toFunctor hZalg ⟨e⟩)
  exact ⟨hZalg, presheaf_relocalizeMap_of B W.left.1 S W.left.2 hS W.hom Q Z.ι
    ((presheaf_relocalizeToYoneda_iff_map Z.ι).mpr h2)⟩

/-- **A property whose base changes along scheme-valued points are `Q`-subspaces cuts out a
`Q`-substack.** Let `P` be a property of the objects of an algebraic stack `𝒳` over `S` which is
inherited along morphisms. If for every scheme-valued point `z` of `𝒳` with values in `W` the
subfunctor of `yoneda W` whose sections over `T` are present exactly when `P` holds at `z T` is a
`Q`-subspace of `W`, then `P` cuts out a `Q`-substack of `𝒳`.

Those subfunctors are algebraic spaces, so the inclusion of the full subcategory is representable
by algebraic spaces
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion`); the
full subcategory is then an algebraic stack by **Stacks 05UM**, and the inclusion has the base
change property `Q` because the lower-shriek extension of a morphism with `Q` has `Q` and any
algebraic space representing the base change is isomorphic to the subfunctor. -/
theorem isSubstackWith_of_forall_isSubspaceWith (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {P : ObjectProperty 𝒳.val.val.obj} (hinh : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    (hsub : ∀ (W : BigFppfOver B S hS) (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
      (_hz : z ⋙ 𝒳.val.val.p = Over.map W.hom),
      Space.IsSubspaceWith B W.left.1 W.left.2 Q
        (fullSubcategoryBaseChangeSubfunctor 𝒳 hinh z)) :
    IsSubstackWith Q 𝒳 P := by
  have hiso : P.IsClosedUnderIsomorphisms := ⟨fun e hx => hinh e.inv hx⟩
  have hfib := isFiberedInGroupoids_fullSubcategoryBased 𝒳 hinh
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) :=
    isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion 𝒳 hinh
      (fun W z hz => (hsub W z hz).1)
  let 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P) hfib
  let j : 𝒵 ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 P)
  have halg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P) :=
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS j hrep 𝒳.property
  refine ⟨hiso, halg, hrep, ?_⟩
  intro W z hz F hF ⟨e⟩
  set Z := fullSubcategoryBaseChangeSubfunctor 𝒳 hinh z
  obtain ⟨eZ⟩ := nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳 hinh z hz
  refine (prop_algebraicSpaceMap_iff B S hS (Space.propertyWith B S hS Q) W F hF).mpr ?_
  change (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
    (OverShriek.relocalizeToYoneda W.hom F)
  have hΛ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      ((OverShriek.relocalizePresheafFunctor W.hom).map Z.ι) :=
    OverShriek.presheaf_map_relocalize _ (fun _ hk => hk) (hsub W z hz).2
  rw [← relocalizeToYoneda_naturality B W.left.1 S W.left.2 hS W.hom
    (PresheafOfCategories.isoOfEquivalenceOver eZ e).inv]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr
    ((presheaf_relocalizeToYoneda_iff_map Z.ι).mp hΛ)

end Stack

end AlgebraicGeometry

end

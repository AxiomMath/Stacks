module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeInertiaCharacterization
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeAutomorphismSequence

/-!
# The automorphism sheaves of a gerbe are flat and locally of finite presentation

Let `𝒲` be an algebraic stack over `S` which is a gerbe in the absolute sense of **Stacks 06QC**
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbe`), let `T` be an object of the big fppf site of
`S` and let `ξ` be an object of the fibre of `𝒲` over `T`. The sheaf `Isom_𝒲(ξ, ξ)` of
automorphisms of `ξ` is an algebraic space over `T` (**Stacks 045G**); this file proves that its
structure morphism to `T` is **flat and locally of finite presentation**, and records the
statement in the form a consumer with an explicit representing scheme needs: if
`Isom_𝒲(ξ, ξ)` is represented by a morphism `g : V ⟶ T` of the site, then the morphism of schemes
underlying `g` is flat and locally of finite presentation.

## Main results

All in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isFlat_and_isLocallyOfFinitePresentation_terminal_isomSpace_of_isGerbe`:
  `Isom_𝒲(ξ, ξ) ⟶ T` is flat and locally of finite presentation, as a morphism of algebraic spaces
  over `T`.
* `flat_and_locallyOfFinitePresentation_of_isGerbe`: if
  the presheaf represented by `Over.mk g` on the slice over `T` is isomorphic to
  `𝒲.p.isomPresheaf ξ ξ`, then the morphism of schemes underlying `g` is flat and locally of
  finite presentation; `…_of_isGerbe_of_equiv` takes the isomorphism as a natural family of
  bijections.
* `flat_and_locallyOfFinitePresentation_of_isGerbe_of_iso_isomSpace` and
  `…_of_equiv_isomSpace`: the same, with `Isom_𝒲(ξ, ξ)` read on the big fppf site of `T`
  through `CategoryTheory.Over.iteratedSliceBackward` (`AlgebraicGeometry.Stack.isomSpace`, the
  shape of `AlgebraicGeometry.Stack.QuotientStackIsomSheavesAlgebraic`), represented by an
  object `Z` of that site.
* `flat_and_locallyOfFinitePresentation_of_isGerbe_fullSubcategoryAlgebraicStack`:
  the same for an object `x` of an algebraic stack `𝒳` lying in a full substack which is a
  gerbe, read on the isomorphism presheaf of `x` in `𝒳` itself.

## Proof

1. By **Stacks 06QJ**
   (`isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbe`)
   the inertia projection `I_𝒲 ⟶ 𝒲` is flat and locally of finite presentation in the sense of
   **Stacks 06PW** and **Stacks 06Q2**. It is representable by algebraic spaces
   (**Stacks 050Q**), so by **Stacks 06FM**
   (`AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_isFlat_of_isFlat` and its
   sibling) every algebraic space representing its base change along a scheme-valued point has
   flat, locally finitely presented structure morphism (the relative property of
   **Stacks 03YK**).
2. The base change of `I_𝒲 ⟶ 𝒲` along the point `𝒮/T ⟶ 𝒲` of `ξ` (its chosen pullbacks) is
   `Isom_𝒲(ξ, ξ)`. By **Stacks 034H** the inertia is `𝒲 ×_{Δ, 𝒲 × 𝒲, Δ} 𝒲` with the inertia
   projection the first projection (the comparison of
   `StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionFiniteType`), so its base change along
   the point is the base change of `Δ` along the diagonal of the point
   (`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`), which is the presheaf of
   vertical morphisms between the chosen pullbacks
   (`CategoryTheory.TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff`), that is
   `Isom_𝒲(ξ, ξ)` (`CategoryTheory.Functor.vertHomPresheafIsoIsomPresheaf`). This is
   `AlgebraicGeometry.Stack.AlgebraicStacks.prop_of_relativeProperty_inertiaProjection`, for an
   arbitrary property of morphisms of algebraic spaces.
3. The property of the representing algebraic space read over `S` is read over `T` by
   **Stacks 04SG** (`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` and
   `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`). When the
   representing space is the Yoneda presheaf of `Z`, its relocalization is the Yoneda presheaf of
   `Z` viewed over `S` (`CategoryTheory.OverShriek.relocalizeYonedaIso`), its structure morphism
   is `yoneda.map` of the structure morphism of `Z`, and an étale-local property of `yoneda.map`
   of a morphism of the site is that property of the underlying morphism of schemes
   (`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`).

For the full substack, the inclusion `P.ι` is a fully faithful 1-morphism over the site, so the
map of isomorphism presheaves it induces
(`AlgebraicGeometry.Stack.isomPresheafMap`, **Stacks 042V**) is an isomorphism
(`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_isomPresheafMap_of_full_of_faithful`).

## References

* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

attribute [local instance] Space.isFlat_isLocalAtTarget_fppf
  Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open TwoFibreProductOver.DiagonalFibre in
/-- **A relative property of the inertia projection holds for the isomorphism sheaves.** Let `P`
be a property of morphisms of algebraic spaces over `S` such that the inertia projection
`I_𝒳 ⟶ 𝒳` of an algebraic stack has the relative property `P` of Stacks 03YK. Then for every
object `ξ` of the fibre of `𝒳` over `T` and every algebraic space `F` over `T` isomorphic to
`Isom_𝒳(ξ, ξ)`, the structure morphism of `F`, read over `S`, has `P`.

The base change of `I_𝒳 ⟶ 𝒳` along the chosen-pullback point of `ξ` is identified with the
category of elements of `Isom_𝒳(ξ, ξ)`: through Stacks 034H the inertia projection is the first
projection of `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳`, its base change is the base change of `Δ` along the
diagonal of the point, and that is the presheaf of vertical morphisms between the chosen
pullbacks of `ξ`. -/
theorem prop_of_relativeProperty_inertiaProjection
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hP : RelativeProperty.{u, u, u + 1} B S hS P
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom)
    (T : BigFppfOver B S hS) (ξ : 𝒳.val.val.p.Fiber T)
    (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B T.left.1 T.left.2 F)
    (e : F ≅ Stack.isomSpace B S hS 𝒳.val T ξ ξ) :
    P (algebraicSpaceMap B S hS T
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)) := by
  have hp := 𝒳.val.isFiberedInGroupoids
  let : 𝒳.val.val.p.IsFibered := hp.isFibered
  let y := Over.iteratedSliceBackward T ⋙ 𝒳.val.val.p.pullbackSliceFunctor ξ
  have hy : y ⋙ 𝒳.val.val.p = Over.map T.hom :=
    Functor.backward_pullbackSliceFunctor_comp 𝒳.val.val.p T ξ
  refine hP T y hy F hF ?_
  have hG : 𝒳.val.val.p ⋙ 𝟭 (BigFppfOver B S hS) = 𝒳.val.val.p := Functor.comp_id _
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (Stack.diagonal.{u, u, u + 1} B S hS 𝒳.val) (Stack.diagonal.{u, u, u + 1} B S hS 𝒳.val)
  let aFun : (Stack.inertia B S hS 𝒳.val).val ⥤ᵇ Q.pt.val :=
    ⟨TwoFibreProductOver.ofRelativeInertia hG,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor hG⟩
  have : Functor.IsEquivalence aFun.toFunctor :=
    (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia hG)
      (TwoFibreProductOver.toRelativeInertia hG)
      (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia hG).symm)
      (TwoFibreProductOver.unitIso hG).symm).isEquivalence_functor
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  obtain ⟨E₁⟩ := Stack.nonempty_equivalenceOver_fst_of_equivalences B S hS
    (Stack.inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳).hom.hom Q.fst.hom aFun
    (BasedFunctor.id 𝒳.val.val) (Iso.refl _) T y hy
  obtain ⟨E₂⟩ := Stack.nonempty_baseChangeEquivalenceOver.{u, u, u + 1} B S hS 𝒳.val
    (CatFiberedInGroupoids.product 𝒳.val 𝒳.val) 𝒳.val
    (Stack.diagonal.{u, u, u + 1} B S hS 𝒳.val) (Stack.diagonal.{u, u, u + 1} B S hS 𝒳.val) Q
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    T (y ⋙ (BasedFunctor.id 𝒳.val.val).toFunctor) hy
  have hY : ((y ⋙ (BasedFunctor.id 𝒳.val.val).toFunctor) ⋙
      (Stack.diagonal.{u, u, u + 1} B S hS 𝒳.val).hom.toFunctor) ⋙ ProdP 𝒳.val.val.p =
        Over.map T.hom := hy
  obtain ⟨E₃⟩ := (nonempty_equivalenceOver_fst_iff hp hY F).2
    ⟨Functor.isoWhiskerRight
      ((Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.val.p T ξ ξ hp).trans e.symm)
      uliftFunctor.{u, u}⟩
  exact ⟨E₁.trans (E₂.trans E₃)⟩

/-- The every-étale-chart condition for the relocalization of an algebraic space `F` over `T`
isomorphic to `Isom_𝒳(ξ, ξ)`, from the relative property of the inertia projection. -/
private theorem holdsOnEveryEtaleChart_relocalizeToYoneda_of_relativeProperty
    {Q : MorphismProperty Scheme.{u}} (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hP : RelativeProperty.{u, u, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        Space.HoldsOnEveryEtaleChart B S hS Q f.hom)
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom)
    (T : BigFppfOver B S hS) (ξ : 𝒳.val.val.p.Fiber T)
    (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B T.left.1 T.left.2 F)
    (e : F ≅ Stack.isomSpace B S hS 𝒳.val T ξ ξ) :
    Space.HoldsOnEveryEtaleChart B S hS Q (OverShriek.relocalizeToYoneda T.hom F) := by
  have _ := Space.holdsOnEveryEtaleChart_respectsIso B S hS Q
  have h := prop_of_relativeProperty_inertiaProjection B S hS _ 𝒳 hP T ξ F hF e
  rwa [Stack.prop_algebraicSpaceMap_iff B S hS
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => Space.HoldsOnEveryEtaleChart B S hS Q f.hom)
    T F hF] at h

/-- The structure morphism of the relocalization of the Yoneda presheaf of an object `Z` of the
site over `T` is `yoneda.map` of the structure morphism of `Z`, viewed over `S`, after the
comparison `Λ h_Z ≅ h_{j Z}` of `CategoryTheory.OverShriek.relocalizeYonedaIso`. -/
theorem relocalizeToYoneda_yoneda_eq (T : BigFppfOver B S hS)
    (Z : BigFppfOver B T.left.1 T.left.2) :
    OverShriek.relocalizeToYoneda T.hom (yoneda.obj Z) =
      ((OverShriek.relocalizeYonedaIso T.hom).hom.app Z) ≫
        yoneda.map (Over.homMk Z.hom : (Over.map T.hom).obj Z ⟶ T) := by
  ext W x
  exact Over.OverMorphism.ext (Over.w x.1.2).symm

/-- **The structure morphism of a representable algebraic space over `T`, read over `S`.** If the
relocalization of the Yoneda presheaf of an object `Z` of the site over `T` satisfies the
every-étale-chart condition of Stacks 03MJ for a property `Q` of morphisms of schemes which is
étale local on the source and the target, then the morphism of schemes underlying the structure
morphism of `Z` has `Q`. -/
theorem prop_toScheme_map_of_holdsOnEveryEtaleChart_relocalizeToYoneda
    {Q : MorphismProperty Scheme.{u}} (hQ : IsEtaleLocalOnSourceAndTarget Q)
    (T : BigFppfOver B S hS) (Z : BigFppfOver B T.left.1 T.left.2)
    (h : Space.HoldsOnEveryEtaleChart B S hS Q
      (OverShriek.relocalizeToYoneda T.hom (yoneda.obj Z))) :
    Q ((BigFppfOver.toScheme B S hS).map (Over.homMk Z.hom : (Over.map T.hom).obj Z ⟶ T)) := by
  have _ := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS Q
  rw [relocalizeToYoneda_yoneda_eq] at h
  refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS hQ _).1 ?_
  exact (MorphismProperty.cancel_left_of_respectsIso
    (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
      Space.HoldsOnEveryEtaleChart B S hS Q f) _ _).1 h

/-- **A property of the inertia projection, read on a representing scheme of an automorphism
sheaf.** If the inertia projection of `𝒳` has the relative property of Stacks 03YK for the
every-étale-chart condition at an étale-local property `Q` of morphisms of schemes, and
`Isom_𝒳(ξ, ξ)` is represented by an object `Z` of the big fppf site of `T`, then the morphism of
schemes underlying the structure morphism of `Z` has `Q`. -/
theorem prop_toScheme_map_of_relativeProperty_inertiaProjection
    {Q : MorphismProperty Scheme.{u}} (hQ : IsEtaleLocalOnSourceAndTarget Q)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hP : RelativeProperty.{u, u, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        Space.HoldsOnEveryEtaleChart B S hS Q f.hom)
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom)
    (T : BigFppfOver B S hS) (ξ : 𝒳.val.val.p.Fiber T)
    (Z : BigFppfOver B T.left.1 T.left.2)
    (e : yoneda.obj Z ≅ Stack.isomSpace B S hS 𝒳.val T ξ ξ) :
    Q ((BigFppfOver.toScheme B S hS).map (Over.homMk Z.hom : (Over.map T.hom).obj Z ⟶ T)) := by
  exact prop_toScheme_map_of_holdsOnEveryEtaleChart_relocalizeToYoneda B S hS hQ T Z
    (holdsOnEveryEtaleChart_relocalizeToYoneda_of_relativeProperty B S hS 𝒳 hP T ξ _
      (isAlgebraicSpace_yoneda B T.left.1 T.left.2 Z) e)

/-- **Stacks 06QJ, read through Stacks 06FM.** The inertia projection of a gerbe has the relative
properties of Stacks 03YK for flatness and for local finite presentation of morphisms of
algebraic spaces: Stacks 06QJ gives flatness and local finite presentation in the sense of
Stacks 06PW and Stacks 06Q2, and the inertia projection is representable by algebraic spaces
(Stacks 050Q), so Stacks 06FM converts them. -/
theorem relativeProperty_isFlat_inertiaProjection_of_isGerbe
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsGerbe B S hS 𝒳) :
    RelativeProperty.{u, u, u + 1} B S hS
        (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => Space.IsFlat B S hS f.hom)
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom ∧
      RelativeProperty.{u, u, u + 1} B S hS
        (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
          Space.IsLocallyOfFinitePresentation B S hS f.hom)
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom := by
  have hrep := Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u,
    u + 1, w} B S hS 𝒳.val 𝒳.property
  obtain ⟨hflat, hlfp⟩ :=
    isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbe B S hS 𝒳 h𝒳
  exact ⟨hasRelativeProperty_isFlat_of_isFlat B S hS _ hrep hflat,
    hasRelativeProperty_isLocallyOfFinitePresentation_of_isLocallyOfFinitePresentation B S hS _
      hrep hlfp⟩

/-- **A relative property of the inertia projection holds for the structure morphism of every
automorphism sheaf, over `T`.** If the inertia projection of `𝒳` has the relative property of
Stacks 03YK for the every-étale-chart condition at `Q`, then `Isom_𝒳(ξ, ξ) ⟶ T` satisfies that
condition, as a morphism of algebraic spaces over `T`. The automorphism sheaf is an algebraic space
because the diagonal of `𝒳` is representable by algebraic spaces (Stacks 045G). -/
theorem holdsOnEveryEtaleChart_terminal_isomSpace_of_relativeProperty
    {Q : MorphismProperty Scheme.{u}}
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hP : RelativeProperty.{u, u, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        Space.HoldsOnEveryEtaleChart B S hS Q f.hom)
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom)
    (T : BigFppfOver B S hS) (ξ : 𝒳.val.val.p.Fiber T) :
    Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q
      (terminal.from (Stack.isomSpace B S hS 𝒳.val T ξ ξ)) := by
  have _ := Space.holdsOnEveryEtaleChart_respectsIso B S hS Q
  have hp := 𝒳.val.isFiberedInGroupoids
  have hpf : 𝒳.val.val.p.IsFibered := hp.isFibered
  obtain ⟨Fisom, hFisom, ⟨eIsom⟩⟩ :=
    (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳.val).mp
      𝒳.property.2.2.1 T ξ ξ
  have hI : IsAlgebraicSpace B T.left.1 T.left.2 (Stack.isomSpace B S hS 𝒳.val T ξ ξ) :=
    isAlgebraicSpace_of_iso B T.left.1 T.left.2
      (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso eIsom).symm hFisom
  exact Space.holdsOnEveryEtaleChart_of_isTerminal B T.left.1 T.left.2
    (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _
    ((Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B T.left.1 S T.left.2 hS T.hom Q _).1
      (holdsOnEveryEtaleChart_relocalizeToYoneda_of_relativeProperty B S hS 𝒳 hP T ξ _ hI
        (Iso.refl _)))

/-- **The automorphism sheaves of a gerbe are flat and locally of finite presentation.** For a
gerbe `𝒲` over `S`, an object `T` of the site and an object `ξ` of the fibre over `T`, the
structure morphism `Isom_𝒲(ξ, ξ) ⟶ T` is flat and locally of finite presentation, as a morphism
of algebraic spaces over `T`. -/
theorem isFlat_and_isLocallyOfFinitePresentation_terminal_isomSpace_of_isGerbe
    (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒲 : IsGerbe B S hS 𝒲)
    (T : BigFppfOver B S hS) (ξ : 𝒲.val.val.p.Fiber T) :
    Space.IsFlat B T.left.1 T.left.2 (terminal.from (Stack.isomSpace B S hS 𝒲.val T ξ ξ)) ∧
      Space.IsLocallyOfFinitePresentation B T.left.1 T.left.2
        (terminal.from (Stack.isomSpace B S hS 𝒲.val T ξ ξ)) := by
  obtain ⟨hflat, hlfp⟩ := relativeProperty_isFlat_inertiaProjection_of_isGerbe B S hS 𝒲 h𝒲
  exact ⟨holdsOnEveryEtaleChart_terminal_isomSpace_of_relativeProperty B S hS 𝒲 hflat T ξ,
    holdsOnEveryEtaleChart_terminal_isomSpace_of_relativeProperty B S hS 𝒲 hlfp T ξ⟩

/-- **A scheme representing an automorphism sheaf of a gerbe is flat and locally of finite
presentation over its base.** For a gerbe `𝒲` over `S` and an object `ξ` of the fibre over `T`,
if `Isom_𝒲(ξ, ξ)`, read on the big fppf site of `T`, is isomorphic to the Yoneda presheaf of an
object `Z` of that site, then the structure morphism of `Z` is flat and locally of finite
presentation. -/
theorem flat_and_locallyOfFinitePresentation_of_isGerbe_of_iso_isomSpace
    (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒲 : IsGerbe B S hS 𝒲)
    (T : BigFppfOver B S hS) (ξ : 𝒲.val.val.p.Fiber T)
    (Z : BigFppfOver B T.left.1 T.left.2)
    (e : yoneda.obj Z ≅ Stack.isomSpace B S hS 𝒲.val T ξ ξ) :
    Flat (B.inclusion.map Z.hom) ∧ LocallyOfFinitePresentation (B.inclusion.map Z.hom) := by
  obtain ⟨hflat, hlfp⟩ := relativeProperty_isFlat_inertiaProjection_of_isGerbe B S hS 𝒲 h𝒲
  exact ⟨prop_toScheme_map_of_relativeProperty_inertiaProjection B S hS
      isEtaleLocalOnSourceAndTarget_flat 𝒲 hflat T ξ Z e,
    prop_toScheme_map_of_relativeProperty_inertiaProjection B S hS
      isEtaleLocalOnSourceAndTarget_locallyOfFinitePresentation 𝒲 hlfp T ξ Z e⟩

/-- `flat_and_locallyOfFinitePresentation_of_isGerbe_of_iso_isomSpace` with the identification
of `Isom_𝒲(ξ, ξ)` with the Yoneda presheaf of `Z` given as a family of bijections over the
objects of the site of `T`, natural in them, as in
`AlgebraicGeometry.Stack.QuotientStackIsomSheavesAlgebraic`. -/
theorem flat_and_locallyOfFinitePresentation_of_isGerbe_of_equiv_isomSpace
    (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒲 : IsGerbe B S hS 𝒲)
    (T : BigFppfOver B S hS) (ξ : 𝒲.val.val.p.Fiber T)
    (Z : BigFppfOver B T.left.1 T.left.2)
    (e : ∀ V, (Stack.isomSpace B S hS 𝒲.val T ξ ξ).obj V ≃ (yoneda.obj Z).obj V)
    (he : ∀ ⦃V₁ V₂⦄ (f : V₁ ⟶ V₂) (z : (Stack.isomSpace B S hS 𝒲.val T ξ ξ).obj V₁),
      e V₂ ((Stack.isomSpace B S hS 𝒲.val T ξ ξ).map f z) = (yoneda.obj Z).map f (e V₁ z)) :
    Flat (B.inclusion.map Z.hom) ∧ LocallyOfFinitePresentation (B.inclusion.map Z.hom) :=
  flat_and_locallyOfFinitePresentation_of_isGerbe_of_iso_isomSpace B S hS 𝒲 h𝒲 T ξ Z
    (NatIso.ofComponents (fun V => (e V).toIso) (fun f => by ext z; exact he f z)).symm

/-- **A morphism representing an automorphism sheaf of a gerbe is flat and locally of finite
presentation.** Let `𝒲` be a gerbe over `S` (Stacks 06QC), let `ξ` be an object of the fibre of
`𝒲` over an object `T` of the site, and let `g : V ⟶ T` be a morphism of the site such that the
presheaf represented by `Over.mk g` on the slice over `T` is isomorphic to the presheaf
`Isom_𝒲(ξ, ξ)` of automorphisms of `ξ`. Then the morphism of schemes underlying `g` is flat and
locally of finite presentation. -/
theorem flat_and_locallyOfFinitePresentation_of_isGerbe
    (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒲 : IsGerbe B S hS 𝒲)
    (T : BigFppfOver B S hS) (ξ : 𝒲.val.val.p.Fiber T)
    {V : BigFppfOver B S hS} (g : V ⟶ T)
    (e : letI : 𝒲.val.val.p.IsFibered := 𝒲.val.isFiberedInGroupoids.isFibered
      yoneda.obj (Over.mk g) ≅ 𝒲.val.val.p.isomPresheaf ξ ξ) :
    Flat ((BigFppfOver.toScheme B S hS).map g) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g) := by
  let : 𝒲.val.val.p.IsFibered := 𝒲.val.isFiberedInGroupoids.isFibered
  exact flat_and_locallyOfFinitePresentation_of_isGerbe_of_iso_isomSpace B S hS 𝒲 h𝒲 T ξ
    ((Over.iteratedSliceForward T).obj (Over.mk g))
    ((Over.iteratedSliceEquiv T).symm.toAdjunction.compYonedaIso.app (Over.mk g) ≪≫
      Functor.isoWhiskerLeft (Over.iteratedSliceBackward T).op e)

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.flat_and_locallyOfFinitePresentation_of_isGerbe` with
the identification of `Isom_𝒲(ξ, ξ)` with the presheaf represented by `Over.mk g` given as a
family of bijections over the slice over `T`, natural in it. -/
theorem flat_and_locallyOfFinitePresentation_of_isGerbe_of_equiv
    (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒲 : IsGerbe B S hS 𝒲)
    (T : BigFppfOver B S hS) (ξ : 𝒲.val.val.p.Fiber T)
    {V : BigFppfOver B S hS} (g : V ⟶ T) :
    letI : 𝒲.val.val.p.IsFibered := 𝒲.val.isFiberedInGroupoids.isFibered
    ∀ (e : ∀ W, (yoneda.obj (Over.mk g)).obj W ≃ (𝒲.val.val.p.isomPresheaf ξ ξ).obj W),
      (∀ ⦃W₁ W₂⦄ (f : W₁ ⟶ W₂) (z : (yoneda.obj (Over.mk g)).obj W₁),
        e W₂ ((yoneda.obj (Over.mk g)).map f z) = (𝒲.val.val.p.isomPresheaf ξ ξ).map f (e W₁ z)) →
      Flat ((BigFppfOver.toScheme B S hS).map g) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g) := fun e he =>
  flat_and_locallyOfFinitePresentation_of_isGerbe B S hS 𝒲 h𝒲 T ξ g
    (NatIso.ofComponents (fun W => (e W).toIso) (fun f => by ext z; exact he f z))

section FullSubcategory

variable {B S hS}

/-- **A fully faithful 1-morphism of categories fibred in groupoids induces isomorphisms of
isomorphism presheaves** (Stacks 042V): the map `Isom_𝒳(x, y) ⟶ Isom_𝒴(F x, F y)` applies `F` to a
local isomorphism and conjugates by the comparison of chosen pullbacks, so it is injective by
faithfulness and surjective by fullness, every morphism of a fibre being invertible. -/
theorem isIso_isomPresheafMap_of_full_of_faithful
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F : 𝒳.val ⥤ᵇ 𝒴.val) [F.toFunctor.Full] [F.toFunctor.Faithful]
    (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U) :
    IsIso (Stack.isomPresheafMap B S hS 𝒳 𝒴 F U x y) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have hF := Stack.isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F
  have happ : ∀ g, IsIso ((Stack.isomPresheafMap B S hS 𝒳 𝒴 F U x y).app g) := by
    intro g
    rw [isIso_iff_bijective]
    have hfull : (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).Full :=
      Functor.Fiber.full_mapOfComp hF.comp_eq g.unop.left
    have hfaith : (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).Faithful :=
      Functor.Fiber.faithful_mapOfComp hF.comp_eq g.unop.left
    refine ⟨fun m m' hmm => ?_, fun n => ?_⟩
    · have hmm' : (hF.mapPullbackFiberIso x g.unop.hom).hom ≫
          (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).map m.1 ≫
          (hF.mapPullbackFiberIso y g.unop.hom).inv =
        (hF.mapPullbackFiberIso x g.unop.hom).hom ≫
          (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).map m'.1 ≫
          (hF.mapPullbackFiberIso y g.unop.hom).inv := congrArg Subtype.val hmm
      exact Subtype.ext (hfaith.map_injective ((cancel_mono _).1 ((cancel_epi _).1 hmm')))
    · obtain ⟨m, hm⟩ := hfull.map_surjective
        ((hF.mapPullbackFiberIso x g.unop.hom).inv ≫ n.1 ≫
          (hF.mapPullbackFiberIso y g.unop.hom).hom)
      exact ⟨⟨m, (𝒳.isFiberedInGroupoids.fiber_isGroupoid g.unop.left).all_isIso m⟩,
        Subtype.ext ((congrArg (fun k => (hF.mapPullbackFiberIso x g.unop.hom).hom ≫ k ≫
          (hF.mapPullbackFiberIso y g.unop.hom).inv) hm).trans (by simp))⟩
  exact NatIso.isIso_of_isIso_app _

/-- **The automorphism sheaves of an object of a full substack which is a gerbe are flat.** Let
`P` cut out a full subcategory of an algebraic stack `𝒳` which is an algebraic stack and a gerbe,
let `x` be an object of the fibre of `𝒳` over `T` with `P x`, and let `g : V ⟶ T` be a morphism of
the site such that the presheaf represented by `Over.mk g` on the slice over `T` is isomorphic to
the presheaf `Isom_𝒳(x, x)` of automorphisms of `x` *in `𝒳`*. Then the morphism of schemes
underlying `g` is flat and locally of finite presentation: the inclusion of the full subcategory
is fully faithful and over the site, so the automorphism presheaves of `x` in the substack and in
`𝒳` agree. -/
theorem flat_and_locallyOfFinitePresentation_of_isGerbe_fullSubcategoryAlgebraicStack
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (Stack.fullSubcategoryBased 𝒳 P))
    (hgerbe : IsGerbe B S hS (Stack.fullSubcategoryAlgebraicStack 𝒳 P hP))
    (T : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber T) (hx : P x.1)
    {V : BigFppfOver B S hS} (g : V ⟶ T)
    (e : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      yoneda.obj (Over.mk g) ≅ 𝒳.val.val.p.isomPresheaf x x) :
    Flat ((BigFppfOver.toScheme B S hS).map g) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g) := by
  let 𝒲 := Stack.fullSubcategoryAlgebraicStack 𝒳 P hP
  let ξ : 𝒲.val.val.p.Fiber T := ⟨⟨x.1, hx⟩, x.2⟩
  have : (Stack.fullSubcategoryBasedInclusion 𝒳 P).toFunctor.Full := inferInstanceAs P.ι.Full
  have : (Stack.fullSubcategoryBasedInclusion 𝒳 P).toFunctor.Faithful :=
    inferInstanceAs P.ι.Faithful
  have hι := isIso_isomPresheafMap_of_full_of_faithful 𝒲.val 𝒳.val
    (Stack.fullSubcategoryBasedInclusion 𝒳 P) T ξ ξ
  exact flat_and_locallyOfFinitePresentation_of_isGerbe B S hS 𝒲 hgerbe T ξ g
    (e ≪≫ (asIso (Stack.isomPresheafMap B S hS 𝒲.val 𝒳.val
      (Stack.fullSubcategoryBasedInclusion 𝒳 P) T ξ ξ)).symm)

end FullSubcategory

end AlgebraicGeometry.Stack.AlgebraicStacks

end

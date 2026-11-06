module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Properness and a change of base scheme (Stacks 03ZM, 03HL, 03HI, 03HE)

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ_h` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h` of Stacks 03I5 part (2).

This file proves that **properness** (Stacks 03ZM) of the structural morphism of an algebraic space
over `W` does not depend on the base it is read over: an algebraic space over `W`, viewed over `S`
and then over a larger base `S'`, has proper structural morphism over `S` as soon as it has one
over `S'`. Together with
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactSmallerBase.lean` this completes the four clauses
of Stacks 03ZM, quasi-compactness being Stacks 03HE and local finite type being the
every-étale-chart condition for an arbitrary property of morphisms of schemes.

That is the step a separation condition on the relative diagonal needs in order to be transferred
along Construction A of Stacks 04X5, in the shape the quantifier of Stacks 04XB leaves it in.

## Main results

* `AlgebraicGeometry.presheaf_relocalizeMap_of`: a relatively representable property of an
  *arbitrary* morphism of presheaves is inherited from its lower-shriek extension. This is
  `AlgebraicGeometry.presheaf_relocalizeChart_iff` with the chart replaced by an arbitrary
  morphism.
* `AlgebraicGeometry.Space.isSeparated_of_relocalizeMap` and
  `AlgebraicGeometry.Space.universallyClosed_of_relocalizeMap`: **Stacks 03HL** part (1) and
  **Stacks 03HI** part (2) are inherited from the lower-shriek extension.
* `AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_of`: **Stacks 03ZM** for the
  structural morphism of the image of Stacks 04SG's forward functor does not depend on the base.
* `AlgebraicGeometry.Space.isSeparated_spacesOverSmallerBaseFunctor_of` and
  `AlgebraicGeometry.Space.universallyClosed_spacesOverSmallerBaseFunctor_of`: the two clauses for
  the structural morphism of the image of Stacks 04SG's forward functor do not depend on the base.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_relocalize_iff`: quasi-compactness of an algebraic
  space is unchanged by the lower-shriek extension.
* `AlgebraicGeometry.Space.isQuasiCompact_relocalize_iff`,
  `AlgebraicGeometry.Space.isQuasiSeparated_relocalize_iff`,
  `AlgebraicGeometry.Space.isFiniteType_relocalize_iff`,
  `AlgebraicGeometry.Space.universallyClosed_relocalize_iff` and
  `AlgebraicGeometry.Space.isProper_relocalize_iff`: the conditions on a *morphism* are unchanged
  by the lower-shriek extension, as equivalences.
* `AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_iff`,
  `AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_iff` and
  `AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_iff`: the three conditions for
  the structural morphism of the image of Stacks 04SG's forward functor do not depend on the base
  scheme, as equivalences.
* `AlgebraicGeometry.Space.isClosedMorphism_of_relocalize` and
  `AlgebraicGeometry.Space.universallyClosed_of_relocalize`: the converses of
  `AlgebraicGeometry.Space.isClosedMorphism_relocalize` and
  `AlgebraicGeometry.Space.universallyClosed_relocalize`.
* `CategoryTheory.Limits.pullbackSelfIsoOfArrowIso` and
  `CategoryTheory.Limits.pullback_diagonal_eq_of_arrowIso`: in any category, the relative
  diagonals of two isomorphic arrows agree up to the comparison of their fibre products.

## Implementation notes

The file carries two developments of the same base-independence, at two different strengths, and
they are kept apart because their hypotheses differ.

The first is stated for an *arbitrary* morphism of presheaves, and is therefore only an
*implication*: reading a condition over the smaller base `S` quantifies over algebraic spaces
over `S`, and each of them is pushed forward to `S'` by `Λ_g`, which preserves algebraicity
(Stacks 03I5 part (2)) and fibre products; the converse direction would need every algebraic space
over `S'` mapping to the representable of `W` to come from one over `S`, which is the essential
surjectivity of the equivalence of Stacks 04SG. This is the form
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactSmallerBase.lean` also uses.

The second is stated for the three conditions which **quantify over the algebraic spaces over the
base** — quasi-compactness of Stacks 03HE, quasi-separatedness of Stacks 03HL part (3) and
properness of Stacks 03ZM — and for those it is an *equivalence*. Essential surjectivity is not
needed there because the test objects of those quantifiers are themselves quasi-compact, hence
carry a quasi-compact surjective étale atlas `a : h_U ⟶ Z` out of a *representable* presheaf; the
fibre product over `Z` is covered by the fibre product over `h_U`
(`AlgebraicGeometry.Space.IsQuasiCompactSpace.of_surjective_etale` applied to the base change of
`a`, which stays surjective and étale by `AlgebraicGeometry.Space.presheaf_of_isPullback`), and
the composite `h_U ⟶ Λ_h G` is a chart, so `AlgebraicGeometry.exists_relocalizeChart` writes it
as the extension of a chart of `G` over `W`. The test may therefore be moved to a representable
test object over `W`, whose underlying scheme is unchanged. Separatedness is *not* such a
condition, which is why it appears only in the implication form.

Being locally of finite type is an étale-chart condition, so its transfer is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`; finite type adds
quasi-compactness. For universal closedness the forward direction is proved elsewhere; its converse is
the mirror image of the forward argument — the transports of points of
`AlgebraicGeometry.Space.relocalizedPointsMap` are **bijective** and induce the point topologies,
so the conjugation that carries a closed map forward carries one back as well.

Passing from the extension `Λ_h` to the structural morphism of Stacks 04SG's forward functor
inserts an isomorphism on each side, so each condition is also needed in the form "invariant under
an isomorphism of arrows". For the conditions stated through the relative diagonal this needs the
diagonals of two isomorphic arrows to be compared, which is
`CategoryTheory.Limits.pullback_diagonal_eq_of_arrowIso`; it holds in any category and is proved
from `CategoryTheory.IsPullback.of_iso`, there being no fibre-product computation to do.

The separated clause is a relatively representable condition on the relative diagonal, so it
reduces to `AlgebraicGeometry.presheaf_relocalizeMap_of`, whose generality is the one the
mathematics varies in: an arbitrary morphism of presheaves and an arbitrary pair of bases. The
every-étale-chart form that serves the quasi-DM condition is of no use here, because being a
closed immersion is not an every-étale-chart condition for any property of morphisms of schemes.

The universally closed clause is a condition on the topology of the point set of every base
change, and it reduces to
`AlgebraicGeometry.Space.isClosedMorphism_of_relocalizeMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/PointsSmallerBase.lean`.

`AlgebraicGeometry.Space.isClosedMorphism_of_isIso`,
`AlgebraicGeometry.Space.isClosedMorphism_respectsIso` and
`AlgebraicGeometry.Space.universallyClosed_respectsIso` are the transports along isomorphisms that
the two comparisons of Stacks 03EH and Stacks 04SG need. They are stated at presheaf level, where
`StacksFrontier/AlgebraicGeometry/Spaces/SeparationMorphismProperties.lean` has only the opposite
implication for closedness and only privately.

None of the equivalences is a numbered result of the source: Stacks 03HE, 03HL and 03ZM are the
definitions, and the independence of the base is a step the source performs inside the proofs of
Stacks 050L and 050N rather than a lemma of its own.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

/-- Pullbacks of presheaves on a big fppf site, given directly: instance search for them times
out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_properSmallerBase
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : AlgebraicGeometry.Scheme.{u}}
    {hS : B.Contains S} :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_properSmallerBase
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : AlgebraicGeometry.Scheme.{u}}
    {hS : B.Contains S} {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  hasPullbacks_presheaf_properSmallerBase.has_limit _

local instance (priority := high) hasLimitsOfShape_discrete_presheaf_properSmallerBase
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : AlgebraicGeometry.Scheme.{u}}
    {hS : B.Contains S} {J : Type} :
    HasLimitsOfShape (Discrete J) ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-! ### A relatively representable property of an arbitrary morphism -/

/-- The reflection statement behind `AlgebraicGeometry.presheaf_relocalizeMap_of`, and the
generalization of `AlgebraicGeometry.isPullback_of_isPullback_relocalizeChart` from a chart to an
arbitrary morphism: the lower-shriek extension reflects fibre products and is faithful, so a square
whose extension is a fibre product is one. -/
theorem isPullback_of_isPullback_relocalizeMap
    {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} {k : X ⟶ Y}
    {T V : BigFppfOver B W hW} {p : yoneda.obj T ⟶ X} {e : yoneda.obj V ⟶ Y} {r : T ⟶ V}
    (hp : IsPullback (relocalizeChart B W S hW hS h p)
      (yoneda.map ((Over.map h).map r))
      ((OverShriek.relocalizePresheafFunctor h).map k)
      (relocalizeChart B W S hW hS h e)) :
    IsPullback p (yoneda.map r) k e := by
  have _ : ReflectsLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_reflectsPullbacks h
  have _ := relocalizePresheaf_faithful h
  have key : IsPullback ((OverShriek.relocalizePresheafFunctor h).map p)
      ((OverShriek.relocalizePresheafFunctor h).map (yoneda.map r))
      ((OverShriek.relocalizePresheafFunctor h).map k)
      ((OverShriek.relocalizePresheafFunctor h).map e) := by
    refine hp.of_iso
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T).symm
      (Iso.refl _)
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h V).symm
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [relocalizeChart]
    · simp only [Iso.symm_hom]
      rw [Iso.comp_inv_eq, Category.assoc,
        relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h r]
      simp
    · simp
    · simp [relocalizeChart]
  exact IsPullback.of_map (OverShriek.relocalizePresheafFunctor h)
    ((OverShriek.relocalizePresheafFunctor h).map_injective
      (by simpa only [Functor.map_comp] using key.w)) key

/-- **A property of an arbitrary morphism of presheaves, tested on representable base changes, is
inherited from its lower-shriek extension.** This is
`AlgebraicGeometry.presheaf_relocalizeChart_iff` with the chart replaced by an arbitrary morphism:
every chart of the extension of the source is the extension of a chart, the representable base
changes correspond, and corresponding base changes have the same underlying morphism of schemes. -/
theorem presheaf_relocalizeMap_of (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q]
    {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hk : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      ((OverShriek.relocalizePresheafFunctor h).map k)) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B W hW)).presheaf k := by
  have _ := relocalizePresheaf_faithful h
  refine MorphismProperty.relative.of_exists (F := yoneda) ?_
  intro V₀ e₀
  have hpull' := hk.1.isPullback (relocalizeChart B W S hW hS h e₀)
  have hQ' := hk.2 (relocalizeChart B W S hW hS h e₀)
    (hk.1.fst (relocalizeChart B W S hW hS h e₀))
    (hk.1.snd (relocalizeChart B W S hW hS h e₀)) hpull'
  set T' := hk.1.pullback (relocalizeChart B W S hW hS h e₀)
  set snd' := hk.1.snd (relocalizeChart B W S hW hS h e₀)
  set fst' := hk.1.fst (relocalizeChart B W S hW hS h e₀)
  obtain ⟨ψ, hψ, fst₀, hfe⟩ := exists_relocalizeChart B W S hW hS h T' fst'
  set ι := relocalizeBaseHom B W S hW hS h hψ
  have hbase : ι ≫ relocalizeOverHom B W S hW hS h (Over.mk ψ) =
      snd' ≫ relocalizeOverHom B W S hW hS h V₀ := by
    apply yoneda.map_injective
    have hA : yoneda.map (ι ≫ relocalizeOverHom B W S hW hS h (Over.mk ψ)) =
        fst' ≫ OverShriek.relocalizeToYoneda h X := by
      rw [yoneda.map_comp, ← relocalizeChart_comp_relocalizeToYoneda B W S hW hS h fst₀,
        hfe, Category.assoc]
    have hB : yoneda.map (snd' ≫ relocalizeOverHom B W S hW hS h V₀) =
        yoneda.map snd' ≫ relocalizeChart B W S hW hS h e₀ ≫
          OverShriek.relocalizeToYoneda h Y := by
      rw [yoneda.map_comp, relocalizeChart_comp_relocalizeToYoneda]
    have hC : fst' ≫ OverShriek.relocalizeToYoneda h X =
        yoneda.map snd' ≫ relocalizeChart B W S hW hS h e₀ ≫
          OverShriek.relocalizeToYoneda h Y := by
      rw [← relocalizeToYoneda_naturality B W S hW hS h k, ← Category.assoc, hpull'.w,
        Category.assoc]
    exact hA.trans (hC.trans hB.symm)
  have hψ₀ : snd'.left ≫ V₀.hom = ψ := by
    have hleft := congrArg Over.Hom.left hbase
    simp only [Over.comp_left, relocalizeOverHom, Over.homMk_left, Over.mk_hom] at hleft
    exact hleft.symm
  set snd₀ : (Over.mk ψ : BigFppfOver B W hW) ⟶ V₀ := Over.homMk snd'.left hψ₀
  have hmap : ι ≫ (Over.map h).map snd₀ = snd' := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, relocalizeBaseHom_left]
    exact Category.id_comp _
  have hsqS : IsPullback (relocalizeChart B W S hW hS h fst₀)
      (yoneda.map ((Over.map h).map snd₀))
      ((OverShriek.relocalizePresheafFunctor h).map k)
      (relocalizeChart B W S hW hS h e₀) := by
    refine hpull'.of_iso (yoneda.mapIso (asIso ι)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, asIso_hom]
      exact hfe
    · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, asIso_hom]
      rw [← yoneda.map_comp, hmap]
    · simp
    · simp
  exact ⟨Over.mk ψ, fst₀, snd₀,
    isPullback_of_isPullback_relocalizeMap B W S hW hS h hsqS, hQ'⟩

namespace Space

/-! ### Closed immersions, separatedness and a change of base -/

/-- **Being a closed immersion is inherited from the lower-shriek extension.** -/
theorem isClosedImmersion_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hk : IsClosedImmersion B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    IsClosedImmersion B W hW k :=
  presheaf_relocalizeMap_of B W S hW hS h
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) k hk

/-- Being separated respects isomorphisms: it is the diagonal of a base-change-stable property of
morphisms of presheaves. -/
theorem isSeparated_respectsIso :
    MorphismProperty.RespectsIso (@Space.IsSeparated B S hS) := by
  have h₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have h₂ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).diagonal)

/-- **Stacks 03HL part (1) is inherited from the lower-shriek extension.** Separatedness is the
relative diagonal being a closed immersion, and the extension of the diagonal *is* the diagonal of
the extension, because the extension preserves fibre products. -/
theorem isSeparated_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hk : IsSeparated B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    IsSeparated B W hW k := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  have hiso : MorphismProperty.RespectsIso (@Space.IsSeparated B S hS) :=
    isSeparated_respectsIso B S hS
  have hdiag : (OverShriek.relocalizePresheafFunctor h).map (pullback.diagonal k) ≫
      (PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) k k).hom =
        pullback.diagonal ((OverShriek.relocalizePresheafFunctor h).map k) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
        pullback.diagonal_fst, CategoryTheory.Functor.map_id]
    · simp only [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp,
        pullback.diagonal_snd, CategoryTheory.Functor.map_id]
  refine isClosedImmersion_of_relocalizeMap B W S hW hS h (pullback.diagonal k) ?_
  refine (MorphismProperty.cancel_right_of_respectsIso
    (@Space.IsClosedImmersion B S hS) _
    (PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) k k).hom).1 ?_
  rwa [hdiag]

/-! ### Universal closedness and a change of base -/

/-- An isomorphism of presheaves is closed on points: the map it induces on points is a
homeomorphism for the topology of Stacks 03BX. -/
theorem isClosedMorphism_of_isIso {A D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : A ⟶ D) [IsIso e] :
    IsClosedMorphism B S hS e := by
  let _ := pointTopology B S hS A
  let _ := pointTopology B S hS D
  refine IsClosedMap.of_inverse (continuous_pointsMap B S hS (inv e)) ?_ ?_
  · intro x
    have hx := congrArg (pointsMap B S hS D) (IsIso.inv_hom_id e)
    rw [pointsMap_comp, pointsMap_id] at hx
    exact congrFun hx x
  · intro x
    have hx := congrArg (pointsMap B S hS A) (IsIso.hom_inv_id e)
    rw [pointsMap_comp, pointsMap_id] at hx
    exact congrFun hx x

/-- Being closed on points respects isomorphisms: an isomorphism is closed on points and a
composition of closed morphisms is closed. -/
theorem isClosedMorphism_respectsIso :
    MorphismProperty.RespectsIso (@Space.IsClosedMorphism B S hS) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf => isClosedMorphism_comp B S hS e.hom f
      (isClosedMorphism_of_isIso B S hS e.hom) hf)
    (fun e f hf => isClosedMorphism_comp B S hS f e.hom hf
      (isClosedMorphism_of_isIso B S hS e.hom))

/-- Being universally closed respects isomorphisms: a base change along a morphism to the target
of `f ≫ e` is a base change of `f` along the composite with the inverse of `e`, and a base change
along a morphism to the target of `e ≫ f` is the base change of `f` with its second projection
read through `e`. -/
theorem universallyClosed_respectsIso :
    MorphismProperty.RespectsIso (@Space.UniversallyClosed B S hS) := by
  have hiso : MorphismProperty.RespectsIso (@Space.IsClosedMorphism B S hS) :=
    isClosedMorphism_respectsIso B S hS
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf Z hZ γ => ?_) (fun e f hf Z hZ γ => ?_)
  · have hsq : IsPullback (pullback.fst γ f) (pullback.snd γ f ≫ e.inv) γ (e.hom ≫ f) := by
      refine (IsPullback.of_hasPullback γ f).of_iso (Iso.refl _) (Iso.refl _) e.symm
        (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
    rw [← hsq.isoPullback_inv_fst]
    exact MorphismProperty.RespectsIso.precomp _ _ _ (hf Z hZ γ)
  · have hsq : IsPullback (pullback.fst (γ ≫ e.inv) f) (pullback.snd (γ ≫ e.inv) f) γ
        (f ≫ e.hom) := by
      refine (IsPullback.of_hasPullback (γ ≫ e.inv) f).of_iso (Iso.refl _) (Iso.refl _)
        (Iso.refl _) e ?_ ?_ ?_ ?_ <;> simp
    rw [← hsq.isoPullback_inv_fst]
    exact MorphismProperty.RespectsIso.precomp _ _ _ (hf Z hZ (γ ≫ e.inv))

/-- **Stacks 03HI part (2) is inherited from the lower-shriek extension.** A base change over `W`
is pushed forward by the extension, which preserves algebraicity (Stacks 03I5 part (2)) and fibre
products, and closedness on points is inherited. -/
theorem universallyClosed_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hk : UniversallyClosed B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    UniversallyClosed B W hW k := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  have hiso : MorphismProperty.RespectsIso (@Space.IsClosedMorphism B S hS) :=
    isClosedMorphism_respectsIso B S hS
  intro Z hZ γ
  refine isClosedMorphism_of_relocalizeMap B W S hW hS h (pullback.fst γ k) ?_
  have hcm := hk _ (isAlgebraicSpace_viewOver B W S hW hS h Z hZ)
    ((OverShriek.relocalizePresheafFunctor h).map γ)
  rw [← PreservesPullback.iso_hom_fst (OverShriek.relocalizePresheafFunctor h) γ k]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hcm

/-! ### Change of base scheme -/

section ChangeOfBase

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- A property of morphisms of presheaves which respects isomorphisms, and holds for the structural
morphism over `S'` of the extension along `h ≫ g`, holds for the extension along `g` of the
structural morphism of the extension along `h`. -/
private theorem map_relocalizeToYoneda_of_comp (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (P : MorphismProperty ((BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (hF : P (OverShriek.relocalizeToYoneda (h ≫ g) F)) :
    P ((OverShriek.relocalizePresheafFunctor g).map (OverShriek.relocalizeToYoneda h F)) := by
  have h1 : P (OverShriek.relocalizeToYoneda (h ≫ g) F ≫
      (OverShriek.relocalizeYonedaComp h g).hom) :=
    (MorphismProperty.cancel_right_of_respectsIso P _ _).2 hF
  rw [OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp h g F] at h1
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).1 h1

/-- A property of morphisms of presheaves which is stable under composing with an isomorphism on
the left holds for the structural morphism of the image of Stacks 04SG's forward functor iff it
holds for the structural morphism of the relocalization. -/
private theorem spacesOverSmallerBaseFunctor_hom_iff
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : ∀ {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ⟶ X') [IsIso e] (q : X' ⟶ Y),
      P (e ≫ q) ↔ P q)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F) :
    P (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) ↔
      P (OverShriek.relocalizeToYoneda h F) := by
  rw [← hP ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app ⟨F, hF⟩)
    (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom),
    Space.relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩]

/-- **Separatedness of the structural morphism of a lower-shriek extension does not depend on the
base.** -/
theorem isSeparated_relocalizeToYoneda_comp_of
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : IsSeparated B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F)) :
    IsSeparated B S hS (OverShriek.relocalizeToYoneda h F) := by
  have _ := isSeparated_respectsIso B S' hS'
  exact isSeparated_of_relocalizeMap B S S' hS hS' g _
    (map_relocalizeToYoneda_of_comp B W S hW hS h S' hS' g F _ hF)

/-- **Universal closedness of the structural morphism of a lower-shriek extension does not depend
on the base.** -/
theorem universallyClosed_relocalizeToYoneda_comp_of
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : UniversallyClosed B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F)) :
    UniversallyClosed B S hS (OverShriek.relocalizeToYoneda h F) := by
  have _ := universallyClosed_respectsIso B S' hS'
  exact universallyClosed_of_relocalizeMap B S S' hS hS' g _
    (map_relocalizeToYoneda_of_comp B W S hW hS h S' hS' g F _ hF)

/-- **Stacks 03HL part (1) for the image of Stacks 04SG's forward functor does not depend on the
base.** -/
theorem isSeparated_spacesOverSmallerBaseFunctor_of
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hsep : IsSeparated B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom)) :
    IsSeparated B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hu
  have _ := isSeparated_respectsIso B S hS
  have _ := isSeparated_respectsIso B S' hS'
  exact (spacesOverSmallerBaseFunctor_hom_iff B W S hW hS h _
    (fun e _ q => MorphismProperty.cancel_left_of_respectsIso _ e q) F hF).2
    (isSeparated_relocalizeToYoneda_comp_of B W S hW hS h S' hS' g F
      ((spacesOverSmallerBaseFunctor_hom_iff B W S' hW hS' (h ≫ g) _
        (fun e _ q => MorphismProperty.cancel_left_of_respectsIso _ e q) F hF).1 hsep))

/-- **Stacks 03HI part (2) for the image of Stacks 04SG's forward functor does not depend on the
base.** -/
theorem universallyClosed_spacesOverSmallerBaseFunctor_of
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (huc : UniversallyClosed B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom)) :
    UniversallyClosed B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hu
  have _ := universallyClosed_respectsIso B S hS
  have _ := universallyClosed_respectsIso B S' hS'
  exact (spacesOverSmallerBaseFunctor_hom_iff B W S hW hS h _
    (fun e _ q => MorphismProperty.cancel_left_of_respectsIso _ e q) F hF).2
    (universallyClosed_relocalizeToYoneda_comp_of B W S hW hS h S' hS' g F
      ((spacesOverSmallerBaseFunctor_hom_iff B W S' hW hS' (h ≫ g) _
        (fun e _ q => MorphismProperty.cancel_left_of_respectsIso _ e q) F hF).1 huc))

/-- **Stacks 03ZM for the image of Stacks 04SG's forward functor does not depend on the base.**
The four clauses are inherited one by one: local finite type from the arbitrary-property
every-étale-chart statement, quasi-compactness from Stacks 03HE read over two bases, and the
separated and universally closed clauses from the two statements above. -/
theorem isProper_spacesOverSmallerBaseFunctor_of
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hp : IsProper B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom)) :
    IsProper B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) :=
  ⟨isSeparated_spacesOverSmallerBaseFunctor_of B W S hW hS h S' hS' g u hu F hF hp.1,
    ⟨(holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B W S hW hS h S' hS' g u hu
        _ F hF).mp hp.2.1.1,
      isQuasiCompact_spacesOverSmallerBaseFunctor_of B W S hW hS h S' hS' g u hu F hF
        hp.2.1.2⟩,
    universallyClosed_spacesOverSmallerBaseFunctor_of B W S hW hS h S' hS' g u hu F hF hp.2.2⟩

end ChangeOfBase

end Space

end AlgebraicGeometry

/-! ### The relative diagonals of two isomorphic arrows -/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {X Y X' Y' : C}

/-- The fibre product of `f` with itself is a fibre product of an isomorphic arrow `f'` with
itself, its two projections read through the isomorphism of the sources. -/
theorem isPullback_pullback_comp_of_arrowIso (f : X ⟶ Y) (f' : X' ⟶ Y') (e₁ : X ⟶ X')
    (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂] (w : e₁ ≫ f' = f ≫ e₂) [HasPullback f f] :
    IsPullback (pullback.fst f f ≫ e₁) (pullback.snd f f ≫ e₁) f' f' :=
  (IsPullback.of_hasPullback f f).of_iso (Iso.refl _) (asIso e₁) (asIso e₁) (asIso e₂)
    (by simp) (by simp) (by simpa using w.symm) (by simpa using w.symm)

/-- The comparison isomorphism of the fibre products with themselves of two isomorphic
arrows. -/
noncomputable def pullbackSelfIsoOfArrowIso (f : X ⟶ Y) (f' : X' ⟶ Y') (e₁ : X ⟶ X')
    (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂] (w : e₁ ≫ f' = f ≫ e₂)
    [HasPullback f f] [HasPullback f' f'] :
    pullback f f ≅ pullback f' f' :=
  (isPullback_pullback_comp_of_arrowIso f f' e₁ e₂ w).isoPullback

/-- The comparison isomorphism `pullbackSelfIsoOfArrowIso` followed by the first projection is
the first projection followed by `e₁`. -/
@[simp]
theorem pullbackSelfIsoOfArrowIso_hom_fst (f : X ⟶ Y) (f' : X' ⟶ Y') (e₁ : X ⟶ X')
    (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂] (w : e₁ ≫ f' = f ≫ e₂)
    [HasPullback f f] [HasPullback f' f'] :
    (pullbackSelfIsoOfArrowIso f f' e₁ e₂ w).hom ≫ pullback.fst f' f' =
      pullback.fst f f ≫ e₁ :=
  (isPullback_pullback_comp_of_arrowIso f f' e₁ e₂ w).isoPullback_hom_fst

/-- The comparison isomorphism `pullbackSelfIsoOfArrowIso` followed by the second projection is
the second projection followed by `e₁`. -/
@[simp]
theorem pullbackSelfIsoOfArrowIso_hom_snd (f : X ⟶ Y) (f' : X' ⟶ Y') (e₁ : X ⟶ X')
    (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂] (w : e₁ ≫ f' = f ≫ e₂)
    [HasPullback f f] [HasPullback f' f'] :
    (pullbackSelfIsoOfArrowIso f f' e₁ e₂ w).hom ≫ pullback.snd f' f' =
      pullback.snd f f ≫ e₁ :=
  (isPullback_pullback_comp_of_arrowIso f f' e₁ e₂ w).isoPullback_hom_snd

/-- **The relative diagonals of two isomorphic arrows agree**, read through the isomorphism of
the sources and the comparison `CategoryTheory.Limits.pullbackSelfIsoOfArrowIso` of the two fibre
products. Both sides are the morphism whose two projections are the identity. -/
theorem pullback_diagonal_eq_of_arrowIso (f : X ⟶ Y) (f' : X' ⟶ Y') (e₁ : X ⟶ X')
    (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂] (w : e₁ ≫ f' = f ≫ e₂)
    [HasPullback f f] [HasPullback f' f'] :
    pullback.diagonal f' =
      inv e₁ ≫ pullback.diagonal f ≫ (pullbackSelfIsoOfArrowIso f f' e₁ e₂ w).hom := by
  refine pullback.hom_ext ?_ ?_ <;> simp

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Invariance under an isomorphism of arrows -/

section ArrowIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Quasi-compactness of a morphism is unchanged by composing with an isomorphism of its
target: the composite is a base change of the morphism along the inverse isomorphism. -/
theorem isQuasiCompact_comp_isIso_iff (q : X ⟶ Y) (ι : Y ⟶ Y') [IsIso ι] :
    IsQuasiCompact B S hS (q ≫ ι) ↔ IsQuasiCompact B S hS q :=
  ⟨fun hq => isQuasiCompact_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (fst := 𝟙 X) (snd := q) (f := q ≫ ι) (g := ι) ⟨by simp⟩) hq,
    fun hq => isQuasiCompact_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (fst := 𝟙 X) (snd := q ≫ ι) (f := q) (g := inv ι)
        ⟨by simp⟩) hq⟩

/-- Quasi-compactness of a morphism is unchanged by composing with an isomorphism of its
source. -/
theorem isQuasiCompact_isIso_comp_iff (e : X ⟶ X') [IsIso e] (q : X' ⟶ Y) :
    IsQuasiCompact B S hS (e ≫ q) ↔ IsQuasiCompact B S hS q :=
  ⟨isQuasiCompact_of_isIso_comp B S hS e, isQuasiCompact_isIso_comp B S hS e⟩

variable (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- An arrow isomorphic to `f` is `f` read through two isomorphisms. -/
private theorem eq_inv_comp_comp_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) : f' = inv e₁ ≫ f ≫ e₂ := by
  rw [← w, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- **Quasi-compactness of a morphism depends only on its arrow up to isomorphism.** -/
theorem isQuasiCompact_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS f' := by
  rw [eq_inv_comp_comp_of_arrowIso B S hS f f' e₁ e₂ w]
  exact isQuasiCompact_isIso_comp B S hS (inv e₁)
    ((isQuasiCompact_comp_isIso_iff B S hS f e₂).2 hf)

/-- **Quasi-separatedness of a morphism depends only on its arrow up to isomorphism**: the two
relative diagonals agree by `CategoryTheory.Limits.pullback_diagonal_eq_of_arrowIso`. -/
theorem isQuasiSeparated_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : IsQuasiSeparated B S hS f) :
    IsQuasiSeparated B S hS f' := by
  show IsQuasiCompact B S hS (pullback.diagonal f')
  rw [pullback_diagonal_eq_of_arrowIso f f' e₁ e₂ w]
  exact isQuasiCompact_isIso_comp B S hS (inv e₁)
    ((isQuasiCompact_comp_isIso_iff B S hS (pullback.diagonal f) _).2 hf)

/-- **Separatedness of a morphism depends only on its arrow up to isomorphism.** -/
theorem isSeparated_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : IsSeparated B S hS f) : IsSeparated B S hS f' := by
  show IsClosedImmersion B S hS (pullback.diagonal f')
  rw [pullback_diagonal_eq_of_arrowIso f f' e₁ e₂ w]
  exact MorphismProperty.RespectsIso.precomp _ (inv e₁) _
    (MorphismProperty.RespectsIso.postcomp _ _ _ hf)

/-- **Being locally of finite type depends only on the arrow up to isomorphism.** -/
theorem isLocallyOfFiniteType_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS f' := by
  rw [eq_inv_comp_comp_of_arrowIso B S hS f f' e₁ e₂ w]
  exact (holdsOnEveryEtaleChart_iso_comp_iff B S hS _ (inv e₁) (f ≫ e₂)).2
    ((holdsOnEveryEtaleChart_comp_iso_iff B S hS _ f e₂).2 hf)

/-- **Being of finite type depends only on the arrow up to isomorphism.** -/
theorem isFiniteType_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : IsFiniteType B S hS f) : IsFiniteType B S hS f' :=
  ⟨isLocallyOfFiniteType_of_arrowIso B S hS f f' e₁ e₂ w hf.1,
    isQuasiCompact_of_arrowIso B S hS f f' e₁ e₂ w hf.2⟩

/-- **Universal closedness depends only on the arrow up to isomorphism.** A test morphism
`g : Z ⟶ Y'` for `f'` becomes the test morphism `g ≫ e₂⁻¹` for `f`, and the comparison of the two
fibre products identifies the two projections to `Z`. -/
theorem universallyClosed_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : UniversallyClosed B S hS f) :
    UniversallyClosed B S hS f' := by
  intro Z hZ g
  have hsq : IsPullback (pullback.fst (g ≫ inv e₂) f)
      (pullback.snd (g ≫ inv e₂) f ≫ e₁) g f' :=
    (IsPullback.of_hasPullback (g ≫ inv e₂) f).of_iso (Iso.refl _) (Iso.refl _) (asIso e₁)
      (asIso e₂) (by simp) (by simp) (by simp) (by simpa using w.symm)
  exact isClosedMap_pointsMap_of_comp_isIso B S hS hsq.isoPullback.inv
    hsq.isoPullback_inv_fst (hf Z hZ (g ≫ inv e₂))

/-- **Properness depends only on the arrow up to isomorphism.** -/
theorem isProper_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : IsProper B S hS f) : IsProper B S hS f' :=
  ⟨isSeparated_of_arrowIso B S hS f f' e₁ e₂ w hf.1,
    isFiniteType_of_arrowIso B S hS f f' e₁ e₂ w hf.2.1,
    universallyClosed_of_arrowIso B S hS f f' e₁ e₂ w hf.2.2⟩

end ArrowIso

section Iso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Quasi-separatedness of a morphism is unchanged by composing with an isomorphism of its
target. -/
theorem isQuasiSeparated_comp_isIso_iff (q : X ⟶ Y) (ι : Y ⟶ Y') [IsIso ι] :
    IsQuasiSeparated B S hS (q ≫ ι) ↔ IsQuasiSeparated B S hS q :=
  ⟨isQuasiSeparated_of_arrowIso B S hS (q ≫ ι) q (𝟙 X) (inv ι) (by simp),
    isQuasiSeparated_of_arrowIso B S hS q (q ≫ ι) (𝟙 X) ι (by simp)⟩

/-- Quasi-separatedness of a morphism is unchanged by composing with an isomorphism of its
source. -/
theorem isQuasiSeparated_isIso_comp_iff (e : X ⟶ X') [IsIso e] (q : X' ⟶ Y) :
    IsQuasiSeparated B S hS (e ≫ q) ↔ IsQuasiSeparated B S hS q :=
  ⟨isQuasiSeparated_of_arrowIso B S hS (e ≫ q) q e (𝟙 Y) (by simp),
    isQuasiSeparated_of_arrowIso B S hS q (e ≫ q) (inv e) (𝟙 Y) (by simp)⟩

/-- Separatedness of a morphism is unchanged by composing with an isomorphism of its
target. -/
theorem isSeparated_comp_isIso_iff (q : X ⟶ Y) (ι : Y ⟶ Y') [IsIso ι] :
    IsSeparated B S hS (q ≫ ι) ↔ IsSeparated B S hS q :=
  ⟨isSeparated_of_arrowIso B S hS (q ≫ ι) q (𝟙 X) (inv ι) (by simp),
    isSeparated_of_arrowIso B S hS q (q ≫ ι) (𝟙 X) ι (by simp)⟩

/-- Separatedness of a morphism is unchanged by composing with an isomorphism of its
source. -/
theorem isSeparated_isIso_comp_iff (e : X ⟶ X') [IsIso e] (q : X' ⟶ Y) :
    IsSeparated B S hS (e ≫ q) ↔ IsSeparated B S hS q :=
  ⟨isSeparated_of_arrowIso B S hS (e ≫ q) q e (𝟙 Y) (by simp),
    isSeparated_of_arrowIso B S hS q (e ≫ q) (inv e) (𝟙 Y) (by simp)⟩

/-- Being of finite type is unchanged by composing with an isomorphism of the target. -/
theorem isFiniteType_comp_isIso_iff (q : X ⟶ Y) (ι : Y ⟶ Y') [IsIso ι] :
    IsFiniteType B S hS (q ≫ ι) ↔ IsFiniteType B S hS q :=
  ⟨isFiniteType_of_arrowIso B S hS (q ≫ ι) q (𝟙 X) (inv ι) (by simp),
    isFiniteType_of_arrowIso B S hS q (q ≫ ι) (𝟙 X) ι (by simp)⟩

/-- Being of finite type is unchanged by composing with an isomorphism of the source. -/
theorem isFiniteType_isIso_comp_iff (e : X ⟶ X') [IsIso e] (q : X' ⟶ Y) :
    IsFiniteType B S hS (e ≫ q) ↔ IsFiniteType B S hS q :=
  ⟨isFiniteType_of_arrowIso B S hS (e ≫ q) q e (𝟙 Y) (by simp),
    isFiniteType_of_arrowIso B S hS q (e ≫ q) (inv e) (𝟙 Y) (by simp)⟩

/-- Properness of a morphism is unchanged by composing with an isomorphism of its target. -/
theorem isProper_comp_isIso_iff (q : X ⟶ Y) (ι : Y ⟶ Y') [IsIso ι] :
    IsProper B S hS (q ≫ ι) ↔ IsProper B S hS q :=
  ⟨isProper_of_arrowIso B S hS (q ≫ ι) q (𝟙 X) (inv ι) (by simp),
    isProper_of_arrowIso B S hS q (q ≫ ι) (𝟙 X) ι (by simp)⟩

/-- Properness of a morphism is unchanged by composing with an isomorphism of its source. -/
theorem isProper_isIso_comp_iff (e : X ⟶ X') [IsIso e] (q : X' ⟶ Y) :
    IsProper B S hS (e ≫ q) ↔ IsProper B S hS q :=
  ⟨isProper_of_arrowIso B S hS (e ≫ q) q e (𝟙 Y) (by simp),
    isProper_of_arrowIso B S hS q (e ≫ q) (inv e) (𝟙 Y) (by simp)⟩

end Iso

/-! ### The lower-shriek extension -/

section Relocalize

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (S' : Scheme.{u}) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- **Quasi-compactness of an algebraic space is unchanged by the lower-shriek extension of
Stacks 03I5 part (2).** A quasi-compact surjective étale atlas out of a representable presheaf is
carried to one by `AlgebraicGeometry.relocalizeChart`, whose object of the site has the same
underlying scheme; conversely every chart of the extension is the extension of a chart
(`AlgebraicGeometry.exists_relocalizeChart`), and surjectivity and étaleness are unchanged
(`AlgebraicGeometry.presheaf_relocalizeChart_iff`). No algebraicity is needed. -/
theorem isQuasiCompactSpace_relocalize_iff (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsQuasiCompactSpace B S' hS' ((OverShriek.relocalizePresheafFunctor k).obj F) ↔
      IsQuasiCompactSpace B S hS F := by
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  constructor
  · rintro ⟨U', a', hU', hsurj', hetale'⟩
    obtain ⟨ψ, hψ, a, rfl⟩ := exists_relocalizeChart B S S' hS hS' k U' a'
    have hsurj : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u}) (BigFppfOver.toScheme B S hS)).presheaf a :=
      (presheaf_relocalizeChart_iff B S S' hS hS' k _ a).1
        ((MorphismProperty.cancel_left_of_respectsIso _ _ _).1 hsurj')
    have hetale : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf a :=
      (presheaf_relocalizeChart_iff B S S' hS hS' k _ a).1
        ((MorphismProperty.cancel_left_of_respectsIso _ _ _).1
          (presheaf_etale_of_isEtale B S' hS' hetale'))
    exact ⟨Over.mk ψ, a, hU', hsurj, isEtale_of_presheaf_etale B S hS hetale⟩
  · rintro ⟨U, a, hU, hsurj, hetale⟩
    refine ⟨(Over.map k).obj U, relocalizeChart B S S' hS hS' k a, hU,
      (presheaf_relocalizeChart_iff B S S' hS hS' k _ a).2 hsurj,
      isEtale_of_presheaf_etale B S' hS'
        ((presheaf_relocalizeChart_iff B S S' hS hS' k _ a).2
          (presheaf_etale_of_isEtale B S hS hetale))⟩

/-- **Quasi-compactness of a morphism of algebraic spaces, in the sense of Stacks 03HE, is
unchanged by the lower-shriek extension of Stacks 03I5 part (2).**

The two quantifiers run over different sets of test objects. In one direction a test object `Z`
over `S` is carried to the test object `Λ_k Z` over `S'`, which is an algebraic space by Stacks
03I4 part (3) and quasi-compact by
`AlgebraicGeometry.Space.isQuasiCompactSpace_relocalize_iff`, and the extension preserves the
fibre product being tested. In the other direction a test object over `S'` need not be an
extension; instead its quasi-compact surjective étale atlas `a` is used, the fibre product over
the test object being covered by the fibre product over the representable source of `a`
(`AlgebraicGeometry.Space.IsQuasiCompactSpace.of_surjective_etale`), and the composite of `a`
with the test morphism is a chart, hence the extension of a chart over `S` by
`AlgebraicGeometry.exists_relocalizeChart`. -/
theorem isQuasiCompact_relocalize_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsQuasiCompact B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      IsQuasiCompact B S hS f := by
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  set Λ := OverShriek.relocalizePresheafFunctor k
  constructor
  · intro hbig Z hZ hqc g
    refine (isQuasiCompactSpace_relocalize_iff B S hS S' hS' k (pullback g f)).1
      (IsQuasiCompactSpace.of_iso B S' hS'
        (hbig (Λ.obj Z) (isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hS') k Z hZ)
          ((isQuasiCompactSpace_relocalize_iff B S hS S' hS' k Z).2 hqc) (Λ.map g))
        (PreservesPullback.iso Λ g f).symm)
  · intro hsmall Z' hZ' hqc' g'
    obtain ⟨U', a', hU', hsurj', hetale'⟩ := hqc'
    refine IsQuasiCompactSpace.of_surjective_etale B S' hS'
      (presheaf_of_isPullback B S' hS'
        (IsPullback.of_hasPullback a' (pullback.fst g' (Λ.map f))) hsurj')
      (presheaf_of_isPullback B S' hS'
        (IsPullback.of_hasPullback a' (pullback.fst g' (Λ.map f)))
        (presheaf_etale_of_isEtale B S' hS' hetale')) ?_
    refine isQuasiCompactSpace_of_iso B S' hS'
      (pullbackRightPullbackFstIso g' (Λ.map f) a').symm ?_
    obtain ⟨ψ, hψ, b, hb⟩ := exists_relocalizeChart B S S' hS hS' k U' (a' ≫ g')
    set e : yoneda.obj U' ⟶ Λ.obj (yoneda.obj (Over.mk ψ)) :=
      yoneda.map (relocalizeBaseHom B S S' hS hS' k hψ) ≫
        (relocalizedYonedaIso B (B.obj hS) (B.obj hS') k (Over.mk ψ)).inv with he
    have _ : IsIso e := by
      rw [he]
      infer_instance
    have hb' : a' ≫ g' = e ≫ Λ.map b := by
      rw [hb, he, relocalizeChart, Category.assoc]
    have hQ : IsQuasiCompactSpace B S hS (pullback b f) :=
      hsmall (yoneda.obj (Over.mk ψ)) (isAlgebraicSpace_yoneda B S hS (Over.mk ψ))
        (isQuasiCompactSpace_yoneda_obj B S hS hU') b
    have hsq : IsPullback (Λ.map (pullback.fst b f) ≫ inv e) (Λ.map (pullback.snd b f))
        (a' ≫ g') (Λ.map f) := by
      refine ((IsPullback.of_hasPullback b f).map Λ).of_iso (Iso.refl _) (asIso e).symm
        (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
      simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id]
      rw [hb', ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    exact IsQuasiCompactSpace.of_iso B S' hS'
      ((isQuasiCompactSpace_relocalize_iff B S hS S' hS' k (pullback b f)).2 hQ)
      hsq.isoPullback

/-- **Quasi-separatedness is unchanged by the lower-shriek extension.** The extension carries the
relative diagonal to the relative diagonal
(`CategoryTheory.OverShriek.relocalize_map_diagonal`), and quasi-compactness of a morphism is
unchanged by `AlgebraicGeometry.Space.isQuasiCompact_relocalize_iff`. -/
theorem isQuasiSeparated_relocalize_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsQuasiSeparated B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      IsQuasiSeparated B S hS f := by
  show IsQuasiCompact B S' hS'
      (pullback.diagonal ((OverShriek.relocalizePresheafFunctor k).map f)) ↔ _
  rw [← OverShriek.relocalize_map_diagonal, isQuasiCompact_comp_isIso_iff]
  exact isQuasiCompact_relocalize_iff B S hS S' hS' k (pullback.diagonal f)

/-- **Being locally of finite type is unchanged by the lower-shriek extension**, being an
étale-chart condition. -/
theorem isLocallyOfFiniteType_relocalize_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) :
    IsLocallyOfFiniteType B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      IsLocallyOfFiniteType B S hS f :=
  holdsOnEveryEtaleChart_relocalizeMap_iff B S S' hS hS' k _ f

/-- **Being of finite type is unchanged by the lower-shriek extension.** -/
theorem isFiniteType_relocalize_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsFiniteType B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      IsFiniteType B S hS f :=
  and_congr (isLocallyOfFiniteType_relocalize_iff B S hS S' hS' k f)
    (isQuasiCompact_relocalize_iff B S hS S' hS' k f)

/-- A map `p : A → C` is closed as soon as it is conjugate, along a surjection `u` and an
injection `v` which induce the topologies of their sources, to a closed map `q : A' → C'`.

The closed sets of the induced topology on `A` are exactly the preimages under `u` of the closed
sets of `A'`; the image under `p` of such a preimage is the preimage under `v` of the image under
`q` of the closed set, because `u` is surjective and `v` is injective. -/
private theorem isClosedMap_of_isClosedMap_of_topology_eq_induced {A C A' C' : Type*}
    [tA : TopologicalSpace A] [tC : TopologicalSpace C] [tA' : TopologicalSpace A']
    [tC' : TopologicalSpace C'] (u : A → A') (v : C → C') (hu : Function.Surjective u)
    (hv : Function.Injective v) (htA : tA = TopologicalSpace.induced u tA')
    (htC : tC = TopologicalSpace.induced v tC') (p : A → C) (q : A' → C')
    (hcomm : ∀ a, q (u a) = v (p a)) (hq : IsClosedMap q) : IsClosedMap p := by
  subst htA
  subst htC
  intro D hD
  obtain ⟨E, hE, hEeq⟩ := isClosed_induced_iff.1 hD
  refine isClosed_induced_iff.2 ⟨q '' E, hq E hE, ?_⟩
  rw [← hEeq]
  ext c
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, hxc⟩
    obtain ⟨a, rfl⟩ := hu x
    exact ⟨a, hx, hv ((hcomm a).symm.trans hxc)⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨u a, ha, hcomm a⟩

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Closedness of a morphism of algebraic spaces is unchanged by the lower-shriek extension.**
The converse of `AlgebraicGeometry.Space.isClosedMorphism_relocalize`: the transports of points
are bijective and induce the two point topologies, so the conjugation which carries a closed map
forward carries one back. -/
theorem isClosedMorphism_of_relocalize (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsClosedMorphism B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f)) :
    IsClosedMorphism B S hS f :=
  isClosedMap_of_isClosedMap_of_topology_eq_induced (relocalizedPointsMap B S S' hS hS' k X)
    (relocalizedPointsMap B S S' hS hS' k Y)
    (relocalizedPointsMap_surjective B S S' hS hS' k X)
    (relocalizedPointsMap_injective B S S' hS hS' k Y)
    (pointTopology_eq_induced_relocalizedPointsMap B S hS S' hS' k X hX)
    (pointTopology_eq_induced_relocalizedPointsMap B S hS S' hS' k Y hY)
    _ _ (fun x => (relocalizedPointsMap_naturality B S S' hS hS' k f x).symm) hf

/-- **Closedness of a morphism of algebraic spaces does not depend on the base scheme.** -/
theorem isClosedMorphism_relocalize_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsClosedMorphism B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      IsClosedMorphism B S hS f :=
  ⟨isClosedMorphism_of_relocalize B S hS S' hS' k hX hY f,
    isClosedMorphism_relocalize B S hS S' hS' k hX hY f⟩

/-- **Universal closedness is unchanged by the lower-shriek extension.** The converse of
`AlgebraicGeometry.Space.universallyClosed_relocalize`: a test morphism `g : Z ⟶ Y` over `S`
becomes the test morphism `Λ_k g` over `S'`, and the extension preserves the fibre product, so
the base change in question is the extension of the base change of `f` along `g`. -/
theorem universallyClosed_of_relocalize (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : UniversallyClosed B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f)) :
    UniversallyClosed B S hS f := by
  set Λ := OverShriek.relocalizePresheafFunctor k
  intro Z hZ g
  refine isClosedMorphism_of_relocalize B S hS S' hS' k
    (isAlgebraicSpace_pullback B S hS g f hZ hX hY) hZ _ ?_
  have key := hf (Λ.obj Z) (isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hS') k Z hZ)
    (Λ.map g)
  show IsClosedMap (pointsMap B S' hS' _ (Λ.map (pullback.fst g f)))
  rw [← PreservesPullback.iso_hom_fst Λ g f, pointsMap_comp]
  exact IsClosedMap.comp key
    (isClosedMap_pointsMap_of_isIso B S' hS' (PreservesPullback.iso Λ g f).hom)

/-- **Universal closedness does not depend on the base scheme.** -/
theorem universallyClosed_relocalize_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    UniversallyClosed B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      UniversallyClosed B S hS f :=
  ⟨universallyClosed_of_relocalize B S hS S' hS' k hX hY f,
    universallyClosed_relocalize B S hS S' hS' k hX hY f⟩

/-- **Properness is unchanged by the lower-shriek extension.** It is the conjunction of
separatedness — proved in both directions, as
`AlgebraicGeometry.Space.isSeparated_relocalize` and
`AlgebraicGeometry.Space.isSeparated_of_relocalize` — with finite type and universal
closedness. -/
theorem isProper_relocalize_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsProper B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      IsProper B S hS f :=
  and_congr
    ⟨fun hsep => isSeparated_of_relocalize B S hS hS' k
        (relativelyRepresentable_pullbackDiagonal B S hS f hX) hsep,
      fun hsep => isSeparated_relocalize B S hS hS' k hsep⟩
    (and_congr (isFiniteType_relocalize_iff B S hS S' hS' k f)
      (universallyClosed_relocalize_iff B S hS S' hS' k hX hY f))

end Relocalize

/-! ### The structural morphism of an algebraic space over a smaller base -/

section Structural

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **Quasi-compactness of the structural morphism of a lower-shriek extension does not depend on
the base.** It is quasi-compactness, over `W` itself, of the structural morphism of `F` to the
terminal object of the big fppf site of `W`. -/
theorem isQuasiCompact_relocalizeToYoneda_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda h F) ↔
      IsQuasiCompact B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F, isQuasiCompact_comp_isIso_iff]
  exact isQuasiCompact_relocalize_iff B W hW S hS h (toYonedaId B W hW F)

/-- **Quasi-separatedness of the structural morphism of a lower-shriek extension does not depend
on the base.** -/
theorem isQuasiSeparated_relocalizeToYoneda_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsQuasiSeparated B S hS (OverShriek.relocalizeToYoneda h F) ↔
      IsQuasiSeparated B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F, isQuasiSeparated_comp_isIso_iff]
  exact isQuasiSeparated_relocalize_iff B W hW S hS h (toYonedaId B W hW F)

/-- **Properness of the structural morphism of a lower-shriek extension does not depend on the
base.** -/
theorem isProper_relocalizeToYoneda_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B W hW F) :
    IsProper B S hS (OverShriek.relocalizeToYoneda h F) ↔
      IsProper B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F, isProper_comp_isIso_iff]
  exact isProper_relocalize_iff B W hW S hS h hF
    (isAlgebraicSpace_yoneda B W hW (Over.mk (𝟙 (B.obj hW)))) (toYonedaId B W hW F)

/-- **Separatedness of the structural morphism of a lower-shriek extension does not depend on
the base.** -/
theorem isSeparated_relocalizeToYoneda_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B W hW F) :
    IsSeparated B S hS (OverShriek.relocalizeToYoneda h F) ↔
      IsSeparated B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F, isSeparated_comp_isIso_iff]
  exact ⟨fun hsep ↦ isSeparated_of_relocalize B W hW hS h
      (relativelyRepresentable_pullbackDiagonal B W hW (toYonedaId B W hW F) hF) hsep,
    fun hsep ↦ isSeparated_relocalize B W hW hS h hsep⟩

/-- **Being of finite type is a property of the structural morphism of a lower-shriek extension
which does not depend on the base.** -/
theorem isFiniteType_relocalizeToYoneda_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsFiniteType B S hS (OverShriek.relocalizeToYoneda h F) ↔
      IsFiniteType B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F, isFiniteType_comp_isIso_iff]
  exact isFiniteType_relocalize_iff B W hW S hS h (toYonedaId B W hW F)

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **Quasi-compactness of the structural morphism of an algebraic space over `W` does not change
when the base is enlarged.** Both sides are the condition over `W` itself. -/
theorem isQuasiCompact_relocalizeToYoneda_comp_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsQuasiCompact B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F) ↔
      IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda h F) :=
  (isQuasiCompact_relocalizeToYoneda_iff B W S' hW hS' (h ≫ g) F).trans
    (isQuasiCompact_relocalizeToYoneda_iff B W S hW hS h F).symm

/-- **Quasi-separatedness of the structural morphism of an algebraic space over `W` does not
change when the base is enlarged.** -/
theorem isQuasiSeparated_relocalizeToYoneda_comp_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsQuasiSeparated B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F) ↔
      IsQuasiSeparated B S hS (OverShriek.relocalizeToYoneda h F) :=
  (isQuasiSeparated_relocalizeToYoneda_iff B W S' hW hS' (h ≫ g) F).trans
    (isQuasiSeparated_relocalizeToYoneda_iff B W S hW hS h F).symm

/-- **Properness of the structural morphism of an algebraic space over `W` does not change when
the base is enlarged.** -/
theorem isProper_relocalizeToYoneda_comp_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B W hW F) :
    IsProper B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F) ↔
      IsProper B S hS (OverShriek.relocalizeToYoneda h F) :=
  (isProper_relocalizeToYoneda_iff B W S' hW hS' (h ≫ g) F hF).trans
    (isProper_relocalizeToYoneda_iff B W S hW hS h F hF).symm

/-- **Quasi-compactness of the structural morphism of the image of Stacks 04SG's forward functor
does not depend on the base.** An algebraic space over `W`, viewed over `S` along `h` and over
`S'` along a factorization `h ≫ g`, has the same quasi-compactness of its structural morphism.

This is the companion at **Stacks 03HE** of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`, read through
the identification `AlgebraicGeometry.Space.relocalizeToYoneda_eq` of that structural morphism
with the relocalization's own. The morphism to `S'` is taken as data, together with the
factorization, so that the statement applies to a given object of the big fppf site of `S'`
without rewriting inside the type of the morphism being tested. -/
theorem isQuasiCompact_spacesOverSmallerBaseFunctor_iff
    (u : B.obj hW ⟶ B.obj hS') (hg : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F) :
    IsQuasiCompact B S' hS'
        (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) ↔
      IsQuasiCompact B S hS
        (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hg
  exact (spacesOverSmallerBaseFunctor_hom_iff B W S' hW hS' (h ≫ g) _
      (isQuasiCompact_isIso_comp_iff B S' hS') F hF).trans
    ((isQuasiCompact_relocalizeToYoneda_comp_iff B W S hW hS h S' hS' g F).trans
      (spacesOverSmallerBaseFunctor_hom_iff B W S hW hS h _
        (isQuasiCompact_isIso_comp_iff B S hS) F hF).symm)

/-- **Quasi-separatedness of the structural morphism of the image of Stacks 04SG's forward
functor does not depend on the base.** This is the companion at **Stacks 03HL** part (3) of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`. -/
theorem isQuasiSeparated_spacesOverSmallerBaseFunctor_iff
    (u : B.obj hW ⟶ B.obj hS') (hg : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F) :
    IsQuasiSeparated B S' hS'
        (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) ↔
      IsQuasiSeparated B S hS
        (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hg
  exact (spacesOverSmallerBaseFunctor_hom_iff B W S' hW hS' (h ≫ g) _
      (isQuasiSeparated_isIso_comp_iff B S' hS') F hF).trans
    ((isQuasiSeparated_relocalizeToYoneda_comp_iff B W S hW hS h S' hS' g F).trans
      (spacesOverSmallerBaseFunctor_hom_iff B W S hW hS h _
        (isQuasiSeparated_isIso_comp_iff B S hS) F hF).symm)

/-- **Properness of the structural morphism of the image of Stacks 04SG's forward functor does
not depend on the base.** This is the companion at **Stacks 03ZM** of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`. -/
theorem isProper_spacesOverSmallerBaseFunctor_iff
    (u : B.obj hW ⟶ B.obj hS') (hg : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F) :
    IsProper B S' hS'
        (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) ↔
      IsProper B S hS
        (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hg
  exact (spacesOverSmallerBaseFunctor_hom_iff B W S' hW hS' (h ≫ g) _
      (isProper_isIso_comp_iff B S' hS') F hF).trans
    ((isProper_relocalizeToYoneda_comp_iff B W S hW hS h S' hS' g F hF).trans
      (spacesOverSmallerBaseFunctor_hom_iff B W S hW hS h _
        (isProper_isIso_comp_iff B S hS) F hF).symm)

end Structural

end AlgebraicGeometry.Space

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth

/-!
# The relative property of a 1-morphism of represented stacks (Stacks 04XB)

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf precoverage, and let `a : 𝒜 ⟶ 𝒞` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S` which is representable by algebraic
spaces. Suppose moreover that `𝒜` and `𝒞` are themselves representable by algebraic spaces `F`
and `G`. Then `a` has `P` in the relative sense of Stacks 03YK exactly when the induced morphism
`F ⟶ G` of representing presheaves has `P` as a morphism of algebraic spaces over `S`.

This is the step the conventions paragraph of Stacks, Properties of Stacks, Section 04XB uses
without further mention, and which the last two paragraphs of the proof of Stacks 06FM need: it
is what lets a diagram of algebraic spaces over a pair of represented stacks be read both as a
diagram of 1-morphisms and as a diagram of morphisms of algebraic spaces.

The forward implication is the base-change computation of Stacks 04XC read at the identity base
change: `P` is local on the target, so it is enough to test the induced morphism on its base
changes along scheme-valued points of `G`, a scheme-valued point of `G` is a 1-morphism out of a
slice of the site (Stacks 04SW, onto), and the presheaf representing the base change of `a` along
it is — by Stacks 04SD for represented stacks — the fibre product of the representing presheaves.
The backward implication is the same identification read in the other direction, together with
stability of `P` under base change.

## Main results

* `AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback`: the identification of the structural
  morphism of the lower-shriek extension of a presheaf representing a base change of `a` with the
  base change of the induced morphism of representing presheaves.
* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`: the bridge of
  Stacks 04XB described above.
* `AlgebraicGeometry.Stack.isRelativelySmooth_iff_isSmooth_representingMap`: that bridge at the
  smooth property.

## Implementation notes

No declaration here carries a `@[stacks]` attribute. The general notion is already tagged as
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) and the general base-change test
as `AlgebraicGeometry.Stack.hasRelativeProperty_iff_forall_space_baseChange` (**Stacks 04XC**);
the statements below are those two read at represented source and target, which is a step of the
Stacks 04XB conventions rather than a numbered result of its own.

`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback` is the isomorphism of arrows behind
`AlgebraicGeometry.Stack.prop_pullbackFst_representingMap_of_prop_relocalize`, which is
its forward corollary and transports the property in one direction only. It is stated here as an
isomorphism because the backward implication of the bridge needs the other direction; that
theorem could be re-derived from it.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base change of the induced morphism of representing presheaves along a scheme-valued
point is the structural morphism of the lower-shriek extension**, with no algebraicity
hypothesis on the two representing presheaves.

This is the content of `AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback`: there the
algebraic-space structure on the fibre product is produced from hypotheses that `F` and `G` are
themselves algebraic spaces, and those hypotheses occur only in the statement. Here the
structure is given, which is what lets the identification be used when only the *fibre* of the
morphism over a scheme-valued point is an algebraic space -- the situation of Stacks 045A, where
`F` and `G` are arbitrary presheaves and only `a` is representable by algebraic spaces.

The scheme-valued point's section of `G` and the induced morphism of representing presheaves are
taken as arguments with defining equations so that a consumer can substitute its own names for
them. -/
noncomputable def arrowIsoRelocalizeFibrePullbackOfPullback
    (U : BigFppfOver B S hS)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ 𝒞)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒞.val.obj) (hy : y ⋙ 𝒞.val.p = Over.map U.hom)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (b : yoneda.obj U ⟶ G)
    (hb : representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
      (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy) = b)
    (m : F ⟶ G) (hm : representingMap B S hS 𝒜 𝒞 F G eF eG a = m)
    (hFG : IsAlgebraicSpace B S hS (pullback b m))
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒞.val.p y
        (CatFiberedInGroupoids.homFunctor a))
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T) :
    Arrow.mk (ObjectProperty.homMk (pullback.fst b m) :
        (⟨pullback b m, hFG⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) ≅
      Arrow.mk (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
            isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) := by
  subst hb
  subst hm
  let : (twoFibreProductStructureFunctor B S hS (schemeSlice B S hS U) 𝒜 𝒞
      (schemeSliceMap B S hS U y hy) a).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) a).pt.property.isFibered
  -- the equivalence of `AlgebraicGeometry.Stack.relocalizeFibreEquivalence`, read with the
  -- 2-fibre product written as the apex of the canonical square
  let eT' : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS (schemeSlice B S hS U) 𝒜 𝒞
        (schemeSliceMap B S hS U y hy) a)
      (presheafOfCategories
        ((OverShriek.relocalizePresheafFunctor U.hom).obj T ⋙ typeToCat)).p :=
    relocalizeFibreEquivalence B S hS U a y T eT
  -- the section of `Λ_U T` named by a class in the fibre of the 2-fibre product has, as its
  -- factorization through `U`, the first of the pair of sections that class corresponds to
  have hclass : ∀ (V : (BigFppfOver B S hS)ᵒᵖ)
      (c : _root_.Quotient (isIsomorphicSetoid
        ((twoFibreProductStructureFunctor B S hS (schemeSlice B S hS U) 𝒜 𝒞
          (schemeSliceMap B S hS U y hy) a).Fiber V.unop))),
      (OverShriek.relocalizeToYoneda U.hom T).app V
          (PresheafOfCategories.isoClassSection eT' V.unop c) =
        (twoFibreProductIsoClassSectionEquiv B S hS (schemeSlice B S hS U) 𝒜 𝒞
          (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
          (schemeSliceMap B S hS U y hy) a V.unop c).val.1 := by
    intro V c
    rw [twoFibreProductIsoClassSectionEquiv_val_fst,
      ← representingMap_relocalizeFibre B S hS U a y T eT hy]
    exact morphismSpaceEquiv_app_isoClassSection B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) a).pt (schemeSlice B S hS U)
      ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
      (relocalizeFibreEquivalence B S hS U a y T eT)
      (schemeSliceEquivalenceOver B S hS U) _ V.unop c
  -- hence the comparison of the fibre product of presheaves with `Λ_U T` is over `h_U`
  have hA : (fibreProductIsoRepresenting B S hS (schemeSlice B S hS U) 𝒜 𝒞
          (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
          (schemeSliceMap B S hS U y hy) a
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) eT').hom ≫
        OverShriek.relocalizeToYoneda U.hom T =
      Presheaf.fibreProductFst
        (representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
          (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
        (representingMap B S hS 𝒜 𝒞 F G eF eG a) := by
    ext V s
    refine (congrArg ((OverShriek.relocalizeToYoneda U.hom T).app V)
      (fibreProductIsoRepresenting_hom_app B S hS (schemeSlice B S hS U) 𝒜 𝒞
        (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
        (schemeSliceMap B S hS U y hy) a _ eT' V s)).trans ?_
    exact (hclass V _).trans (congrArg (fun t => t.val.1)
      ((twoFibreProductIsoClassSectionEquiv B S hS (schemeSlice B S hS U) 𝒜 𝒞
        (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
        (schemeSliceMap B S hS U y hy) a V.unop).apply_symm_apply s))
  refine Arrow.isoMk (ObjectProperty.isoMk _
    ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
      fibreProductIsoRepresenting B S hS (schemeSlice B S hS U) 𝒜 𝒞
        (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
        (schemeSliceMap B S hS U y hy) a
        ((OverShriek.relocalizePresheafFunctor U.hom).obj T) eT')) (Iso.refl _) ?_
  apply ObjectProperty.hom_ext
  change ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
      fibreProductIsoRepresenting B S hS (schemeSlice B S hS U) 𝒜 𝒞
        (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
        (schemeSliceMap B S hS U y hy) a
        ((OverShriek.relocalizePresheafFunctor U.hom).obj T) eT').hom ≫
      OverShriek.relocalizeToYoneda U.hom T =
    pullback.fst
      (representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
        (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
      (representingMap B S hS 𝒜 𝒞 F G eF eG a) ≫ 𝟙 _
  rw [Category.comp_id, Iso.trans_hom, Category.assoc, hA, Iso.symm_hom]
  exact (Presheaf.isPullback_fibreProduct _ _).isoPullback_inv_fst

/-- **The base change of the induced morphism of representing presheaves along a scheme-valued
point is the structural morphism of the lower-shriek extension representing the base change**,
as an isomorphism of arrows over the representable algebraic space of the scheme.

Both arrows are arrows over `h_U`: the left-hand one is the first projection of the fibre product
of the induced morphism `F ⟶ G` with the section of `G` named by the scheme-valued point, and the
right-hand one is the structural morphism of the lower-shriek extension of a presheaf `T`
representing the base change of `a` along that point. They agree because, over each object of the
site, both read a class in the fibre of the 2-fibre product as the section of `F` in the pair it
corresponds to under Stacks 04SD for represented stacks. -/
noncomputable def arrowIsoRelocalizeFibrePullback
    (U : BigFppfOver B S hS)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ 𝒞)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒞.val.obj) (hy : y ⋙ 𝒞.val.p = Over.map U.hom)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒞.val.p y
        (CatFiberedInGroupoids.homFunctor a))
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T) :
    Arrow.mk (ObjectProperty.homMk (pullback.fst
          (representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
            (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
          (representingMap B S hS 𝒜 𝒞 F G eF eG a)) :
        (⟨pullback
            (representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
              (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
            (representingMap B S hS 𝒜 𝒞 F G eF eG a),
          isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS U) hF hG⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) ≅
      Arrow.mk (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
            isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) :=
  arrowIsoRelocalizeFibrePullbackOfPullback B S hS U a y hy F G eF eG _ rfl _ rfl
    (isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS U) hF hG) T eT hT

/-- **The bridge of Stacks 04XB for represented source and target.** A 1-morphism
`a : 𝒜 ⟶ 𝒞` of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces, between two categories themselves representable by algebraic
spaces `F` and `G`, has the relative property `P` of Stacks 03YK exactly when the induced
morphism `F ⟶ G` of representing presheaves has `P` as a morphism of algebraic spaces over `S`.

The representing equivalences are arguments rather than existentially quantified, so the
statement applies to any chosen pair; the induced morphism depends on them, while its having `P`
does not. -/
theorem hasRelativeProperty_iff_prop_representingMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    HasRelativeProperty B S hS P a ha ↔
      P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) := by
  constructor
  · intro hP
    refine Space.prop_homMk_of_forall_yoneda B S hS P hF hG _ (fun U v => ?_)
    obtain ⟨T, hT, ⟨eT⟩⟩ := ha U
      (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS U G eG v))
      (CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS U G eG v))
    exact prop_pullbackFst_representingMap_of_prop_relocalize B S hS P U a _
      (CatFiberedInGroupoids.homFunctor_comp_p _) F G eF eG hF hG T eT hT v
      (representingMap_schemePointMap B S hS U G eG v)
      ((prop_algebraicSpaceMap_iff B S hS P U T hT).mp (hP U _
        (CatFiberedInGroupoids.homFunctor_comp_p _) T hT ⟨eT⟩))
  · intro hprop
    rw [hasRelativeProperty_iff_relocalize.{u, v} B S hS P a ha]
    rintro U y hy T hT ⟨eT⟩
    refine (P.arrow_mk_iso_iff
      (arrowIsoRelocalizeFibrePullback B S hS U a y hy F G eF eG hF hG T eT hT)).mp ?_
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk
            (representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
              (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy)) :
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨G, hG⟩)
        (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
          (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)).flip hprop

/-- **The bridge of Stacks 04XB at the smooth property.** A 1-morphism representable by algebraic
spaces, between two categories fibred in groupoids representable by algebraic spaces `F` and `G`,
is smooth in the sense of Stacks 04XB exactly when the induced morphism `F ⟶ G` of representing
presheaves is a smooth morphism of algebraic spaces over `S`.

This is the statement the last two paragraphs of the proof of Stacks 06FM use to read the two
vertical arrows of a smooth diagram as smooth morphisms of algebraic spaces. -/
theorem isRelativelySmooth_iff_isSmooth_representingMap
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    IsRelativelySmooth B S hS a ↔
      Space.IsSmooth B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) := by
  constructor
  · rintro ⟨_, hP⟩
    exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) a ha F G hF hG eF eG).1 hP
  · exact fun h => ⟨ha, (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) a ha F G hF hG eF eG).2 h⟩

end AlgebraicGeometry.Stack

end

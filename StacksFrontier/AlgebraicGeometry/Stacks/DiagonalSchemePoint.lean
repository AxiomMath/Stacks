module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism

/-!
# Stacks 04YR at a scheme-valued point, and the conditions of Stacks 04YS it gives

Let `S` be a scheme contained in a big fppf site `B`, let `f' : 𝒰 ⟶ 𝒴'` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`, and suppose both `𝒰` and `𝒴'` are
representable by algebraic spaces, by presheaves `A` and `H` through chosen equivalences over the
site. Stacks 04SW turns `f'` into a morphism `h = A ⟶ H` of algebraic spaces over `S`
(`AlgebraicGeometry.Stack.representingMap`). This file identifies the morphism of representing
presheaves induced by the *relative diagonal* of `f'` with the relative diagonal
`Δ_h : A ⟶ A ×_H A` of `h`, modulo the comparison of Stacks 04SD between a presheaf representing
`𝒰 ×_{𝒴'} 𝒰` and the fibre product `A ×_H A`.

This is Stacks 04YR read at a scheme-valued point: when `𝒴'` is the stack of a scheme `U` over
`S` and `𝒰` is the base change of a 1-morphism `f : 𝒳 ⟶ 𝒴` along a scheme-valued point of `𝒴`,
the left-hand leg of the base-change square for the diagonal becomes a relative diagonal of a
morphism of algebraic spaces. It turns a condition of Stacks 04XB on `Δ_{f'}` into the same
condition on `Δ_h`.

Three consequences follow, all for a 1-morphism of *represented* categories fibred in groupoids:

* the equivalence of conditions (1) and (2) of Stacks 04YS: `f'` is separated exactly when
  `Δ_{f'}` is a closed immersion in the sense of Stacks 04XB;
* the equivalence of Stacks 04YU: `f'` is locally separated exactly when `Δ_{f'}` is an immersion
  in the sense of Stacks 04XB;
* part (2) of Stacks 04XS: `Δ_{f'}` is locally of finite type in the sense of Stacks 04XB.

## Main results

* `CategoryTheory.MorphismProperty.presheaf_of_forall_yoneda`: a property of morphisms of
  presheaves of the form `P.presheaf` may be tested on base changes along morphisms from
  representable presheaves.
* `AlgebraicGeometry.Stack.prop_relocalize_iff_prop_pullbackFst_representingMap`: the
  identification of Stacks 04XC at a scheme-valued point, read as an equivalence of properties
  and with no hypothesis on the property.
* `AlgebraicGeometry.Stack.prop_representingMap_of_relativeProperty` and
  `AlgebraicGeometry.Stack.relativeProperty_of_prop_representingMap`: the two halves of the
  comparison of Stacks 04XB for represented source and target, with no instance argument.
* `AlgebraicGeometry.Stack.representingMap_relativeDiagonal`: Stacks 04YR at a scheme-valued
  point, the identification described above.
* `AlgebraicGeometry.Stack.prop_representingMap_relativeDiagonal_iff`: that identification read
  as an equivalence of properties of morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.isClosedImmersion_relativeDiagonal_iff_isSeparated_representingMap`:
  the equivalence of conditions (1) and (2) of Stacks 04YS over a represented base.
* `AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_iff_isLocallySeparated_representingMap`:
  the equivalence of Stacks 04YU over a represented base.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_relativeDiagonal_of_representing`: part (2) of
  Stacks 04XS over a represented base.

## Implementation notes

The two halves of the comparison of Stacks 04XB are stated without the two instance arguments of
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`. Locality at the target for
the fppf topology is replaced by the hypothesis that `P` may be tested on base changes along
morphisms from representable presheaves, a theorem for every property of the form `P.presheaf`
(`CategoryTheory.MorphismProperty.presheaf_of_forall_yoneda`). The fppf locality of being a
closed immersion and of being locally of finite type (Stacks 0420 and Stacks 041X) is not
available in this library.

No declaration here carries a `@[stacks]` attribute. Stacks 04YR is a lemma of the Categories
chapter, whose tag is on its absolute form; Stacks 04YS, 04YU and 04XS are statements about
1-morphisms of algebraic stacks, of which the statements here are the represented case only.

`CategoryTheory.MorphismProperty.RespectsIso` of being an immersion of schemes is not found by
instance search, so it is passed explicitly, as
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`.

## References

* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04YU](https://stacks.math.columbia.edu/tag/04YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

universe v u

/-- A property of morphisms of presheaves of the form `P.presheaf` may be tested on base changes
along morphisms from representable presheaves: if every base change of `m : F ⟶ G` along a
morphism `yoneda.obj V ⟶ G` has `P.presheaf`, then so does `m`. -/
theorem presheaf_of_forall_yoneda {C : Type u} [Category.{v} C]
    (P : MorphismProperty C) [P.RespectsIso] {F G : Cᵒᵖ ⥤ Type v} (m : F ⟶ G)
    (h : ∀ (V : C) (v : yoneda.obj V ⟶ G), P.presheaf (pullback.fst v m)) :
    P.presheaf m := by
  refine ⟨fun a g => ?_, fun a b g fst snd BC => ?_⟩
  · obtain ⟨c, snd', fst', Sq⟩ := (h a g).rep (𝟙 (yoneda.obj a))
    refine ⟨c, snd', fst' ≫ pullback.snd g m, ?_⟩
    have hp := IsPullback.paste_horiz Sq (IsPullback.of_hasPullback g m).flip
    simpa using hp
  · refine (h a g).property (𝟙 (yoneda.obj a)) BC.flip.isoPullback.hom snd ?_
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, BC.flip.isoPullback_hom_fst]

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Bridge

variable (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ 𝒞)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)

/-- The identification of Stacks 04XC at a scheme-valued point, for any property respecting
isomorphisms. For a scheme-valued point `y` of `𝒞` over `U` whose induced morphism of
representing presheaves is `b : h_U ⟶ G`, and a presheaf `T` representing the base change of `a`
along `y`, the structural morphism of the lower-shriek extension of `T` has `P` if and only if the
base change of the induced morphism `F ⟶ G` along `b` has `P`. -/
theorem prop_relocalize_iff_prop_pullbackFst_representingMap (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒞.val.obj) (hy : y ⋙ 𝒞.val.p = Over.map U.hom)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒞.val.p y
        (CatFiberedInGroupoids.homFunctor a))
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T) (b : yoneda.obj U ⟶ G)
    (hb : representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
      (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy) = b) :
    P (ObjectProperty.homMk (pullback.fst b (representingMap B S hS 𝒜 𝒞 F G eF eG a)) :
        (⟨pullback b (representingMap B S hS 𝒜 𝒞 F G eF eG a),
          isAlgebraicSpace_pullback B S hS b (representingMap B S hS 𝒜 𝒞 F G eF eG a)
            (isAlgebraicSpace_yoneda B S hS U) hF hG⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) ↔
      P (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
            isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) := by
  subst hb
  exact P.arrow_mk_iso_iff
    (arrowIsoRelocalizeFibrePullback B S hS U a y hy F G eF eG hF hG T eT hT)

/-- The forward half of the comparison of Stacks 04XB for represented source and target. Let
`a : 𝒜 ⟶ 𝒞` be a 1-morphism representable by algebraic spaces between two categories fibred in
groupoids representable by algebraic spaces `F` and `G`, and suppose `P` may be tested on base
changes along morphisms from representable presheaves. If every algebraic space representing a
base change of `a` along a scheme-valued point of `𝒞` has structural morphism with `P`, then the
induced morphism `F ⟶ G` of representing presheaves has `P`. -/
theorem prop_representingMap_of_relativeProperty
    (hdetect : ∀ (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (k : X ⟶ Y),
      (∀ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y),
        P (ObjectProperty.homMk (pullback.fst v k) :
          (⟨pullback v k, isAlgebraicSpace_pullback B S hS v k
            (isAlgebraicSpace_yoneda B S hS V) hX hY⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))) →
      P (ObjectProperty.homMk k : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩))
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒞.val.obj)
      (_hy : y ⋙ 𝒞.val.p = Over.map U.hom)
      (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒞.val.p y
          (CatFiberedInGroupoids.homFunctor a))
        (presheafOfCategories (T ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩))) :
    P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) := by
  refine hdetect F G hF hG _ (fun V v => ?_)
  obtain ⟨T, hT, ⟨eT⟩⟩ := ha V
    (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS V G eG v))
    (CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS V G eG v))
  refine (prop_relocalize_iff_prop_pullbackFst_representingMap B S hS P a F G hF hG eF eG V
    (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS V G eG v))
    (CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS V G eG v)) T eT hT v
    (representingMap_schemePointMap B S hS V G eG v)).mpr ?_
  exact (prop_algebraicSpaceMap_iff B S hS P V T hT).mp
    (hP V (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS V G eG v))
      (CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS V G eG v)) T hT ⟨eT⟩)

/-- The backward half of the comparison of Stacks 04XB for represented source and target, for a
property stable under base change. If the morphism `F ⟶ G` of representing presheaves induced by
a 1-morphism `a : 𝒜 ⟶ 𝒞` has `P`, then every algebraic space representing a base change of `a`
along a scheme-valued point of `𝒞` has structural morphism with `P`. -/
theorem relativeProperty_of_prop_representingMap [P.IsStableUnderBaseChange]
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒞.val.obj) (hy : y ⋙ 𝒞.val.p = Over.map U.hom)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒞.val.p y
        (CatFiberedInGroupoids.homFunctor a))
      (presheafOfCategories (T ⋙ typeToCat)).p)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩)) := by
  obtain ⟨eT⟩ := he
  refine (prop_algebraicSpaceMap_iff B S hS P U T hT).mpr ?_
  refine (prop_relocalize_iff_prop_pullbackFst_representingMap B S hS P a F G hF hG eF eG U y hy
    T eT hT _ rfl).mp ?_
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk
          (representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
            (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy)) :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨G, hG⟩)
      (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)).flip hprop

end Bridge

section SchemePoint

variable (𝒰 𝒴' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f' : 𝒰 ⟶ 𝒴')
    (A H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eA : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (A ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒴'.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    [(twoFibreProductStructureFunctor B S hS 𝒰 𝒰 𝒴' f' f').IsFibered]
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒰 𝒰 𝒴' f' f')
      (presheafOfCategories (T ⋙ typeToCat)).p)

/-- Stacks 04YR at a scheme-valued point. Let `f' : 𝒰 ⟶ 𝒴'` be a 1-morphism of categories
fibred in groupoids over the big fppf site of `S` with `𝒰` and `𝒴'` representable by algebraic
spaces `A` and `H`, and write `h : A ⟶ H` for the morphism of representing presheaves it induces
(Stacks 04SW). Then the morphism of representing presheaves induced by the relative diagonal
`Δ_{f'} : 𝒰 ⟶ 𝒰 ×_{𝒴'} 𝒰` is the relative diagonal `Δ_h : A ⟶ A ×_H A`, modulo the comparison
of Stacks 04SD between a presheaf `T` representing `𝒰 ×_{𝒴'} 𝒰` and the fibre product `A ×_H A`
of presheaves, and the comparison of that fibre product with the pullback. -/
theorem representingMap_relativeDiagonal :
    representingMap B S hS 𝒰
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt A T eA eT
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') ≫
      (fibreProductIsoRepresenting B S hS 𝒰 𝒰 𝒴' A A H eA eA eH f' f' T eT).inv ≫
        (Presheaf.fibreProductIsoPullback _ _).hom =
      pullback.diagonal (representingMap B S hS 𝒰 𝒴' A H eA eH f') := by
  have hd1 : representingMap B S hS 𝒰
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt A T eA eT
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') ≫ representingMap B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt 𝒰 T A eT eA
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').fst = 𝟙 A :=
    (@representingMap_comp B S hS 𝒰
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt 𝒰 A T A eA eT eA
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f')
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').fst).symm.trans
      (representingMap_id B S hS 𝒰 A eA)
  have hd2 : representingMap B S hS 𝒰
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt A T eA eT
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') ≫ representingMap B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt 𝒰 T A eT eA
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').snd = 𝟙 A :=
    (@representingMap_comp B S hS 𝒰
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt 𝒰 A T A eA eT eA
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f')
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').snd).symm.trans
      (representingMap_id B S hS 𝒰 A eA)
  have hpb := Presheaf.isPullback_fibreProduct
    (representingMap B S hS 𝒰 𝒴' A H eA eH f') (representingMap B S hS 𝒰 𝒴' A H eA eH f')
  have hfp1 : (Presheaf.fibreProductIsoPullback
        (representingMap B S hS 𝒰 𝒴' A H eA eH f')
        (representingMap B S hS 𝒰 𝒴' A H eA eH f')).hom ≫
      pullback.fst (representingMap B S hS 𝒰 𝒴' A H eA eH f')
        (representingMap B S hS 𝒰 𝒴' A H eA eH f') =
      Presheaf.fibreProductFst (representingMap B S hS 𝒰 𝒴' A H eA eH f')
        (representingMap B S hS 𝒰 𝒴' A H eA eH f') := hpb.isoPullback_hom_fst
  have hfp2 : (Presheaf.fibreProductIsoPullback
        (representingMap B S hS 𝒰 𝒴' A H eA eH f')
        (representingMap B S hS 𝒰 𝒴' A H eA eH f')).hom ≫
      pullback.snd (representingMap B S hS 𝒰 𝒴' A H eA eH f')
        (representingMap B S hS 𝒰 𝒴' A H eA eH f') =
      Presheaf.fibreProductSnd (representingMap B S hS 𝒰 𝒴' A H eA eH f')
        (representingMap B S hS 𝒰 𝒴' A H eA eH f') := hpb.isoPullback_hom_snd
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.diagonal_fst, Category.assoc, Category.assoc, hfp1,
      ← fibreProductIsoRepresenting_hom_comp_representingMap_fst
        B S hS 𝒰 𝒰 𝒴' A A H eA eA eH f' f' T eT, Iso.inv_hom_id_assoc]
    exact hd1
  · rw [pullback.diagonal_snd, Category.assoc, Category.assoc, hfp2,
      ← fibreProductIsoRepresenting_hom_comp_representingMap_snd
        B S hS 𝒰 𝒰 𝒴' A A H eA eA eH f' f' T eT, Iso.inv_hom_id_assoc]
    exact hd2

/-- Stacks 04YR at a scheme-valued point, read as an equivalence of properties. A property of
morphisms of algebraic spaces over `S` which respects isomorphisms holds of the morphism of
representing presheaves induced by the relative diagonal of `f'` exactly when it holds of the
relative diagonal of the induced morphism `h : A ⟶ H`. -/
theorem prop_representingMap_relativeDiagonal_iff
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (hA : IsAlgebraicSpace B S hS A) (hH : IsAlgebraicSpace B S hS H)
    (hT : IsAlgebraicSpace B S hS T) :
    P (ObjectProperty.homMk (representingMap B S hS 𝒰
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt A T eA eT
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f')) :
        (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶ ⟨T, hT⟩) ↔
      P (ObjectProperty.homMk
          (pullback.diagonal (representingMap B S hS 𝒰 𝒴' A H eA eH f')) :
        (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨pullback (representingMap B S hS 𝒰 𝒴' A H eA eH f')
              (representingMap B S hS 𝒰 𝒴' A H eA eH f'),
            isAlgebraicSpace_pullback B S hS _ _ hA hA hH⟩) := by
  refine P.arrow_mk_iso_iff (Arrow.isoMk (Iso.refl _) (ObjectProperty.isoMk _
    ((fibreProductIsoRepresenting B S hS 𝒰 𝒰 𝒴' A A H eA eA eH f' f' T eT).symm ≪≫
      Presheaf.fibreProductIsoPullback _ _)) ?_)
  exact ObjectProperty.hom_ext _ ((Category.id_comp _).trans
    (representingMap_relativeDiagonal B S hS 𝒰 𝒴' f' A H eA eH T eT).symm)

end SchemePoint

section Conditions

variable (𝒰 𝒴' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f' : 𝒰 ⟶ 𝒴')
    (A H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eA : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (A ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒴'.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (hA : IsAlgebraicSpace B S hS A) (hH : IsAlgebraicSpace B S hS H)
    [(twoFibreProductStructureFunctor B S hS 𝒰 𝒰 𝒴' f' f').IsFibered]
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒰 𝒰 𝒴' f' f')
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hT : IsAlgebraicSpace B S hS T)

/-- For a property `Q` of schemes stable under base change, the relative diagonal of `f'`
satisfies the condition of Stacks 04XB for `Q` exactly when the diagonal of `h : A ⟶ H` has the
presheaf property induced by `Q`; the forward direction needs the relative diagonal to be
representable. -/
private theorem relativeDiagonal_condition_iff_presheaf_diagonal
    (hA : IsAlgebraicSpace B S hS A) (hH : IsAlgebraicSpace B S hS H)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒰 𝒰 𝒴' f' f')
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hT : IsAlgebraicSpace B S hS T)
    (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange] :
    (IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f').hom →
      (∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt.val.obj)
        (_hy : y ⋙ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f' f').pt.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒰.val.p
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt.val.p y
            (CatFiberedInGroupoids.homFunctor
              (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f')))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) →
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.diagonal (representingMap B S hS 𝒰 𝒴' A H eA eH f'))) ∧
    ((Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.diagonal (representingMap B S hS 𝒰 𝒴' A H eA eH f')) →
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt.val.obj)
        (_hy : y ⋙ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f' f').pt.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒰.val.p
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt.val.p y
            (CatFiberedInGroupoids.homFunctor
              (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f')))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) := by
  have hQ := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := Q)
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ k => (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf k.hom
  have hst : P.IsStableUnderBaseChange :=
    ⟨fun sq hf => (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS sq) hf⟩
  have hri := hst.respectsIso
  have key := prop_representingMap_relativeDiagonal_iff B S hS 𝒰 𝒴' f' A H eA eH T eT P hA hH hT
  exact ⟨fun hΔ h => key.mp (prop_representingMap_of_relativeProperty B S hS P
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') A T hA hT eA eT
      (fun X Y _ _ k hk => MorphismProperty.presheaf_of_forall_yoneda _ k hk) hΔ h),
    fun h U y hy F hF he => relativeProperty_of_prop_representingMap B S hS P
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') A T hA hT eA eT (key.mpr h) U y hy F hF he⟩

include hA hH T eT hT in
/-- The equivalence of conditions (1) and (2) of Stacks 04YS over a represented base. Let
`f' : 𝒰 ⟶ 𝒴'` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
with `𝒰` and `𝒴'` representable by algebraic spaces `A` and `H`, and let `h : A ⟶ H` be the
morphism of algebraic spaces it induces. Then the relative diagonal of `f'` is a closed immersion
in the sense of Stacks 04XB exactly when `h` is separated. -/
theorem isClosedImmersion_relativeDiagonal_iff_isSeparated_representingMap
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f').hom) :
    IsClosedImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') ↔
      Space.IsSeparated B S hS (representingMap B S hS 𝒰 𝒴' A H eA eH f') :=
  let h := relativeDiagonal_condition_iff_presheaf_diagonal B S hS 𝒰 𝒴' f' A H eA eH hA hH T eT hT
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
  ⟨h.1 hΔ, h.2⟩

include hA hH T eT hT in
/-- The equivalence of Stacks 04YU over a represented base. Let `f' : 𝒰 ⟶ 𝒴'` be a 1-morphism
of categories fibred in groupoids over the big fppf site of `S` with `𝒰` and `𝒴'` representable
by algebraic spaces `A` and `H`, and let `h : A ⟶ H` be the morphism of algebraic spaces it
induces. Then the relative diagonal of `f'` is an immersion in the sense of Stacks 04XB exactly
when `h` is locally separated. -/
theorem isImmersion_relativeDiagonal_iff_isLocallySeparated_representingMap
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f').hom) :
    IsImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') ↔
      Space.IsLocallySeparated B S hS (representingMap B S hS 𝒰 𝒴' A H eA eH f') :=
  let h := relativeDiagonal_condition_iff_presheaf_diagonal B S hS 𝒰 𝒴' f' A H eA eH hA hH T eT hT
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
  ⟨h.1 hΔ, h.2⟩

include eA eH hA hH T eT hT in
/-- Part (2) of Stacks 04XS over a represented base. The relative diagonal of a 1-morphism
`f' : 𝒰 ⟶ 𝒴'` of categories fibred in groupoids over the big fppf site of `S` whose source and
target are representable by algebraic spaces is locally of finite type in the sense of
Stacks 04XB. -/
theorem isLocallyOfFiniteType_relativeDiagonal_of_representing :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt.val.obj)
      (_hy : y ⋙ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        f' f').pt.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒰.val.p
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' f').pt.val.p y
          (CatFiberedInGroupoids.homFunctor
            (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f')))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  (relativeDiagonal_condition_iff_presheaf_diagonal B S hS 𝒰 𝒴' f' A H eA eH hA hH T eT hT
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})).2
    (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS
      (representingMap B S hS 𝒰 𝒴' A H eA eH f') hA)

end Conditions

end AlgebraicGeometry.Stack

end

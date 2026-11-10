module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction

/-!
# The base change of a chart along an étale, separated, stabilizer-preserving 1-morphism

Let `h : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` which is étale, separated, and
induces isomorphisms on automorphism groups at every point (Stacks 0DTW), and let
`x : 𝒮_U ⟶ 𝒳` be a 1-morphism from the algebraic stack of an object `U` of the big fppf site.
This file proves the first step of the proof of Stacks 0DUS: the 2-fibre product
`U' = 𝒳' ×_𝒳 𝒮_U` is the algebraic stack of an object `W` of the site, and the induced morphism
`W ⟶ U` is an étale and separated morphism of schemes.

## Main results

* `AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isEtale_of_inducesIsomorphismAt`:
  `h` is representable by algebraic spaces, by Stacks 0CIW, 0DU9 and 0DU7.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_hom_of_isSeparated`: for `h`
  representable, separatedness in the sense of Stacks 04YW is separatedness in the relative sense
  of Stacks 04XB, by Stacks 04YS.
* `AlgebraicGeometry.Stack.prop_representingMap_of_relativeProperty_yoneda`: a relative property
  of a 1-morphism whose target is the algebraic stack of an object of the site holds for the
  induced morphism of representing presheaves; it is tested at the identity point, so no
  locality of the property is needed.
* `AlgebraicGeometry.Stack.ChartBaseChange.exists_etale_isSeparated_chartBaseChange`: the
  base change `𝒳' ×_𝒳 𝒮_U` is the algebraic stack of an object `W` of the site whose induced
  morphism to `U` is étale and separated. Representability of `W` is Stacks 0418.

## References

* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 0DU9](https://stacks.math.columbia.edu/tag/0DU9)
* [Stacks Project, Tag 0DU7](https://stacks.math.columbia.edu/tag/0DU7)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace AlgebraicStacks

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **An étale 1-morphism inducing isomorphisms on all automorphism groups is representable by
algebraic spaces.** An étale 1-morphism is unramified (Stacks 0CIW), so by Stacks 0DU9 the
comparison `ℐ_𝒳' ⟶ 𝒳' ×_𝒳 ℐ_𝒳` is an equivalence, and then `h` is representable by algebraic
spaces by Stacks 0DU7. -/
theorem isRepresentableByAlgebraicSpaces_of_isEtale_of_inducesIsomorphismAt (h : 𝒳' ⟶ 𝒳)
    (he : IsEtale B S hS h) (hauto : ∀ q, InducesIsomorphismAt B S hS h q) :
    IsRepresentableByAlgebraicSpaces B S hS h.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isStabilizerPreserving B S hS h
    ((inertiaPullbackComparison_isEquivalenceOver_iff_inducesIsomorphismAt B S hS h
      (isUnramified_of_isEtale B S hS he)).2 hauto)

/-- **Stacks 04YS, (3) ⇒ (1).** A 1-morphism of algebraic stacks representable by algebraic
spaces which is separated in the sense of Stacks 04YW — its relative diagonal is proper — is
separated in the relative sense of Stacks 04XB. -/
theorem isSeparated_hom_of_isSeparated (h : 𝒳' ⟶ 𝒳)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom)
    (hsep : AlgebraicStacks.IsSeparated B S hS h) :
    Stack.IsSeparated B S hS h.hom :=
  ((isSeparated_relativeDiagonal_tfae B S hS h hrep).out 3 1).1 hsep

end AlgebraicStacks

section RepresentableTarget

variable (B S hS) in
/-- **The base change of the representing map along a scheme-valued point is the lower-shriek
extension of the represented base change**, so a property of the latter transfers to the former.
This is `AlgebraicGeometry.Stack.prop_pullbackFst_representingMap_of_prop_relocalize` with its
two instance hypotheses on `P` (base-change stability and fppf locality on the target, neither
of which its proof uses) replaced by invariance under isomorphisms of arrows, which is what the
transfer uses. -/
theorem prop_pullbackFst_representingMap_of_prop_relocalize_of_respectsIso
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (U : BigFppfOver B S hS)
    {𝒜 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (h : 𝒜 ⟶ 𝒵)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj) (hy : y ⋙ 𝒵.val.p = Over.map U.hom)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒵.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒵.val.p y
        (CatFiberedInGroupoids.homFunctor h))
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T)
    (a : yoneda.obj U ⟶ G)
    (ha : representingMap B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
      (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy) = a)
    (hprop : P (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
      (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
          isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
        AlgebraicSpaces B S hS) ⟶
      (schemeSpace U : AlgebraicSpaces B S hS))) :
    P (ObjectProperty.homMk (pullback.fst a (representingMap B S hS 𝒜 𝒵 F G eF eG h)) :
        (⟨pullback a (representingMap B S hS 𝒜 𝒵 F G eF eG h),
          isAlgebraicSpace_pullback B S hS a (representingMap B S hS 𝒜 𝒵 F G eF eG h)
            (isAlgebraicSpace_yoneda B S hS U) hF hG⟩ :
          AlgebraicSpaces B S hS) ⟶
      (schemeSpace U : AlgebraicSpaces B S hS)) := by
  subst ha
  let : (twoFibreProductStructureFunctor B S hS (schemeSlice B S hS U) 𝒜 𝒵
      (schemeSliceMap B S hS U y hy) h).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) h).pt.property.isFibered
  -- the equivalence of `AlgebraicGeometry.Stack.relocalizeFibreEquivalence`, read with the
  -- 2-fibre product written as the apex of the canonical square
  let eT' : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS (schemeSlice B S hS U) 𝒜 𝒵
        (schemeSliceMap B S hS U y hy) h)
      (presheafOfCategories
        ((OverShriek.relocalizePresheafFunctor U.hom).obj T ⋙ typeToCat)).p :=
    relocalizeFibreEquivalence B S hS U h y T eT
  -- the section of `Λ_U T` named by a class in the fibre of the 2-fibre product has, as its
  -- factorization through `U`, the first of the pair of sections that class corresponds to
  have hclass : ∀ (V : (BigFppfOver B S hS)ᵒᵖ)
      (c : _root_.Quotient (isIsomorphicSetoid
        ((twoFibreProductStructureFunctor B S hS (schemeSlice B S hS U) 𝒜 𝒵
          (schemeSliceMap B S hS U y hy) h).Fiber V.unop))),
      (OverShriek.relocalizeToYoneda U.hom T).app V
          (PresheafOfCategories.isoClassSection eT' V.unop c) =
        (twoFibreProductIsoClassSectionEquiv B S hS (schemeSlice B S hS U) 𝒜 𝒵
          (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
          (schemeSliceMap B S hS U y hy) h V.unop c).val.1 := by
    intro V c
    rw [twoFibreProductIsoClassSectionEquiv_val_fst,
      ← representingMap_relocalizeFibre B S hS U h y T eT hy]
    exact morphismSpaceEquiv_app_isoClassSection B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) h).pt (schemeSlice B S hS U)
      ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
      (relocalizeFibreEquivalence B S hS U h y T eT)
      (schemeSliceEquivalenceOver B S hS U) _ V.unop c
  -- hence the comparison of the fibre product of presheaves with `Λ_U T` is over `h_U`
  have hA : (fibreProductIsoRepresenting B S hS (schemeSlice B S hS U) 𝒜 𝒵
          (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
          (schemeSliceMap B S hS U y hy) h
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) eT').hom ≫
        OverShriek.relocalizeToYoneda U.hom T =
      Presheaf.fibreProductFst
        (representingMap B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
          (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
        (representingMap B S hS 𝒜 𝒵 F G eF eG h) := by
    ext V s
    refine (congrArg ((OverShriek.relocalizeToYoneda U.hom T).app V)
      (fibreProductIsoRepresenting_hom_app B S hS (schemeSlice B S hS U) 𝒜 𝒵
        (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
        (schemeSliceMap B S hS U y hy) h _ eT' V s)).trans ?_
    exact (hclass V _).trans (congrArg (fun t => t.val.1)
      ((twoFibreProductIsoClassSectionEquiv B S hS (schemeSlice B S hS U) 𝒜 𝒵
        (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
        (schemeSliceMap B S hS U y hy) h V.unop).apply_symm_apply s))
  -- transport the property along the resulting isomorphism of algebraic spaces over `h_U`
  have hiso : Arrow.mk (ObjectProperty.homMk (pullback.fst
          (representingMap B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
            (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
          (representingMap B S hS 𝒜 𝒵 F G eF eG h)) :
        (⟨pullback
            (representingMap B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
              (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
            (representingMap B S hS 𝒜 𝒵 F G eF eG h),
          isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS U) hF hG⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) ≅
      Arrow.mk (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
            isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) := by
    refine Arrow.isoMk (ObjectProperty.isoMk _
      ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
        fibreProductIsoRepresenting B S hS (schemeSlice B S hS U) 𝒜 𝒵
          (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
          (schemeSliceMap B S hS U y hy) h
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) eT')) (Iso.refl _) ?_
    apply ObjectProperty.hom_ext
    change ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
        fibreProductIsoRepresenting B S hS (schemeSlice B S hS U) 𝒜 𝒵
          (yoneda.obj U) F G (schemeSliceEquivalenceOver B S hS U) eF eG
          (schemeSliceMap B S hS U y hy) h
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) eT').hom ≫
        OverShriek.relocalizeToYoneda U.hom T =
      pullback.fst
        (representingMap B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
          (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy))
        (representingMap B S hS 𝒜 𝒵 F G eF eG h) ≫ 𝟙 _
    rw [Category.comp_id, Iso.trans_hom, Category.assoc, hA, Iso.symm_hom]
    exact (Presheaf.isPullback_fibreProduct _ _).isoPullback_inv_fst
  exact (P.arrow_mk_iso_iff hiso).mpr hprop


/-- **A relative property towards the stack of an object of the site holds for the representing
map.** If `f : 𝒜 ⟶ 𝒵` is representable by algebraic spaces and has the relative property `P`
(Stacks 04XB), and `𝒵` is represented by `h_U` for an object `U` of the site, then the induced
morphism `F ⟶ h_U` of representing presheaves has `P`.

The property is tested at the identity point of `h_U`: the base change of the representing map
along the identity is the representing map itself, so only invariance under isomorphisms of
arrows is needed, and no locality of `P` on the target. -/
theorem prop_representingMap_of_relativeProperty_yoneda
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {𝒜 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒜 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hPf : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hy : y ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒵.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒵.val.p (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒵 F (yoneda.obj U) eF eG f) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶
        (schemeSpace U : AlgebraicSpaces B S hS)) := by
  set m := representingMap B S hS 𝒜 𝒵 F (yoneda.obj U) eF eG f with hm
  obtain ⟨T, hT, ⟨eT⟩⟩ := hf U
    (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS U (yoneda.obj U) eG (𝟙 _)))
    (CatFiberedInGroupoids.homFunctor_comp_p
      (schemePointMap B S hS U (yoneda.obj U) eG (𝟙 _)))
  have hprop := prop_pullbackFst_representingMap_of_prop_relocalize_of_respectsIso B S hS P U f
    (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS U (yoneda.obj U) eG (𝟙 _)))
    (CatFiberedInGroupoids.homFunctor_comp_p
      (schemePointMap B S hS U (yoneda.obj U) eG (𝟙 _)))
    F (yoneda.obj U) eF eG hF (isAlgebraicSpace_yoneda B S hS U) T eT hT (𝟙 _)
    (representingMap_schemePointMap B S hS U (yoneda.obj U) eG (𝟙 _))
    ((prop_algebraicSpaceMap_iff B S hS P U T hT).mp
      (hPf U (CatFiberedInGroupoids.homFunctor
          (schemePointMap B S hS U (yoneda.obj U) eG (𝟙 _)))
        (CatFiberedInGroupoids.homFunctor_comp_p
          (schemePointMap B S hS U (yoneda.obj U) eG (𝟙 _))) T hT ⟨eT⟩))
  have hiso : Arrow.mk (ObjectProperty.homMk (pullback.fst (𝟙 (yoneda.obj U)) m) :
      (⟨pullback (𝟙 (yoneda.obj U)) m, isAlgebraicSpace_pullback B S hS (𝟙 _) m
        (isAlgebraicSpace_yoneda B S hS U) hF (isAlgebraicSpace_yoneda B S hS U)⟩ :
        AlgebraicSpaces B S hS) ⟶
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) ≅
    Arrow.mk (ObjectProperty.homMk m :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) := by
    let e : (⟨pullback (𝟙 (yoneda.obj U)) m, isAlgebraicSpace_pullback B S hS (𝟙 _) m
          (isAlgebraicSpace_yoneda B S hS U) hF (isAlgebraicSpace_yoneda B S hS U)⟩ :
          AlgebraicSpaces B S hS) ≅ ⟨F, hF⟩ :=
      ObjectProperty.isoMk _ (asIso (pullback.snd (𝟙 (yoneda.obj U)) m))
    refine Arrow.isoMk' _ _ e (Iso.refl _) ?_
    apply ObjectProperty.hom_ext
    change pullback.snd (𝟙 (yoneda.obj U)) m ≫ m = pullback.fst (𝟙 (yoneda.obj U)) m ≫ 𝟙 _
    rw [Category.comp_id, ← pullback.condition, Category.comp_id]
  exact (P.arrow_mk_iso_iff hiso).mp hprop

end RepresentableTarget

namespace ChartBaseChange

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)

/-- A relative property (Stacks 04XB) of `h` holds for the projection `𝒳' ×_𝒳 𝒮_U ⟶ 𝒮_U`, since
it is a base change of `h` (Stacks 045C). -/
private theorem relativeProperty_chartBaseChangeSquare_snd
    (P : MorphismProperty (AlgebraicSpaces B S hS)) (hP : RelativeProperty B S hS P h.hom) :
    RelativeProperty B S hS P (chartBaseChangeSquare h x).snd.hom :=
  relativeProperty_baseChange.{u, u, u + 1} B S hS P
    𝒳'.val 𝒳.val (schemeStack.{u, w} B S hS U).val h.hom x.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom x.hom).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        h.hom x.hom)) hP

/-- The projection `𝒳' ×_𝒳 𝒮_U ⟶ 𝒮_U` is separated in the relative sense of Stacks 04XB when
`h` is: it is a base change of `h` (Stacks 045C). -/
theorem isSeparated_chartBaseChangeSquare_snd (hsep : Stack.IsSeparated B S hS h.hom) :
    Stack.IsSeparated B S hS (chartBaseChangeSquare h x).snd.hom :=
  relativeProperty_chartBaseChangeSquare_snd h x (Space.separatedProperty B S hS) hsep

/-- The 1-morphism `f : 𝒰' ⟶ 𝒮_U` of a base-changed chart is separated in the relative sense of
Stacks 04XB when `h` is. -/
theorem isSeparated_chartMap (hsep : Stack.IsSeparated B S hS h.hom)
    {𝒰' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (eK : StacksRepresentableCFG.EquivalenceOver 𝒰'.val.p
      (chartBaseChangeSquare h x).pt.val.val.p) :
    Stack.IsSeparated B S hS (chartMap h x eK) := by
  have hK : Functor.IsEquivalence eK.hom.functor := eK.toEquivalence.isEquivalence_functor
  have hid : Functor.IsEquivalence
      (BasedFunctor.id (schemeStack.{u, w} B S hS U).val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  exact relativeProperty_of_equivalences B S hS (Space.separatedProperty B S hS)
    (chartMap h x eK).hom (chartBaseChangeSquare h x).snd.hom.hom ⟨eK.hom.functor, eK.hom.w⟩
    (BasedFunctor.id _) (Iso.refl _) (isSeparated_chartBaseChangeSquare_snd h x hsep)

/-- **The base change of a chart along an étale, separated, stabilizer-preserving 1-morphism is a
scheme étale and separated over the chart.** Let `h : 𝒳' ⟶ 𝒳` be étale, separated in the sense
of Stacks 04YW, and induce isomorphisms between the automorphism groups at every point
(Stacks 0DTW). For every `x : 𝒮_U ⟶ 𝒳` there are an object `W` of the site, an equivalence
`𝒮_W ≃ 𝒳' ×_𝒳 𝒮_U` over the site, and a morphism `W ⟶ U` of the site, naming the induced
1-morphism `𝒮_W ⟶ 𝒮_U`, which is an étale and separated morphism of schemes.

This is the first step of the proof of Stacks 0DUS: `h` is representable by algebraic spaces
(Stacks 0DU9 and 0DU7), so `𝒳' ×_𝒳 U` is an algebraic space, étale and separated over `U`; it is
then a scheme by Stacks 0418. -/
theorem exists_etale_isSeparated_chartBaseChange (he : IsEtale B S hS h)
    (hsep : AlgebraicStacks.IsSeparated B S hS h)
    (hauto : ∀ q, InducesIsomorphismAt B S hS h q) :
    ∃ (W : BigFppfOver B S hS)
      (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
        (chartBaseChangeSquare h x).pt.val.val.p) (fU : W ⟶ U),
      yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
        (PresheafOfCategories.sliceElementsEquivalenceOver W)
        (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK) ∧
      Etale ((BigFppfOver.toScheme B S hS).map fU) ∧
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map fU) := by
  have hrep := AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isEtale_of_inducesIsomorphismAt
    h he hauto
  have hsep' := AlgebraicStacks.isSeparated_hom_of_isSeparated h hrep hsep
  have : (Space.separatedProperty B S hS).RespectsIso := by
    have := Space.isSeparated_respectsIso B S hS
    exact MorphismProperty.RespectsIso.inverseImage (@Space.IsSeparated B S hS)
      (ObjectProperty.ι _)
  obtain ⟨F, hF, ⟨eF⟩⟩ := isRepresentableByAlgebraicSpace_chartBaseChangeSquare_pt h x hrep
  have hU := isAlgebraicSpace_yoneda B S hS U
  set m := representingMap B S hS (chartBaseChangeSquare h x).pt.val
    (schemeStack.{u, w} B S hS U).val F (yoneda.obj U) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (chartBaseChangeSquare h x).snd.hom
  have hsnd := isRepresentableByAlgebraicSpaces_chartBaseChangeSquare_snd B S hS h x hrep
  have hmsep : Space.IsSeparated B S hS m :=
    prop_representingMap_of_relativeProperty_yoneda (Space.separatedProperty B S hS)
      (chartBaseChangeSquare h x).snd.hom hsnd (isSeparated_chartBaseChangeSquare_snd h x hsep')
      F hF U eF (PresheafOfCategories.sliceElementsEquivalenceOver U)
  have hmet : Space.IsEtale B S hS m := by
    obtain ⟨-, hrel⟩ := isRelativelyEtale_of_isEtale B S hS h hrep he
    exact isEtale_representingMap_of_isRelativelyEtale B S hS
      (chartBaseChangeSquare h x).snd.hom hsnd F (yoneda.obj U) hF hU eF
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      ⟨hsnd, relativeProperty_chartBaseChangeSquare_snd h x (Space.etaleMorphisms B S hS) hrel⟩
  -- Stacks 0418: `F` is representable
  obtain ⟨W, _snd, fst, hpb⟩ :=
    Space.relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS m hF hU
      (Space.isLocallyQuasiFinite_of_isEtale B S hS hU hmet) hmsep (𝟙 (yoneda.obj U))
  have : IsIso fst := hpb.flip.isIso_snd_of_isIso
  let eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
      (chartBaseChangeSquare h x).pt.val.val.p :=
    ((PresheafOfCategories.sliceElementsEquivalenceOver W).trans
      (PresheafOfCategories.equivalenceOverOfIso (asIso fst))).trans eF.symm
  obtain ⟨fU, hfU⟩ : ∃ fU : W ⟶ U, yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W)
      (yoneda.obj U) (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK) :=
    ⟨_, yoneda.map_preimage _⟩
  have hsepW : Space.IsSeparated B S hS (yoneda.map fU) := by
    rw [hfU]
    exact prop_representingMap_of_relativeProperty_yoneda (Space.separatedProperty B S hS)
      (chartMap h x eK) (isRepresentableByAlgebraicSpaces_chartMap h x eK hrep)
      (isSeparated_chartMap h x hsep' eK) (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) U
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
  exact ⟨W, eK, fU, hfU, etale_toScheme_map_of_chartMap h x eK hrep he fU hfU,
    (Space.isSeparated_yoneda_map_iff B S hS fU).1 hsepW⟩

end ChartBaseChange

end AlgebraicGeometry.Stack

end

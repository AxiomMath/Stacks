module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PropertySchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange

/-!
# Testing a relative property on algebraic-space base changes (Stacks 04XC)

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf topology, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories
fibred in groupoids over the big fppf site of `S` which is representable by algebraic spaces.
By definition (Stacks 03YK) `f` *has `P`* when the base change of `f` along every
*scheme*-valued point of `𝒴` has `P`. Stacks 04XC extends that test to all base changes along
1-morphisms out of a stack *representable by an algebraic space*: `f` has `P` exactly when, for
every 2-fibre product square over `g : 𝒵 ⟶ 𝒴` with `𝒵` representable by an algebraic space, the
morphism of representing presheaves induced by the first projection of that square has `P`.

The implication from the general test to the scheme-valued one is instantiation: the big fppf
site of a scheme `U` over `S` is representable by an algebraic space
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeSlice`), a scheme-valued point is
a 1-morphism out of it, and the canonical 2-fibre product square over it has first projection
inducing the structural morphism of the lower-shriek extension of the representing presheaf
(`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`) — which is exactly what Stacks 03YK
tests, by `AlgebraicGeometry.Stack.hasRelativeProperty_iff_relocalize`.

The other implication is the content. Write `m` for the morphism of representing presheaves
induced by the first projection of a given square. Since `P` is local on the base for the fppf
topology, it is enough to test `m` on its base changes along scheme-valued points of the target
(`AlgebraicGeometry.Space.prop_homMk_of_forall_yoneda`). A scheme-valued point of the target is a
section of its representing presheaf, hence (Stacks 04SW, onto) a 1-morphism
`U → 𝒵` (`AlgebraicGeometry.Stack.schemePointMap`); the base change of `f` along its composite
with `g` is representable by Stacks 0302 and has `P` by Stacks 045C; and the presheaf representing
it is, by Stacks 04SD for represented stacks
(`AlgebraicGeometry.Stack.fibreProductIsoRepresenting`), the fibre product of the representing
presheaves — that is, the base change of `m` along the point.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_forall_space_baseChange`: **Stacks 04XC**.

## Implementation notes

The chosen representing equivalences of the two corners are universally quantified, so the
condition is independent of those choices; algebraicity of the source and target stacks is not
needed, only representability of `f` by algebraic spaces.

## References

* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
  [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)

omit [P.IsStableUnderBaseChange] in
/-- **The base change of the induced morphism of representing presheaves along a scheme-valued
point is the structural morphism of the lower-shriek extension representing the base change.** So
the property of the latter, which is what Stacks 03YK tests, transfers to the former, which is
what a locality argument for the former needs. -/
theorem prop_pullbackFst_representingMap_of_prop_relocalize
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
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))) :
    P (ObjectProperty.homMk (pullback.fst a (representingMap B S hS 𝒜 𝒵 F G eF eG h)) :
        (⟨pullback a (representingMap B S hS 𝒜 𝒵 F G eF eG h),
          isAlgebraicSpace_pullback B S hS a (representingMap B S hS 𝒜 𝒵 F G eF eG h)
            (isAlgebraicSpace_yoneda B S hS U) hF hG⟩ :
          AlgebraicSpaces B S hS) ⟶
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) := by
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
    show ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
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

/-- The content of **Stacks 04XC**: a 1-morphism with the relative property `P` has `P` on the
morphism of representing presheaves induced by the first projection of every 2-fibre product
square over a stack representable by an algebraic space. -/
theorem prop_representingMap_of_hasRelativeProperty
    (hP : HasRelativeProperty B S hS P f hf)
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (g : 𝒵 ⟶ 𝒴) (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒵.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) := by
  have hQrep := isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS 𝒳 𝒴 𝒵 f g Q hQ hf
  have hQprop := hasRelativeProperty_baseChange.{u, u, u, v} B S hS P 𝒳 𝒴 𝒵 f g Q hQ hf hP
  refine Space.prop_homMk_of_forall_yoneda B S hS P hF hG _ (fun U a => ?_)
  -- the scheme-valued point of `𝒵` named by `a`
  have hy := CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS U G eG a)
  obtain ⟨T, hT, ⟨eT⟩⟩ := hQrep U _ hy
  exact prop_pullbackFst_representingMap_of_prop_relocalize B S hS P U Q.fst _ hy
    F G eF eG hF hG T eT hT a (representingMap_schemePointMap B S hS U G eG a)
    ((prop_algebraicSpaceMap_iff B S hS P U T hT).mp (hQprop U _ hy T hT ⟨eT⟩))

/-- The easy implication of **Stacks 04XC**: a 1-morphism whose every algebraic-space base change
has `P` has the relative property `P`, because a scheme-valued point of the target is a
1-morphism out of the big fppf site of that scheme, which is representable by an algebraic
space. -/
theorem hasRelativeProperty_of_forall_space_baseChange
    (H : ∀ (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
        (_h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵)
        (g : 𝒵 ⟶ 𝒴) (Q : Bicategory.TwoCommSq g f)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
        (eF : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
        (eG : StacksRepresentableCFG.EquivalenceOver
          𝒵.val.p (presheafOfCategories (G ⋙ typeToCat)).p),
        P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :
          (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS))) :
    HasRelativeProperty B S hS P f hf := by
  rw [hasRelativeProperty_iff_relocalize B S hS P f hf]
  intro U y hy T hT he
  obtain ⟨e⟩ := he
  have hp := H (schemeSlice B S hS U) (isRepresentableByAlgebraicSpace_schemeSlice B S hS U)
    (schemeSliceMap B S hS U y hy)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f)
    ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
    (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
    (isAlgebraicSpace_yoneda B S hS U)
    (relocalizeFibreEquivalence B S hS U f y T e)
    (schemeSliceEquivalenceOver B S hS U)
  rw [representingMap_relocalizeFibre B S hS U f y T e hy] at hp
  exact hp

/-- **Stacks 04XC.** A 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which is representable by algebraic spaces has the relative property `P` exactly when, for every
2-fibre product square over a 1-morphism out of a stack representable by an algebraic space, the
morphism of representing presheaves induced by the first projection of that square has `P` as a
morphism of algebraic spaces over `S`.

The chosen representing equivalences are universally quantified, so the condition does not depend
on them; and algebraicity of `𝒳` and `𝒴` is not needed, only representability of `f` by algebraic
spaces. -/
@[stacks 04XC]
theorem hasRelativeProperty_iff_forall_space_baseChange :
    HasRelativeProperty B S hS P f hf ↔
      ∀ (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
        (_h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵)
        (g : 𝒵 ⟶ 𝒴) (Q : Bicategory.TwoCommSq g f)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
        (eF : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
        (eG : StacksRepresentableCFG.EquivalenceOver
          𝒵.val.p (presheafOfCategories (G ⋙ typeToCat)).p),
        P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :
          (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) :=
  ⟨fun hP 𝒵 _ g Q hQ F G hF hG eF eG =>
    prop_representingMap_of_hasRelativeProperty B S hS P f hf hP 𝒵 g Q hQ F G hF hG eF eG,
    hasRelativeProperty_of_forall_space_baseChange B S hS P f hf⟩

end AlgebraicGeometry.Stack

end

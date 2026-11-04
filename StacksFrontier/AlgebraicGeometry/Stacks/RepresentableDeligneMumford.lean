module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex

/-!
# A category representable by an algebraic space is Deligne-Mumford (Stacks 03YS, part (1))

Let `S` be a scheme contained in a big fppf site `B`. A category fibred in groupoids over the
big fppf site of `S` which is representable by an algebraic space over `S` in the sense of
Stacks 04SV is an algebraic stack, and in fact a Deligne-Mumford stack.

Stacks deduces this from part (2) by Lemma 03YQ, invariance of the Deligne-Mumford condition
under equivalence over the site; that lemma is not in this library, and neither is Stacks 0459,
invariance of a *relative property* under equivalence. Neither is
needed here. Three of the four clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` are already
stated for an arbitrary category representable by an algebraic space
(`AlgebraicGeometry.Stack.isStackInGroupoids_of_isRepresentableByAlgebraicSpace`,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor`,
`AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace`), so all
that has to move along the equivalence `e` of Stacks 04SV is the presentation clause — and that
moves by two *structural* comparisons of 2-fibre products rather than by a transport of the
relative property.

The presentation is the scheme atlas of the representing algebraic space followed by the
backward 1-morphism of `e`, i.e.
`presentationBasedFunctor B S hS U atl ⋙ e.inv`. For a scheme-valued point `y` of the category,
`CategoryTheory.TwoFibreProductOver.mapBase` along `e.inv` carries the 2-fibre product that
`AlgebraicGeometry.Stack.prop_presentationBasedFunctor` already tests — the one taken over the
category of elements, at the point `y ⋙ e.hom` — to the one taken over the category itself. Its
second leg is then the presentation on the nose; its first leg is `y` only up to the unit
isomorphism of `e`, and `CategoryTheory.TwoFibreProductOver.reindex` absorbs exactly that.

## Main results

* `CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_reindex`: reindexing a 2-fibre
  product over `𝒞` along a 2-isomorphism of its first leg is an equivalence over the first
  factor.
* `AlgebraicGeometry.Stack.prop_transportedPresentation`: the presentation clause of
  `AlgebraicGeometry.Stack.IsAlgebraicStack` for the transported atlas and an arbitrary property
  of morphisms of algebraic spaces over `S` stable under base change.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_isRepresentableByAlgebraicSpace`: **Stacks 026O**
  for a category representable by an algebraic space.
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isRepresentableByAlgebraicSpace`:
  **Stacks 03YS**, part (1).

## Implementation notes

`CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_reindex` reads
`CategoryTheory.TwoFibreProductOver.isEquivalence_reindex` of
`StacksFrontier.CategoryTheory.TwoFibreProductOverReindex` through
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`. It is subsumed by
`CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver` of
`StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict`, which builds the same equivalence over
the first factor with neither of the two fibred-in-groupoids hypotheses and as a datum rather than
a `Nonempty`; the weaker form is kept for its two consumers in other modules.

Both comparisons are kept at general categories: inlined at the concrete site types, the `rfl`
they reduce to times out in the **kernel**, while the general statements are checked once, at
abstract types.

Stacks 026O for an arbitrary representable category subsumes two special cases —
`AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory` (the category of elements of an
algebraic space, from Stacks 03YS part (2)) and
`AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory` (the big fppf site of a scheme,
from part (3)) — each of which is this result applied to the corresponding instance of
Stacks 04SV. Both are kept as separate declarations, since each carries its own Stacks tag.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PresheafOfCategories

namespace CategoryTheory.TwoFibreProductOver

universe vR₁ vR₂ vR₃ vR₄ uR₁ uR₂ uR₃ uR₄

variable {𝒞 : Type uR₁} [Category.{vR₁} 𝒞] {𝒳 : Type uR₂} [Category.{vR₂} 𝒳]
  {𝒴 : Type uR₃} [Category.{vR₃} 𝒴] {𝒮 : Type uR₄} [Category.{vR₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F F' : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- **Reindexing the first leg of a 2-fibre product over `𝒞` along a 2-isomorphism does not
change its first projection, up to equivalence over the first factor.** This is
`CategoryTheory.TwoFibreProductOver.reindex`, which commutes with the first projection on the
nose, read through
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`. -/
theorem nonempty_equivalenceOver_reindex (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x))
    (h : (fst p𝒳 p𝒴 p𝒮 F G).IsFiberedInGroupoids)
    (h' : (fst p𝒳 p𝒴 p𝒮 F' G).IsFiberedInGroupoids) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (fst p𝒳 p𝒴 p𝒮 F G)
      (fst p𝒳 p𝒴 p𝒮 F' G)) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h h'
    (reindex (p𝒴 := p𝒴) (G := G) α hα) (reindex_comp_fst α hα) (isEquivalence_reindex α hα)

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Stack

/-- **The presentation clause of Stacks 026O for a category representable by an algebraic
space.** Let `e` identify a category fibred in groupoids `𝒳` over the big fppf site of `S` with
the category of elements of an algebraic space `F` over `S`, let `atl : h_U ⟶ F` be a morphism
of presheaves with a property `P` of morphisms of algebraic spaces over `S` stable under base
change, and let the presentation of `𝒳` be the induced 1-morphism of Stacks 045A followed by the
backward 1-morphism of `e`. Then every algebraic space representing a base change of that
presentation along a scheme-valued point of `𝒳` has structural morphism with `P`.

The 2-fibre product is compared with the one
`AlgebraicGeometry.Stack.prop_presentationBasedFunctor` tests in two steps: postcomposing both
legs with `e.inv` (`CategoryTheory.TwoFibreProductOver.mapBase`), which lands the second leg on
the presentation exactly, and reindexing the first leg along the unit isomorphism of `e`
(`CategoryTheory.TwoFibreProductOver.reindex`), which is what makes the point `y ⋙ e.hom ⋙ e.inv`
into `y`. -/
theorem prop_transportedPresentation
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (U : BigFppfOver B S hS) (atl : yoneda.obj U ⟶ F)
    (hatl : P (ObjectProperty.homMk atl :
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩))
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (schemeFibredCategory B S hS U).val.p
        𝒳.val.p y
        (BasedFunctor.comp (presentationBasedFunctor B S hS U atl)
          (⟨e.inv.functor, e.inv.w⟩ :
            (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val)).toFunctor)
      (presheafOfCategories (G ⋙ typeToCat)).p)) :
    P (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)) := by
  have hinve : Functor.IsEquivalence e.inv.functor := e.isEquivalence_inv_functor
  have hy' : (y ⋙ e.hom.functor) ⋙ (fibredCategory B S hS F).val.p = Over.map V.hom :=
    (congrArg (fun k : 𝒳.val.obj ⥤ BigFppfOver B S hS => y ⋙ k) e.hom.w).trans hy
  have hy'' : ((y ⋙ e.hom.functor) ⋙ e.inv.functor) ⋙ 𝒳.val.p = Over.map V.hom :=
    (congrArg (fun k : (fibredCategory B S hS F).val.obj ⥤ BigFppfOver B S hS =>
      (y ⋙ e.hom.functor) ⋙ k) e.inv.w).trans hy'
  have hα : ∀ x : BigFppfOver B V.left.1 V.left.2,
      𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj x)) (e.unitIso.inv.app (y.obj x)) := by
    intro x
    have hx : 𝒳.val.p.obj (y.obj x) = (Over.map V.hom).obj x :=
      congrArg (fun k : BigFppfOver B V.left.1 V.left.2 ⥤ BigFppfOver B S hS => k.obj x) hy
    have hl := e.isHomLift_unitIso_inv_app (y.obj x)
    rw [hx] at hl
    exact hl
  have hfpbf := fst_isFiberedInGroupoids_overMap V.hom
    (schemeFibredCategory B S hS U).val.p (fibredCategory B S hS F).val.p
    (y ⋙ e.hom.functor) (presentationBasedFunctor B S hS U atl).toFunctor
    (schemeFibredCategory B S hS U).isFiberedInGroupoids
    (fibredCategory B S hS F).isFiberedInGroupoids hy'
    (presentationBasedFunctor B S hS U atl).w
  have hw := (BasedFunctor.comp (presentationBasedFunctor B S hS U atl)
      (⟨e.inv.functor, e.inv.w⟩ : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val)).w
  have hfmid := fst_isFiberedInGroupoids_overMap V.hom _ 𝒳.val.p _ _
    (schemeFibredCategory B S hS U).isFiberedInGroupoids 𝒳.isFiberedInGroupoids hy'' hw
  have hfcl := fst_isFiberedInGroupoids_overMap V.hom _ 𝒳.val.p y _
    (schemeFibredCategory B S hS U).isFiberedInGroupoids 𝒳.isFiberedInGroupoids hy hw
  refine prop_presentationBasedFunctor B S hS P U hF atl hatl V (y ⋙ e.hom.functor) hy' G hG
    (he.map fun eq => ?_)
  refine StacksRepresentableCFG.EquivalenceOver.trans
    (TwoFibreProductOver.nonempty_equivalenceOver_mapBase (y ⋙ e.hom.functor)
      (presentationBasedFunctor B S hS U atl).toFunctor e.inv.functor e.inv.w
      hfpbf hfmid).some
    (StacksRepresentableCFG.EquivalenceOver.trans
      (TwoFibreProductOver.nonempty_equivalenceOver_reindex
        (Functor.isoWhiskerLeft y e.unitIso).symm hα hfmid hfcl).some eq)

/-- **Stacks 026O for a category representable by an algebraic space.** A category fibred in
groupoids over the big fppf site of `S` which is representable by an algebraic space over `S` is
an algebraic stack.

It is a stack in groupoids and has a diagonal representable by algebraic spaces by the two
consequences of Stacks 02ZZ, and a surjective smooth scheme atlas of the representing
algebraic space presents it, by
`AlgebraicGeometry.Stack.prop_transportedPresentation`. -/
theorem isAlgebraicStack_of_isRepresentableByAlgebraicSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  obtain ⟨F, hF, ⟨e⟩⟩ := id h𝒳
  obtain ⟨U, atl, hsurj, hsmooth⟩ := Space.exists_isSurjective_isSmooth_atlas B S hS hF
  refine ⟨𝒳.isFiberedInGroupoids,
    ⟨isStack_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳,
     isStackInGroupoids_of_isRepresentableByAlgebraicSpace.{u, w} B S hS 𝒳 h𝒳⟩,
    isRepresentableByAlgebraicSpaces_diagonalBasedFunctor B S hS 𝒳 h𝒳,
    U, BasedFunctor.comp (presentationBasedFunctor B S hS U atl) ⟨e.inv.functor, e.inv.w⟩,
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳 U _,
    fun V y hy G hG he => ⟨?_, ?_⟩⟩
  · exact prop_transportedPresentation B S hS (Space.surjectiveMorphismProperty B S hS) hF e
      U atl hsurj V y hy G hG he
  · exact prop_transportedPresentation B S hS (Space.smoothMorphismProperty B S hS) hF e
      U atl hsmooth V y hy G hG he

/-- **Stacks 03YS, part (1).** A category fibred in groupoids over the big fppf site of `S`
which is representable by an algebraic space over `S` is a Deligne-Mumford stack.

It is an algebraic stack by
`AlgebraicGeometry.Stack.isAlgebraicStack_of_isRepresentableByAlgebraicSpace`, and the
surjective étale scheme atlas of Stacks 025Y for the representing algebraic space presents it
étale-ly, again by `AlgebraicGeometry.Stack.prop_transportedPresentation`. -/
@[stacks 03YS "part (1)"]
theorem isDeligneMumfordStack_of_isRepresentableByAlgebraicSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val := by
  obtain ⟨F, hF, ⟨e⟩⟩ := id h𝒳
  obtain ⟨U, atl, hsurjp, hetalep⟩ := hF.exists_atlas
  have hsurj : Space.IsSurjective B S hS atl :=
    (Space.surjective_iff_surjective_pointsMap B S hS F hF U atl).1 hsurjp
  have hetale : Space.IsEtale B S hS atl :=
    (Space.isEtale_iff_presheaf_of_yoneda B S hS atl).2 hetalep
  refine ⟨isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS 𝒳 h𝒳,
    𝒳.isFiberedInGroupoids, U,
    Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp (presentationBasedFunctor B S hS U atl) ⟨e.inv.functor, e.inv.w⟩),
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳 U _,
    fun V y hy G hG he => ⟨?_, ?_⟩⟩
  · exact prop_transportedPresentation B S hS (Space.surjectiveMorphismProperty B S hS) hF e
      U atl hsurj V y hy G hG he
  · exact prop_transportedPresentation B S hS (Space.etaleMorphisms B S hS) hF e
      U atl hetale V y hy G hG he

end Stack

end AlgebraicGeometry

end

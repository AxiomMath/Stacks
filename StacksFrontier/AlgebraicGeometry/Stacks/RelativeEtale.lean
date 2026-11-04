module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSchemePointCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange

/-!
# The bridge of Stacks 04XB at étaleness, and étaleness of a comparison 1-morphism

`AlgebraicGeometry.Stack.IsRelativelyEtale` is the relative property of **Stacks 03YK** at
étaleness of morphisms of algebraic spaces over `S`, written out longhand. This module proves the
bridge of **Stacks 04XB** for it — a 1-morphism between categories representable by algebraic
spaces is relatively étale exactly when the induced morphism of representing presheaves is an
étale morphism of algebraic spaces — and deduces that the comparison 1-morphism between two
2-fibre products of one cospan is relatively étale.

## Main results

* `AlgebraicGeometry.Stack.isEtale_representingMap_of_isRelativelyEtale` and
  `AlgebraicGeometry.Stack.isRelativelyEtale_of_isEtale_representingMap`, combined in
  `AlgebraicGeometry.Stack.isRelativelyEtale_iff_isEtale_representingMap`: the **Stacks 04XB**
  bridge at étaleness.
* `AlgebraicGeometry.Stack.isIso_representingMap`: a 1-morphism with a 2-inverse induces an
  isomorphism of representing presheaves.
* `AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_isTwoFibreProduct`: the comparison
  1-morphism from one 2-fibre product of a cospan to another is relatively étale.

## Implementation notes

`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` does not apply at
étaleness: it takes `[P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]` as an instance
argument, and that instance is not available for `AlgebraicGeometry.Space.etaleMorphisms`. Both
directions are proved here from the arrow isomorphism
`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback`, which mentions no property, and, for
the forward direction, from `AlgebraicGeometry.Space.isEtale_of_forall_pullback_yoneda`:
étaleness needs only one surjective étale chart of the target, by Stacks 03FS. The remaining
ingredients ask only for `RespectsIso` and `IsStableUnderBaseChange`, which étaleness of
morphisms of algebraic spaces has, by
`AlgebraicGeometry.Space.etaleMorphisms_isStableUnderBaseChange` (Stacks 03FU).

## References

* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Bridge

variable {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)

include ha hF hG in
/-- **The forward half of the bridge of Stacks 04XB at étaleness.** If `a : 𝒜 ⟶ 𝒞` is relatively
étale, then the morphism `F ⟶ G` of representing presheaves it induces is an étale morphism of
algebraic spaces over `S`. -/
theorem isEtale_representingMap_of_isRelativelyEtale
    (h : IsRelativelyEtale B S hS a) :
    Space.IsEtale B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) := by
  obtain ⟨-, hrel⟩ := h
  refine Space.isEtale_of_forall_pullback_yoneda B S hS hF hG _ (fun U v => ?_)
  set y := CatFiberedInGroupoids.homFunctor (schemePointMap B S hS U G eG v)
  have hy := CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS U G eG v)
  obtain ⟨T, hT, ⟨eT⟩⟩ := ha U y hy
  have h3 := ((Space.etaleMorphisms B S hS).arrow_mk_iso_iff
    (arrowIsoRelocalizeFibrePullback B S hS U a y hy F G eF eG hF hG T eT hT)).mpr
    ((prop_algebraicSpaceMap_iff B S hS (Space.etaleMorphisms B S hS) U T hT).mp
      (hrel U y hy T hT ⟨eT⟩))
  have hv : representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
      (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy) = v :=
    representingMap_schemePointMap B S hS U G eG v
  rwa [hv] at h3

include ha hF hG in
/-- **The converse half of the bridge of Stacks 04XB at étaleness.** If the morphism `F ⟶ G` of
representing presheaves induced by `a : 𝒜 ⟶ 𝒞` is étale, then `a` is relatively étale. -/
theorem isRelativelyEtale_of_isEtale_representingMap
    (h : Space.IsEtale B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a)) :
    IsRelativelyEtale B S hS a := by
  refine ⟨ha, fun U y hy T hT he => ?_⟩
  obtain ⟨eT⟩ := he
  refine (prop_algebraicSpaceMap_iff B S hS (Space.etaleMorphisms B S hS) U T hT).2 ?_
  refine ((Space.etaleMorphisms B S hS).arrow_mk_iso_iff
    (arrowIsoRelocalizeFibrePullback B S hS U a y hy F G eF eG hF hG T eT hT)).mp ?_
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk (representingMap B S hS (schemeSlice B S hS U) 𝒞 (yoneda.obj U) G
          (schemeSliceEquivalenceOver B S hS U) eG (schemeSliceMap B S hS U y hy)) :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
      (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)).flip h

include ha hF hG in
/-- **The bridge of Stacks 04XB at étaleness.** A 1-morphism `a : 𝒜 ⟶ 𝒞` of categories fibred in
groupoids over the big fppf site of `S` which is representable by algebraic spaces, between two
categories themselves representable by algebraic spaces `F` and `G`, is étale in the sense of
Stacks 04XB exactly when the induced morphism `F ⟶ G` of representing presheaves is an étale
morphism of algebraic spaces over `S`.

This is the étale counterpart of
`AlgebraicGeometry.Stack.isRelativelySmooth_iff_isSmooth_representingMap`. -/
theorem isRelativelyEtale_iff_isEtale_representingMap :
    IsRelativelyEtale B S hS a ↔
      Space.IsEtale B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) :=
  ⟨isEtale_representingMap_of_isRelativelyEtale B S hS a ha F G hF hG eF eG,
    isRelativelyEtale_of_isEtale_representingMap B S hS a ha F G hF hG eF eG⟩

end Bridge

/-- **A 1-morphism with a 2-inverse induces an isomorphism of representing presheaves.** If
`k : 𝒜 ⟶ ℬ` and `l : ℬ ⟶ 𝒜` are 1-morphisms whose two composites are 2-isomorphic to the
identities, then the morphism `F ⟶ G` of representing presheaves induced by `k` is an
isomorphism, with inverse the one induced by `l`. -/
theorem isIso_representingMap
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (k : 𝒜 ⟶ ℬ) (l : ℬ ⟶ 𝒜) (h₁ : k ≫ l ≅ 𝟙 𝒜) (h₂ : l ≫ k ≅ 𝟙 ℬ)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    IsIso (representingMap B S hS 𝒜 ℬ F G eF eG k) := by
  refine ⟨representingMap B S hS ℬ 𝒜 G F eG eF l, ?_, ?_⟩
  · rw [← representingMap_comp B S hS F G F eF eG eF k l,
      representingMap_congr_twoIso B S hS F F eF eF h₁, representingMap_id]
  · rw [← representingMap_comp B S hS G F G eG eF eG l k,
      representingMap_congr_twoIso B S hS G G eG eG h₂, representingMap_id]

/-- **The comparison 1-morphism between two 2-fibre products of one cospan is relatively étale.**
Let `Pq` and `Qq` be 2-fibre products of the same cospan of categories fibred in groupoids over
the big fppf site of `S`, both representable by algebraic spaces, and let `k` be any morphism of
2-commutative squares from `Pq` to `Qq`. Then `k` is étale in the sense of Stacks 04XB. -/
theorem isRelativelyEtale_preHom_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {Pq Qq : Bicategory.TwoCommSq f g}
    (hPq : Bicategory.IsTwoFibreProduct Pq) (hQq : Bicategory.IsTwoFibreProduct Qq)
    (k : Bicategory.TwoCommSq.PreHom Pq Qq)
    (hPrep : IsRepresentableByAlgebraicSpace B S hS Pq.pt)
    (hQrep : IsRepresentableByAlgebraicSpace B S hS Qq.pt) :
    IsRelativelyEtale B S hS k.hom := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hPrep
  obtain ⟨W, hW, ⟨eW⟩⟩ := hQrep
  have hrep : IsRepresentableByAlgebraicSpaces B S hS k.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS k.hom
      ⟨A, hA, ⟨eA⟩⟩ ⟨W, hW, ⟨eW⟩⟩
  -- the 2-inverse supplied by terminality of the two 2-fibre products
  obtain ⟨e₁, -, -⟩ := Quotient.exact (hPq.hom_ext
    (Quotient.mk _ (k.comp (Quotient.out (hPq.from Qq)))) (𝟙 Pq))
  obtain ⟨e₂, -, -⟩ := Quotient.exact (hQq.hom_ext
    (Quotient.mk _ ((Quotient.out (hPq.from Qq)).comp k)) (𝟙 Qq))
  have hiso := isIso_representingMap B S hS k.hom (Quotient.out (hPq.from Qq)).hom
    e₁ e₂ A W eA eW
  exact isRelativelyEtale_of_isEtale_representingMap B S hS k.hom hrep A W hA hW eA eW
    (Space.isEtale_of_isIso B S hS _)

end AlgebraicGeometry.Stack

end

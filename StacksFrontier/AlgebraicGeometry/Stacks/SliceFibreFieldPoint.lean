module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingLiftedFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuasiFiniteChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SliceChartUnramifiedSpacePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ZeroLocusChartBaseChange

/-!
# The fibre of the Stacks 06MD slice over the field-valued point

Let `𝒳` be an algebraic stack, let `V` be an open subspace of an algebraic space `U` carrying
`r` global functions `c₁, …, c_r`, let `fV : V ⟶ 𝒳` be a 1-morphism and let
`g : Spec k ⟶ 𝒳` be a field-valued point. The **Stacks 06MD** slice of `V` is the zero locus
`Z = V(c₁, …, c_r) ∩ V`, and `fZ : Z ⟶ 𝒳` is its inclusion followed by `fV`.

This file identifies the fibre `Z ×_𝒳 Spec k` inside the fibre `F = V ×_𝒳 Spec k`: it is the
zero locus in `F` of the pullbacks of `c₁, …, c_r` along the projection `F ⟶ V`. This is step 1
of the chart construction of **Stacks 06N3**, at `U := V`, and it is what lets the fibre
hypotheses of **Stacks 06N2** — which are conditions on an open subspace of `F` — be read as
conditions on the slice itself.

## Main results

* `AlgebraicGeometry.Stack.exists_isIso_representingMap_twoFibreProductSquare_swap`: the
  canonical 2-fibre products of a cospan and of its reverse have isomorphic representing
  presheaves, compatibly with both projections.
* `AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_fibreOverFieldPoint_zeroLocusOnOpen`:
  a representing algebraic space of `Z ×_𝒳 Spec k` is the vanishing subfunctor of the
  pulled-back functions inside a representing algebraic space of `V ×_𝒳 Spec k`, compatibly
  with the projection to `V` and with the structure morphism to `Spec k`.

## Implementation notes

The cospan of the fibre of the slice is oriented `(fZ, g)` while the 2-fibre product square
whose inner square is cartesian is oriented `(g, fV)`, so the orientation has to be exchanged
once on representing presheaves; that is what the first result is for. The statement of the
second result is at an arbitrary subfunctor `W` of the fibre equal to the vanishing subfunctor,
so a consumer which has another name for the zero locus in the fibre receives the isomorphism
onto that name.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Swap

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {𝒜 ℬ : AlgebraicStacks.{u, w} B S hS}
  (p : 𝒜 ⟶ 𝒳) (q : ℬ ⟶ 𝒳)
  (X Y A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eX : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS p q).pt.val.val.p
    (presheafOfCategories (X ⋙ typeToCat)).p)
  (eY : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS q p).pt.val.val.p
    (presheafOfCategories (Y ⋙ typeToCat)).p)
  (eA : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
    (presheafOfCategories (A ⋙ typeToCat)).p)
  (eC : StacksRepresentableCFG.EquivalenceOver ℬ.val.val.p
    (presheafOfCategories (C ⋙ typeToCat)).p)

/-- **Exchanging the legs of a cospan does not change the representing presheaf of its 2-fibre
product.** Let `p : 𝒜 ⟶ 𝒳` and `q : ℬ ⟶ 𝒳` be 1-morphisms of algebraic stacks, let `X` represent
the apex of the canonical 2-fibre product square of `(p, q)` and let `Y` represent the apex of
the canonical square of `(q, p)`. Then the morphism `X ⟶ Y` which **Stacks 04SW** reads off the
mediating 1-morphism is invertible, and it carries each projection of `Y` to the projection of
`X` onto the same corner — the projection onto `ℬ` to the *second* projection of `(p, q)` and the
projection onto `𝒜` to its *first*.

Exchanging the legs of a 2-commutative square produces a 2-fibre product of the reversed cospan
(`CategoryTheory.Bicategory.isTwoFibreProduct_swap`), so both squares are 2-fibre products of the
cospan `(q, p)` and
`AlgebraicGeometry.Stack.exists_isIso_representingMap_of_isTwoFibreProduct` compares them. -/
theorem exists_isIso_representingMap_twoFibreProductSquare_swap :
    ∃ m : X ⟶ Y, IsIso m ∧
      m ≫ representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS q p).pt.val
          ℬ.val Y C eY eC (twoFibreProductSquareAlgebraicStacks B S hS q p).fst.hom =
        representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS p q).pt.val
          ℬ.val X C eX eC (twoFibreProductSquareAlgebraicStacks B S hS p q).snd.hom ∧
      m ≫ representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS q p).pt.val
          𝒜.val Y A eY eA (twoFibreProductSquareAlgebraicStacks B S hS q p).snd.hom =
        representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS p q).pt.val
          𝒜.val X A eX eA (twoFibreProductSquareAlgebraicStacks B S hS p q).fst.hom :=
  exists_isIso_representingMap_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        p.hom q.hom))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      q.hom p.hom)
    X Y C A eX eY eC eA

end Swap

section Fibre

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  {r : ℕ}
  (c : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)
  (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V)
  (fV : algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1 ⟶ 𝒳)
  (Z : Subfunctor V.toFunctor) (hZsp : IsAlgebraicSpace B S hS Z.toFunctor)
  (hZ : Z = zeroLocusOnOpen B S hS U hU c V)
  (fZ : algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZsp ⟶ 𝒳)
  (hfZ : fZ = algebraicSpaceStackMap.{u, w} B S hS hZsp hV.1 Z.ι ≫ fV)
  (FV : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFV : IsAlgebraicSpace B S hS FV)
  (eFV : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g).val.val.p
    (presheafOfCategories (FV ⋙ typeToCat)).p)
  (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 Z.toFunctor hZsp k hk toBase fZ g).val.val.p
    (presheafOfCategories (Q ⋙ typeToCat)).p)

variable (W : Subfunctor FV)
  (hW : W = Space.vanishingSubfunctor B S hS ⟨FV, hFV⟩
    (fun i => Space.globalFunctionsMap B S hS
      (ObjectProperty.homMk
          (fibreSpaceProjection B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g FV eFV) :
        (⟨FV, hFV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V.toFunctor, hV.1⟩)
      (Space.globalFunctionsMap B S hS
        (ObjectProperty.homMk V.ι :
          (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩) (c i))))

include hZ hfZ hW in
/-- **The fibre of the Stacks 06MD slice over the field point is the zero locus of the
pulled-back functions in the fibre.** Let `Z = V(c₁, …, c_r) ∩ V` be the slice of the open
subspace `V ⊆ U` cut out by `r` global functions on `U`, let `FV` represent the fibre
`V ×_𝒳 Spec k` and let `Q` represent the fibre `Z ×_𝒳 Spec k`. Then `Q` is isomorphic to the
subfunctor `W ⊆ FV` on which the pullbacks of `c₁, …, c_r` to `FV` vanish, and the isomorphism
is compatible both with the projection to `V` and with the structure morphism to `Spec k`.

The slice is the vanishing subfunctor of the restrictions of the `cᵢ` to `V` on the nose
(`AlgebraicGeometry.Stack.vanishingSubfunctor_globalFunctionsMap_ι_eq_zeroLocusOnOpen`), and
forming a vanishing subfunctor commutes with pullback
(`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage`), so `W` is the
inverse image of `Z` along the projection `FV ⟶ V`. That inverse image is a fibre product of the
cospan `(FV ⟶ V, Z ⟶ V)` (**Stacks 083Q**), and so is `Q`: the inner square of
`AlgebraicGeometry.Stack.restrictionInnerSquare` is cartesian on representing presheaves
(`AlgebraicGeometry.Stack.isPullback_representingMap_restrictionInnerSquare`, **Stacks 02XD**),
and its two legs are carried to the projection of `Q` and to the projection of `FV` by the leg
exchange of
`AlgebraicGeometry.Stack.exists_isIso_representingMap_twoFibreProductSquare_swap` and by
`AlgebraicGeometry.Stack.exists_isIso_representingMap_of_isTwoFibreProduct`. No closedness of
the slice is used.

The compatibility with the structure morphism is the remaining projection of the same comparison,
read through `AlgebraicGeometry.Stack.representingMap_restrictionSquare_fst`, which splits the
projection of the restricted base change onto `Spec k` as the inner projection followed by the
projection of `V ×_𝒳 Spec k`. -/
theorem exists_iso_vanishingSubfunctor_fibreOverFieldPoint_zeroLocusOnOpen :
    ∃ e : Q ≅ W.toFunctor,
      e.hom ≫ W.ι ≫
          fibreSpaceProjection B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g FV eFV =
        fibreSpaceProjection B S hS 𝒳 Z.toFunctor hZsp k hk toBase fZ g Q eQ ≫ Z.ι ∧
      e.hom ≫ W.ι ≫
          fibreSpaceStructureMorphism B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g FV eFV =
        fibreSpaceStructureMorphism B S hS 𝒳 Z.toFunctor hZsp k hk toBase fZ g Q eQ := by
  classical
  subst hfZ
  have hZv : Z = Space.vanishingSubfunctor B S hS ⟨V.toFunctor, hV.1⟩
      (fun i => Space.globalFunctionsMap B S hS
        (ObjectProperty.homMk V.ι :
          (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩) (c i)) :=
    hZ.trans (vanishingSubfunctor_globalFunctionsMap_ι_eq_zeroLocusOnOpen B S hS U hU c V hV).symm
  have hW' : W = Z.preimage
      (fibreSpaceProjection B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g FV eFV) := by
    rw [hW, hZv]
    exact Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage B S hS _ _
  subst hW'
  obtain ⟨P, hP, ⟨eP⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g fV).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
      (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)).val
      (algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1).val g.hom.hom fV.hom.hom
      (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 V.toFunctor hV.1
        fV)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)
  obtain ⟨Q', hQ', ⟨eQ'⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (restrictionSquare.{u, w} B S hS 𝒳 V.toFunctor Z.toFunctor hV.1 hZsp Z.ι fV
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1).val
      (twoFibreProductSquareAlgebraicStacks B S hS g fV).pt.val
      (algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZsp).val
      (twoFibreProductSquareAlgebraicStacks B S hS g fV).snd.hom.hom
      (algebraicSpaceStackMap.{u, w} B S hS hZsp hV.1 Z.ι).hom.hom
      (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS
        (algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1) Z.toFunctor hZsp
        (algebraicSpaceStackMap.{u, w} B S hS hZsp hV.1 Z.ι))
      ⟨P, hP, ⟨eP⟩⟩
  have hsq := isPullback_representingMap_restrictionInnerSquare.{u, w} B S hS 𝒳 V.toFunctor hV.1
    Z hZsp fV (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g P Q' eP eQ'
  obtain ⟨mP, hmP, hmP1, hmP2⟩ := exists_isIso_representingMap_twoFibreProductSquare_swap
    B S hS 𝒳 fV g FV P V.toFunctor (yoneda.obj (fieldPointObject B S hS k hk toBase))
    eFV eP (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
  obtain ⟨n, hn, hn1, hn2⟩ := exists_isIso_representingMap_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (algebraicSpaceStackMap.{u, w} B S hS hZsp hV.1 Z.ι ≫ fV).hom g.hom))
    (Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS g
        (algebraicSpaceStackMap.{u, w} B S hS hZsp hV.1 Z.ι ≫ fV))
      (isTwoFibreProduct_restrictionSquare.{u, w} B S hS 𝒳 V.toFunctor Z.toFunctor hV.1 hZsp Z.ι
        fV (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
        (algebraicSpaceStackMap.{u, w} B S hS hZsp hV.1 Z.ι ≫ fV).hom))
    Q Q' (yoneda.obj (fieldPointObject B S hS k hk toBase)) Z.toFunctor eQ eQ'
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have := hmP
  have := hn
  have hmP1' : mP ≫ representingMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS g fV).pt.val
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)).val P
        (yoneda.obj (fieldPointObject B S hS k hk toBase)) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (twoFibreProductSquareAlgebraicStacks B S hS g fV).fst.hom =
      fibreSpaceStructureMorphism B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g FV eFV := hmP1
  have hfinal : IsPullback
      (n ≫ representingMap B S hS
          (restrictionSquare.{u, w} B S hS 𝒳 V.toFunctor Z.toFunctor hV.1 hZsp Z.ι fV
            (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS g fV).pt.val Q' P eQ' eP
          (restrictionInnerSquare.{u, w} B S hS 𝒳 V.toFunctor Z.toFunctor hV.1 hZsp Z.ι fV
            (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g).fst.hom ≫
        inv mP)
      (fibreSpaceProjection B S hS 𝒳 Z.toFunctor hZsp k hk toBase
        (algebraicSpaceStackMap.{u, w} B S hS hZsp hV.1 Z.ι ≫ fV) g Q eQ)
      (fibreSpaceProjection B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g FV eFV) Z.ι :=
    hsq.of_iso' (asIso n) (asIso mP) (Iso.refl _) (Iso.refl _) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id]; exact hn2)
      (by rw [Iso.refl_hom, Category.comp_id]; exact hmP2) (by simp)
  refine ⟨IsPullback.isoIsPullback _ _ hfinal
    (Subfunctor.isPullback_preimage _ Z).flip, ?_, ?_⟩
  · rw [(Subfunctor.isPullback_preimage
      (fibreSpaceProjection B S hS 𝒳 V.toFunctor hV.1 k hk toBase fV g FV eFV) Z).flip.w,
      ← Category.assoc, IsPullback.isoIsPullback_hom_snd]
  · rw [← Category.assoc, IsPullback.isoIsPullback_hom_fst, ← hmP1']
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← representingMap_restrictionSquare_fst.{u, w} B S hS 𝒳 V.toFunctor Z.toFunctor hV.1 hZsp
      Z.ι fV (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g P Q' eP
      (yoneda.obj (fieldPointObject B S hS k hk toBase))
      (PresheafOfCategories.sliceElementsEquivalenceOver _) eQ']
    exact hn1

end Fibre

end AlgebraicGeometry.Stack

end

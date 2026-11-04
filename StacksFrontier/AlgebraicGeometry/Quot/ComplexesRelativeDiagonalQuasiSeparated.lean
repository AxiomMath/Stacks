module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesIsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDiagonalReduction
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentableRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFaithfulBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize

/-!
# The diagonal of `Complexes_{X/B} ⟶ B` is quasi-compact and quasi-separated (towards 0DPX)

Let `f : X ⟶ B` be a proper, flat, finitely presented morphism of algebraic spaces over a scheme
`S` (Situation 0DLE). The quasi-separatedness half of Stacks 0DPX says that the diagonal of
`Complexes_{X/B}` over `B` is quasi-compact and quasi-separated. The source deduces it from
Stacks 0DPW: for two objects `(T, E)`, `(T, E')` over one test scheme `T ⟶ B`, the isomorphism
sheaf `Isom(E, E')` is an algebraic space of finite presentation over `T`.

This file carries out that deduction for the projection `Complexes_{X/B} ⟶ 𝒮_B` of Remark 0DLI,
whose relative diagonal is the diagonal over `B`. The finite presentation of `Isom(E, E')` is the
hypothesis `hIsom`, read on the relative derived Isom functor of `X_T ⟶ T`
(`AlgebraicGeometry.Space.relativeDerivedIsomFunctor`); the rest is proved:

1. two objects of `Complexes_{X/B}` over `U` whose images in `𝒮_B` are identified over `𝟙 U` lie
   over the same test scheme, since `𝒮_B` is fibred in sets, so they are `(T, E)` and `(T, E')`;
2. their isomorphism sheaf is the relative derived Isom functor
   (`ComplexesSituation.complexesIsomPresheafIsoRelativeDerivedIsomFunctor`);
3. an algebraic space `H ⟶ T` of finite presentation, read on the big fppf site of `T`
   (Stacks 04SG), is an algebraic space over `T` whose structure morphism is quasi-compact and
   quasi-separated
   (`AlgebraicGeometry.Space.exists_isAlgebraicSpace_qcqs_of_isFinitePresentation`);
4. `AlgebraicGeometry.Stack.exists_isRepresentable_and_prop_relativeDiagonal_of_faithful`
   concludes.

## Main definitions

* `AlgebraicGeometry.Space.quasiCompactQuasiSeparated`: the property of a morphism of algebraic
  spaces of being quasi-compact and quasi-separated.

## Main results

* `AlgebraicGeometry.Space.respectsIso_quasiCompactQuasiSeparated`: that property respects
  isomorphisms.
* `AlgebraicGeometry.Space.exists_isAlgebraicSpace_qcqs_of_isFinitePresentation`: step 3.
* `AlgebraicGeometry.Space.ComplexesSituation.exists_isomPresheaf_qcqs_of_isom`: steps 1 and 2.
* `ComplexesSituation.exists_isRepresentable_and_qcqs_relativeDiagonal_complexesToBase`:
  the relative diagonal of `Complexes_{X/B} ⟶ 𝒮_B` is representable by algebraic spaces,
  quasi-compact and quasi-separated, granted `hIsom`.

## References

* [Stacks Project, Tag 0DPX](https://stacks.math.columbia.edu/tag/0DPX)
* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The property of a morphism of algebraic spaces over `S` of being quasi-compact and
quasi-separated. -/
abbrev quasiCompactQuasiSeparated : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ g => IsQuasiCompact B S hS g.hom ∧ IsQuasiSeparated B S hS g.hom

variable (B S hS) in
/-- Being quasi-compact and quasi-separated respects isomorphisms of algebraic spaces. -/
instance respectsIso_quasiCompactQuasiSeparated :
    (quasiCompactQuasiSeparated B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e g hg => ⟨isQuasiCompact_of_arrowIso B S hS g.hom (e.hom ≫ g).hom e.inv.hom (𝟙 _)
        (by simp) hg.1,
      isQuasiSeparated_of_arrowIso B S hS g.hom (e.hom ≫ g).hom e.inv.hom (𝟙 _)
        (by simp) hg.2⟩)
    (fun e g hg => ⟨isQuasiCompact_of_arrowIso B S hS g.hom (g ≫ e.hom).hom (𝟙 _) e.hom.hom
        (by simp) hg.1,
      isQuasiSeparated_of_arrowIso B S hS g.hom (g ≫ e.hom).hom (𝟙 _) e.hom.hom
        (by simp) hg.2⟩)

/-- **An algebraic space of finite presentation over a scheme `U`, read on the big fppf site of
`U`, is quasi-compact and quasi-separated over `U`.** Let `R` be a functor on the test schemes over
`U` which is an algebraic space of finite presentation over `U`, represented by `p : H ⟶ U`. Then
the algebraic space over `U` that `p` is by Stacks 04SG lifts `R`, read on the big fppf site of
`U`, and its structure morphism, read over `S`, is quasi-compact and quasi-separated: it is `p` up
to an isomorphism of the source. -/
theorem exists_isAlgebraicSpace_qcqs_of_isFinitePresentation (U : BigFppfOver B S hS)
    {R : (SchemesOver ((schemeSpaceFunctor B S hS).obj U))ᵒᵖ ⥤ Type (u + 1)}
    (hR : IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj U) R) :
    ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
      Nonempty (G ⋙ uliftFunctor.{u + 1, u} ≅
        ((Over.iteratedSliceBackward U).op ⋙ (overSchemeTest U).op ⋙ R) ⋙
          uliftFunctor.{u, u + 1}) ∧
      quasiCompactQuasiSeparated B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)) := by
  obtain ⟨H, p, hp, ⟨e⟩⟩ := hR
  let Y := spaceOverSmallerBase B U.left.1 S U.left.2 hS U.hom H p.hom
  refine ⟨Y.1, Y.2, ⟨?_⟩, ?_⟩
  · let e₁ : Y.1 ≅ (Over.iteratedSliceBackward U).op ⋙
        OverShriek.fiber (𝟙 (yoneda.obj U)) p.hom := Iso.refl _
    exact Functor.isoWhiskerRight e₁ _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (ComplexesSituation.overToSchemesOverPointsIso p).symm _ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e) ≪≫
      ComplexesSituation.uliftIsoSelf _
  · refine (Stack.prop_algebraicSpaceMap_iff B S hS _ U Y.1 Y.2).2 ?_
    have hw := relocalizeSpaceOverSmallerBaseIso_hom_comp B U.left.1 S U.left.2 hS U.hom H p.hom
    have hqc := (isQuasiCompact_isIso_comp_iff B S hS
      (relocalizeSpaceOverSmallerBaseIso B U.left.1 S U.left.2 hS U.hom H p.hom).hom p.hom).2 hp.2.1
    have hqs := (isQuasiSeparated_isIso_comp_iff B S hS
      (relocalizeSpaceOverSmallerBaseIso B U.left.1 S U.left.2 hS U.hom H p.hom).hom p.hom).2 hp.2.2
    show IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda U.hom Y.1) ∧
      IsQuasiSeparated B S hS (OverShriek.relocalizeToYoneda U.hom Y.1)
    rw [← hw]
    exact ⟨hqc, hqs⟩

namespace ComplexesSituation

attribute [local instance] complexesCategory

/-- **The isomorphism sheaves of `Complexes_{X/B}` over one point of `B` are quasi-compact and
quasi-separated**, granted that `Isom(E, E')` is an algebraic space of finite presentation over
`T` for two objects `(T, E)`, `(T, E')` over one test scheme. Two objects `x`, `x'` of the fibre
over `U` whose images in `𝒮_B` are identified over `𝟙 U` lie over the same test scheme, `𝒮_B`
being fibred in sets; their isomorphism sheaf is the relative derived Isom functor of `X_U ⟶ U`. -/
theorem exists_isomPresheaf_qcqs_of_isom (D : ComplexesSituation B S hS)
    (hIsom : ∀ (A : ComplexesObject D) (E' : derivedModules B S hS (D.space A.T)),
      D.IsRelativelyPerfect A.T E' → D.HasNoNegativeFibreExt A.T E' →
      IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
        (relativeDerivedIsomFunctor (D.projection A.T) A.E E')) :
    letI : (complexesCFG D).val.p.IsFibered := (complexesCFG D).isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x x' : (complexesCFG D).val.p.Fiber U),
      (∃ φ : (complexesToBase D).obj x.1 ⟶ (complexesToBase D).obj x'.1,
        (baseCFG D.Y).val.p.IsHomLift (𝟙 U) φ) →
      ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (G ⋙ uliftFunctor.{u + 1, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ (complexesCFG D).val.p.isomPresheaf x x') ⋙
            uliftFunctor.{u, u + 1}) ∧
        quasiCompactQuasiSeparated B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)) := by
  let : (complexesCFG D).val.p.IsFibered := (complexesCFG D).isFiberedInGroupoids.isFibered
  rintro U ⟨⟨⟨Tl, Tr, Th⟩, E, hE₁, hE₂⟩, hx⟩ ⟨⟨⟨Tl', Tr', Th'⟩, E', hE₁', hE₂'⟩, hx'⟩ ⟨φ, hφ⟩
  change Tl = U at hx
  change Tl' = U at hx'
  subst hx hx'
  have hl : φ.down.left = 𝟙 _ :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (baseCFG D.Y).val.p _ _ _ φ hφ).symm
  have hw := CostructuredArrow.w φ.down
  obtain ⟨⟨⟩⟩ := Tr
  obtain ⟨⟨⟩⟩ := Tr'
  have hTh : Th = Th' := by
    have hl' : φ.down.left = 𝟙 Tl' := hl
    have hw' : (schemeSpaceFunctor B S hS).map φ.down.left ≫ Th' = Th := hw
    have h1 : (schemeSpaceFunctor B S hS).map φ.down.left = 𝟙 _ :=
      (congrArg (fun k => (schemeSpaceFunctor B S hS).map k) hl').trans
        ((schemeSpaceFunctor B S hS).map_id Tl')
    exact (hw'.symm.trans (congrArg (· ≫ Th') h1)).trans (Category.id_comp Th')
  subst hTh
  let A : ComplexesObject D := ⟨⟨Tl', ⟨⟨⟩⟩, Th⟩, E, hE₁, hE₂⟩
  obtain ⟨G, hG, ⟨e⟩, hP⟩ :=
    exists_isAlgebraicSpace_qcqs_of_isFinitePresentation Tl' (hIsom A E' hE₁' hE₂')
  let i := complexesIsomPresheafIsoRelativeDerivedIsomFunctor A E' hE₁' hE₂'
  let j := e ≪≫ Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Over.iteratedSliceBackward Tl').op i.symm) uliftFunctor.{u, u + 1}
  exact ⟨G, hG, ⟨j⟩, hP⟩

/-- **The diagonal of `Complexes_{X/B}` over `B` is quasi-compact and quasi-separated**, granted
that `Isom(E, E')` is an algebraic space of finite presentation over `T` for any two objects
`(T, E)`, `(T, E')` of `Complexes_{X/B}` over one test scheme `T ⟶ B` (Stacks 0DPW, the input the
source's proof of Stacks 0DPX takes). The relative diagonal of the projection
`Complexes_{X/B} ⟶ 𝒮_B` of Remark 0DLI is representable by algebraic spaces (Stacks 02ZW), and
every algebraic space representing one of its base changes along a scheme-valued point over `U`
is quasi-compact and quasi-separated over `U` (Properties of Stacks, Section 04XB). -/
theorem exists_isRepresentable_and_qcqs_relativeDiagonal_complexesToBase
    (D : ComplexesSituation B S hS)
    (hIsom : ∀ (A : ComplexesObject D) (E' : derivedModules B S hS (D.space A.T)),
      D.IsRelativelyPerfect A.T E' → D.HasNoNegativeFibreExt A.T E' →
      IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
        (relativeDerivedIsomFunctor (D.projection A.T) A.E E')) :
    ∃ _hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonalBasedFunctor B S hS (complexesCFG D) (baseCFG D.Y)
          (complexesToBase D)),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (Stack.twoFibreProduct B S hS (baseCFG D.Y) (complexesCFG D) (complexesCFG D)
            (complexesToBase D) (complexesToBase D)).val.obj)
        (_hy : y ⋙ (Stack.twoFibreProduct B S hS (baseCFG D.Y) (complexesCFG D) (complexesCFG D)
            (complexesToBase D) (complexesToBase D)).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) (complexesCFG D).val.p
            (Stack.twoFibreProduct B S hS (baseCFG D.Y) (complexesCFG D) (complexesCFG D)
              (complexesToBase D) (complexesToBase D)).val.p y
            (Stack.relativeDiagonalBasedFunctor B S hS (complexesCFG D) (baseCFG D.Y)
              (complexesToBase D)).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        IsQuasiCompact B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ∧
          IsQuasiSeparated B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  have : (baseCFG D.Y).val.p.Faithful := baseBasedCategory_faithful D.Y
  exact Stack.exists_isRepresentable_and_prop_relativeDiagonal_of_faithful B S hS (complexesCFG D)
    (baseCFG D.Y) (complexesToBase D) (quasiCompactQuasiSeparated B S hS)
    (exists_isomPresheaf_qcqs_of_isom D hIsom)

end ComplexesSituation

end AlgebraicGeometry.Space

end

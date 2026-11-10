module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivityBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFppfDescent
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# Separatedness of a base change of an algebraic stack, read off one morphism of spaces

Let `f₀ : 𝒳₀ ⟶ Y₀` be a 1-morphism from an algebraic stack to an algebraic space over `S`, let
`Δ₀ : 𝒳₀ ⟶ 𝒳₀ ×_{Y₀} 𝒳₀` be its relative diagonal, and let `g₀ : 𝒱₀ ⟶ 𝒳₀ ×_{Y₀} 𝒳₀` be a
locally essentially surjective 1-morphism from a stack represented by an algebraic space `V₀`.
The base change of `Δ₀` along `g₀` is represented by an algebraic space `T₀`, and the first
projection induces a morphism of algebraic spaces `m₀ : T₀ ⟶ V₀`; write `b₀ : V₀ ⟶ Y₀` for the
morphism induced by `𝒱₀ ⟶ 𝒳₀ ×_{Y₀} 𝒳₀ ⟶ 𝒳₀ ⟶ Y₀`.

For every morphism of algebraic spaces `q : Y' ⟶ Y₀` the base change `f' : 𝒳₀ ×_{Y₀} Y' ⟶ Y'`
is separated exactly when the base change `Y' ×_{Y₀} T₀ ⟶ Y' ×_{Y₀} V₀` of `m₀` along `q` is
proper. This is the step of the proof of Stacks 0CPZ which turns the separatedness of the stages
`Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` into properness of the stages of one morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.exists_iso_comp_representingMap_fst_of_isTwoFibreProduct`: two
  2-fibre products of one cospan with represented apexes induce isomorphic first projections of
  representing presheaves.
* `AlgebraicGeometry.Stack.isSeparated_baseChange_iff_isProper`: the criterion above.

## Implementation notes

The proof follows the source. By Stacks 04YR (`AlgebraicGeometry.Stack.diagonalBaseChangeSquare`)
the relative diagonal `Δ'` of `f'` is the base change of `Δ₀` along
`r × r : 𝒳' ×_{Y'} 𝒳' ⟶ 𝒳₀ ×_{Y₀} 𝒳₀`. The base change `ℰ` of `g₀` along `r × r` is locally
essentially surjective onto `𝒳' ×_{Y'} 𝒳'`, so properness of `Δ'` is properness of its base change
along `ℰ ⟶ 𝒳' ×_{Y'} 𝒳'` (Stacks 045C and 045D), a morphism between represented stacks, which is
the base change of `m₀` along `ℰ ⟶ 𝒱₀` by the pasting law. Finally `ℰ` itself is the 2-fibre
product of `𝒱₀ ⟶ Y₀` and `Y' ⟶ Y₀`, again by pasting (`r × r` is a base change of `r`, which is
a base change of `Y' ⟶ Y₀`), so it is represented by `Y' ×_{Y₀} V₀` (Stacks 04SD).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Properness of morphisms of algebraic spaces over `S` is invariant under isomorphism of
arrows: if `f ≫ b = a ≫ f'` with `a` and `b` isomorphisms, `f` is proper exactly when `f'` is. -/
theorem _root_.AlgebraicGeometry.Space.isProper_iff_of_comm_iso
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hF' : IsAlgebraicSpace B S hS F') (hG' : IsAlgebraicSpace B S hS G')
    (f : F ⟶ G) (f' : F' ⟶ G') (a : F ≅ F') (b : G ≅ G') (w : f ≫ b.hom = a.hom ≫ f') :
    Space.IsProper B S hS f ↔ Space.IsProper B S hS f' := by
  have : (Space.properProperty B S hS).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have : (Space.properProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have e : Arrow.mk (ObjectProperty.homMk f :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) ≅
      Arrow.mk (ObjectProperty.homMk f' :
        (⟨F', hF'⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G', hG'⟩ : AlgebraicSpaces B S hS)) :=
    Arrow.isoMk (ObjectProperty.isoMk _ a) (ObjectProperty.isoMk _ b)
      (ObjectProperty.hom_ext _ w.symm)
  exact (Space.properProperty B S hS).arrow_mk_iso_iff e

section Comparison

variable {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵}

/-- **Two 2-fibre products of one cospan induce isomorphic first projections.** If `P₁` and `P₂`
are 2-fibre products of the same cospan, with apexes represented by `T₁` and `T₂` and first
factor represented by `F`, the morphisms `T₁ ⟶ F` and `T₂ ⟶ F` induced by the first projections
differ by an isomorphism `T₁ ≅ T₂`: the comparison 1-morphisms supplied by terminality compose to
1-morphisms 2-isomorphic to identities, and Stacks 04SW is defined on 2-isomorphism classes. -/
theorem exists_iso_comp_representingMap_fst_of_isTwoFibreProduct
    {P₁ P₂ : Bicategory.TwoCommSq f g}
    (h₁ : Bicategory.IsTwoFibreProduct P₁) (h₂ : Bicategory.IsTwoFibreProduct P₂)
    (T₁ T₂ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (e₁ : StacksRepresentableCFG.EquivalenceOver P₁.pt.val.p
      (presheafOfCategories (T₁ ⋙ typeToCat)).p)
    (e₂ : StacksRepresentableCFG.EquivalenceOver P₂.pt.val.p
      (presheafOfCategories (T₂ ⋙ typeToCat)).p)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    ∃ i : T₁ ≅ T₂, i.hom ≫ representingMap B S hS P₂.pt 𝒳 T₂ F e₂ eF P₂.fst =
      representingMap B S hS P₁.pt 𝒳 T₁ F e₁ eF P₁.fst := by
  let A := Bicategory.twoFibreProductPreHom h₂ P₁
  let D := Bicategory.twoFibreProductPreHom h₁ P₂
  refine ⟨Iso.mk (representingMap B S hS P₁.pt P₂.pt T₁ T₂ e₁ e₂ A.hom)
    (representingMap B S hS P₂.pt P₁.pt T₂ T₁ e₂ e₁ D.hom) ?_ ?_, ?_⟩
  · obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel h₁ (A.comp D)
      (Bicategory.TwoCommSq.PreHom.id P₁)
    have key : representingMap B S hS P₁.pt P₁.pt T₁ T₁ e₁ e₁ (A.hom ≫ D.hom) =
        representingMap B S hS P₁.pt P₁.pt T₁ T₁ e₁ e₁ (𝟙 _) :=
      representingMap_congr_twoIso B S hS T₁ T₁ e₁ e₁ θ
    rw [← representingMap_comp B S hS T₁ T₂ T₁ e₁ e₂ e₁, key, representingMap_id]
  · obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel h₂ (D.comp A)
      (Bicategory.TwoCommSq.PreHom.id P₂)
    have key : representingMap B S hS P₂.pt P₂.pt T₂ T₂ e₂ e₂ (D.hom ≫ A.hom) =
        representingMap B S hS P₂.pt P₂.pt T₂ T₂ e₂ e₂ (𝟙 _) :=
      representingMap_congr_twoIso B S hS T₂ T₂ e₂ e₂ θ
    rw [← representingMap_comp B S hS T₂ T₁ T₂ e₂ e₁ e₂, key, representingMap_id]
  · change representingMap B S hS P₁.pt P₂.pt T₁ T₂ e₁ e₂ A.hom ≫ _ = _
    rw [← representingMap_comp B S hS T₁ T₂ F e₁ e₂ eF,
      ← representingMap_congr_twoIso B S hS T₁ F e₁ eF A.isoFst]

end Comparison

section BaseChange

variable {𝒳₀ : AlgebraicStacks.{u, w} B S hS} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {hY₀ : IsAlgebraicSpace B S hS Y₀} (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B S hS Y₀ hY₀)
  {𝒱₀ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (g₀ : 𝒱₀ ⟶ twoFibreProduct B S hS (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val
    𝒳₀.val 𝒳₀.val f₀.hom.hom f₀.hom.hom)
  (V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eV₀ : StacksRepresentableCFG.EquivalenceOver 𝒱₀.val.p
    (presheafOfCategories (V₀ ⋙ typeToCat)).p)
  (T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eT₀ : StacksRepresentableCFG.EquivalenceOver
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g₀
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳₀.val
        (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val f₀.hom)).pt.val.p
    (presheafOfCategories (T₀ ⋙ typeToCat)).p)

/-- The morphism of algebraic spaces `m₀ : T₀ ⟶ V₀` induced by the first projection of the base
change of the relative diagonal of `f₀` along `g₀`. -/
noncomputable abbrev diagonalCoverBaseChangeMap : T₀ ⟶ V₀ :=
  representingMap B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g₀
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳₀.val
        (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val f₀.hom)).pt 𝒱₀ T₀ V₀ eT₀ eV₀
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g₀
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳₀.val
        (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val f₀.hom)).fst

/-- The morphism of algebraic spaces `b₀ : V₀ ⟶ Y₀` induced by
`𝒱₀ ⟶ 𝒳₀ ×_{Y₀} 𝒳₀ ⟶ 𝒳₀ ⟶ Y₀`. -/
noncomputable abbrev diagonalCoverStructureMap : V₀ ⟶ Y₀ :=
  representingMap B S hS 𝒱₀ (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val V₀ Y₀ eV₀
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (g₀ ≫ diagonalProdFst B S hS f₀ ≫ f₀.hom)

/-- **Separatedness of a base change of `f₀`, read off one morphism of algebraic spaces.** With
`m₀ : T₀ ⟶ V₀` and `b₀ : V₀ ⟶ Y₀` as above and `g₀` locally essentially surjective, for every
morphism of algebraic spaces `q : Y' ⟶ Y₀` the base change `𝒳₀ ×_{Y₀} Y' ⟶ Y'` of `f₀` is
separated exactly when the base change `Y' ×_{Y₀} T₀ ⟶ Y' ×_{Y₀} V₀` of `m₀` is proper. The
latter is given as any morphism `φ` with the two components of the base change. -/
theorem isSeparated_baseChange_iff_isProper
    (hV₀ : IsAlgebraicSpace B S hS V₀) (hT₀ : IsAlgebraicSpace B S hS T₀)
    (hg₀ : ∀ (U : BigFppfOver B S hS)
      (t : (twoFibreProduct B S hS (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val
        𝒳₀.val 𝒳₀.val f₀.hom.hom f₀.hom.hom).val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒱₀.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor g₀).obj z ⟶ t.1,
            (twoFibreProduct B S hS (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val
              𝒳₀.val 𝒳₀.val f₀.hom.hom f₀.hom.hom).val.p.IsHomLift k φ)
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y') (q : Y' ⟶ Y₀)
    (φ : pullback q (diagonalCoverBaseChangeMap B S hS f₀ g₀ V₀ eV₀ T₀ eT₀ ≫
        diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀) ⟶
      pullback q (diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀))
    (hφ₁ : φ ≫ pullback.fst _ _ = pullback.fst _ _)
    (hφ₂ : φ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ diagonalCoverBaseChangeMap B S hS f₀ g₀ V₀ eV₀ T₀ eT₀) :
    AlgebraicStacks.IsSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f₀
          (algebraicSpaceStackMap.{u, w} B S hS hY' hY₀ q)).snd ↔
      Space.IsProper B S hS φ := by
  set p' := algebraicSpaceStackMap.{u, w} B S hS hY' hY₀ q
  have h𝒱₀ : IsRepresentableByAlgebraicSpace B S hS 𝒱₀ := ⟨V₀, hV₀, ⟨eV₀⟩⟩
  -- `Y' ⟶ Y₀` is representable by algebraic spaces
  have hp' : IsRepresentableByAlgebraicSpaces B S hS p'.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS Y' hY') p'.hom
  -- the square defining `𝒳' = 𝒳₀ ×_{Y₀} Y'`
  let K := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f₀.hom p'.hom
  have hK : Bicategory.IsTwoFibreProduct K :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f₀.hom p'.hom
  have hr : IsRepresentableByAlgebraicSpaces B S hS K.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ p'.hom f₀.hom K hK hp'
  -- `r × r` is a base change of `r`
  let Dc := diagonalCoverSquare B S hS f₀ p'
  have hDc : Bicategory.IsTwoFibreProduct Dc := isTwoFibreProduct_diagonalCoverSquare B S hS f₀ p'
  have hρ : IsRepresentableByAlgebraicSpaces B S hS Dc.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ K.fst
      (diagonalProdFst B S hS f₀) Dc hDc hr
  -- `𝒳' ×_{Y'} 𝒳'` is the base change of `𝒳₀ ×_{Y₀} 𝒳₀` along `Y' ⟶ Y₀`
  let Z := K.pasteFst Dc
  have hZ : Bicategory.IsTwoFibreProduct Z := Bicategory.isTwoFibreProduct_pasteFst K hK Dc hDc
  -- the base change `ℰ` of the cover `g₀` along `r × r`
  let C := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g₀ Dc.fst
  have hC : Bicategory.IsTwoFibreProduct C :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g₀ Dc.fst
  have hCfst : IsRepresentableByAlgebraicSpaces B S hS C.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ Dc.fst g₀ C hC hρ
  obtain ⟨E, hE, ⟨eE⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS C.pt 𝒱₀
    C.fst hCfst h𝒱₀
  -- `ℰ` is the 2-fibre product of `𝒱₀ ⟶ Y₀` and `Y' ⟶ Y₀`
  let O := Z.pasteFst C
  have hO : Bicategory.IsTwoFibreProduct O := Bicategory.isTwoFibreProduct_pasteFst Z hZ C hC
  let Kc := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (g₀ ≫ diagonalProdFst B S hS f₀ ≫ f₀.hom) p'.hom
  have hKc : Bicategory.IsTwoFibreProduct Kc :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  obtain ⟨Ec, -, ⟨eEc⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS Kc.pt 𝒱₀
    Kc.fst (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ p'.hom _ Kc
      hKc hp') h𝒱₀
  have hIII := isPullback_representingMap_of_isTwoFibreProduct B S hS hO V₀ Y' Y₀ E Ec eV₀
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) eE eEc
  rw [show representingMap B S hS _ _ Y' Y₀ (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) p'.hom = q from
    representingMap_associatedMap B S hS Y' Y₀ q] at hIII
  -- the relative diagonal `Δ'` of the base change is the base change of `Δ₀` along `r × r`
  let Dd := diagonalBaseChangeSquare B S hS f₀ p'
  have hDd : Bicategory.IsTwoFibreProduct Dd :=
    isTwoFibreProduct_diagonalBaseChangeSquare B S hS f₀ p'
  have hΔ' : IsRepresentableByAlgebraicSpaces B S hS Dd.fst.hom :=
    isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f₀ p').snd
  have hΔ₀ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳₀.val
        (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val f₀.hom).hom :=
    isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f₀
  -- the base change of `Δ'` along the cover `ℰ ⟶ 𝒳' ×_{Y'} 𝒳'`
  let Q' := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} C.snd Dd.fst
  have hQ' : Bicategory.IsTwoFibreProduct Q' :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hQ'fst : IsRepresentableByAlgebraicSpaces B S hS Q'.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ Dd.fst C.snd Q' hQ'
      hΔ'
  obtain ⟨T', hT', ⟨eT'⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS Q'.pt C.pt
    Q'.fst hQ'fst ⟨E, hE, ⟨eE⟩⟩
  -- pasted with the square of Stacks 04YR, it is a base change of `Δ₀` along `ℰ ⟶ 𝒱₀ ⟶ 𝒵₀`
  let N' := (Dd.pasteFst Q').reindexFst C.iso.symm
  have hN' : Bicategory.IsTwoFibreProduct N' :=
    Bicategory.isTwoFibreProduct_reindexFst C.iso.symm
      (Bicategory.isTwoFibreProduct_pasteFst Dd hDd Q' hQ')
  -- and so is the pasting of the base change of `Δ₀` along `g₀` with its base change along
  -- `ℰ ⟶ 𝒱₀`
  let Q₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g₀
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳₀.val
      (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val f₀.hom)
  have hQ₀ : Bicategory.IsTwoFibreProduct Q₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hQ₀fst : IsRepresentableByAlgebraicSpaces B S hS Q₀.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ _ g₀ Q₀ hQ₀ hΔ₀
  let R := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} C.fst Q₀.fst
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hRfst : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ Q₀.fst C.fst R hR
      hQ₀fst
  obtain ⟨TR, hTR, ⟨eTR⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS R.pt C.pt
    R.fst hRfst ⟨E, hE, ⟨eE⟩⟩
  have hM : Bicategory.IsTwoFibreProduct (Q₀.pasteFst R) :=
    Bicategory.isTwoFibreProduct_pasteFst Q₀ hQ₀ R hR
  obtain ⟨i, hi⟩ := exists_iso_comp_representingMap_fst_of_isTwoFibreProduct B S hS hN' hM
    T' TR E eT' eTR eE
  have : (twoFibreProductStructureFunctor B S hS C.pt Q₀.pt 𝒱₀ C.fst Q₀.fst).IsFibered :=
    R.pt.property.isFibered
  have hI := isPullback_representingMap_twoFibreProductSquare B S hS C.pt Q₀.pt 𝒱₀ E T₀ V₀
    eE eT₀ eV₀ C.fst Q₀.fst TR eTR
  -- properness of `Δ'` is properness of its base change along the cover `ℰ ⟶ 𝒳' ×_{Y'} 𝒳'`
  have hprBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have hprLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  have hsep : AlgebraicStacks.IsSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f₀ p').snd ↔
      HasRelativeProperty B S hS (fun _ _ k => Space.IsProper B S hS k.hom) Q'.fst hQ'fst :=
    ⟨fun h => hasRelativeProperty_baseChange.{u, u, u} B S hS _ _ _ _ Dd.fst C.snd Q' hQ' hΔ' h,
      fun h => hasRelativeProperty_of_baseChange.{u, u, u, u} B S hS _ _ _ _ Dd.fst C.snd Q' hQ'
        hΔ' (localEssSurj_twoFibreProductSquare_snd B S hS g₀ Dc.fst hg₀) h⟩
  refine hsep.trans ((hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (fun _ _ k => Space.IsProper B S hS k.hom) Q'.fst hQ'fst T' E hT' hE eT' eE).trans ?_)
  change Space.IsProper B S hS (representingMap B S hS Q'.pt C.pt T' E eT' eE Q'.fst) ↔ _
  -- the base change of `m₀` along `Y' ×_{Y₀} V₀ ⟶ V₀`
  have hA : IsPullback (pullback.snd q (diagonalCoverBaseChangeMap B S hS f₀ g₀ V₀ eV₀ T₀ eT₀ ≫
      diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀)) φ
      (diagonalCoverBaseChangeMap B S hS f₀ g₀ V₀ eV₀ T₀ eT₀)
      (pullback.snd q (diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀)) :=
    IsPullback.of_bot (by rw [hφ₁]; exact (IsPullback.of_hasPullback _ _).flip) hφ₂.symm
      (IsPullback.of_hasPullback _ _).flip
  -- `ℰ` is `Y' ×_{Y₀} V₀`
  let j := hIII.flip.isoIsPullback _ _ (IsPullback.of_hasPullback q
    (diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀))
  have hj : j.hom ≫ pullback.snd q (diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀) =
      representingMap B S hS C.pt 𝒱₀ E V₀ eE eV₀ C.fst :=
    hIII.flip.isoIsPullback_hom_snd _ _ _
  have hI' : IsPullback (representingMap B S hS R.pt C.pt TR E eTR eE R.fst ≫ j.hom)
      (representingMap B S hS R.pt Q₀.pt TR T₀ eTR eT₀ R.snd)
      (pullback.snd q (diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀))
      (diagonalCoverBaseChangeMap B S hS f₀ g₀ V₀ eV₀ T₀ eT₀) :=
    hI.of_iso (Iso.refl _) j (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp]; rfl)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
      (by simp only [Iso.refl_hom, Category.comp_id, hj])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  let k := hI'.isoIsPullback _ _ hA.flip
  have hk : k.hom ≫ φ = representingMap B S hS R.pt C.pt TR E eTR eE R.fst ≫ j.hom :=
    hI'.isoIsPullback_hom_fst _ _ hA.flip
  refine Space.isProper_iff_of_comm_iso B S hS hT' hE
    (isAlgebraicSpace_pullback B S hS _ _ hY' hT₀ hY₀)
    (isAlgebraicSpace_pullback B S hS _ _ hY' hV₀ hY₀) _ φ (i ≪≫ k) j ?_
  rw [Iso.trans_hom, Category.assoc, hk, ← Category.assoc]
  exact congrArg (· ≫ j.hom) hi.symm

end BaseChange

end AlgebraicGeometry.Stack

end

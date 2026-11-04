module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact

/-!
# Quasi-compactness of an algebraic stack and a change of base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site. Construction A of Stacks, Section 04WT views a
category over the big fppf site of `S` as one over the big fppf site of `S'`, by composing its
structure functor with `CategoryTheory.Over.map g`. This file proves that quasi-compactness of an
algebraic stack (**Stacks 04YB**) is unchanged by that view, in both directions.

## Main definitions

* `AlgebraicGeometry.Stack.changeBaseFieldValuedPoint` and
  `AlgebraicGeometry.Stack.unchangeBaseFieldValuedPoint`: a field-valued point of Stacks 04XE of a
  category over the big fppf site of `S` read over the big fppf site of `S'`, and back.
* `AlgebraicGeometry.Stack.changeBasePointsEquiv`: the resulting bijection on the point sets of
  Stacks 04XG.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_surjective_changeBaseFunctor_iff`: a 1-morphism is surjective
  on points exactly when Construction A of it is.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStack_iff`: an algebraic stack
  over `S` is quasi-compact exactly when Construction A of it is quasi-compact over `S'`.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XE](https://stacks.math.columbia.edu/tag/04XE)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t v' t' v'' t'' w

/-! ### Surjectivity on points of a composite -/

/-- **A composite of two 1-morphisms surjective on the points of Stacks 04XG is surjective on
points.** -/
theorem pointsMap_surjective_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)}
    {𝒵 : BasedCategory.{v'', t''} (BigFppfOver B S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids) (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵)
    (hF : Function.Surjective (pointsMap B S hS 𝒳 h𝒳 h𝒴 F))
    (hG : Function.Surjective (pointsMap B S hS 𝒴 h𝒴 h𝒵 G)) :
    Function.Surjective (pointsMap B S hS 𝒳 h𝒳 h𝒵 (F.comp G)) := by
  intro z
  obtain ⟨w, rfl⟩ := hG z
  obtain ⟨w', rfl⟩ := hF w
  exact ⟨w', (pointsMap_comp B S hS 𝒳 h𝒳 h𝒴 h𝒵 F G w').symm⟩

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- Precomposing with a 1-morphism whose underlying functor is an equivalence keeps a map
surjective on points. -/
private theorem pointsMap_surjective_comp_of_isEquivalence (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)}
    {𝒵 : BasedCategory.{v'', t''} (BigFppfOver B S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids) (F : 𝒳 ⥤ᵇ 𝒴) (hF : F.toFunctor.IsEquivalence) (G : 𝒴 ⥤ᵇ 𝒵)
    (hG : Function.Surjective (pointsMap B S hS 𝒴 h𝒴 h𝒵 G)) :
    Function.Surjective (pointsMap B S hS 𝒳 h𝒳 h𝒵 (F.comp G)) := by
  have := hF
  exact pointsMap_surjective_comp B S hS h𝒳 h𝒴 h𝒵 F G
    (pointsMap_surjective_of_essSurj B S hS _ _ F) hG

/-! ### Field-valued points and Construction A -/

section Points

variable {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)}

/-- **A field-valued point of Stacks 04XE is carried along Construction A.** The object of the
total category, the field and the identification of the underlying scheme of the base object with
the field spectrum are unchanged; the base object of the site is composed with `g`. -/
noncomputable def changeBaseFieldValuedPoint (p : FieldValuedPoint B S hS 𝒳) :
    FieldValuedPoint B S' hS' (changeBase B S S' hS hS' g 𝒳) where
  carrier := p.carrier
  field := p.field
  base := (Over.map g).obj p.base
  isSpec := p.isSpec
  obj := p.obj
  «over» := congrArg (Over.map g).obj p.over

/-- **A field-valued point of Construction A of `𝒳` is a field-valued point of `𝒳`.** The object
of the total category and the field are unchanged, and the base object of the site is the image of
that object under the structure functor of `𝒳`. -/
noncomputable def unchangeBaseFieldValuedPoint
    (p : FieldValuedPoint B S' hS' (changeBase B S S' hS hS' g 𝒳)) :
    FieldValuedPoint B S hS 𝒳 where
  carrier := p.carrier
  field := p.field
  base := 𝒳.p.obj p.obj
  isSpec := eqToIso (congrArg (BigFppfOver.toScheme B S' hS').obj p.over) ≪≫ p.isSpec
  obj := p.obj
  «over» := rfl

/-- Construction A preserves common refinement of field-valued points. -/
theorem hasCommonExtension_changeBaseFieldValuedPoint {p q : FieldValuedPoint B S hS 𝒳}
    (h : FieldValuedPoint.HasCommonExtension p q) :
    FieldValuedPoint.HasCommonExtension
      (changeBaseFieldValuedPoint B S S' hS hS' g p)
      (changeBaseFieldValuedPoint B S S' hS hS' g q) := by
  obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ := h
  exact ⟨changeBaseFieldValuedPoint B S S' hS hS' g r, ⟨a⟩, ⟨b⟩⟩

/-- Reading a field-valued point of Construction A of `𝒳` as one of `𝒳` preserves common
refinement. -/
theorem hasCommonExtension_unchangeBaseFieldValuedPoint
    {p q : FieldValuedPoint B S' hS' (changeBase B S S' hS hS' g 𝒳)}
    (h : FieldValuedPoint.HasCommonExtension p q) :
    FieldValuedPoint.HasCommonExtension
      (unchangeBaseFieldValuedPoint B S S' hS hS' g p)
      (unchangeBaseFieldValuedPoint B S S' hS hS' g q) := by
  obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ := h
  exact ⟨unchangeBaseFieldValuedPoint B S S' hS hS' g r, ⟨a⟩, ⟨b⟩⟩

/-- **The points of Stacks 04XG are unchanged by Construction A.** The bijection induced on the
quotients of Stacks 04XF by `AlgebraicGeometry.Stack.changeBaseFieldValuedPoint` and
`AlgebraicGeometry.Stack.unchangeBaseFieldValuedPoint`. -/
noncomputable def changeBasePointsEquiv (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) :
    points B S hS 𝒳 h𝒳 ≃
      points B S' hS' (changeBase B S S' hS hS' g 𝒳)
        ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).2 h𝒳) where
  toFun := Quotient.map (changeBaseFieldValuedPoint B S S' hS hS' g)
    fun _ _ h => hasCommonExtension_changeBaseFieldValuedPoint B S S' hS hS' g h
  invFun := Quotient.map (unchangeBaseFieldValuedPoint B S S' hS hS' g)
    fun _ _ h => hasCommonExtension_unchangeBaseFieldValuedPoint B S S' hS hS' g h
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h p => exact Quotient.sound ⟨p, ⟨𝟙 p.obj⟩, ⟨𝟙 p.obj⟩⟩
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h p => exact Quotient.sound ⟨p, ⟨𝟙 p.obj⟩, ⟨𝟙 p.obj⟩⟩

/-- The bijection of `AlgebraicGeometry.Stack.changeBasePointsEquiv` commutes with the map on
points of a 1-morphism and of Construction A of it. -/
theorem changeBasePointsEquiv_pointsMap (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (h𝒴 : 𝒴.p.IsFiberedInGroupoids) (F : 𝒳 ⥤ᵇ 𝒴) (x : points B S hS 𝒳 h𝒳) :
    changeBasePointsEquiv B S S' hS hS' g 𝒴 h𝒴 (pointsMap B S hS 𝒳 h𝒳 h𝒴 F x) =
      pointsMap B S' hS' (changeBase B S S' hS hS' g 𝒳)
        ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).2 h𝒳)
        ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒴).2 h𝒴)
        (changeBaseFunctor B S S' hS hS' g F)
        (changeBasePointsEquiv B S S' hS hS' g 𝒳 h𝒳 x) := by
  induction x using Quotient.inductionOn with
  | h p => rfl

/-- **A 1-morphism over the big fppf site of `S` is surjective on the points of Stacks 04XG
exactly when Construction A of it is.** -/
theorem pointsMap_surjective_changeBaseFunctor_iff (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (h𝒴 : 𝒴.p.IsFiberedInGroupoids) (F : 𝒳 ⥤ᵇ 𝒴) :
    Function.Surjective (pointsMap B S' hS' (changeBase B S S' hS hS' g 𝒳)
        ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).2 h𝒳)
        ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒴).2 h𝒴)
        (changeBaseFunctor B S S' hS hS' g F)) ↔
      Function.Surjective (pointsMap B S hS 𝒳 h𝒳 h𝒴 F) := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (changeBasePointsEquiv B S S' hS hS' g 𝒴 h𝒴 y)
    refine ⟨(changeBasePointsEquiv B S S' hS hS' g 𝒳 h𝒳).symm x, ?_⟩
    apply (changeBasePointsEquiv B S S' hS hS' g 𝒴 h𝒴).injective
    rw [changeBasePointsEquiv_pointsMap B S S' hS hS' g h𝒳 h𝒴 F, Equiv.apply_symm_apply, hx]
  · intro h y
    obtain ⟨x, hx⟩ := h ((changeBasePointsEquiv B S S' hS hS' g 𝒴 h𝒴).symm y)
    refine ⟨changeBasePointsEquiv B S S' hS hS' g 𝒳 h𝒳 x, ?_⟩
    rw [← changeBasePointsEquiv_pointsMap B S S' hS hS' g h𝒳 h𝒴 F, hx,
      Equiv.apply_symm_apply]

end Points

/-! ### Descending a presentation along Construction A -/

/-- **A 1-morphism to Construction A of `𝒳` out of the slice of the site of `S'` at an object `U'`
descends to a 1-morphism to `𝒳` out of the slice of the site of `S` at an object with the same
underlying scheme as `U'`, keeping surjectivity on points.** -/
theorem exists_affine_presentation_of_changeBase
    (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (U' : BigFppfOver B S' hS')
    (a : (schemeFibredCategory B S' hS' U').based ⥤ᵇ changeBase B S S' hS hS' g 𝒳)
    (ha : Function.Surjective (pointsMap B S' hS' (schemeFibredCategory B S' hS' U').based
      (schemeFibredCategory B S' hS' U').isFiberedInGroupoids
      ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).2 h𝒳) a)) :
    ∃ (h₀ : U'.left ⟶ B.obj hS)
      (b : (schemeFibredCategory B S hS (Over.mk h₀)).based ⥤ᵇ 𝒳),
      Function.Surjective (pointsMap B S hS (schemeFibredCategory B S hS (Over.mk h₀)).based
        (schemeFibredCategory B S hS (Over.mk h₀)).isFiberedInGroupoids h𝒳 b) := by
  have haw : a.toFunctor ⋙ (changeBase B S S' hS hS' g 𝒳).p = Over.forget U' := a.w
  have hy : (Over.iteratedSliceBackward U' ⋙ a.toFunctor) ⋙
      (changeBase B S S' hS hS' g 𝒳).p = Over.map U'.hom :=
    (congrArg (fun F => Over.iteratedSliceBackward U' ⋙ F) haw).trans
      (Over.iteratedSliceBackward_forget U')
  obtain ⟨h₀, hy₀, hg₀⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒳 U'
    (Over.iteratedSliceBackward U' ⋙ a.toFunctor) hy
  have hbw : (Over.iteratedSliceForward (Over.mk h₀) ⋙
      (Over.iteratedSliceBackward U' ⋙ a.toFunctor)) ⋙ 𝒳.p =
        Over.forget (Over.mk h₀) :=
    (congrArg (fun F => Over.iteratedSliceForward (Over.mk h₀) ⋙ F) hy₀).trans
      (Over.iteratedSliceForward_comp_map (Over.mk h₀))
  refine ⟨h₀,
    { toFunctor := Over.iteratedSliceForward (Over.mk h₀) ⋙
        (Over.iteratedSliceBackward U' ⋙ a.toFunctor)
      w := hbw }, ?_⟩
  · refine (pointsMap_surjective_changeBaseFunctor_iff B S S' hS hS' g
      (schemeFibredCategory B S hS (Over.mk h₀)).isFiberedInGroupoids h𝒳 _).1 ?_
    exact pointsMap_surjective_comp_of_isEquivalence B S' hS'
      ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g
        (schemeFibredCategory B S hS (Over.mk h₀)).based).2
        (schemeFibredCategory B S hS (Over.mk h₀)).isFiberedInGroupoids)
      (schemeFibredCategory B S' hS' U').isFiberedInGroupoids
      ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).2 h𝒳)
      (factorSliceFunctor B S S' hS hS' g hg₀)
      (isEquivalence_factorSliceFunctor B S S' hS hS' g hg₀) a ha

/-! ### Quasi-compactness and Construction A -/

/-- **An algebraic stack with a 1-morphism from the slice at an affine object of the site which is
surjective on points is quasi-compact.** -/
theorem isQuasiCompactStack_of_pointsMap_surjective_affine (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (a : (schemeFibredCategory B S hS V).val ⥤ᵇ 𝒳.val.val)
    (ha : Function.Surjective (pointsMap B S hS (schemeFibredCategory B S hS V).val
      (schemeFibredCategory B S hS V).isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids a)) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
  isQuasiCompactStack_of_isSurjective.{u, w} B S hS
    (𝒰 := schemeStack.{u, w} B S hS V)
    (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom a))
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS V hV) ha

/-- **A quasi-compact algebraic stack has a 1-morphism from the slice at an affine object of the
site which is surjective on points.** -/
theorem exists_pointsMap_surjective_affine_of_isQuasiCompactStack
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
      (a : (schemeFibredCategory B S hS V).val ⥤ᵇ 𝒳.val.val),
      Function.Surjective (pointsMap B S hS (schemeFibredCategory B S hS V).val
        (schemeFibredCategory B S hS V).isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids a) := by
  obtain ⟨V, hV, a, hasurj, -⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 h
  exact ⟨V, hV, a.hom.hom, hasurj⟩

/-- **Quasi-compactness of an algebraic stack is unchanged by Construction A of Stacks 04X5.** An
algebraic stack over `S` is quasi-compact in the sense of Stacks 04YB exactly when the algebraic
stack over `S'` that Construction A produces from it is. -/
theorem isQuasiCompactStack_changeBaseAlgebraicStack_iff (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    IsQuasiCompactStack.{u, w} B S' hS'
        (changeBaseAlgebraicStack B S S' hS hS' g 𝒳).val
        (changeBaseAlgebraicStack B S S' hS hS' g 𝒳).property ↔
      IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property := by
  constructor
  · intro h
    obtain ⟨U', hU', a, ha⟩ := exists_pointsMap_surjective_affine_of_isQuasiCompactStack
      B S' hS' (changeBaseAlgebraicStack B S S' hS hS' g 𝒳) h
    obtain ⟨h₀, b, hb⟩ := exists_affine_presentation_of_changeBase B S S' hS hS' g
      𝒳.val.val 𝒳.val.isFiberedInGroupoids U' a ha
    exact isQuasiCompactStack_of_pointsMap_surjective_affine.{u, w} B S hS 𝒳 (Over.mk h₀) hU' b hb
  · intro h
    obtain ⟨V, hV, a, ha⟩ :=
      exists_pointsMap_surjective_affine_of_isQuasiCompactStack B S hS 𝒳 h
    refine isQuasiCompactStack_of_pointsMap_surjective_affine.{u, w} B S' hS'
      (changeBaseAlgebraicStack B S S' hS hS' g 𝒳) ((Over.map g).obj V) hV
      ((factorSliceInverse B S S' hS hS' g V).comp
        (changeBaseFunctor B S S' hS hS' g a)) ?_
    exact pointsMap_surjective_comp_of_isEquivalence B S' hS'
      (schemeFibredCategory B S' hS' ((Over.map g).obj V)).isFiberedInGroupoids
      ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g
        (schemeFibredCategory B S hS V).val).2
        (schemeFibredCategory B S hS V).isFiberedInGroupoids)
      ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳.val.val).2
        𝒳.val.isFiberedInGroupoids)
      (factorSliceInverse B S S' hS hS' g V)
      (isEquivalence_factorSliceInverse B S S' hS hS' g V) (changeBaseFunctor B S S' hS hS' g a)
      ((pointsMap_surjective_changeBaseFunctor_iff B S S' hS hS' g
        (schemeFibredCategory B S hS V).isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids a).2 ha)

end AlgebraicGeometry.Stack

end

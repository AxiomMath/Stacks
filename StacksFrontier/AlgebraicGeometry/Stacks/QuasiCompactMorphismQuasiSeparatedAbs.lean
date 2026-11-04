module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStackAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianStack

/-!
# Quasi-compact morphisms into a quasi-separated algebraic stack, over `Spec(ℤ)`

**Stacks 075S**, part (1): a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks with `𝒳` quasi-compact
and `𝒴` quasi-separated is quasi-compact.  The base carries it as
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack_absolute`, with
quasi-separatedness read over the terminal scheme `⊤_ Scheme` (a hypothesis `hZ` that the site
contains it).  The definition of a Noetherian algebraic stack
(`AlgebraicGeometry.Stack.IsNoetherianStack`, Stacks 0510) reads quasi-separatedness over
`Spec(ULift ℤ)` instead, as `AlgebraicGeometry.Stack.IsQuasiSeparatedAbs`.  This file proves the
statement of part (1) for an arbitrary base `T` with quasi-separated underlying space, reached from
`S` by any morphism `g : S ⟶ T` of the site, and reads it at `T = Spec(ULift ℤ)`.

The proof is that of the base's absolute statement with the terminal scheme replaced by `T`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack_of_changeBase`
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack_of_isQuasiSeparatedAbs`

## References

* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : Scheme.{u}) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)

/-- The view over `T`, along `g : S ⟶ T`, of an algebraic stack over `S` (Stacks 04X6). -/
noncomputable abbrev viewAlong (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.{u, w} B T hT :=
  (algebraicStackConstructionObjEquiv.{u, w} B S T hS hT g 𝒳).1

/-- The 1-morphism of views over `T` that the hom-bijection of **Stacks 04X5** assigns to a
1-morphism of algebraic stacks over `S`. -/
noncomputable abbrev viewAlongHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    viewAlong.{u, w} B S hS T hT g 𝒳 ⟶ viewAlong.{u, w} B S hS T hT g 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    (algebraicStackConstructionHomEquiv.{u, w} B S T hS hT g 𝒳 𝒴 f).val

/-- **Quasi-compactness of a 2-fibre product descends from a view to `S`.** -/
theorem isQuasiCompactStack_twoFibreProductAlgebraicStack_of_viewAlong
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (k : 𝒴 ⟶ 𝒵)
    (h : IsQuasiCompactStack.{u, w} B T hT
      (twoFibreProductAlgebraicStack B T hT
        (viewAlongHom.{u, w} B S hS T hT g f) (viewAlongHom.{u, w} B S hS T hT g k)).val
      (twoFibreProductAlgebraicStack B T hT
        (viewAlongHom.{u, w} B S hS T hT g f)
        (viewAlongHom.{u, w} B S hS T hT g k)).property) :
    IsQuasiCompactStack.{u, w} B S hS (twoFibreProductAlgebraicStack B S hS f k).val
      (twoFibreProductAlgebraicStack B S hS f k).property := by
  refine (isQuasiCompactStack_changeBaseAlgebraicStack_iff.{u, w} B S T hS hT g
    (twoFibreProductAlgebraicStack B S hS f k)).1 ?_
  have hess : (changeBaseTwoFibreProductInv B S T hS hT g 𝒵.val 𝒳.val 𝒴.val f.hom.hom
      k.hom.hom).toFunctor.EssSurj := by
    have := isEquivalence_changeBaseTwoFibreProductInv B S T hS hT g 𝒵.val 𝒳.val 𝒴.val
      f.hom.hom k.hom.hom
    infer_instance
  exact @isQuasiCompactStack_of_essSurj B T hT
    (twoFibreProductAlgebraicStack B T hT
      (viewAlongHom.{u, w} B S hS T hT g f) (viewAlongHom.{u, w} B S hS T hT g k))
    (changeBaseAlgebraicStack B S T hS hT g (twoFibreProductAlgebraicStack B S hS f k))
    (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (changeBaseTwoFibreProductInv B S T hS hT g 𝒵.val 𝒳.val 𝒴.val f.hom.hom k.hom.hom)))
    hess h

/-- **Stacks 075S, part (1), with quasi-separatedness read over a base `T`.**  Let
`g : S ⟶ T` be a morphism of the site with `T` quasi-separated.  A 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` with `𝒳` quasi-compact and `𝒴` quasi-separated over `T` (viewed over
`T` along `g`) is quasi-compact. -/
theorem isQuasiCompactMorphism_of_isQuasiCompactStack_of_changeBase
    (hTqs : QuasiSeparatedSpace T)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒴 : IsQuasiSeparatedOver.{u, w} B T hT (viewAlong.{u, w} B S hS T hT g 𝒴)) :
    IsQuasiCompactMorphism.{u, w} B S hS f := by
  intro 𝒵 k h𝒵
  refine isQuasiCompactStack_twoFibreProductAlgebraicStack_of_viewAlong.{u, w}
    B S hS T hT g k f ?_
  exact isQuasiCompactMorphism_of_isQuasiCompactStack.{u, w} B T hT hTqs
    (viewAlongHom.{u, w} B S hS T hT g f)
    ((isQuasiCompactStack_changeBaseAlgebraicStack_iff.{u, w} B S T hS hT g 𝒳).2 h𝒳) h𝒴
    (viewAlong.{u, w} B S hS T hT g 𝒵)
    (viewAlongHom.{u, w} B S hS T hT g k)
    ((isQuasiCompactStack_changeBaseAlgebraicStack_iff.{u, w} B S T hS hT g 𝒵).2 h𝒵)

/-- **Stacks 075S, part (1)**, with quasi-separatedness of the target in the sense of
`AlgebraicGeometry.Stack.IsQuasiSeparatedAbs` (Stacks 050D part (8), over `Spec(ULift ℤ)`), the
reading used by `AlgebraicGeometry.Stack.IsNoetherianStack`.  Nothing is asked of the base scheme
`S` or of the site. -/
theorem isQuasiCompactMorphism_of_isQuasiCompactStack_of_isQuasiSeparatedAbs
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒴 : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒴) :
    IsQuasiCompactMorphism.{u, w} B S hS f :=
  isQuasiCompactMorphism_of_isQuasiCompactStack_of_changeBase.{u, w} B S hS _
    (contains_specULiftZ B) (toIntObject B S hS) inferInstance f h𝒳 h𝒴

end AlgebraicGeometry.Stack

end

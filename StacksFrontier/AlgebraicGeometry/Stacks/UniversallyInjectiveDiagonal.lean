module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Universal injectivity and the relative diagonal (Stacks 0CPN)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is universally injective exactly when its
relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective. These are parts (1) and (2) of
**Stacks 0CPN**.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal`: the relative diagonal
  `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` of a 1-morphism of algebraic stacks, at the canonical model of the
  2-fibre product.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp_fst` and
  `..._comp_snd`: both projections undo the relative diagonal, on the nose.
* `AlgebraicGeometry.Stack.injective_pointsMap_of_isSurjective_relativeDiagonal`: a morphism
  with surjective relative diagonal is injective on points.
* `AlgebraicGeometry.Stack.isSurjective_relativeDiagonal_baseChange`: surjectivity of the
  relative diagonal is stable under base change.
* `AlgebraicGeometry.Stack.universallyInjective_iff_isSurjective_relativeDiagonal`:
  **Stacks 0CPN, parts (1) and (2)**.

## Implementation notes

The two implications are proved from three ingredients already in the library, with no reference
to geometric points — which is how the source argues, through part (3) of 0CPN.

*Surjective diagonal implies injective on points.* If `x₁` and `x₂` are points of `𝒳` with the
same image in `|𝒴|`, then **Stacks 04XH**
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_of_isTwoFibreProduct`) produces a point of
`𝒳 ×_𝒴 𝒳` projecting to `x₁` and to `x₂`; surjectivity of `Δ_f` writes that point as `Δ_f(x)`,
and both projections undo `Δ_f`, so `x₁ = x = x₂`.

*Universally injective implies surjective diagonal.* Taking the base change along `f` itself, the
hypothesis says the first projection of `𝒳 ×_𝒴 𝒳` is injective on points; a point `t` of
`𝒳 ×_𝒴 𝒳` and `Δ_f` applied to its first projection then have the same first projection, hence
agree.

*Surjective diagonal implies universally injective.* The hypothesis is only about `f`, so it has
to be propagated to the base change, and what does that is **Stacks 04YR** over the big fppf site
(`CategoryTheory.TwoFibreProductOver.isEquivalence_diagonalBaseChangeComparison`): the diagonal of
the base change of `f` along `g` is the base change of `Δ_f` along the morphism induced on
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒳) ⟶ 𝒳 ×_𝒴 𝒳`. Surjectivity is stable under base change
(**Stacks 04ZU**), so the diagonal of the base change is surjective, and the previous paragraph
applies to it. Since universal injectivity quantifies over every model of the base change, it is
enough to verify it at the canonical one, and
`AlgebraicGeometry.Stack.injective_pointsMap_fst_of_isTwoFibreProduct` transports the conclusion
to an arbitrary model.

Stacks 04YR is available as an equivalence of the underlying categories; **Stacks 003Z (2)**
(`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`) upgrades it to a quasi-inverse
strictly over the site together with a vertical counit, which is what makes the comparison a
1-morphism of algebraic stacks with an inverse up to a 2-morphism. The map on points does not see
2-morphisms (`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`), so the comparison is
then a bijection on points and the surjectivity transports.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

variable {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a 1-morphism of algebraic stacks over
`S`, at the canonical model `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProduct` of the
2-fibre product: it sends an object `x` to the triple `(x, x, id)`. -/
def relativeDiagonal (f : 𝒳 ⟶ 𝒴) : 𝒳 ⟶ twoFibreProduct B S hS f f :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (Stack.relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom))

/-- The first projection undoes the relative diagonal. -/
@[simp]
theorem relativeDiagonal_comp_fst (f : 𝒳 ⟶ 𝒴) :
    relativeDiagonal B S hS f ≫ (twoFibreProductSquare B S hS f f).fst = 𝟙 𝒳 := rfl

/-- The second projection undoes the relative diagonal. -/
@[simp]
theorem relativeDiagonal_comp_snd (f : 𝒳 ⟶ 𝒴) :
    relativeDiagonal B S hS f ≫ (twoFibreProductSquare B S hS f f).snd = 𝟙 𝒳 := rfl

end AlgebraicStacks

variable {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- On points, the first projection undoes the relative diagonal. -/
private theorem pointsMap_fst_comp_pointsMap_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.pointsMap B S hS
        (AlgebraicStacks.twoFibreProductSquare B S hS f f).fst ∘
      AlgebraicStacks.pointsMap B S hS (AlgebraicStacks.relativeDiagonal B S hS f) = id := by
  rw [← AlgebraicStacks.pointsMap_comp, AlgebraicStacks.relativeDiagonal_comp_fst,
    AlgebraicStacks.pointsMap_id]

/-- **A 1-morphism of algebraic stacks whose relative diagonal is surjective is injective on
points.** Two points of `𝒳` with the same image in `|𝒴|` lift to a point of `𝒳 ×_𝒴 𝒳` by
Stacks 04XH, that point is the image of a point `x` of `𝒳` under `Δ_f`, and both projections
undo `Δ_f`. -/
theorem injective_pointsMap_of_isSurjective_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hΔ : IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f)) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS f) := by
  have hfst := pointsMap_fst_comp_pointsMap_relativeDiagonal B S hS f
  have hsnd : AlgebraicStacks.pointsMap B S hS
        (AlgebraicStacks.twoFibreProductSquare B S hS f f).snd ∘
      AlgebraicStacks.pointsMap B S hS (AlgebraicStacks.relativeDiagonal B S hS f) = id := by
    rw [← AlgebraicStacks.pointsMap_comp, AlgebraicStacks.relativeDiagonal_comp_snd,
      AlgebraicStacks.pointsMap_id]
  intro a b hab
  obtain ⟨p, hp₁, hp₂⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS f f)
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS f f) a b hab
  obtain ⟨c, rfl⟩ := hΔ p
  rw [← hp₁, ← hp₂]
  exact (congrFun hfst c).trans (congrFun hsnd c).symm

/-- **A universally injective 1-morphism of algebraic stacks has surjective relative diagonal.**
Universal injectivity applied to the base change of `f` along `f` itself says that the first
projection of `𝒳 ×_𝒴 𝒳` is injective on points, and `Δ_f` applied to the first projection of a
point has the same first projection as that point. -/
theorem isSurjective_relativeDiagonal_of_universallyInjective (f : 𝒳 ⟶ 𝒴)
    (hf : UniversallyInjective B S hS f) :
    IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f) := by
  have hfst := pointsMap_fst_comp_pointsMap_relativeDiagonal B S hS f
  exact fun t =>
    ⟨AlgebraicStacks.pointsMap B S hS (AlgebraicStacks.twoFibreProductSquare B S hS f f).fst t,
      hf 𝒳 f (AlgebraicStacks.twoFibreProductSquare B S hS f f)
        (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS f f) (congrFun hfst _)⟩

/-- **Surjectivity of the relative diagonal is stable under base change.** This is Stacks 04YR —
the diagonal of a base change is the base change of the diagonal — combined with Stacks 04ZU. -/
theorem isSurjective_relativeDiagonal_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hΔ : IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f)) :
    IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd) := by
  set U := AlgebraicStacks.twoFibreProductSquare B S hS f g
  have hh : CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p = 𝒳.val.val.p := f.hom.hom.w
  have hs : CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒴.val.val.p = 𝒵.val.val.p := g.hom.hom.w
  -- The morphism `r × r` induced by the first projection on both factors.
  let mapDiagMor : AlgebraicStacks.twoFibreProduct B S hS U.snd U.snd ⟶
      AlgebraicStacks.twoFibreProduct B S hS f f :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := TwoFibreProductOver.mapDiag hs, w := rfl })
  -- The canonical base-change square of `Δ_f` along it, and Stacks 04ZU.
  set K := AlgebraicStacks.twoFibreProductSquare B S hS mapDiagMor
    (AlgebraicStacks.relativeDiagonal B S hS f)
  have hKfst : IsSurjective B S hS K.fst :=
    isSurjective_of_isTwoFibreProduct B S hS K.swap (Bicategory.isTwoFibreProduct_swap
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS mapDiagMor
        (AlgebraicStacks.relativeDiagonal B S hS f))) hΔ
  -- Stacks 04YR: the comparison from `𝒵 ×_𝒴 𝒳` into that square is an equivalence over the site.
  have hcmpw : TwoFibreProductOver.diagonalBaseChangeComparison hh hs ⋙ K.pt.val.val.p =
      U.pt.val.val.p :=
    TwoFibreProductOver.diagonalBaseChangeComparison_comp_structureFunctor hh hs
  obtain ⟨Finv, hFinv, -, ε, -, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    U.pt.val.val.p K.pt.val.val.p (CatFiberedInGroupoids.isFiberedInGroupoids U.pt.val)
    (CatFiberedInGroupoids.isFiberedInGroupoids K.pt.val)
    (TwoFibreProductOver.diagonalBaseChangeComparison hh hs) hcmpw
    (TwoFibreProductOver.isEquivalence_diagonalBaseChangeComparison hh hs)
  let cmpMor : U.pt ⟶ K.pt := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      { toFunctor := TwoFibreProductOver.diagonalBaseChangeComparison hh hs, w := hcmpw })
  let invMor : K.pt ⟶ U.pt := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom { toFunctor := Finv, w := hFinv })
  let counit : invMor ≫ cmpMor ⟶ 𝟙 K.pt :=
    Bicategory.InducedBicategory.Hom₂.mk (Bicategory.InducedBicategory.Hom₂.mk
      { toNatTrans := ε.hom, isHomLift' := hε })
  have hcmpsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS cmpMor) := by
    have h : AlgebraicStacks.pointsMap B S hS cmpMor ∘
        AlgebraicStacks.pointsMap B S hS invMor = id := by
      rw [← AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS counit,
        AlgebraicStacks.pointsMap_id]
    exact Function.RightInverse.surjective (congrFun h)
  have hdec : cmpMor ≫ K.fst = AlgebraicStacks.relativeDiagonal B S hS U.snd := rfl
  have hfinal : Function.Surjective (AlgebraicStacks.pointsMap B S hS (cmpMor ≫ K.fst)) := by
    rw [AlgebraicStacks.pointsMap_comp]
    exact hKfst.comp hcmpsurj
  exact hdec ▸ hfinal

/-- **A 1-morphism of algebraic stacks with surjective relative diagonal is universally
injective.** The relative diagonal of every base change of `f` is surjective by
`AlgebraicGeometry.Stack.isSurjective_relativeDiagonal_baseChange`, so every base change is
injective on points. -/
theorem universallyInjective_of_isSurjective_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hΔ : IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f)) :
    UniversallyInjective B S hS f := fun _ g _ hP =>
  injective_pointsMap_fst_of_isTwoFibreProduct B S hS hP
    (Bicategory.isTwoFibreProduct_swap
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS f g))
    (injective_pointsMap_of_isSurjective_relativeDiagonal B S hS _
      (isSurjective_relativeDiagonal_baseChange B S hS f g hΔ))

/-- **Stacks 0CPN, parts (1) and (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is
universally injective if and only if its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective. -/
@[stacks 0CPN "parts (1) and (2)"]
theorem universallyInjective_iff_isSurjective_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    UniversallyInjective B S hS f ↔
      IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f) :=
  ⟨isSurjective_relativeDiagonal_of_universallyInjective B S hS f,
    universallyInjective_of_isSurjective_relativeDiagonal B S hS f⟩

end AlgebraicGeometry.Stack

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableDiagonal.SchemeAndRepresentableSources
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Representable
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalClauses
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningIsScheme
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# Stacks 0BPV at representability by schemes

For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is representable by schemes (**Stacks 02Y7**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. This is property (a) of **Stacks 0BPV**.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableCFG_iff_of_comp_forget`: a category fibred in
  groupoids over `𝒞` lying over a slice `𝒞/U` is representable over `𝒞/U` if and only if it is
  representable over `𝒞`.
* `AlgebraicGeometry.Stack.isRepresentableMorphism_relativeDiagonal_outer_of_inner`: the
  implication from `Δ` to `Δ'`.
* `AlgebraicGeometry.Stack.isRepresentableMorphism_relativeDiagonal_inner_iff_outer`:
  **Stacks 0BPV**, property (a).

## Implementation notes

The implication from `Δ'` to `Δ` is a base change across the cartesian diagonal square of
**Stacks 0BPU**, `AlgebraicGeometry.Stack.isRepresentableMorphism_relativeDiagonal_inner_of_outer`.

For the converse, let `U` be a scheme and `g : U ⟶ 𝒳' ×_{𝒴'} 𝒳'` a 1-morphism; the task is to
show that `T' = U ×_{𝒳' ×_{𝒴'} 𝒳'} 𝒳'` is a scheme. Let `c : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` be the
thickening of the first assertion of Stacks 0BPU and `U₀ = U ×_{𝒳' ×_{𝒴'} 𝒳'} (𝒳 ×_𝒴 𝒳)`. Then
`U₀ ⟶ U` is a thickening (**Stacks 0BPR**), so `U₀` is a scheme by **Stacks 0BPW** clause (2);
choose a scheme `X` and an equivalence `e : X ⟶ U₀`. The 2-fibre product `T = X ×_{𝒳 ×_𝒴 𝒳} 𝒳`
is a scheme because `Δ` is representable. Pasting it with the cartesian diagonal square of
Stacks 0BPU exhibits `T` as a 2-fibre product of `X ⟶ U ⟶ 𝒳' ×_{𝒴'} 𝒳'` with `Δ'`, so `T` is
equivalent to `X ×_U T'`, whose projection to `T'` is a base change of the thickening
`X ⟶ U₀ ⟶ U`. Hence `T ⟶ T'` is a thickening out of a scheme, and `T'` is a scheme by Stacks 0BPW
clause (2) once more.

Representability of a category fibred in groupoids over `𝒞/U` and over `𝒞` are compared through
`Stacks.RepresentableMorphism.isRepresentableCFG_iff_nonempty_isTerminal`: both say that the
category has a terminal object.

## References

* [Stacks Project, Tag 02Y7](https://stacks.math.columbia.edu/tag/02Y7)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0BPW](https://stacks.math.columbia.edu/tag/0BPW)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace Stacks.RepresentableMorphism

/-- **Representability over a slice is representability over the base.** Let `p : A ⥤ 𝒞` be
fibred in groupoids and let `F : A ⥤ 𝒞/U` lie over `𝒞`, so that `F ⋙ Over.forget U = p`. Then
`F` is a representable category fibred in groupoids over `𝒞/U` if and only if `p` is one over
`𝒞`. -/
theorem isRepresentableCFG_iff_of_comp_forget {𝒞 : Type*} [Category 𝒞] {A : Type*} [Category A]
    {p : A ⥤ 𝒞} (hp : p.IsFiberedInGroupoids) {U : 𝒞} (F : A ⥤ Over U)
    (hF : F ⋙ Over.forget U = p) :
    IsRepresentableCFG F ↔ IsRepresentableCFG p :=
  (isRepresentableCFG_iff_nonempty_isTerminal
      (Functor.IsFiberedInGroupoids.of_comp_over U p F hF hp)).trans
    (isRepresentableCFG_iff_nonempty_isTerminal hp).symm

end Stacks.RepresentableMorphism

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- **The implication from `Δ` to `Δ'` of property (a) of Stacks 0BPV.** If the restricted
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` of a morphism of thickenings of algebraic stacks is
representable by schemes (**Stacks 02Y7**), so is the ambient one `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'`. -/
theorem isRepresentableMorphism_relativeDiagonal_outer_of_inner
    (hin : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p
      (AlgebraicStacks.twoFibreProduct B S hS m.inner m.inner).val.val.p
      (CatFiberedInGroupoids.homFunctor
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom)) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p
      (AlgebraicStacks.twoFibreProduct B S hS m.outer m.outer).val.val.p
      (CatFiberedInGroupoids.homFunctor
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) := by
  classical
  intro U G hG
  let g : schemeStack B S hS U ⟶ AlgebraicStacks.twoFibreProduct B S hS m.outer m.outer :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := G, w := hG })
  let Q' := AlgebraicStacks.twoFibreProductSquare B S hS g
    (AlgebraicStacks.relativeDiagonal B S hS m.outer)
  refine (Stacks.RepresentableMorphism.isRepresentableCFG_iff_of_comp_forget
    Q'.pt.val.property _ TwoFibreProductOver.fst_comp_eq).2 ?_
  let W := AlgebraicStacks.twoFibreProductSquare B S hS g (selfProductDiagonalMap B S hS m)
  have hWfst : IsThickening W.fst := isThickening_fst_of_isTwoFibreProduct B S hS
    (isThickening_selfProductDiagonalMap B S hS m) W
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS g
      (selfProductDiagonalMap B S hS m))
  obtain ⟨X, E, hE⟩ := (isRepresentableCFG_iff_of_isThickening B S hS W.fst hWfst).2
    (AlgebraicGeometry.isRepresentableCFG_schemeFibredCategory B S hS U)
  obtain ⟨Einv, hEinv, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
  let e : schemeStack B S hS X ⟶ W.pt :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := Einv, w := hEinv.comm })
  have : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk E Einv ε.symm η).isEquivalence_inverse
  let g₀ := e ≫ W.snd
  let Qt := AlgebraicStacks.twoFibreProductSquare B S hS g₀
    (AlgebraicStacks.relativeDiagonal B S hS m.inner)
  have hT : Stacks.RepresentableMorphism.IsRepresentableCFG Qt.pt.val.val.p :=
    (Stacks.RepresentableMorphism.isRepresentableCFG_iff_of_comp_forget
      Qt.pt.val.property _ TwoFibreProductOver.fst_comp_eq).1
      (hin X (CatFiberedInGroupoids.homFunctor g₀.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g₀.hom))
  let R := (selfProductDiagonalSquare B S hS m).pasteFst (k := g₀) Qt
  let θ : g₀ ≫ selfProductDiagonalMap B S hS m ≅ (e ≫ W.fst) ≫ g :=
    Bicategory.associator e W.snd (selfProductDiagonalMap B S hS m) ≪≫
      Bicategory.whiskerLeftIso e W.iso.symm ≪≫ (Bicategory.associator e W.fst g).symm
  have hR' : Bicategory.IsTwoFibreProduct (R.reindexFst θ) :=
    Bicategory.isTwoFibreProduct_reindexFst θ <| Bicategory.isTwoFibreProduct_pasteFst _
      (isTwoFibreProduct_selfProductDiagonalSquare B S hS m) Qt
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS g₀
        (AlgebraicStacks.relativeDiagonal B S hS m.inner))
  let V := AlgebraicStacks.twoFibreProductSquare B S hS (e ≫ W.fst) Q'.fst
  have hV := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (e ≫ W.fst) Q'.fst
  have hpaste : Bicategory.IsTwoFibreProduct (Q'.pasteFst V) :=
    Bicategory.isTwoFibreProduct_pasteFst Q'
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS g
        (AlgebraicStacks.relativeDiagonal B S hS m.outer)) V hV
  let d := Bicategory.twoFibreProductPreHom hpaste (R.reindexFst θ)
  have : (CatFiberedInGroupoids.homFunctor d.hom.hom).IsEquivalence :=
    isEquivalence_homFunctor_preHom B S hS hR' hpaste d
  exact (isRepresentableCFG_iff_of_isThickening B S hS (d.hom ≫ V.snd)
    (isThickening_comp_of_isEquivalence B S hS d.hom V.snd
      (isThickening_snd_of_isTwoFibreProduct B S hS
        (isThickening_comp_of_isEquivalence B S hS e W.fst hWfst) V hV))).1 hT

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is representable by schemes (**Stacks 02Y7**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (a) of seventeen: representable by schemes"]
theorem isRepresentableMorphism_relativeDiagonal_inner_iff_outer :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p
        (AlgebraicStacks.twoFibreProduct B S hS m.inner m.inner).val.val.p
        (CatFiberedInGroupoids.homFunctor
          (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom) ↔
      Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p
        (AlgebraicStacks.twoFibreProduct B S hS m.outer m.outer).val.val.p
        (CatFiberedInGroupoids.homFunctor
          (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) :=
  ⟨isRepresentableMorphism_relativeDiagonal_outer_of_inner B S hS m,
    isRepresentableMorphism_relativeDiagonal_inner_of_outer B S hS m⟩

end Diagonal

end AlgebraicGeometry.Stack

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningMorphismTopologicalProperties

/-!
# Representability in a morphism of thickenings of algebraic stacks (Stacks 0CJ9, part (11))

Stacks 0CJ9 part (11) reads, verbatim:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Then
> (11) `f` is representable if and only if `f'` is representable.

Representable means representable by schemes (**Stacks 02Y7**): every base change along a
1-morphism out of a scheme is (equivalent to) a scheme.

The source's proof: if `f'` is representable, then so is `f`, because for a scheme `T` and
`T → 𝒴` the base change `𝒳 ×_𝒴 T` is `𝒳 ×_{𝒳'} (𝒳' ×_{𝒴'} T)`, a closed substack of a scheme.
Conversely, for a scheme `T'` and `T' → 𝒴'`, the base change
`𝒳 ×_𝒴 (𝒴 ×_{𝒴'} T') ⟶ 𝒳' ×_{𝒴'} T'` is a thickening (**Stacks 0BPR**) whose source is a
scheme, so its target is a scheme by **Stacks 0BPW**.

Here both directions are the second half of that argument, through the thickenings of
`AlgebraicGeometry.Stack.exists_isThickening_baseChange_comp` and
`AlgebraicGeometry.Stack.exists_isThickening_baseChange_of_twoIso`, and **Stacks 0BPW** clause
(2), `AlgebraicGeometry.Stack.isRepresentableCFG_iff_of_isThickening`, used in both directions:
from `f'` to `f`, the base change of `f` along `T → 𝒴` is a thickening of the base change of `f'`
along `T → 𝒴 → 𝒴'`, which is a scheme; from `f` to `f'`, the base change `𝒴 ×_{𝒴'} T'` is a
thickening of the scheme `T'`, hence equivalent to a scheme `T`, and the base change of `f` along
`T → 𝒴` is a scheme mapping by a thickening onto the base change of `f'` along `T'`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableMorphism_inner_iff_outer`: **Stacks 0CJ9**, part (11).

## References

* [Stacks Project, Tag 02Y7](https://stacks.math.columbia.edu/tag/02Y7)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0BPW](https://stacks.math.columbia.edu/tag/0BPW)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}

/-- **Stacks 0CJ9, part (11), from the ambient 1-morphism to the restricted one.** The base
change of `f` along a scheme-valued point `g : U ⟶ 𝒴` is a thickening of the base change of `f'`
along `g ≫ j`, which is a scheme; so it is a scheme by **Stacks 0BPW** clause (2). -/
theorem isRepresentableMorphism_inner_of_outer (m : ThickeningMorphism i j hi hj)
    (h : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p 𝒴'.val.val.p
      (CatFiberedInGroupoids.homFunctor m.outer.hom)) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor m.inner.hom) := by
  classical
  intro U G hG
  let g : schemeStack B S hS U ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := G, w := hG })
  refine (Stacks.RepresentableMorphism.isRepresentableCFG_iff_of_comp_forget
    (AlgebraicStacks.twoFibreProductSquare B S hS g m.inner).pt.val.property _
    TwoFibreProductOver.fst_comp_eq).2 ?_
  obtain ⟨c, hc, -⟩ := exists_isThickening_baseChange_comp B S hS m g
  exact (isRepresentableCFG_iff_of_isThickening B S hS c hc).2
    ((Stacks.RepresentableMorphism.isRepresentableCFG_iff_of_comp_forget
      (AlgebraicStacks.twoFibreProductSquare B S hS (g ≫ j) m.outer).pt.val.property _
      TwoFibreProductOver.fst_comp_eq).1
      (h U (CatFiberedInGroupoids.homFunctor (g ≫ j).hom)
        (CatFiberedInGroupoids.homFunctor_comp_p (g ≫ j).hom)))

/-- **Stacks 0CJ9, part (11), from the restricted 1-morphism to the ambient one.** For a
scheme-valued point `g : U ⟶ 𝒴'`, the base change `U ×_{𝒴'} 𝒴` is a thickening of `U`, hence
equivalent to a scheme `X` by **Stacks 0BPW** clause (2); the base change of `f` along
`X ⟶ U ×_{𝒴'} 𝒴 ⟶ 𝒴` is a scheme, and it maps by a thickening onto the base change of `f'` along
`g`, which is therefore a scheme by Stacks 0BPW clause (2) once more. -/
theorem isRepresentableMorphism_outer_of_inner (m : ThickeningMorphism i j hi hj)
    (h : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor m.inner.hom)) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p 𝒴'.val.val.p
      (CatFiberedInGroupoids.homFunctor m.outer.hom) := by
  classical
  intro U G hG
  let g : schemeStack B S hS U ⟶ 𝒴' :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := G, w := hG })
  refine (Stacks.RepresentableMorphism.isRepresentableCFG_iff_of_comp_forget
    (AlgebraicStacks.twoFibreProductSquare B S hS g m.outer).pt.val.property _
    TwoFibreProductOver.fst_comp_eq).2 ?_
  -- `U ×_{𝒴'} 𝒴` is a thickening of `U`, hence a scheme
  let W := AlgebraicStacks.twoFibreProductSquare B S hS g j
  have hWfst : IsThickening W.fst := isThickening_fst_of_isTwoFibreProduct B S hS hj W
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS g j)
  obtain ⟨X, E, hE⟩ := (isRepresentableCFG_iff_of_isThickening B S hS W.fst hWfst).2
    (AlgebraicGeometry.isRepresentableCFG_schemeFibredCategory B S hS U)
  obtain ⟨Einv, hEinv, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
  let e : schemeStack B S hS X ⟶ W.pt :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := Einv, w := hEinv.comm })
  have : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk E Einv ε.symm η).isEquivalence_inverse
  let θ : (e ≫ W.fst) ≫ g ≅ (e ≫ W.snd) ≫ j :=
    Bicategory.associator e W.fst g ≪≫ Bicategory.whiskerLeftIso e W.iso ≪≫
      (Bicategory.associator e W.snd j).symm
  obtain ⟨c, hc, -⟩ :=
    exists_isThickening_baseChange_of_twoIso B S hS m (e ≫ W.snd) g (e ≫ W.fst)
      (isThickening_comp_of_isEquivalence B S hS e W.fst hWfst) θ
  -- the base change of `f` along `X ⟶ 𝒴` is a scheme, `f` being representable
  exact (isRepresentableCFG_iff_of_isThickening B S hS c hc).1
    ((Stacks.RepresentableMorphism.isRepresentableCFG_iff_of_comp_forget
      (AlgebraicStacks.twoFibreProductSquare B S hS (e ≫ W.snd) m.inner).pt.val.property _
      TwoFibreProductOver.fst_comp_eq).1
      (h X (CatFiberedInGroupoids.homFunctor (e ≫ W.snd).hom)
        (CatFiberedInGroupoids.homFunctor_comp_p (e ≫ W.snd).hom)))

/-- **Stacks 0CJ9, part (11).** In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of
algebraic stacks over `S`, the restricted 1-morphism `f` is representable (by schemes,
**Stacks 02Y7**) if and only if the ambient 1-morphism `f'` is. -/
@[stacks 0CJ9 "part (11): representable"]
theorem isRepresentableMorphism_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor m.inner.hom) ↔
      Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p 𝒴'.val.val.p
        (CatFiberedInGroupoids.homFunctor m.outer.hom) :=
  ⟨isRepresentableMorphism_outer_of_inner B S hS m, isRepresentableMorphism_inner_of_outer B S hS m⟩

end AlgebraicGeometry.Stack

end

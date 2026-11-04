module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# The projection formula morphism for sheaves of modules on a ringed space

This file constructs the canonical morphism of [Stacks, Tag 0FZE] (equivalently the map whose
invertibility is [Stacks, Tag 01E8]): for a morphism of ringed spaces `f : X ⟶ Y`, a sheaf of
`𝒪_X`-modules `G` and a sheaf of `𝒪_Y`-modules `H`,

`f_* G ⊗_{𝒪_Y} H ⟶ f_* (G ⊗_{𝒪_X} f^* H)`.

## Main definitions

* `Stacks.ProjectionFormula.projectionFormulaMap'`: the abstract construction
  `CategoryTheory.adjunctionTensorMap` — the adjoint transpose of an oplax comparison
  `α : A ⋙ L ⟶ L.prod L ⋙ B` followed by the counit in the first factor, imported here — run on
  the ringed-space
  pullback-pushforward adjunction and the comparison morphism of
  `Stacks.RingedSpace.comparisonNatTrans`.  It is primed because
  `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` is the same construction for
  a morphism of
  *schemes*; the two are distinct morphisms between distinct objects, and this one asks less of
  its argument, a morphism of ringed spaces rather than of schemes.

## Main results

* `Stacks.ProjectionFormula.adjunctionTensorMap_homEquiv`: tensoring an adjoint transpose and
  then applying the abstract map is itself an adjoint transpose, with the counit gone.
* `Stacks.ProjectionFormula.projectionFormulaMap'_natural`: naturality in both module arguments.
* `Stacks.ProjectionFormula.projectionFormulaMap'_unit`: tensoring the adjunction unit on the
  left and then applying the projection formula map is the adjoint transpose of the comparison.
  This is the identity that lets a surjectivity hypothesis about `𝒪_Y ⟶ f_* 𝒪_X` be transported
  to one about the unit `H ⟶ f_* f^* H`.

## Implementation notes

The construction needs only the *oplax* comparison `f^*(A ⊗ B) ⟶ f^* A ⊗ f^* B`, which is the
direction the pullback adjunction supplies and which
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean` constructs
unconditionally as `Stacks.RingedSpace.comparisonNatTrans`. No invertibility of that comparison
— that is, no part of [Stacks, Tag 01CD] — is used, and `projectionFormulaMap'` is therefore
complete and axiom-clean, with no unproved step.

Notes in this repository record the projection formula as absent, and one of them says more
than that: it says of
`Stacks.RingedSpace.comparison` that it "runs the other way, `f^*(A ⊗ B) ⟶ f^* A ⊗ f^* B`, so the
morphism the formula asserts to be invertible has yet to be constructed". That is false:
the oplax direction is exactly the direction out of which the projection formula map
is built, so the comparison running "the other way" is what makes the construction possible
rather than what blocks it. What remains open is invertibility, not existence.

The abstract core — `CategoryTheory.adjunctionTensorMap` with its naturality and unit
identities — is imported rather than restated: it is already declared, with exactly these
statements, alongside the scheme-level
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap`. Only the
one identity the ringed-space development needs in addition,
`Stacks.ProjectionFormula.adjunctionTensorMap_homEquiv`, is proved in the abstract section
below.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.ProjectionFormula

/-! ### The abstract construction -/

section Abstract

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **Tensoring an adjoint transpose and then applying the projection formula map is itself an
adjoint transpose.** For `v : L F ⟶ G`, tensoring the transpose `adj.homEquiv v : F ⟶ R G` with
`H` and composing with the projection formula map at `(G, H)` gives the transpose of
`α` at `(F, H)` followed by `v` in the first tensor factor. The counit has disappeared.

This is the identity that lets a surjectivity hypothesis stated along a map `F ⟶ R G` be
transported to one stated along a unit. -/
@[reassoc]
lemma adjunctionTensorMap_homEquiv (F H : C) (G : D) (v : L.obj F ⟶ G) :
    A.map (adj.homEquiv _ _ v ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α G H =
      adj.homEquiv _ _ (α.app (F, H) ≫ B.map (v ×ₘ 𝟙 (L.obj H))) := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionTensorMap
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  have ha := α.naturality (adj.homEquiv _ _ v ×ₘ 𝟙 H)
  change L.map (A.map (adj.homEquiv _ _ v ×ₘ 𝟙 H)) ≫ α.app (R.obj G, H) =
    α.app (F, H) ≫ B.map (L.map (adj.homEquiv _ _ v) ×ₘ L.map (𝟙 H)) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  congr 2
  apply Prod.ext
  · exact (adj.homEquiv _ _).symm_apply_apply v
  · simp

end Abstract

/-! ### The projection formula morphism on a ringed space -/

universe u

open AlgebraicGeometry RingedSpaceModuleAdjunction Stacks.RingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The projection formula morphism of [Stacks, Tag 0FZE]**, for a morphism of ringed spaces
`f : X ⟶ Y`, a sheaf of `𝒪_X`-modules `G` and a sheaf of `𝒪_Y`-modules `H`:

`f_* G ⊗_{𝒪_Y} H ⟶ f_* (G ⊗_{𝒪_X} f^* H)`.

It is the adjoint transpose of the comparison morphism `Stacks.RingedSpace.comparisonNatTrans`
followed by the counit of `f^* ⊣ f_*` in the first tensor factor. Only the oplax direction of the
comparison is used, so this morphism exists unconditionally; its invertibility for an affine `f`
and quasi-coherent `G`, `H` is the content of the tag and is not proved here. -/
noncomputable def projectionFormulaMap'
    (G : SheafOfModules.{u} (structureRingSheaf X))
    (H : SheafOfModules.{u} (structureRingSheaf Y)) :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj
        ((pushforwardFunctor f).obj G, H) ⟶
      (pushforwardFunctor f).obj
        (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).obj
          (G, (pullbackFunctor f).obj H)) :=
  adjunctionTensorMap (pullbackAdjunction f)
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)))
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
    (comparisonNatTrans f) G H

lemma projectionFormulaMap'_eq
    (G : SheafOfModules.{u} (structureRingSheaf X))
    (H : SheafOfModules.{u} (structureRingSheaf Y)) :
    projectionFormulaMap' f G H =
      adjunctionTensorMap (pullbackAdjunction f)
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)))
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
        (comparisonNatTrans f) G H :=
  rfl

/-- The projection formula morphism is natural in both module arguments. -/
@[reassoc]
lemma projectionFormulaMap'_natural
    {G G' : SheafOfModules.{u} (structureRingSheaf X)}
    {H H' : SheafOfModules.{u} (structureRingSheaf Y)} (g : G ⟶ G') (k : H ⟶ H') :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).map
        ((pushforwardFunctor f).map g ×ₘ k) ≫ projectionFormulaMap' f G' H' =
      projectionFormulaMap' f G H ≫ (pushforwardFunctor f).map
        (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).map
          (g ×ₘ (pullbackFunctor f).map k)) :=
  adjunctionTensorMap_natural (pullbackAdjunction f)
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)))
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
    (comparisonNatTrans f) g k

/-- **Tensoring the unit of `f^* ⊣ f_*` and then applying the projection formula morphism is the
adjoint transpose of the comparison.** -/
@[reassoc]
lemma projectionFormulaMap'_unit (F H : SheafOfModules.{u} (structureRingSheaf Y)) :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).map
        ((pullbackAdjunction f).unit.app F ×ₘ 𝟙 H) ≫
        projectionFormulaMap' f ((pullbackFunctor f).obj F) H =
      (pullbackAdjunction f).homEquiv _ _ ((comparisonNatTrans f).app (F, H)) :=
  adjunctionTensorMap_unit (pullbackAdjunction f)
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)))
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
    (comparisonNatTrans f) F H

end Stacks.ProjectionFormula

end

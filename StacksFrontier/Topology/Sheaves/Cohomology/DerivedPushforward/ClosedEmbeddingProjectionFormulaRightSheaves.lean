module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaMate

/-!
# The ordinary projection formula with the pushforward on the right

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `F` a sheaf of `𝒪_Y`-modules and
`G` a sheaf of `𝒪_X`-modules.  The projection-formula morphism with the pushforward in the right
tensor factor is

`F ⊗_{𝒪_Y} f_*G ⟶ f_*(f^*F ⊗_{𝒪_X} G)`,

the adjoint transpose of the comparison `f^*(F ⊗ f_*G) ⟶ f^*F ⊗ f^*f_*G` of [Stacks, Tag 01CD]
followed by the counit of `f^* ⊣ f_*` in the right tensor factor.  It is the abstract
`Stacks.ProjectionFormula.adjunctionTensorMapSnd` at the ringed-space adjunction.

This file shows that it is the morphism `Stacks.ProjectionFormula.projectionFormulaMap'` of
[Stacks, Tag 0FZE], which has the pushforward on the left, conjugated by the symmetry constraints
of [Stacks, Tag 01CA] on both sides.  Consequently it is an isomorphism whenever `f` is a
homeomorphism onto a closed subset, by
`Stacks.ClosedEmbeddingProjectionFormula.isIso_projectionFormulaMap'_of_isClosedEmbedding`.

## Main definitions

* `Stacks.ProjectionFormula.projectionFormulaMapRight'`: the morphism
  `F ⊗_{𝒪_Y} f_*G ⟶ f_*(f^*F ⊗_{𝒪_X} G)`.

## Main results

* `Stacks.ProjectionFormula.adjunctionTensorMapSnd_eq_comp`: in the abstract, the construction
  with the counit in the second factor is the one with the counit in the first, conjugated by
  morphisms exchanging the two arguments of the bifunctors that are compatible with the
  comparison and the counit.
* `Stacks.ProjectionFormula.projectionFormulaMapRight'_natural`: naturality in both arguments.
* `Stacks.ProjectionFormula.map_projectionFormulaMapRight'_comp_counit`: its defining transpose
  relation.
* `Stacks.ProjectionFormula.projectionFormulaMapRight'_eq_braiding`: it is the left-handed
  morphism conjugated by the two symmetry constraints.
* `Stacks.ClosedEmbeddingProjectionFormula.isIso_projectionFormulaMapRight'_of_isClosedEmbedding`:
  it is an isomorphism for a homeomorphism onto a closed subset and arbitrary `F` and `G`.

## Implementation notes

The comparison with the left-handed morphism is proved after transposing along `f^* ⊣ f_*`.
Only one compatibility is not formal: that the comparison of [Stacks, Tag 01CD] commutes with
the symmetry constraints, which is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`.  The symmetry constraint
used is that of `Stacks.PullbackTensorCoherence.braidedCategory`, whose whiskerings are the
action of the tensor product sheaf on morphisms by
`Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor` and `whiskerRight_eq_sheafTensor`.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

/-! ### The abstract comparison of the two one-sided constructions -/

section Abstract

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The projection-formula map with the counit in the second factor, as a conjugate of the one
with the counit in the first.**  For an adjunction `L ⊣ R`, bifunctors `A`, `B` and a comparison
`α : A ⋙ L ⟶ (L × L) ⋙ B`, suppose given `a : A (H, R G) ⟶ A (R G, H)` and morphisms `b`, `b'`
exchanging the two arguments of `B` which commute with the counit, and suppose `L a` carries `α`
at `(R G, H)` followed by `b'` to `α` at `(H, R G)`.  Then
`CategoryTheory.adjunctionTensorMap` conjugated by `a` and `R b` is
`adjunctionTensorMapSnd`.

In the intended instance `a`, `b` and `b'` are symmetry constraints of a symmetric monoidal
structure.  Every morphism is an explicit binder, so that the instance is applied by `exact`. -/
theorem adjunctionTensorMapSnd_eq_comp (H : C) (G : D)
    (a : A.obj (H, R.obj G) ⟶ A.obj (R.obj G, H))
    (b : B.obj (G, L.obj H) ⟶ B.obj (L.obj H, G))
    (b' : B.obj (L.obj (R.obj G), L.obj H) ⟶ B.obj (L.obj H, L.obj (R.obj G)))
    (hb : B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) ≫ b =
      b' ≫ B.map (𝟙 (L.obj H) ×ₘ adj.counit.app G))
    (h : L.map a ≫ α.app (R.obj G, H) ≫ b' = α.app (H, R.obj G)) :
    adjunctionTensorMapSnd adj A B α H G =
      a ≫ adjunctionTensorMap adj A B α G H ≫ R.map b := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adjunctionTensorMapSnd, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  rw [map_comp_map_map_comp_counit, map_adjunctionTensorMap_comp_counit, Category.assoc, hb, ← h]
  simp only [Category.assoc]

end Abstract

/-! ### The right-handed morphism on a ringed space -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The projection-formula morphism with the pushforward on the right**,
`F ⊗_{𝒪_Y} f_*G ⟶ f_*(f^*F ⊗_{𝒪_X} G)`, for a morphism of ringed spaces `f`, a sheaf of
`𝒪_Y`-modules `F` and a sheaf of `𝒪_X`-modules `G`: the adjoint transpose of the comparison of
[Stacks, Tag 01CD] followed by the counit of `f^* ⊣ f_*` in the right tensor factor.  It exists
for every `f`. -/
def projectionFormulaMapRight' (F : SheafOfModules.{u} (structureRingSheaf Y))
    (G : SheafOfModules.{u} (structureRingSheaf X)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
        (F, (pushforwardFunctor f).obj G) ⟶
      (pushforwardFunctor f).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj
          ((pullbackFunctor f).obj F, G)) :=
  adjunctionTensorMapSnd (pullbackAdjunction f)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf))
    (comparisonNatTrans f) F G

/-- The right-handed projection-formula morphism is natural in both module arguments. -/
@[reassoc]
lemma projectionFormulaMapRight'_natural
    {F F' : SheafOfModules.{u} (structureRingSheaf Y)}
    {G G' : SheafOfModules.{u} (structureRingSheaf X)} (k : F ⟶ F') (g : G ⟶ G') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).map
        (k ×ₘ (pushforwardFunctor f).map g) ≫ projectionFormulaMapRight' f F' G' =
      projectionFormulaMapRight' f F G ≫ (pushforwardFunctor f).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
          ((pullbackFunctor f).map k ×ₘ g)) :=
  adjunctionTensorMapSnd_natural (pullbackAdjunction f)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf))
    (comparisonNatTrans f) k g

/-- **The right-handed projection-formula morphism, transposed.**  Pulling it back along `f` and
following with the counit of `f^* ⊣ f_*` gives the comparison of [Stacks, Tag 01CD] followed by
the counit in the right tensor factor.  There is no hypothesis on `f`. -/
@[reassoc]
lemma map_projectionFormulaMapRight'_comp_counit
    (F : SheafOfModules.{u} (structureRingSheaf Y))
    (G : SheafOfModules.{u} (structureRingSheaf X)) :
    (pullbackFunctor f).map (projectionFormulaMapRight' f F G) ≫
        (pullbackAdjunction f).counit.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj
            ((pullbackFunctor f).obj F, G)) =
      (comparisonNatTrans f).app (F, (pushforwardFunctor f).obj G) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
          (𝟙 ((pullbackFunctor f).obj F) ×ₘ (pullbackAdjunction f).counit.app G) := by
  have h := ((pullbackAdjunction f).homEquiv
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
        (F, (pushforwardFunctor f).obj G))
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj
        ((pullbackFunctor f).obj F, G))).symm_apply_apply
    ((comparisonNatTrans f).app (F, (pushforwardFunctor f).obj G) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
        (𝟙 ((pullbackFunctor f).obj F) ×ₘ (pullbackAdjunction f).counit.app G))
  exact h

section Braiding

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

-- `structureSheafRing` is `@[instance_reducible]`, so it unfolds at `implicit`
-- transparency already, but its reduct stops at an explicit-constructor projection while
-- `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`; these two Mathlib
-- definitions are the gap between them.
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **The right-handed projection-formula morphism is the left-handed one conjugated by the
symmetry constraints** of [Stacks, Tag 01CA]:
`F ⊗ f_*G ≅ f_*G ⊗ F ⟶ f_*(G ⊗ f^*F) ≅ f_*(f^*F ⊗ G)`.

This is `adjunctionTensorMapSnd_eq_comp`; its one non-formal hypothesis is the compatibility of
the comparison of [Stacks, Tag 01CD] with the symmetry constraints,
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`, and the other is the
naturality of the symmetry constraint, read through the identification of the whiskerings with
the tensor product sheaf on morphisms. -/
theorem projectionFormulaMapRight'_eq_braiding
    (F : SheafOfModules.{u} (structureRingSheaf Y))
    (G : SheafOfModules.{u} (structureRingSheaf X)) :
    projectionFormulaMapRight' f F G =
      (β_ ((pushforwardFunctor f).obj G) F).inv ≫ projectionFormulaMap' f G F ≫
        (pushforwardFunctor f).map (β_ G ((pullbackFunctor f).obj F)).hom := by
  have hr : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
        ((pullbackAdjunction f).counit.app G ×ₘ 𝟙 ((pullbackFunctor f).obj F)) =
      (pullbackAdjunction f).counit.app G ▷ (pullbackFunctor f).obj F := by
    refine Eq.trans ?_ (Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor X.sheaf
      ((pullbackAdjunction f).counit.app G) ((pullbackFunctor f).obj F)).symm
    exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have hl : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
        (𝟙 ((pullbackFunctor f).obj F) ×ₘ (pullbackAdjunction f).counit.app G) =
      (pullbackFunctor f).obj F ◁ (pullbackAdjunction f).counit.app G := by
    refine Eq.trans ?_ (Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor X.sheaf
      ((pullbackFunctor f).obj F) ((pullbackAdjunction f).counit.app G)).symm
    exact (congrArg (· ≫ _) ((NatTrans.congr_app (CategoryTheory.Functor.map_id _ _) _).trans
      (NatTrans.id_app _ _))).trans (Category.id_comp _)
  have hn := BraidedCategory.braiding_naturality_left ((pullbackAdjunction f).counit.app G)
    ((pullbackFunctor f).obj F)
  have h2 := Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding f
    ((pushforwardFunctor f).obj G) F
  have h : (pullbackFunctor f).map (β_ ((pushforwardFunctor f).obj G) F).inv ≫
        Stacks.PullbackTensorCoherence.pullbackTensorComparison f ((pushforwardFunctor f).obj G) F ≫
          (β_ ((pullbackFunctor f).obj ((pushforwardFunctor f).obj G))
            ((pullbackFunctor f).obj F)).hom =
      Stacks.PullbackTensorCoherence.pullbackTensorComparison f F
        ((pushforwardFunctor f).obj G) := by
    rw [← h2, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    exact (congrArg (· ≫ _) ((pullbackFunctor f).map_id _)).trans (Category.id_comp _)
  exact adjunctionTensorMapSnd_eq_comp (pullbackAdjunction f)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf))
    (comparisonNatTrans f) F G (a := (β_ ((pushforwardFunctor f).obj G) F).inv)
    (b := (β_ G ((pullbackFunctor f).obj F)).hom)
    (b' := (β_ ((pullbackFunctor f).obj ((pushforwardFunctor f).obj G))
      ((pullbackFunctor f).obj F)).hom)
    ((congrArg (· ≫ _) hr).trans (hn.trans (congrArg (_ ≫ ·) hl.symm))) h

end Braiding

end Stacks.ProjectionFormula

namespace Stacks.ClosedEmbeddingProjectionFormula

open Stacks.ProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The ordinary projection formula with the pushforward on the right, for a closed
embedding.**  For a morphism of ringed spaces whose underlying continuous map is a homeomorphism
onto a closed subset and *arbitrary* sheaves of modules `F` on `Y` and `G` on `X`, the morphism
`F ⊗_{𝒪_Y} f_*G ⟶ f_*(f^*F ⊗_{𝒪_X} G)` is an isomorphism.

It is the left-handed morphism conjugated by two symmetry constraints, by
`Stacks.ProjectionFormula.projectionFormulaMapRight'_eq_braiding`, and the left-handed morphism
is invertible by `isIso_projectionFormulaMap'_of_isClosedEmbedding`. -/
theorem isIso_projectionFormulaMapRight'_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (F : SheafOfModules.{u} (structureRingSheaf Y))
    (G : SheafOfModules.{u} (structureRingSheaf X)) :
    IsIso (projectionFormulaMapRight' f F G) := by
  have hpf := isIso_projectionFormulaMap'_of_isClosedEmbedding f G F hf
  let := Stacks.PullbackGradedAlgebra.monoidalCategory X
  let := Stacks.PullbackGradedAlgebra.monoidalCategory Y
  let := Stacks.PullbackTensorCoherence.braidedCategory X
  let := Stacks.PullbackTensorCoherence.braidedCategory Y
  rw [projectionFormulaMapRight'_eq_braiding]
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (IsIso.comp_isIso' hpf ((pushforwardFunctor f).mapIso (β_ G _)).isIso_hom)

/-- **The projection-formula isomorphism with the pushforward on the right, for a closed
embedding**, `F ⊗_{𝒪_Y} f_*G ≅ f_*(f^*F ⊗_{𝒪_X} G)`, whose forward map is
`Stacks.ProjectionFormula.projectionFormulaMapRight'`. -/
def projectionFormulaIsoRight
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (F : SheafOfModules.{u} (structureRingSheaf Y))
    (G : SheafOfModules.{u} (structureRingSheaf X)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
        (F, (pushforwardFunctor f).obj G) ≅
      (pushforwardFunctor f).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj
          ((pullbackFunctor f).obj F, G)) :=
  have := isIso_projectionFormulaMapRight'_of_isClosedEmbedding f hf F G
  asIso (projectionFormulaMapRight' f F G)

end Stacks.ClosedEmbeddingProjectionFormula

end

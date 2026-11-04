module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# The derived tensor product of a ringed site read at two models of the derived category

`HasDerivedCategory` is a *choice* of a localization of the cochain complexes at the
quasi-isomorphisms, and the repository works with two choices side by side: the standard one and
the locally small one of Tag 079Q. The derived tensor product of Tag 06YU,
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, takes the model as an instance
argument, so it exists at both, and nothing so far compares the two. This file does: given a
functor `G` from one model to the other compatible with the two localization functors, the
derived tensor product at the first model followed by `G` is the derived tensor product at the
second model of the images under `G`, naturally in both variables.

## Main definitions

* `StacksDraft.DerivedModel.lifting₂WhiskeringLeft`: a descent of a bifunctor along a
  localization `L₂` is, after precomposing in both variables with a functor `G` carrying `L₁` to
  `L₂`, a descent along `L₁`.
* `StacksDraft.DerivedModel.lift₂ModelIso`: two descents of matching bifunctors along `L₁` and
  `L₂` agree up to `G`.
* `StacksDraft.DerivedModel.derivedTensorModelIso`: the same for the derived tensor product of a
  ringed site, at any two models `i₁` and `i₂` and any two derived tensor products in the sense
  of Tag 06YU.
* `StacksDraft.DerivedModel.derivedTensorModelIsoApp`: its component at a pair of objects.

## Implementation notes

Both derived tensor products descend the total tensor product of K-flat complexes along the
functor from the K-flat complexes to the derived category
(`Stacks.SheafOfModules.DerivedMonoidal.tensorLifting`), and the K-flat complexes localize to
either model (`Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ_isLocalization`). So the
comparison is `CategoryTheory.Localization.lift₂NatIso` along the K-flat localization of the
*first* model, the descent at the second model being read along it through `G`. No coherence is
checked by hand.

Nothing here carries a project tag: the statement is about two Lean choices of one mathematical
object, and the source has nothing to say about it. The two models are always passed explicitly,
never left to instance search, for the reason recorded in
`StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe u d d₁ d₂

namespace StacksDraft.DerivedModel

/-! ### Two descents of one bifunctor along two localizations -/

section Abstract

variable {A : Type*} [Category* A] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  (L₁ : A ⥤ D₁) (L₂ : A ⥤ D₂) (W : MorphismProperty A) (G : D₁ ⥤ D₂)

/-- **A descent along `L₂`, read along `L₁` through `G`.** If `T₂` descends `S₂` along `L₂` in
both variables and `e : L₁ ⋙ G ≅ L₂`, then `T₂` precomposed with `G` in both variables descends
`S₂` along `L₁`. -/
@[instance_reducible]
def lifting₂WhiskeringLeft (S₂ : A ⥤ A ⥤ D₂) (T₂ : D₂ ⥤ D₂ ⥤ D₂)
    [Localization.Lifting₂ L₂ L₂ W W S₂ T₂] (e : L₁ ⋙ G ≅ L₂) :
    Localization.Lifting₂ L₁ L₁ W W S₂ ((((whiskeringLeft₂ D₂).obj G).obj G).obj T₂) where
  iso :=
    (Iso.refl _ : (((whiskeringLeft₂ D₂).obj L₁).obj L₁).obj
        ((((whiskeringLeft₂ D₂).obj G).obj G).obj T₂) ≅
      (((whiskeringLeft₂ D₂).obj (L₁ ⋙ G)).obj (L₁ ⋙ G)).obj T₂) ≪≫
    (((whiskeringLeft₂ D₂).mapIso e).app (L₁ ⋙ G)).app T₂ ≪≫
    (((whiskeringLeft₂ D₂).obj L₂).mapIso e).app T₂ ≪≫
    Localization.Lifting₂.iso L₂ L₂ W W S₂ T₂

variable [L₁.IsLocalization W] [W.ContainsIdentities]

/-- **Two descents of matching bifunctors agree up to the comparison.** Let `T₁` descend `S₁`
along `L₁` and `T₂` descend `S₂` along `L₂`, in both variables, and let `G` carry `L₁` to `L₂`
and `S₁` to `S₂`. Then `T₁` followed by `G` is `T₂` precomposed with `G` in both variables.
Both are descents of `S₂` along the localization `L₁`, so this is
`CategoryTheory.Localization.lift₂NatIso`. -/
def lift₂ModelIso (S₁ : A ⥤ A ⥤ D₁) (S₂ : A ⥤ A ⥤ D₂) (T₁ : D₁ ⥤ D₁ ⥤ D₁)
    (T₂ : D₂ ⥤ D₂ ⥤ D₂) [Localization.Lifting₂ L₁ L₁ W W S₁ T₁]
    [Localization.Lifting₂ L₂ L₂ W W S₂ T₂] (e : L₁ ⋙ G ≅ L₂)
    (σ : S₁ ⋙ (whiskeringRight A D₁ D₂).obj G ≅ S₂) :
    T₁ ⋙ (whiskeringRight D₁ D₁ D₂).obj G ≅ (((whiskeringLeft₂ D₂).obj G).obj G).obj T₂ :=
  letI := lifting₂WhiskeringLeft L₁ L₂ W G S₂ T₂ e
  Localization.lift₂NatIso L₁ L₁ W W (S₁ ⋙ (whiskeringRight A D₁ D₂).obj G) S₂
    (T₁ ⋙ (whiskeringRight D₁ D₁ D₂).obj G) ((((whiskeringLeft₂ D₂).obj G).obj G).obj T₂) σ

end Abstract

/-! ### The derived tensor product of a ringed site at two models -/

section DerivedTensor

open Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (i₁ : HasDerivedCategory.{d₁} (Mod R)) (i₂ : HasDerivedCategory.{d₂} (Mod R))
  (G : @DerivedCategory (Mod R) _ _ i₁ ⥤ @DerivedCategory (Mod R) _ _ i₂)
  (hQ : @DerivedCategory.Q (Mod R) _ _ i₁ ⋙ G ≅ @DerivedCategory.Q (Mod R) _ _ i₂)

/-- The bifunctor of a derived tensor product in the sense of Tag 06YU at the model `i`, with the
model passed explicitly. -/
abbrev tensorAt (i : HasDerivedCategory.{d} (Mod R))
    (T : @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct C _ J R _ _ i _ _ _) :=
  @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensor C _ J R _ _ i _ _ _ T

/-- The functor from the K-flat complexes into the first model, followed by `G`, is the functor
into the second model. -/
def kFlatComplexQModelIso :
    @kFlatComplexQ C _ J R _ _ i₁ ⋙ G ≅ @kFlatComplexQ C _ J R _ _ i₂ :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (KFlatComplexes R).ι hQ

/-- The total tensor product of K-flat complexes, pushed into the first model and then along `G`,
is the total tensor product pushed into the second model. -/
def kFlatTensorSourceModelIso :
    @kFlatTensorSource C _ J R _ _ i₁ ⋙ (whiskeringRight _ _ _).obj G ≅
      @kFlatTensorSource C _ J R _ _ i₂ :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ hQ.app _)
      (fun g ↦ hQ.hom.naturality _))
    (fun f ↦ by
      ext Y
      exact hQ.hom.naturality _)

/-- **The derived tensor product does not depend on the model, up to the comparison.** For any
two models `i₁` and `i₂` of `D(Mod(O))`, any functor `G` between them compatible with the two
localization functors, and any two derived tensor products `T₁` and `T₂` in the sense of
Tag 06YU at the two models, `G(A ⊗^𝐋 B)` is `G(A) ⊗^𝐋 G(B)`, naturally in `A` and `B`. -/
def derivedTensorModelIso
    (T₁ : @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct C _ J R _ _ i₁ _ _ _)
    (T₂ : @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct C _ J R _ _ i₂ _ _ _) :
    tensorAt R i₁ T₁ ⋙ (whiskeringRight _ _ _).obj G ≅
      (((whiskeringLeft₂ _).obj G).obj G).obj (tensorAt R i₂ T₂) :=
  letI := @tensorLifting C _ J R _ _ i₁ T₁
  letI := @tensorLifting C _ J R _ _ i₂ T₂
  haveI := @kFlatComplexQ_isLocalization C _ J R _ _ i₁
  lift₂ModelIso (@kFlatComplexQ C _ J R _ _ i₁) (@kFlatComplexQ C _ J R _ _ i₂)
    (kFlatComplexQuasiIso R) G (@kFlatTensorSource C _ J R _ _ i₁)
    (@kFlatTensorSource C _ J R _ _ i₂) (tensorAt R i₁ T₁) (tensorAt R i₂ T₂)
    (kFlatComplexQModelIso R i₁ i₂ G hQ) (kFlatTensorSourceModelIso R i₁ i₂ G hQ)

/-- The component of `StacksDraft.DerivedModel.derivedTensorModelIso` at a pair of objects:
`G(A ⊗^𝐋 B) ≅ G(A) ⊗^𝐋 G(B)`. -/
def derivedTensorModelIsoApp
    (T₁ : @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct C _ J R _ _ i₁ _ _ _)
    (T₂ : @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct C _ J R _ _ i₂ _ _ _)
    (A B : @DerivedCategory (Mod R) _ _ i₁) :
    G.obj (((tensorAt R i₁ T₁).obj A).obj B) ≅
      ((tensorAt R i₂ T₂).obj (G.obj A)).obj (G.obj B) :=
  ((derivedTensorModelIso R i₁ i₂ G hQ T₁ T₂).app A).app B

/-- **Naturality of the comparison in both variables at once**: `G` of the tensor product of two
morphisms, followed by the comparison, is the comparison followed by the tensor product of their
images under `G`. -/
theorem derivedTensorModelIsoApp_naturality
    (T₁ : @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct C _ J R _ _ i₁ _ _ _)
    (T₂ : @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct C _ J R _ _ i₂ _ _ _)
    {A A' B B' : @DerivedCategory (Mod R) _ _ i₁} (x : A ⟶ A') (y : B ⟶ B') :
    G.map (((tensorAt R i₁ T₁).map x).app B ≫ ((tensorAt R i₁ T₁).obj A').map y) ≫
        (derivedTensorModelIsoApp R i₁ i₂ G hQ T₁ T₂ A' B').hom =
      (derivedTensorModelIsoApp R i₁ i₂ G hQ T₁ T₂ A B).hom ≫
        (((tensorAt R i₂ T₂).map (G.map x)).app (G.obj B) ≫
          ((tensorAt R i₂ T₂).obj (G.obj A')).map (G.map y)) := by
  have h₁ := congrArg (fun τ ↦ τ.app B)
    ((derivedTensorModelIso R i₁ i₂ G hQ T₁ T₂).hom.naturality x)
  have h₂ := ((derivedTensorModelIso R i₁ i₂ G hQ T₁ T₂).hom.app A').naturality y
  simp only [NatTrans.comp_app] at h₁
  dsimp at h₁ h₂
  simp only [derivedTensorModelIsoApp, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [h₂, ← Category.assoc, h₁, Category.assoc]

end DerivedTensor

end StacksDraft.DerivedModel

end

module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoxSheafHomMapNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtIsomorphism

/-!
# Invertibility of transposes at a pure pair

Read through the evaluation bijection `Stacks.Cohomology.DerivedKunnethExt.sheafHomEvalEquiv`, a
morphism `x : C ⟶ R𝓗om(K, K)` becomes `C ⊗^𝐋 K ⟶ K`.  This file records when that transpose is an
isomorphism, and that the property is preserved by the comparison `boxSheafHomMap` at a pure pair.

## Main results

* `CategoryTheory.isIso_of_bijective_precomp`: a morphism precomposition with which is bijective
  onto every object is an isomorphism.
* `Stacks.Cohomology.DerivedKunnethExt.isIso_sheafHomEvalEquiv_of_bijective`: the transpose of `x`
  is an isomorphism as soon as `φ ↦ x ≫ R𝓗om(K, φ)` is a bijection onto every target.
* `Stacks.Cohomology.DerivedKunnethExt.injective_comp_map_of_isIso`: if the transpose of `s` is an
  isomorphism then `χ ↦ s ≫ R𝓗om(Z, χ)` is injective.
* `Stacks.Cohomology.DerivedKunnethExt.isIso_sheafHomEvalEquiv_boxSheafHomMap`: for `x`, `y` with
  invertible transposes and an isomorphism `u`, the transpose of
  `u ≫ (Lp^*x ⊗ Lq^*y) ≫ boxSheafHomMap` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace CategoryTheory

/-- **A morphism precomposition with which is bijective onto every object is an isomorphism.** -/
theorem isIso_of_bijective_precomp {C : Type*} [Category C] {A B : C} (θ : A ⟶ B)
    (h : ∀ T : C, Function.Bijective (fun φ : B ⟶ T => θ ≫ φ)) : IsIso θ := by
  obtain ⟨g, hg⟩ := (h A).2 (𝟙 A)
  have hg' : θ ≫ g = 𝟙 A := hg
  exact ⟨⟨g, hg', (h B).1 (by simp [reassoc_of% hg'])⟩⟩

end CategoryTheory

namespace Stacks.Cohomology.DerivedKunnethExt

attribute [local instance] HasDerivedCategory.standard

-- As in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtIsomorphism`: the
-- derived categories of this file are those of `SheafOfModules.instAbelian`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local implicit_reducible] CategoryTheory.sheafCompose

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The transpose of `x : C ⟶ R𝓗om(K, K)` is an isomorphism** as soon as `φ ↦ x ≫ R𝓗om(K, φ)`
is a bijection onto every target. -/
theorem isIso_sheafHomEvalEquiv_of_bijective {C K : DerivedCategory (Mod Z.sheaf)}
    (x : C ⟶ sheafHomObj Z K K)
    (hx : ∀ T : DerivedCategory (Mod Z.sheaf), Function.Bijective (fun φ : K ⟶ T =>
      x ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op K)).map φ)) :
    IsIso (sheafHomEvalEquiv Z C K K x) := by
  refine CategoryTheory.isIso_of_bijective_precomp _ fun T => ?_
  have hf : (fun φ : K ⟶ T => sheafHomEvalEquiv Z C K K x ≫ φ) = sheafHomEvalEquiv Z C K T ∘
      fun φ => x ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op K)).map φ := by
    funext φ
    simp only [Function.comp_apply, sheafHomEvalEquiv_comp_map]
  rw [hf]
  exact (sheafHomEvalEquiv Z C K T).bijective.comp (hx T)

/-- **If the transpose of `s : C ⟶ R𝓗om(Z₀, Z₀)` is an isomorphism, `χ ↦ s ≫ R𝓗om(Z₀, χ)` is
injective**: its transpose is the transpose of `s` followed by `χ`. -/
theorem injective_comp_map_of_isIso {C Z₀ Z' : DerivedCategory (Mod Z.sheaf)}
    (s : C ⟶ sheafHomObj Z Z₀ Z₀) (hs : IsIso (sheafHomEvalEquiv Z C Z₀ Z₀ s)) :
    Function.Injective (fun χ : Z₀ ⟶ Z' =>
      s ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op Z₀)).map χ) := by
  intro χ χ' h
  have h' := congrArg (sheafHomEvalEquiv Z C Z₀ Z') h
  simp only [sheafHomEvalEquiv_comp_map] at h'
  exact (cancel_epi _).1 h'

/-- Postcomposition with `R𝓗om(Z₀, -)` after a fixed morphism is additive. -/
theorem comp_map_add {C Z₀ Z' : DerivedCategory (Mod Z.sheaf)} (s : C ⟶ sheafHomObj Z Z₀ Z₀)
    (χ χ' : Z₀ ⟶ Z') :
    s ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op Z₀)).map (χ + χ') =
      s ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op Z₀)).map χ +
        s ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op Z₀)).map χ' := by
  have : ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op Z₀)).Additive :=
    AlgebraicGeometry.RingedSite.additive_derivedSheafHom_obj
      (Stacks.SheafOfModules.ringedSite Z.sheaf) Z₀
  rw [Functor.map_add, Preadditive.comp_add]

/-- The flip of the middle two factors is an isomorphism. -/
instance isIso_middleFour (H G A B : DerivedCategory (Mod Z.sheaf)) :
    IsIso (middleFour Z H G A B) := by
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  exact ⟨⟨tensorδ H G A B, tensorμ_tensorδ H G A B, tensorδ_tensorμ H G A B⟩⟩

end OneSpace

section Box

variable {X Y W : RingedSpace.{u, u}} (p : W ⟶ X) (q : W ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison `boxSheafHomMap` at a pure pair has an invertible transpose** when the two
factors do: for `x : C ⟶ R𝓗om(K, K)` on `X` and `y : D ⟶ R𝓗om(M, M)` on `Y` with invertible
transposes and an isomorphism `u : E ⟶ Lp^*C ⊗^𝐋 Lq^*D`, the transpose of
`u ≫ (Lp^*x ⊗ Lq^*y) ≫ boxSheafHomMap` is an isomorphism.  By
`Stacks.Cohomology.DerivedKunnethExt.sheafHomEvalEquiv_tensorMap_comp_boxSheafHomMap` it is a
composite of isomorphisms. -/
theorem isIso_sheafHomEvalEquiv_boxSheafHomMap {C K : DerivedCategory (Mod X.sheaf)}
    {D M : DerivedCategory (Mod Y.sheaf)} {E : DerivedCategory (Mod W.sheaf)}
    (x : C ⟶ sheafHomObj X K K) (y : D ⟶ sheafHomObj Y M M)
    (u : E ⟶ tensorObj W ((derivedPullbackFunctor p).obj C) ((derivedPullbackFunctor q).obj D))
    [IsIso u] [IsIso (sheafHomEvalEquiv X C K K x)] [IsIso (sheafHomEvalEquiv Y D M M y)] :
    IsIso (sheafHomEvalEquiv W E _ _ (u ≫ tensorMap W ((derivedPullbackFunctor p).map x)
      ((derivedPullbackFunctor q).map y) ≫ boxSheafHomMap p q K K M M)) := by
  rw [sheafHomEvalEquiv_comp, sheafHomEvalEquiv_tensorMap_comp_boxSheafHomMap]
  have := isIso_tensorMap W u (𝟙 (tensorObj W ((derivedPullbackFunctor p).obj K)
    ((derivedPullbackFunctor q).obj M))) inferInstance inferInstance
  have := isIso_tensorMap W ((pullbackEvalIso p C K).hom ≫
      (derivedPullbackFunctor p).map (sheafHomEvalEquiv X C K K x))
    ((pullbackEvalIso q D M).hom ≫ (derivedPullbackFunctor q).map (sheafHomEvalEquiv Y D M M y))
    inferInstance inferInstance
  infer_instance

/-- **Postcomposition with a pure-pair composite is injective.** For `x : C ⟶ R𝓗om(K, K)` on `X`
and `y : D ⟶ R𝓗om(M, M)` on `Y` such that `φ ↦ x ≫ R𝓗om(K, φ)` and `ψ ↦ y ≫ R𝓗om(M, ψ)` are
bijections onto every target, and an isomorphism `u`, the map
`χ ↦ (u ≫ (Lp^*x ⊗ Lq^*y) ≫ boxSheafHomMap) ≫ R𝓗om(K ⊠ M, χ)` is injective.  The statement
mentions only composites, so it can be read at any spelling of the objects. -/
theorem injective_comp_map_boxSheafHomMap {C K : DerivedCategory (Mod X.sheaf)}
    {D M : DerivedCategory (Mod Y.sheaf)} {E : DerivedCategory (Mod W.sheaf)}
    (x : C ⟶ sheafHomObj X K K) (y : D ⟶ sheafHomObj Y M M)
    (u : E ⟶ tensorObj W ((derivedPullbackFunctor p).obj C) ((derivedPullbackFunctor q).obj D))
    (hu : IsIso u)
    (hx : ∀ T : DerivedCategory (Mod X.sheaf), Function.Bijective (fun φ : K ⟶ T =>
      x ≫ ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).map φ))
    (hy : ∀ T : DerivedCategory (Mod Y.sheaf), Function.Bijective (fun ψ : M ⟶ T =>
      y ≫ ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op M)).map ψ))
    (Z' : DerivedCategory (Mod W.sheaf)) :
    Function.Injective (fun χ : boxProd p q K M ⟶ Z' =>
      (u ≫ tensorMap W ((derivedPullbackFunctor p).map x) ((derivedPullbackFunctor q).map y) ≫
        boxSheafHomMap p q K K M M) ≫
        ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op (boxProd p q K M))).map χ) := by
  have := hu
  have := isIso_sheafHomEvalEquiv_of_bijective X x hx
  have := isIso_sheafHomEvalEquiv_of_bijective Y y hy
  exact injective_comp_map_of_isIso W _ (isIso_sheafHomEvalEquiv_boxSheafHomMap p q x y u)

/-- **The pure-pair composite against a pure map of targets.**  Postcomposing
`u ≫ (Lp^*x ⊗ Lq^*y) ≫ boxSheafHomMap` with `R𝓗om(K ⊠ M, φ ⊠ ψ)` moves `φ` and `ψ` onto `x` and
`y`: this is the naturality of `boxSheafHomMap` in its targets
(`Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap_naturality_target`). -/
theorem comp_boxSheafHomMap_map {C K K' : DerivedCategory (Mod X.sheaf)}
    {D M M' : DerivedCategory (Mod Y.sheaf)} {E : DerivedCategory (Mod W.sheaf)}
    (x : C ⟶ sheafHomObj X K K) (y : D ⟶ sheafHomObj Y M M)
    (u : E ⟶ tensorObj W ((derivedPullbackFunctor p).obj C) ((derivedPullbackFunctor q).obj D))
    (φ : K ⟶ K') (ψ : M ⟶ M') :
    (u ≫ tensorMap W ((derivedPullbackFunctor p).map x) ((derivedPullbackFunctor q).map y) ≫
        boxSheafHomMap p q K K M M) ≫
        ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op (boxProd p q K M))).map
          (tensorMap W ((derivedPullbackFunctor p).map φ) ((derivedPullbackFunctor q).map ψ)) =
      u ≫ tensorMap W ((derivedPullbackFunctor p).map
          (x ≫ ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).map φ))
        ((derivedPullbackFunctor q).map
          (y ≫ ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op M)).map ψ)) ≫
        boxSheafHomMap p q K K' M M' := by
  rw [Category.assoc, Category.assoc, ← boxSheafHomMap_naturality_target, ← Category.assoc
    (tensorMap W _ _), tensorMap_comp, Functor.map_comp, Functor.map_comp]

/-- `comp_boxSheafHomMap_map` with the two composites `x ≫ R𝓗om(K, φ)` and `y ≫ R𝓗om(M, ψ)`
named. -/
theorem comp_boxSheafHomMap_map_of_eq {C K K' : DerivedCategory (Mod X.sheaf)}
    {D M M' : DerivedCategory (Mod Y.sheaf)} {E : DerivedCategory (Mod W.sheaf)}
    (x : C ⟶ sheafHomObj X K K) (y : D ⟶ sheafHomObj Y M M)
    (u : E ⟶ tensorObj W ((derivedPullbackFunctor p).obj C) ((derivedPullbackFunctor q).obj D))
    (φ : K ⟶ K') (ψ : M ⟶ M') (x' : C ⟶ sheafHomObj X K K') (y' : D ⟶ sheafHomObj Y M M')
    (hx : x ≫ ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).map φ = x')
    (hy : y ≫ ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op M)).map ψ = y') :
    (u ≫ tensorMap W ((derivedPullbackFunctor p).map x) ((derivedPullbackFunctor q).map y) ≫
        boxSheafHomMap p q K K M M) ≫
        ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op (boxProd p q K M))).map
          (tensorMap W ((derivedPullbackFunctor p).map φ) ((derivedPullbackFunctor q).map ψ)) =
      u ≫ tensorMap W ((derivedPullbackFunctor p).map x') ((derivedPullbackFunctor q).map y') ≫
        boxSheafHomMap p q K K' M M' := by
  subst hx hy
  exact comp_boxSheafHomMap_map p q x y u φ ψ

end Box

end Stacks.Cohomology.DerivedKunnethExt

end

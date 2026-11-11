module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceParasitic
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceNonExact
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceReflectsExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInternalHomRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceTensor

/-!
# Stacks 0GQS: the restrictions `a`, `b`, `c`, `d` of modules to an algebraic space

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks with `𝒰` the algebraic stack of an
algebraic space `U`, and let `a : ℱ ↦ f^*ℱ|_{U_étale}` and its restrictions `b`, `c`, `d` to
`LQCoh(𝒪_𝒳)`, `LQCoh^fbc(𝒪_𝒳)` and `QCoh(𝒪_𝒳)` be as in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionToAlgebraicSpaceQuasicoherent.lean`. This file
proves item (11) of Stacks 0GQS and collects all its items in one statement.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.acyclic_iff_acyclic_qcohSpaceRestriction`: item (11),
  for `f` flat and surjective, `d` preserves and reflects exactness of complexes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.spaceRestriction_properties`: **Stacks 0GQS**, all
  its items.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- **Stacks 0GQS, item (11).** If `f` is flat and surjective, a complex `ℱ^•` of `QCoh(𝒪_𝒳)` is
exact if and only if `d(ℱ^•)` is exact.

`d` is exact (items (4) and (5)), so it commutes with cohomology; and an object `𝒢` of
`QCoh(𝒪_𝒳)` with `d(𝒢) = 0` is parasitic by item (10), hence zero, being quasi-coherent. -/
theorem acyclic_iff_acyclic_qcohSpaceRestriction (hf : AlgebraicStacks.IsFlat B S hS f)
    (hsurj : Stack.IsSurjective B S hS f)
    (K : CochainComplex (AlgebraicStacks.quasicoherentModules B S hS 𝒳) ℤ) :
    K.Acyclic ↔
      (((qcohSpaceRestriction B S hS 𝒳 U hU f).mapHomologicalComplex _).obj K).Acyclic := by
  have := preservesFiniteLimits_qcohSpaceRestriction_of_isFlat B S hS 𝒳 U hU f hf
  have := preservesFiniteColimits_qcohSpaceRestriction B S hS 𝒳 U hU f
  let := Space.abelian_quasicoherentSheaves_algebraicSpace B S hS ⟨U, hU⟩
  refine (Functor.acyclic_mapHomologicalComplex_iff (qcohSpaceRestriction B S hS 𝒳 U hU f)
    (fun G hG => ?_) _ K).symm
  exact isZero_of_isParasitic B S hS 𝒳 G
    (isParasitic_of_isZero_lqcohFbcSpaceRestriction_obj B S hS 𝒳 U hU f hf hsurj
      ((qcohToLqcohFbc B S hS 𝒳).obj G) hG)

section Statement

attribute [local instance] Space.modulesMonoidalCategory hasSheafCompose_forget_ringCat
  quasicoherentModulesMonoidal

/-- **Stacks 0GQS.** Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks with `𝒰` the algebraic
stack of an algebraic space `U`; let `a : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(U_étale, 𝒪_U)`,
`ℱ ↦ f^*ℱ|_{U_étale}`, and let `b`, `c`, `d` be its restrictions to `LQCoh(𝒪_𝒳)`,
`LQCoh^fbc(𝒪_𝒳)` and `QCoh(𝒪_𝒳)`, with values in `QCoh(U_étale, 𝒪_U)`. Then, in the order of
the source:
1. `a` is exact;
2. `b` is exact;
3. `c` is exact;
4. `d` is right exact, but not exact in general: for some such data `d` does not preserve finite
   limits;
5. if `f` is flat, `d` is exact (it preserves finite limits);
6. if `f` is flat, `c` kills parasitic objects;
7. if `f` is flat, `c = d ∘ Q`: `c` carries the counit `Q(ℱ) ⟶ ℱ` of the coherator to an
   isomorphism `d(Q(ℱ)) ≅ c(ℱ)`, and these form a natural isomorphism `Q ⋙ d ≅ c`;
8. `a`, `b`, `c`, `d` commute with colimits, in particular with arbitrary direct sums;
9. `a`, `b`, `c`, `d` commute with tensor products: natural isomorphisms of bifunctors
   `X(ℱ ⊗ 𝒢) ≅ X(ℱ) ⊗ X(𝒢)`, for the tensor products of `Mod(𝒳_étale, 𝒪_𝒳)`, `LQCoh(𝒪_𝒳)`,
   `LQCoh^fbc(𝒪_𝒳)`, `QCoh(𝒪_𝒳)` and of `Mod(U_étale, 𝒪_U)`, `QCoh(U_étale, 𝒪_U)`;
10. if `f` is flat and surjective, `ℱ ∈ LQCoh^fbc(𝒪_𝒳)` and `c(ℱ) = 0`, then `ℱ` is parasitic;
11. if `f` is flat and surjective, a complex `ℱ^•` of `QCoh(𝒪_𝒳)` is exact if and only if
    `d(ℱ^•)` is exact;
12. if `f` is flat, `d(hom(ℱ, 𝒢)) = 𝓗om_{𝒪_U}(d(ℱ), d(𝒢))` for `ℱ` quasi-coherent (Stacks 0GQT,
    `AlgebraicGeometry.Stack.FlatFppf.spaceChartRestrictionCoheratorInternalHomIso`, stated there
    for all modules `𝒢` and with no finiteness on `ℱ`).

Each item is the declaration of the same number in the files imported here. -/
@[stacks 0GQS "all the items (1)-(12) of the section about the functors a, b, c, d"]
theorem spaceRestriction_properties :
    -- (1)
    exactFunctor _ _ (spaceRestriction B S hS 𝒳 U hU f) ∧
    -- (2)
    exactFunctor _ _ (lqcohSpaceRestriction B S hS 𝒳 U hU f) ∧
    -- (3)
    exactFunctor _ _ (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f) ∧
    -- (4)
    PreservesFiniteColimits (qcohSpaceRestriction B S hS 𝒳 U hU f) ∧
    (∃ (B' : BigFppfSite.{u}) (S' : Scheme.{u}) (hS' : B'.Contains S')
      (𝒳' : AlgebraicStacks.{u, w} B' S' hS') (U' : (BigFppfOver B' S' hS')ᵒᵖ ⥤ Type u)
      (hU' : IsAlgebraicSpace B' S' hS' U') (f' : algebraicSpaceStack.{u, w} B' S' hS' U' hU' ⟶ 𝒳'),
      ¬ PreservesFiniteLimits (qcohSpaceRestriction B' S' hS' 𝒳' U' hU' f')) ∧
    -- (5)
    (AlgebraicStacks.IsFlat B S hS f →
      PreservesFiniteLimits (qcohSpaceRestriction B S hS 𝒳 U hU f)) ∧
    -- (6)
    (AlgebraicStacks.IsFlat B S hS f → ∀ F : lqcohFbcModules B S hS 𝒳,
      IsParasitic B S hS 𝒳 .etale F.obj.val →
        IsZero ((lqcohFbcSpaceRestriction B S hS 𝒳 U hU f).obj F)) ∧
    -- (7)
    (AlgebraicStacks.IsFlat B S hS f →
      (∀ F : lqcohFbcModules B S hS 𝒳, IsIso ((lqcohSpaceRestriction B S hS 𝒳 U hU f).map
        ((lqcohFbcCoheratorCounit B S hS 𝒳).app F))) ∧
      Nonempty (etaleLqcohFbcCoherator B S hS 𝒳 ⋙ qcohSpaceRestriction B S hS 𝒳 U hU f ≅
        lqcohFbcSpaceRestriction B S hS 𝒳 U hU f)) ∧
    -- (8)
    PreservesColimitsOfSize.{u, u} (spaceRestriction B S hS 𝒳 U hU f) ∧
    PreservesColimitsOfSize.{u, u} (lqcohSpaceRestriction B S hS 𝒳 U hU f) ∧
    PreservesColimitsOfSize.{u, u} (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f) ∧
    PreservesColimitsOfSize.{u, u} (qcohSpaceRestriction B S hS 𝒳 U hU f) ∧
    -- (9)
    Nonempty (etaleModulesTensor B S hS 𝒳 ⋙
        (Functor.whiskeringRight _ _ _).obj (spaceRestriction B S hS 𝒳 U hU f) ≅
      spaceRestriction B S hS 𝒳 U hU f ⋙ curriedTensor (Space.Modules.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (spaceRestriction B S hS 𝒳 U hU f)) ∧
    Nonempty (lqcohTensor B S hS 𝒳 ⋙
        (Functor.whiskeringRight _ _ _).obj (lqcohSpaceRestriction B S hS 𝒳 U hU f) ≅
      lqcohSpaceRestriction B S hS 𝒳 U hU f ⋙
        curriedTensor (Space.QuasicoherentSheaves.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (lqcohSpaceRestriction B S hS 𝒳 U hU f)) ∧
    Nonempty (lqcohFbcTensor B S hS 𝒳 ⋙
        (Functor.whiskeringRight _ _ _).obj (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f) ≅
      lqcohFbcSpaceRestriction B S hS 𝒳 U hU f ⋙
        curriedTensor (Space.QuasicoherentSheaves.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f)) ∧
    Nonempty (curriedTensor (AlgebraicStacks.quasicoherentModules B S hS 𝒳) ⋙
        (Functor.whiskeringRight _ _ _).obj (qcohSpaceRestriction B S hS 𝒳 U hU f) ≅
      qcohSpaceRestriction B S hS 𝒳 U hU f ⋙
        curriedTensor (Space.QuasicoherentSheaves.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (qcohSpaceRestriction B S hS 𝒳 U hU f)) ∧
    -- (10)
    (AlgebraicStacks.IsFlat B S hS f → Stack.IsSurjective B S hS f →
      ∀ F : lqcohFbcModules B S hS 𝒳,
        IsZero ((lqcohFbcSpaceRestriction B S hS 𝒳 U hU f).obj F) →
          IsParasitic B S hS 𝒳 .etale F.obj.val) ∧
    -- (11)
    (AlgebraicStacks.IsFlat B S hS f → Stack.IsSurjective B S hS f →
      ∀ K : CochainComplex (AlgebraicStacks.quasicoherentModules B S hS 𝒳) ℤ, K.Acyclic ↔
        (((qcohSpaceRestriction B S hS 𝒳 U hU f).mapHomologicalComplex _).obj K).Acyclic) ∧
    -- (12)
    (AlgebraicStacks.IsFlat B S hS f →
      ∀ (F G : _root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)),
        F.IsQuasicoherentOnSite →
        Nonempty (spaceChartRestriction B S hS 𝒳 U hU f
            (FlatFppf.coheratorInternalHom B S hS 𝒳 F G) ≅
          Space.smallEtaleInternalHomSmall B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
            (spaceChartRestriction B S hS 𝒳 U hU f G))) :=
  ⟨exactFunctor_spaceRestriction B S hS 𝒳 U hU f,
    exactFunctor_lqcohSpaceRestriction B S hS 𝒳 U hU f,
    exactFunctor_lqcohFbcSpaceRestriction B S hS 𝒳 U hU f,
    preservesFiniteColimits_qcohSpaceRestriction B S hS 𝒳 U hU f,
    not_preservesFiniteLimits_qcohSpaceRestriction,
    preservesFiniteLimits_qcohSpaceRestriction_of_isFlat B S hS 𝒳 U hU f,
    isZero_lqcohFbcSpaceRestriction_obj_of_isParasitic B S hS 𝒳 U hU f,
    fun hf => ⟨isIso_lqcohSpaceRestriction_map_lqcohFbcCoheratorCounit_app B S hS 𝒳 U hU f hf,
      ⟨lqcohFbcCoheratorCompQcohSpaceRestrictionIso B S hS 𝒳 U hU f hf⟩⟩,
    preservesColimitsOfSize_spaceRestriction B S hS 𝒳 U hU f,
    preservesColimitsOfSize_lqcohSpaceRestriction B S hS 𝒳 U hU f,
    preservesColimitsOfSize_lqcohFbcSpaceRestriction B S hS 𝒳 U hU f,
    preservesColimitsOfSize_qcohSpaceRestriction B S hS 𝒳 U hU f,
    ⟨spaceRestrictionTensorIso B S hS 𝒳 U hU f⟩, ⟨lqcohSpaceRestrictionTensorIso B S hS 𝒳 U hU f⟩,
    ⟨lqcohFbcSpaceRestrictionTensorIso B S hS 𝒳 U hU f⟩,
    ⟨qcohSpaceRestrictionTensorIso B S hS 𝒳 U hU f⟩,
    isParasitic_of_isZero_lqcohFbcSpaceRestriction_obj B S hS 𝒳 U hU f,
    acyclic_iff_acyclic_qcohSpaceRestriction B S hS 𝒳 U hU f,
    fun hf F G hF => ⟨FlatFppf.spaceChartRestrictionCoheratorInternalHomIso B S hS 𝒳 U hU f hf
      F G hF⟩⟩

end Statement

end AlgebraicGeometry.Stack.AlgebraicStacks

end

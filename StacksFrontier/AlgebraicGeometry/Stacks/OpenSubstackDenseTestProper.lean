module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.General
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# Properness of an open substack over the base from a dense valuative test

Let `𝒞` be an algebraic stack over a locally Noetherian quasi-separated scheme `S`, locally of
finite type over `S`, and let `V ⊆ W` be open substacks of `𝒞` with `W` quasi-compact and
separated over `S` and `|W|` contained in the closure of `|V|`. If the 1-morphisms `V ⟶ W ⟶ S`
satisfy the existence part of the valuative criterion with dense test, and Chow's lemma for
algebraic stacks holds, then `W ⟶ S` is proper.

## Main definitions

* `AlgebraicGeometry.Stack.OpenSubstack.homOfLE`: the factorization `V ⟶ W` of the inclusion of
  an open substack `V` through an open substack `W` containing it.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.isOpenEmbedding_pointsMap_inclusion`: the map on points
  of the inclusion of an open substack is an open embedding.
* `AlgebraicGeometry.Stack.OpenSubstack.isQuasiCompactStack_of_le`: an open substack of a
  quasi-compact, locally Noetherian open substack is quasi-compact.
* `AlgebraicStacks.isProper_inclusion_comp_structureMorphism_of_denseTestExistence`: properness
  of `W ⟶ S` from the dense valuative test for `V ⟶ W ⟶ S`, with Chow's lemma for algebraic
  stacks as the hypothesis `hchow`.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0E9C](https://stacks.math.columbia.edu/tag/0E9C)
-/

@[expose] public section

open CategoryTheory Topology

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace OpenSubstack

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- For open substacks `V ⊆ W` of `𝒳`, the 1-morphism `V ⟶ W` whose composite with the inclusion
of `W` is the inclusion of `V`, definitionally. -/
noncomputable abbrev homOfLE (V W : OpenSubstack 𝒳) (hle : V.property ≤ W.property) :
    V.toAlgebraicStack ⟶ W.toAlgebraicStack :=
  W.factor B S hS V.inclusion fun x => hle _ x.property

/-- The composite of `homOfLE V W` with the inclusion of `W` is the inclusion of `V`. -/
theorem homOfLE_comp_inclusion (V W : OpenSubstack 𝒳) (hle : V.property ≤ W.property) :
    homOfLE B S hS V W hle ≫ W.inclusion = V.inclusion := rfl

/-- The map on points of the inclusion of an open substack is an open embedding. -/
theorem isOpenEmbedding_pointsMap_inclusion (V : OpenSubstack 𝒳) :
    @IsOpenEmbedding _ _ (pointTopology B S hS V.toAlgebraicStack.val)
      (pointTopology B S hS 𝒳.val) (AlgebraicStacks.pointsMap B S hS V.inclusion) := by
  let := pointTopology B S hS V.toAlgebraicStack.val
  let := pointTopology B S hS 𝒳.val
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_pointsMap B S hS _ _ V.inclusion.hom.hom)
    (pointsMap_injective_of_fullyFaithful B S hS V.inclusion)
    (AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS V.inclusion V.isOpenImmersion)

/-- For open substacks `V ⊆ W` of `𝒳` with `W` quasi-compact and locally Noetherian, `V` is
quasi-compact. -/
theorem isQuasiCompactStack_of_le (V W : OpenSubstack 𝒳) (hle : V.property ≤ W.property)
    (hqc : IsQuasiCompactStack.{u, w} B S hS W.toAlgebraicStack.val
      W.toAlgebraicStack.property)
    (hN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) W.toAlgebraicStack) :
    IsQuasiCompactStack.{u, w} B S hS V.toAlgebraicStack.val V.toAlgebraicStack.property := by
  let := pointTopology B S hS V.toAlgebraicStack.val
  let := pointTopology B S hS W.toAlgebraicStack.val
  let := pointTopology B S hS 𝒳.val
  have := AlgebraicStacks.noetherianSpace_points_of_isQuasiCompactStack B S hS
    W.toAlgebraicStack hqc hN
  have hk : IsInducing (AlgebraicStacks.pointsMap B S hS (homOfLE B S hS V W hle)) :=
    .of_comp (continuous_pointsMap B S hS _ _ (homOfLE B S hS V W hle).hom.hom)
      (isOpenEmbedding_pointsMap_inclusion B S hS W).continuous
      (AlgebraicStacks.pointsMap_comp' B S hS (homOfLE B S hS V W hle) W.inclusion ▸
        (isOpenEmbedding_pointsMap_inclusion B S hS V).isInducing)
  exact ⟨hk.isCompact_iff.2 (TopologicalSpace.NoetherianSpace.isCompact _)⟩

end OpenSubstack

namespace AlgebraicStacks

/-- Let `𝒞` be an algebraic stack over a locally Noetherian quasi-separated scheme `S` with
`𝒞 ⟶ S` locally of finite type, and let `V ⊆ W` be open substacks of `𝒞`. Assume that `W ⟶ S` is
separated, that `W` is quasi-compact, that every point of `|W|` lies in the closure of `|V|`, and
that every 2-commutative diagram `Spec K ⟶ V ⟶ W ⟶ S`, `Spec A ⟶ S` with `A` a discrete
valuation ring with fraction field `K` admits a dotted arrow to `W` after an extension of `K` and
passage to a dominating valuation ring. If moreover Chow's lemma for algebraic stacks holds (the
hypothesis `hchow`), then `W ⟶ S` is proper. -/
theorem isProper_inclusion_comp_structureMorphism_of_denseTestExistence
    [IsLocallyNoetherian S] [QuasiSeparatedSpace S]
    {𝒞 : AlgebraicStacks.{u, w} B S hS} (V W : OpenSubstack 𝒞)
    (hle : V.property ≤ W.property)
    (hlft : IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒞))
    (hsep : IsSeparated B S hS (W.inclusion ≫ structureMorphism B S hS 𝒞))
    (hqc : IsQuasiCompactStack.{u, w} B S hS W.toAlgebraicStack.val
      W.toAlgebraicStack.property)
    (hdense : W.pointSet B S hS ⊆ @closure _ (pointTopology B S hS 𝒞.val) (V.pointSet B S hS))
    (hlift : ValuativeCriterion.DenseTestExistence B S hS (OpenSubstack.homOfLE B S hS V W hle)
      (W.inclusion ≫ structureMorphism B S hS 𝒞))
    (hchow : ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {𝒳' : AlgebraicStacks.{u, w} B S hS}
      {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y → Space.IsAbsolutelyQuasiSeparated B S hS hZ Y →
      ∀ (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f' → IsFiniteType B S hS f' →
        ∃ (X Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
          (_ : IsAlgebraicSpace B S hS Xbar)
          (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳') (i : X ⟶ Xbar) (g : Xbar ⟶ Y),
          IsProper B S hS a ∧ Stack.IsSurjective B S hS a ∧
          Space.IsOpenImmersion B S hS i ∧ Space.IsProper B S hS g ∧
          Nonempty (a ≫ f' ≅ algebraicSpaceStackMap.{u, w} B S hS hX hY (i ≫ g))) :
    IsProper B S hS (W.inclusion ≫ structureMorphism B S hS 𝒞) := by
  let k := OpenSubstack.homOfLE B S hS V W hle
  let _ : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) :=
    (exists_scheme_atlas_iff_scheme B S hS _ _).2
      (inferInstanceAs (IsLocallyNoetherian S))
  have hWlft : IsLocallyOfFiniteType B S hS (W.inclusion ≫ structureMorphism B S hS 𝒞) :=
    isLocallyOfFiniteType_comp B S hS W.inclusion _
      (isLocallyOfFiniteType_of_isOpenImmersion B S hS W.inclusion W.isOpenImmersion) hlft
  have hWqs : IsQuasiSeparatedOver.{u, w} B S hS W.toAlgebraicStack := by
    change IsQuasiSeparated B S hS _
    exact comp_structureMorphism B S hS W.inclusion ▸ isQuasiSeparated_of_isSeparated B S hS hsep
  have hWqc : IsQuasiCompactMorphism B S hS (W.inclusion ≫ structureMorphism B S hS 𝒞) :=
    isQuasiCompactMorphism_of_isQuasiCompactStack B S hS inferInstance _ hqc
      (isQuasiSeparatedOver_schemeStack B S hS _ (inferInstanceAs (QuasiSeparatedSpace S)))
  have hkqc : IsQuasiCompactMorphism B S hS k :=
    isQuasiCompactMorphism_of_isQuasiCompactStack B S hS inferInstance k
      (OpenSubstack.isQuasiCompactStack_of_le B S hS V W hle hqc
        (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS _ hWlft h𝒴)) hWqs
  have hklft : IsLocallyOfFiniteType B S hS k :=
    isLocallyOfFiniteType_of_comp B S hS k W.inclusion
      (isLocallyOfFiniteType_of_isOpenImmersion B S hS V.inclusion V.isOpenImmersion)
  exact isProper_of_denseTestExistence_of_chowLemma B S hS _ k h𝒴 ⟨hWlft, hWqc⟩ ⟨hklft, hkqc⟩
    hsep (dense_range_pointsMap_of_pointSet_subset_closure B S hS W k hdense) hlift hchow

end AlgebraicStacks

end AlgebraicGeometry.Stack

end

module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperComparison
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure

/-!
# Two compactifications give the same upper shriek

Let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S` and let `j₁ : X ⟶ X̄₁`,
`j₂ : X ⟶ X̄₂` be two compactifications of `X` over `Y`. The scheme-theoretic closure `Z` of
`X` in `X̄₁ ×_Y X̄₂` dominates both: the projections `g₁ : Z ⟶ X̄₁` and `g₂ : Z ⟶ X̄₂` are
isomorphisms over `X` (`AlgebraicGeometry.GraphClosure.preimage_closureFst`), and `Z` is proper
over `Y`. Comparing the twisted inverse images of `Z ⟶ Y` and `X̄ₖ ⟶ Y` over `X` then compares
`j₁^* ∘ ā₁` and `j₂^* ∘ ā₂`. This is the proof of [Stacks, Tag 0AA0].

## Main definitions

* `Stacks.Duality.DominatingCompactification`: the closure `Z` of `X` in `X̄₁ ×_Y X̄₂`, with its
  two projections and the open immersion of `X`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.DominatingCompactification

variable {S : Scheme.{u}} {X Y : FTS S} (f : X ⟶ Y)
  (j₁ j₂ : CompactificationOf (Over.mk f.left))

/-- The two compactifications agree on `X` over `Y`. -/
theorem immersion_comp_toBase_eq :
    j₁.immersion ≫ j₁.toBase = 𝟙 X.left ≫ j₂.immersion ≫ j₂.toBase := by
  rw [Category.id_comp, immersion_comp_toBase, immersion_comp_toBase]

/-- The graph `X ⟶ X̄₁ ×_Y X̄₂` of the two open immersions. -/
abbrev graph : X.left ⟶ pullback j₁.toBase j₂.toBase :=
  GraphClosure.graph j₁.toBase j₂.toBase j₁.immersion j₂.immersion (𝟙 X.left)
    (immersion_comp_toBase_eq f j₁ j₂)

/-- The dominating compactification: the scheme-theoretic closure of the graph. -/
abbrev space : Scheme.{u} := (graph f j₁ j₂).image

/-- The open immersion of `X` into the dominating compactification. -/
abbrev immersion : X.left ⟶ space f j₁ j₂ := (graph f j₁ j₂).toImage

/-- The projection of the dominating compactification to the first compactification. -/
abbrev fst : space f j₁ j₂ ⟶ j₁.space :=
  GraphClosure.closureFst j₁.toBase j₂.toBase j₁.immersion j₂.immersion (𝟙 X.left)
    (immersion_comp_toBase_eq f j₁ j₂)

/-- The projection of the dominating compactification to the second compactification. -/
abbrev snd : space f j₁ j₂ ⟶ j₂.space :=
  GraphClosure.closureSnd j₁.toBase j₂.toBase j₁.immersion j₂.immersion (𝟙 X.left)
    (immersion_comp_toBase_eq f j₁ j₂)

/-- The two projections of the dominating compactification agree as morphisms to `Y`. -/
theorem fst_comp_toBase : fst f j₁ j₂ ≫ j₁.toBase = snd f j₁ j₂ ≫ j₂.toBase := by
  simp [fst, snd, GraphClosure.closureFst, GraphClosure.closureSnd, pullback.condition]

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- The graph is quasi-compact: followed by the separated projection to `X̄₁` it is the
quasi-compact open immersion `j₁`. -/
instance : QuasiCompact (graph f j₁ j₂) := by
  have : QuasiCompact (graph f j₁ j₂ ≫ pullback.fst j₁.toBase j₂.toBase) := by
    rw [GraphClosure.graph_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst j₁.toBase j₂.toBase)

/-- The map of `X` into the dominating compactification is an open immersion. -/
instance : IsOpenImmersion (immersion f j₁ j₂) := inferInstance

/-- The identity of `X` is a closed immersion. -/
instance : IsClosedImmersion (𝟙 X.left) := inferInstance

/-- The first projection is an isomorphism over `X`. -/
theorem isPullback_fst : IsPullback (immersion f j₁ j₂) (𝟙 X.left) (fst f j₁ j₂) j₁.immersion :=
  isPullback_id_of_preimage_opensRange_eq _ _ _ (GraphClosure.toImage_closureFst _ _ _ _ _ _)
    (GraphClosure.preimage_closureFst _ _ _ _ _ _)

/-- The second projection is an isomorphism over `X`. -/
theorem isPullback_snd : IsPullback (immersion f j₁ j₂) (𝟙 X.left) (snd f j₁ j₂) j₂.immersion :=
  isPullback_id_of_preimage_opensRange_eq _ _ _
    (by rw [GraphClosure.toImage_closureSnd, Category.id_comp])
    (GraphClosure.preimage_closureSnd _ _ _ _ _ _)

/-- The dominating compactification is proper over the first one. -/
instance : IsProper (fst f j₁ j₂) := by
  dsimp [fst, GraphClosure.closureFst]
  infer_instance

/-- The dominating compactification is proper over the second one. -/
instance : IsProper (snd f j₁ j₂) := by
  dsimp [snd, GraphClosure.closureSnd]
  infer_instance

/-- The underlying scheme of `X`, as an object over `Y`, is quasi-compact. -/
instance : CompactSpace (Over.mk f.left).left := inferInstanceAs (CompactSpace X.left)

/-- The underlying scheme of `X`, as an object over `Y`, is quasi-separated. -/
instance : QuasiSeparatedSpace (Over.mk f.left).left :=
  inferInstanceAs (QuasiSeparatedSpace X.left)

/-- The dominating compactification is quasi-compact: it is proper over `Y`. -/
instance : CompactSpace (space f j₁ j₂) :=
  QuasiCompact.compactSpace_of_compactSpace (fst f j₁ j₂ ≫ j₁.toBase)

/-- The dominating compactification is quasi-separated: it is separated over `Y`. -/
instance : QuasiSeparatedSpace (space f j₁ j₂) :=
  quasiSeparatedSpace_of_quasiSeparated (fst f j₁ j₂ ≫ j₁.toBase)

/-- The map of [Stacks, Tag 0A9L] comparing `a_{g₁}` with the identity over `X`. -/
abbrev restrictionMapFst :=
  twistedInverseImageRestrictionMapOfIsPullback (fst f j₁ j₂) j₁.immersion (immersion f j₁ j₂)
    (isPullback_fst f j₁ j₂)

/-- The map of [Stacks, Tag 0A9L] comparing `a_{g₂}` with the identity over `X`. -/
abbrev restrictionMapSnd :=
  twistedInverseImageRestrictionMapOfIsPullback (snd f j₁ j₂) j₂.immersion (immersion f j₁ j₂)
    (isPullback_snd f j₁ j₂)

/-- **Two compactifications give isomorphic upper shrieks at `K`**, wherever the maps of
[Stacks, Tag 0A9L] for the two projections of the dominating compactification are invertible at
`ā₁(K)` and `ā₂(K)`: `j₁^* ā₁ K ≅ j_Z^* a_Z K ≅ j₂^* ā₂ K`. -/
def upperShriekObjIsoOfIsIso (K : quasiCoherentDerivedCategory Y.left)
    [IsIso ((restrictionMapFst f j₁ j₂).app ((twistedInverseImage j₁.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j₁.toBase)).obj K))]
    [IsIso ((restrictionMapSnd f j₁ j₂).app ((twistedInverseImage j₂.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j₂.toBase)).obj K))] :
    (upperShriek f j₁).obj K ≅ (upperShriek f j₂).obj K :=
  ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback j₁.immersion).app _).symm ≪≫
    (twistedInverseImageCompRestrictIsoOfIsPullback (fst f j₁ j₂) j₁.immersion
      (immersion f j₁ j₂) (isPullback_fst f j₁ j₂) j₁.toBase K).symm ≪≫
    (OpenImmersion.restrictedDerivedRestrict (immersion f j₁ j₂)).mapIso
      ((twistedInverseImageCongr (fst_comp_toBase f j₁ j₂) _ _).app K) ≪≫
    twistedInverseImageCompRestrictIsoOfIsPullback (snd f j₁ j₂) j₂.immersion
      (immersion f j₁ j₂) (isPullback_snd f j₁ j₂) j₂.toBase K ≪≫
    (restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback j₂.immersion).app _

end Stacks.Duality.DominatingCompactification

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCoverSurjective

/-!
# The property of the chart maps in the chart cover of a fibre product

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a local property of morphisms
of `WAdm^count` stable under base change in the sense of Stacks 0GBC, and let `f : X ⟶ Y` and
`g : Z ⟶ Y` be morphisms of locally countably indexed formal algebraic spaces over `S`.
**Lemma 87.21.7 (Stacks 0GBD)** asserts that the equivalent conditions of Stacks 0ANG pass from
`f` to the second projection `pr₂ : X ×_Y Z ⟶ Z`, and its proof does this by exhibiting
condition (3) on one particular covering of `X ×_Y Z`: a covering `{Vⱼ ⟶ Y}` as in Definition
0AIM is chosen, then coverings `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and `{Wⱼₖ ⟶ Vⱼ ×_Y Z}` of the same kind, and
the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` are shown to cover `X ×_Y Z`, to map to `Z` through `Wⱼₖ`,
and — the last clause — to have `P` on the chart map `Uⱼᵢ ×_{Vⱼ} Wⱼₖ ⟶ Wⱼₖ`.

This module proves the last clause on that covering.

## Main results

* `AlgebraicGeometry.FormalSpace.hasBaseChangeCoverOverPullbackSnd_of_chartFibreProducts`: the
  fibre products of charts `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form a covering of `X ×_Y Z` as in
  `AlgebraicGeometry.FormalSpace.HasBaseChangeCoverOverPullbackSndOn`, given the ring-level
  presentation `hAN3` of each of them by a completed tensor product (clause (3) of Stacks 0AN3).
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_pullback_snd_countablyIndexed`:
  condition (3) of Stacks 0ANG for `pr₂` at the class `WAdm^count`, the property of the chart
  maps included.

## Implementation notes

The hypothesis `hiso` is the invariance of `P` under isomorphism of targets: Stacks 0AN3
presents a chart of the fibre product by an isomorphism of chart rings rather than by an
equality.

## References

* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0GBC](https://stacks.math.columbia.edu/tag/0GBC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Given a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and coverings `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and
`{Wⱼₖ ⟶ Vⱼ ×_Y Z}` of the same kind, the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form an affine étale
covering of `X ×_Y Z` each member of which maps to `Z` through the affine formal algebraic space
`Wⱼₖ`, representable étale over `Z`, by a morphism that is a chart base change of `f` along `g`.
The hypothesis `hAN3` is clause (3) of Stacks 0AN3 for these fibre products: the chart ring of
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` is the completed tensor product of the chart rings of `Uⱼᵢ` and `Wⱼₖ` over
that of `Vⱼ`, compatibly with the projection to `Wⱼₖ`. -/
theorem hasBaseChangeCoverOverPullbackSnd_of_chartFibreProducts
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hAN3 : ∀ (j : J) (i : I j) (k : K j), IsChartBaseChangeOn B S hS C f g
      (pullback.snd (a j i ≫ pullback.fst (v j) f) (b j k ≫ pullback.fst (v j) g))) :
    HasBaseChangeCoverOverPullbackSndOn B S hS C f g := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨Σ j, I j × K j, fun p ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
    ⟨fun p ↦ ?_, fun p ↦ ?_,
      isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hV.2.2 a
        (fun j ↦ (hU j).2.2) b fun j ↦ (hW j).2.2⟩, fun p ↦ ?_⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hV.1 p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hV.1 p.1))
      ((hU p.1).1 p.2.1) ((hW p.1).1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hV.2.1 p.1) ((hU p.1).2.1 p.2.1) ((hW p.1).2.1 p.2.2)
  · exact ⟨W p.1 p.2.2, b p.1 p.2.2 ≫ pullback.snd (v p.1) g,
      pullback.snd (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
        (b p.1 p.2.2 ≫ pullback.fst (v p.1) g), (hW p.1).1 p.2.2,
      IsRepresentableEtale.comp B S hS ((hW p.1).2.1 p.2.2)
        (isRepresentableEtale_pullback_snd B S hS (v p.1) g (hV.2.1 p.1)),
      chartPullbackMap_comp_snd B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
      hAN3 p.1 p.2.1 p.2.2⟩

/-- Condition (3) of Stacks 0ANG for the second projection `pr₂ : X ×_Y Z ⟶ Z` at the class
`WAdm^count`, with the property of the chart maps included. Let `P` be a local property of
morphisms of `WAdm^count` stable under base change in the sense of Stacks 0GBC, invariant under
isomorphism of targets. If `f : X ⟶ Y` satisfies condition (1) of Stacks 0ANG, then on the
covering of `X ×_Y Z` by the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` of charts, the second projection
satisfies condition (3): the covering is an affine étale covering, each of its members maps to
`Z` through an affine formal algebraic space representable étale over `Z`, and the chart map of
each member has `P`. -/
theorem hasPropertyAfterSourceCover_pullback_snd_countablyIndexed
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hAN3 : ∀ (j : J) (i : I j) (k : K j), IsChartBaseChangeOn B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible f g
      (pullback.snd (a j i ≫ pullback.fst (v j) f) (b j k ≫ pullback.fst (v j) g)))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
      (pullback.snd f g) :=
  hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible P (fun _ ↦ True)
    (completedTensorBaseChangeAxiom_of_isStableUnderBaseChange P hP) hiso f g
    (hasBaseChangeCoverOverPullbackSnd_of_chartFibreProducts B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible f g V v hV U a hU W b hW hAN3)
    hf (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)

end

end AlgebraicGeometry.FormalSpace

end

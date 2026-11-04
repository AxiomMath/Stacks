module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCoverSurjective

/-!
# Types of fibre products of formal algebraic spaces, from the chart cover

`StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes` proves the five clauses of
**Stacks 0GBB** from, among other inputs, Stacks 0AJ7 for the charts of `Y` (`h0AJ7`) and the
covering of `X ×_Y Z` by the chart fibre products (`hcover`). Both are theorems of the library:
Stacks 0AJ7 is `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace.isSeparated`, and the
joint surjectivity of the chart fibre products is
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_chartPullbackMap` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCoverSurjective`. This file states the
five clauses without those two hypotheses, and clause (1) with the hypothesis `h0AKX`
discharged as well.

## Main results

* `AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasWithProperty_pullback_of_formalChartPullbacks`:
  the common content of the five clauses, for an arbitrary property of fppf sheaves.
* `AlgebraicGeometry.FormalSpace.isLocallyCountablyIndexed_pullback_of_formalChartPullbacks` and
  its four siblings: the five clauses of Stacks 0GBB on the remaining inputs.
* `AlgebraicGeometry.FormalSpace.isLocallyCountablyIndexed_pullback_of_atlasChartLocality`:
  clause (1) with the hypothesis `h0AKX` discharged.

## References

* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The common content of the five clauses of **Stacks 0GBB**: the chart fibre products
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form an atlas of `X ×_Y Z` as in Definition 0AIM all of whose members satisfy
`P`, so condition (2) of Stacks 0AKX for `P` passes from `X` and `Z` to `X ×_Y Z`. -/
theorem hasAffineEtaleAtlasWithProperty_pullback_of_formalChartPullbacks
    (P : FppfSheaf B S hS → Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hXatlas : HasAffineEtaleAtlasWithProperty B S hS X P)
    (hZatlas : HasAffineEtaleAtlasWithProperty B S hS Z P)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas B S hS P)
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS P) :
    HasAffineEtaleAtlasWithProperty B S hS (pullback f g) P := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, J, V, v, hVaff, hVet, hVsurj⟩ := hY
  choose I U a hUaff hUet hUsurj using fun j ↦ (h0AJ3f (V j) (v j) (hVaff j) (hVet j)).2
  choose K W b hWaff hWet hWsurj using fun j ↦ (h0AJ3g (V j) (v j) (hVaff j) (hVet j)).2
  refine ⟨Σ j, I j × K j,
    fun p ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
    fun p ↦ ?_, fun p ↦ ?_, ?_, fun p ↦ ?_⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hVaff p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hVaff p.1))
      (hUaff p.1 p.2.1) (hWaff p.1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hVet p.1) (hUet p.1 p.2.1) (hWet p.1 p.2.2)
  · exact isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hVsurj a hUsurj b hWsurj
  · exact hPaff _ _ (hUaff p.1 p.2.1) (hVaff p.1) (hWaff p.1 p.2.2)
      (h0AKX X hXatlas (U p.1 p.2.1) (a p.1 p.2.1 ≫ pullback.snd (v p.1) f) (hUaff p.1 p.2.1)
        (IsRepresentableEtale.comp B S hS (hUet p.1 p.2.1)
          (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVet p.1))))
      (h0AKX Z hZatlas (W p.1 p.2.2) (b p.1 p.2.2 ≫ pullback.snd (v p.1) g) (hWaff p.1 p.2.2)
        (IsRepresentableEtale.comp B S hS (hWet p.1 p.2.2)
          (isRepresentableEtale_pullback_snd B S hS (v p.1) g (hVet p.1))))

/-- Stacks 0GBB, clause (1), from the chart cover. If `X` and `Z` are locally countably indexed,
then so is `X ×_Y Z`. The hypotheses `h0AKX`, `h0AJ3f`, `h0AJ3g`, `hPaff` and `hset` are the inputs
of the source which the library does not carry; unlike `hasAffineEtaleAtlasWithProperty_pullback`,
neither the separatedness of affine formal algebraic spaces nor the chart cover of `X ×_Y Z` is
assumed. -/
theorem isLocallyCountablyIndexed_pullback_of_formalChartPullbacks
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas B S hS (IsCountablyIndexed B S hS))
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS (IsCountablyIndexed B S hS))
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback f g)) :
    IsLocallyCountablyIndexed B S hS (pullback f g) :=
  have h := hasAffineEtaleAtlasWithProperty_pullback_of_formalChartPullbacks
    B S hS (IsCountablyIndexed B S hS) f g hY
    hX.2 hZ.2 h0AKX h0AJ3f h0AJ3g hPaff
  ⟨isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty B S hS hset h, h⟩

/-- Stacks 0GBB, clause (2), from the chart cover. If `X` and `Z` are locally countably indexed and
classical, then so is `X ×_Y Z`. The hypotheses `h0AKX`, `h0AJ3f`, `h0AJ3g`, `hPaff` and `hset` are
the inputs of the source which the library does not carry. -/
theorem isLocallyCountablyIndexedAndClassical_pullback_of_formalChartPullbacks
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Z ⟶ Y) (hX : IsLocallyCountablyIndexedAndClassical B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexedAndClassical B S hS Z)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas B S hS
      fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T)
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS
      fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T)
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback f g)) :
    IsLocallyCountablyIndexedAndClassical B S hS (pullback f g) :=
  have h := hasAffineEtaleAtlasWithProperty_pullback_of_formalChartPullbacks B S hS
    (fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T) f g hY hX.2 hZ.2 h0AKX
    h0AJ3f h0AJ3g hPaff
  ⟨isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty B S hS hset h, h⟩

/-- Stacks 0GBB, clause (3), from the chart cover. If `X` and `Z` are locally weakly adic, then so
is `X ×_Y Z`. The hypotheses `h0AKX`, `h0AJ3f`, `h0AJ3g`, `hPaff` and `hset` are the inputs of the
source which the library does not carry; unlike `hasAffineEtaleAtlasWithProperty_pullback`, neither
the separatedness of affine formal algebraic spaces nor the chart cover of `X ×_Y Z` is assumed. -/
theorem isLocallyWeaklyAdic_pullback_of_formalChartPullbacks
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyWeaklyAdic B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyWeaklyAdic B S hS Z)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas B S hS (IsWeaklyAdic B S hS))
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS (IsWeaklyAdic B S hS))
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback f g)) :
    IsLocallyWeaklyAdic B S hS (pullback f g) :=
  have h := hasAffineEtaleAtlasWithProperty_pullback_of_formalChartPullbacks
    B S hS (IsWeaklyAdic B S hS) f g hY
    hX.2 hZ.2 h0AKX h0AJ3f h0AJ3g hPaff
  ⟨isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty B S hS hset h, h⟩

/-- Stacks 0GBB, clause (4), from the chart cover. If `X` and `Z` are locally adic\*, then so is
`X ×_Y Z`. The hypotheses `h0AKX`, `h0AJ3f`, `h0AJ3g`, `hPaff` and `hset` are the inputs of the
source which the library does not carry. -/
theorem isLocallyAdicStar_pullback_of_formalChartPullbacks
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas B S hS (IsAdicStar B S hS))
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS (IsAdicStar B S hS))
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback f g)) :
    IsLocallyAdicStar B S hS (pullback f g) :=
  have h := hasAffineEtaleAtlasWithProperty_pullback_of_formalChartPullbacks
    B S hS (IsAdicStar B S hS) f g hY
    hX.2 hZ.2 h0AKX h0AJ3f h0AJ3g hPaff
  ⟨isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty B S hS hset h, h⟩

/-- Stacks 0GBB, clause (5), from the chart cover. If `X` and `Z` are locally Noetherian and
`X_red ⟶ Y_red` is locally of finite type, then `X ×_Y Z` is locally Noetherian. The affine input
`hPaff` is assumed relative to the finite type condition, which the source transfers to the chart
maps by Stacks 0GB7 and Morphisms of Spaces Lemma 67.23.4. -/
theorem isLocallyNoetherian_pullback_of_formalChartPullbacks
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hfin : HasLocallyOfFiniteTypeReduction B S hS f)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas B S hS (IsNoetherian B S hS))
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : HasLocallyOfFiniteTypeReduction B S hS f →
      AffineChartFibreProductStable B S hS (IsNoetherian B S hS))
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback f g)) :
    IsLocallyNoetherian B S hS (pullback f g) :=
  have h := hasAffineEtaleAtlasWithProperty_pullback_of_formalChartPullbacks
    B S hS (IsNoetherian B S hS) f g hY
    hX.2 hZ.2 h0AKX h0AJ3f h0AJ3g (hPaff hfin)
  ⟨isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty B S hS hset h, h⟩

/-- **Stacks 0GBB, clause (1), with the hypothesis `h0AKX` discharged.** If `X` and `Z` are
locally countably indexed, then so is `X ×_Y Z`.

Stacks 0AKX (2) ⟹ (1) for countable indexing is a theorem of this library,
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas`
of `StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedChartLocality.lean`, so it is no
longer assumed. The binders that remain are its two inputs — `h0AJ2` for Stacks 0AJ2 at the
fibre products of the members of the atlas with the chart, and `hCoproductEtale` for the assembly
of a finite family into one morphism out of the coproduct — together with the other four binders of
`isLocallyCountablyIndexed_pullback_of_formalChartPullbacks`: `h0AJ3f`, `h0AJ3g`, `hPaff` and
`hset`. Nothing else is assumed.

Clause (1) is the only one of the five that can be stated this way. For the four other properties
`AlgebraicGeometry.FormalSpace.PropertyOfFiniteDisjointUnions` is open, so
`AlgebraicGeometry.FormalSpace.HasAffineEtaleRefinementWithProperty` is unavailable and Stacks 0AKX
(2) ⟹ (1) stays a hypothesis there in one shape or another.

It carries no `@[stacks]` registration, since every binder after `hZ` is an input the source
proves. -/
theorem isLocallyCountablyIndexed_pullback_of_atlasChartLocality {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    (hCoproductEtale : CoproductsRepresentableEtale B S hS)
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS (IsCountablyIndexed B S hS))
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback f g)) :
    IsLocallyCountablyIndexed B S hS (pullback f g) :=
  isLocallyCountablyIndexed_pullback_of_formalChartPullbacks B S hS f g hX hY hZ
    (isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas B S hS h0AJ2
      hCoproductEtale) h0AJ3f h0AJ3g hPaff hset

end AlgebraicGeometry.FormalSpace

end

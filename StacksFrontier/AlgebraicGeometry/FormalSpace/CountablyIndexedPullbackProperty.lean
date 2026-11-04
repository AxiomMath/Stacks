module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartPullbackAtlasCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorChartBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertySourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined

/-!
# Base change of a local property of morphisms of locally countably indexed formal spaces

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a local property of morphisms
of `WAdm^count` which is stable under base change (Stacks 0GBC), and let `f : X ⟶ Y` and
`g : Z ⟶ Y` be morphisms of locally countably indexed formal algebraic spaces over `S`.
**Stacks 0GBD** says that if `f` satisfies the equivalent conditions of Stacks 0ANG, then so
does the second projection `pr₂ : X ×_Y Z ⟶ Z`.

## Main results

* `AlgebraicGeometry.FormalSpace.isChartOfClass_isCountablyWeaklyAdmissible_of_isCountablyIndexed`:
  a countably indexed fppf sheaf is the formal spectrum of a countably indexed weakly admissible
  topological ring.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_chartCovers`: the fibre
  product of two formal algebraic spaces over a third is a formal algebraic space as soon as
  the charts of the source's proof of Stacks 0GBD exist.

## Implementation notes

The proof is the source's. A covering `{Vⱼ ⟶ Y}` as in Definition 0AIM is taken from the atlas
by countably indexed affine formal algebraic spaces which `Y` carries, and coverings
`{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and `{Wⱼₖ ⟶ Vⱼ ×_Y Z}` of the same kind are chosen with *countably
indexed* members: each `Uⱼᵢ` is a chart of `Vⱼ ×_Y Xₗ` for a member `Xₗ` of the countably
indexed atlas of `X`, so that `Uⱼᵢ` is representable over the countably indexed affine formal
algebraic space `Xₗ` and is countably indexed by Stacks 0AKQ. The fibre products
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` then cover `X ×_Y Z`, and Stacks 0AN3 clause (3) presents each of them by a
completed tensor product, on which stability of `P` under base change gives `P`.

Situation 0CBA, which defines a local property, opens with "Let `P` be a property of morphisms
of `WAdm^count`, invariant under isomorphism of source and target in this category".
`TopologicalRing.PropertyIsLocal` records the three axioms that follow that sentence and not
the invariance itself, so the invariance under isomorphism of targets which the proof uses is
stated as the hypothesis `hiso` of type `PropertyIsInvariantUnderTargetIsoOn`; it is part of the
source's hypothesis that `P` be local.

## References

* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GBC](https://stacks.math.columbia.edu/tag/0GBC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A countably indexed fppf sheaf is a chart of the class `WAdm^count`: it is the formal
spectrum of a countably indexed weakly admissible topological ring, namely the limit of the
section rings of a sequential presentation (Stacks 0AIK and 0AN1). -/
theorem isChartOfClass_isCountablyWeaklyAdmissible_of_isCountablyIndexed
    {U : FppfSheaf B S hS} (hU : IsCountablyIndexed B S hS U) :
    IsChartOfClass B S hS TopologicalRing.IsCountablyWeaklyAdmissible U := by
  obtain ⟨A, i₁, i₂, i₃, i₄, Q, hwa, hcount, he⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hU
  exact ⟨A, i₁, i₂, i₃, i₄, ⟨hwa, hcount⟩, Q, he⟩

/-- Conversely, a chart of the class `WAdm^count` is countably indexed: the formal spectrum of
a countably indexed weakly admissible topological ring is countably indexed (Stacks 0AN1). -/
theorem isCountablyIndexed_of_isChartOfClass_isCountablyWeaklyAdmissible
    {U : FppfSheaf B S hS}
    (hU : IsChartOfClass B S hS TopologicalRing.IsCountablyWeaklyAdmissible U) :
    IsCountablyIndexed B S hS U := by
  obtain ⟨A, i₁, i₂, i₃, i₄, ⟨hwa, hcount⟩, Q, ⟨e⟩⟩ := hU
  exact isCountablyIndexed_of_isPresentingRing B S hS U A ⟨hwa,
    ⟨{ Q.weakIdealColimitPresentation with
      colimitIso := e ≪≫ Q.weakIdealColimitPresentation.colimitIso }⟩⟩ hcount

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The affine case of Stacks 0GBB, clause (1).** The fibre product of two countably indexed
affine formal algebraic spaces over a third is countably indexed: by Stacks 0AN3 clause (3) it
is the formal spectrum of the completed tensor product of their weakly admissible topological
rings, which has a countable fundamental system of neighbourhoods of `0` by Lemma 87.4.12
(Stacks 0GB4). -/
theorem isCountablyIndexed_pullback_of_isCountablyIndexed {U V W : FppfSheaf B S hS}
    (t : U ⟶ V) (s : W ⟶ V) (hU : IsCountablyIndexed B S hS U)
    (hV : IsCountablyIndexed B S hS V) (hW : IsCountablyIndexed B S hS W) :
    IsCountablyIndexed B S hS (pullback t s) := by
  obtain ⟨A₀, j0a, j0b, j0c, j0d, ⟨h₀, hc₀⟩, D₀, ⟨eV⟩⟩ :=
    isChartOfClass_isCountablyWeaklyAdmissible_of_isCountablyIndexed B S hS hV
  obtain ⟨A₁, j1a, j1b, j1c, j1d, ⟨h₁, hc₁⟩, D₁, ⟨eU⟩⟩ :=
    isChartOfClass_isCountablyWeaklyAdmissible_of_isCountablyIndexed B S hS hU
  obtain ⟨A, j2a, j2b, j2c, j2d, ⟨hA, hcA⟩, D, ⟨eW⟩⟩ :=
    isChartOfClass_isCountablyWeaklyAdmissible_of_isCountablyIndexed B S hS hW
  obtain ⟨c₁, hc₁map, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq h₀ h₁
    (eU.inv ≫ t ≫ eV.hom)
  obtain ⟨c, hcmap, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq h₀ hA
    (eW.inv ≫ s ≫ eV.hom)
  let : Algebra A₀ A₁ := c₁.toRingHom.toAlgebra
  let : Algebra A₀ A := c.toRingHom.toAlgebra
  have hsq1 : t ≫ eV.hom = eU.hom ≫ formalSpectrumMap h₀ c₁ := by
    rw [hc₁map, Iso.hom_inv_id_assoc]
  have hsq2 : s ≫ eV.hom = eW.hom ≫ formalSpectrumMap h₀ c := by
    rw [hcmap, Iso.hom_inv_id_assoc]
  have hpb : IsPullback (pullback.fst t s ≫ eU.hom) (pullback.snd t s ≫ eW.hom)
      (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) :=
    (IsPullback.of_hasPullback t s).of_iso (Iso.refl _) eU eW eV (by simp)
      (by simp) (by simp [hsq1]) (by simp [hsq2])
  obtain ⟨DT, -, -, eT, -⟩ :=
    exists_quotientSystem_iso_pullback_completedTensorProduct_of_isWeaklyAdmissible B S hS
      h₀ h₁ hA D₀ D₁ D c₁ c rfl rfl
  exact isCountablyIndexed_of_isChartOfClass_isCountablyWeaklyAdmissible B S hS
    ⟨_, _, _, _, _, TopologicalRing.isCountablyWeaklyAdmissible_completedTensorProduct
      ⟨h₁, hc₁⟩ ⟨hA, hcA⟩, DT, ⟨hpb.isoPullback ≪≫ eT⟩⟩

end

/-- **Stacks 0AJ3 for the fibre product of the source's proof of Stacks 0GBD.** Let `f : X ⟶ Y`
and `g : Z ⟶ Y` be morphisms of formal algebraic spaces. Given a covering `{Vⱼ ⟶ Y}` as in
Definition 0AIM and coverings `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and `{Wⱼₖ ⟶ Vⱼ ×_Y Z}` of the same kind, the
fibre product `X ×_Y Z` is a formal algebraic space: the chart fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ`
are an atlas of it, and its set-theoretic condition is
`satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts`, whose three inputs
of representable relative products are Stacks 0AIP for `X`, `Y` and `Z`. -/
theorem isFormalAlgebraicSpace_pullback_of_chartCovers
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j)) :
    IsFormalAlgebraicSpace B S hS (pullback f g) := by
  obtain ⟨Λ, T, -, c, -, -, hc, -⟩ :=
    exists_affineEtaleCover_chartFactorization_pullback_snd B S hS f g V v hV U a hU W b hW
  exact ⟨satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS f g
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX)
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hZ) hX.1 hZ.1,
    Λ, T, c, hc⟩

/-- **Stacks 0GBB, clause (1), on the chart cover of the source's proof.** With the covers of
`isFormalAlgebraicSpace_pullback_of_chartCovers`, if the charts `Vⱼ`, `Uⱼᵢ` and `Wⱼₖ` are
countably indexed, then `X ×_Y Z` is locally countably indexed: the chart fibre products
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` are an atlas of it, and they are countably indexed by
`isCountablyIndexed_pullback_of_isCountablyIndexed`. -/
theorem isLocallyCountablyIndexed_pullback_of_chartCovers
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVc : ∀ j, IsCountablyIndexed B S hS (V j))
    (hUc : ∀ j i, IsCountablyIndexed B S hS (U j i))
    (hWc : ∀ j k, IsCountablyIndexed B S hS (W j k)) :
    IsLocallyCountablyIndexed B S hS (pullback f g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨isFormalAlgebraicSpace_pullback_of_chartCovers B S hS f g hX hY hZ V v hV U a hU W b
    hW, Σ j, I j × K j, fun p ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
    fun p ↦ ?_, fun p ↦ ?_,
    isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hV.2.2 a
      (fun j ↦ (hU j).2.2) b fun j ↦ (hW j).2.2, fun p ↦ ?_⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hV.1 p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hV.1 p.1))
      ((hU p.1).1 p.2.1) ((hW p.1).1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hV.2.1 p.1) ((hU p.1).2.1 p.2.1) ((hW p.1).2.1 p.2.2)
  · exact isCountablyIndexed_pullback_of_isCountablyIndexed B S hS _ _ (hUc p.1 p.2.1)
      (hVc p.1) (hWc p.1 p.2.2)

section TargetCover

variable {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) {V U W : FppfSheaf B S hS}
  (v : V ⟶ Y) (a : U ⟶ pullback v f) (b : W ⟶ pullback v g)

/-- The comparison `W ×_Z (X ×_Y Z) ⟶ V ×_Y X` for a chart `b : W ⟶ V ×_Y Z`, induced by the
map `W ⟶ V` and the projection `X ×_Y Z ⟶ X`. -/
private def chartFibreCompare :
    pullback (b ≫ pullback.snd v g) (pullback.snd f g) ⟶ pullback v f :=
  pullback.lift (pullback.fst (b ≫ pullback.snd v g) (pullback.snd f g) ≫ b ≫ pullback.fst v g)
    (pullback.snd (b ≫ pullback.snd v g) (pullback.snd f g) ≫ pullback.fst f g) (by
      have h := pullback.condition (f := b ≫ pullback.snd v g) (g := pullback.snd f g) =≫ g
      simp only [Category.assoc] at h ⊢
      rw [pullback.condition (f := v) (g := g), h, ← pullback.condition (f := f) (g := g)])

/-- The map `U ×_V W ⟶ W ×_Z (X ×_Y Z)` from a chart fibre product to the fibre of `pr₂` over
the chart `W ⟶ Z`. -/
private def chartFibreMap :
    pullback (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ⟶
      pullback (b ≫ pullback.snd v g) (pullback.snd f g) :=
  pullback.lift (pullback.snd (a ≫ pullback.fst v f) (b ≫ pullback.fst v g))
    (chartPullbackMap B S hS f g v a b) (chartPullbackMap_comp_snd B S hS f g v a b).symm

/-- `W ×_Z (X ×_Y Z)` is the fibre product of `W` with `V ×_Y X` over `V`. -/
private theorem isPullback_chartFibreCompare :
    IsPullback (pullback.fst (b ≫ pullback.snd v g) (pullback.snd f g))
      (chartFibreCompare B S hS f g v b) (b ≫ pullback.fst v g) (pullback.fst v f) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback v f)
  have e1 : chartFibreCompare B S hS f g v b ≫ pullback.snd v f =
      pullback.snd (b ≫ pullback.snd v g) (pullback.snd f g) ≫ pullback.fst f g :=
    pullback.lift_snd _ _ _
  have e2 : (b ≫ pullback.fst v g) ≫ v = (b ≫ pullback.snd v g) ≫ g := by
    simp only [Category.assoc, pullback.condition]
  rw [e1, e2]
  exact (IsPullback.of_hasPullback (b ≫ pullback.snd v g) (pullback.snd f g)).paste_vert
    (IsPullback.of_hasPullback f g).flip

/-- `U ×_V W` is the base change of the chart `a : U ⟶ V ×_Y X` along the comparison
`W ×_Z (X ×_Y Z) ⟶ V ×_Y X`. -/
private theorem isPullback_chartFibreMap :
    IsPullback (pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g))
      (chartFibreMap B S hS f g v a b) a (chartFibreCompare B S hS f g v b) := by
  have hcomm : pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ≫ a =
      chartFibreMap B S hS f g v a b ≫ chartFibreCompare B S hS f g v b := by
    refine pullback.hom_ext ?_ ?_
    · simp only [chartFibreCompare, chartFibreMap, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
      exact pullback.condition
    · simp only [chartFibreCompare, chartFibreMap, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, chartPullbackMap_comp_fst]
  refine IsPullback.of_bot ?_ hcomm (isPullback_chartFibreCompare B S hS f g v b).flip
  rw [show chartFibreMap B S hS f g v a b ≫
      pullback.fst (b ≫ pullback.snd v g) (pullback.snd f g) =
        pullback.snd (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) from pullback.lift_fst _ _ _]
  exact IsPullback.of_hasPullback _ _

end TargetCover

/-- **The chart argument of Stacks 0GBD, in the form of condition (2) of Stacks 0ANG for
`pr₂`**, at an arbitrary class `C` of weakly admissible topological rings. Given a covering
`{Vⱼ ⟶ Y}` as in Definition 0AIM and coverings `{Uⱼᵢ ⟶ Vⱼ ×_Y X}`, `{Wⱼₖ ⟶ Vⱼ ×_Y Z}` of the
same kind, with presentations of the charts `Vⱼ` and `Uⱼᵢ` by rings of the class, the charts
`Wⱼₖ ⟶ Z` cover `Z`, the chart fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` cover `Wⱼₖ ×_Z (X ×_Y Z)`, and
each of them maps to `Wⱼₖ` by a morphism with `P`, the completed tensor product presenting it
by Stacks 0AN3 clause (3) and the base-change axiom giving `P`. -/
theorem hasPropertyAfterTargetCover_pullback_snd_of_chartPresentations
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hbc : CompletedTensorBaseChangeAxiom.{u} C P Q)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVch : ∀ j, IsChartOfClass B S hS C (V j))
    (hUch : ∀ j i, IsChartOfClass B S hS C (U j i))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C Q g) :
    HasPropertyAfterTargetCover B S hS C P (pullback.snd f g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨Σ j, K j, fun p ↦ W p.1 p.2, fun p ↦ b p.1 p.2 ≫ pullback.snd (v p.1) g,
    ⟨fun p ↦ (hW p.1).1 p.2, fun p ↦ IsRepresentableEtale.comp B S hS ((hW p.1).2.1 p.2)
      (isRepresentableEtale_pullback_snd B S hS (v p.1) g (hV.2.1 p.1)),
      Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (fun j ↦ pullback.snd (v j) g) b
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd g v hV.2.2) fun j ↦ (hW j).2.2⟩,
    fun p ↦ ⟨I p.1, fun i ↦ pullback (a p.1 i ≫ pullback.fst (v p.1) f)
      (b p.1 p.2 ≫ pullback.fst (v p.1) g),
      fun i ↦ chartFibreMap B S hS f g (v p.1) (a p.1 i) (b p.1 p.2),
      ⟨fun i ↦ ?_, fun i ↦ ?_, ?_⟩, fun i ↦ ?_⟩⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hV.1 p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hV.1 p.1))
      ((hU p.1).1 i) ((hW p.1).1 p.2)
  · exact isRepresentableEtale_of_isPullback B S hS
      (isPullback_chartFibreMap B S hS f g (v p.1) (a p.1 i) (b p.1 p.2)) ((hU p.1).2.1 i)
  · exact isLocallySurjective_sigmaDesc_of_isPullback B S hS _
      (fun i ↦ isPullback_chartFibreMap B S hS f g (v p.1) (a p.1 i) (b p.1 p.2)) (hU p.1).2.2
  · rw [show chartFibreMap B S hS f g (v p.1) (a p.1 i) (b p.1 p.2) ≫ pullback.fst _ _ =
      pullback.snd (a p.1 i ≫ pullback.fst (v p.1) f) (b p.1 p.2 ≫ pullback.fst (v p.1) g) from
        pullback.lift_fst _ _ _]
    exact hasPropertyOnAffineChartMap_of_isChartBaseChangeOn B S hS C P Q hbc hiso f g hf hg _
      (isChartBaseChangeOf_chartPullback B S hS C hCwa f g V v hV U a hU W b hW hVch hUch
        p.1 i p.2)

/-- **The chart argument of Stacks 0GBD, in the form of condition (3) of Stacks 0ANG with charts
of the class.** On the covering of `X ×_Y Z` by the chart fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ`,
each mapping to the chart `Wⱼₖ` of `Z`, the second projection has `P` on charts, and the members
of the covering and their target charts are charts of the class `C`, as soon as the charts `Vⱼ`,
`Uⱼᵢ`, `Wⱼₖ` and the chart fibre products are. This is the form of condition (3) that the
implication (3) ⟹ (1) of Stacks 0ANG,
`hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal`, consumes. -/
theorem hasPropertyAfterSourceCoverOfClass_pullback_snd_of_chartPresentations
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hbc : CompletedTensorBaseChangeAxiom.{u} C P Q)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVch : ∀ j, IsChartOfClass B S hS C (V j))
    (hUch : ∀ j i, IsChartOfClass B S hS C (U j i))
    (hWch : ∀ j k, IsChartOfClass B S hS C (W j k))
    (hTch : ∀ j i k, IsChartOfClass B S hS C
      (pullback (a j i ≫ pullback.fst (v j) f) (b j k ≫ pullback.fst (v j) g)))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C Q g) :
    HasPropertyAfterSourceCoverOfClass B S hS C P (pullback.snd f g) := by
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
      hTch p.1 p.2.1 p.2.2, hWch p.1 p.2.2,
      hasPropertyOnAffineChartMap_of_isChartBaseChangeOn B S hS C P Q hbc hiso f g hf hg _
        (isChartBaseChangeOf_chartPullback B S hS C hCwa f g V v hV U a hU W b hW hVch hUch
          p.1 p.2.1 p.2.2)⟩

/-- **The chart argument of Stacks 0GBD on locally countably indexed formal algebraic spaces,
at the étale case of Stacks 0AJH.** Let `P` be a local property of morphisms of `WAdm^count`
stable under base change, invariant under isomorphism of targets, and let `f : X ⟶ Y`,
`g : Z ⟶ Y` be morphisms of locally countably indexed formal algebraic spaces. If `f`
satisfies condition (1) of Stacks 0ANG, then `X ×_Y Z` is locally countably indexed
(Stacks 0GBB, clause (1)), and `pr₂` satisfies condition (2) of Stacks 0ANG and condition (3)
in the form with charts of the class.

The covering is the source's: `{Vⱼ ⟶ Y}` is the countably indexed atlas of `Y`, the charts
`Uⱼᵢ` of `Vⱼ ×_Y X` come from `exists_affineEtaleCover_pullback_of_atlas` for the countably
indexed atlas of `X`, so that each maps representably to a countably indexed member of it and
is countably indexed by Stacks 0AKQ, and the charts `Wⱼₖ` of `Vⱼ ×_Y Z` come from the same
lemma for the atlas of `Z`. The one input is `hEt`, the étale case of Stacks 0AJH, through
which the fibre products `Vⱼ ×_Y Xₘ` have atlases at all. -/
theorem isLocallyCountablyIndexed_pullback_and_hasPropertyAfterCovers_of_etale
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    IsLocallyCountablyIndexed B S hS (pullback f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterSourceCoverOfClass B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) := by
  obtain ⟨J, V, v, hVaff, hVet, hVsurj, hVc⟩ := hY.2
  obtain ⟨M, Xm, x, hXaff, hXet, hXsurj, hXc⟩ := hX.2
  obtain ⟨N, Zn, z, hZaff, hZet, hZsurj, hZc⟩ := hZ.2
  have hV : IsAffineEtaleCover B S hS V v := ⟨hVaff, hVet, hVsurj⟩
  choose I U a ι r hU hr hra using fun j ↦ exists_affineEtaleCover_pullback_of_atlas B S hS
    hEt f (v j) (hVet j) x ⟨hXaff, hXet, hXsurj⟩
  choose K W b ιZ rZ hW hrZ hrbZ using fun j ↦ exists_affineEtaleCover_pullback_of_atlas B S hS
    hEt g (v j) (hVet j) z ⟨hZaff, hZet, hZsurj⟩
  have hUc : ∀ j i, IsCountablyIndexed B S hS (U j i) := fun j i ↦
    isCountablyIndexed_of_isRepresentable B S hS (r j i)
      ((hU j).1 i) (hXaff (ι j i)) (hr j i).1 (hXc (ι j i))
  have hWc : ∀ j k, IsCountablyIndexed B S hS (W j k) := fun j k ↦
    isCountablyIndexed_of_isRepresentable B S hS (rZ j k)
      ((hW j).1 k) (hZaff (ιZ j k)) (hrZ j k).1 (hZc (ιZ j k))
  have ch := fun {T : FppfSheaf B S hS} (hT : IsCountablyIndexed B S hS T) ↦
    isChartOfClass_isCountablyWeaklyAdmissible_of_isCountablyIndexed B S hS hT
  have hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], TopologicalRing.IsCountablyWeaklyAdmissible R →
        TopologicalRing.IsWeaklyAdmissible R := by intro R _ _ _ _ h; exact h.1
  exact ⟨isLocallyCountablyIndexed_pullback_of_chartCovers B S hS f g hX.1 hY.1 hZ.1 V v hV U a
      hU W b hW hVc hUc hWc,
    hasPropertyAfterTargetCover_pullback_snd_of_chartPresentations B S hS _ hCwa P
      (fun _ ↦ True) (completedTensorBaseChangeAxiom_of_isStableUnderBaseChange P hP) hiso f g V v
      hV U a hU W b hW (fun j ↦ ch (hVc j))
      (fun j i ↦ ch (hUc j i)) hf (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g),
    hasPropertyAfterSourceCoverOfClass_pullback_snd_of_chartPresentations B S hS _ hCwa P
      (fun _ ↦ True) (completedTensorBaseChangeAxiom_of_isStableUnderBaseChange P hP) hiso f g V v
      hV U a hU W b hW (fun j ↦ ch (hVc j))
      (fun j i ↦ ch (hUc j i)) (fun j k ↦ ch (hWc j k))
      (fun j i k ↦ ch (isCountablyIndexed_pullback_of_isCountablyIndexed B S hS _ _ (hUc j i)
        (hVc j) (hWc j k)))
      hf (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)⟩

end AlgebraicGeometry.FormalSpace

end

module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.Topology.Constructible.MeetConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The complement of a finitely presented closed subspace is retrocompact

Let `X` be an algebraic space over a scheme `S` and let `Z ⊆ X` be a closed subspace whose
inclusion is of finite presentation.  Then the inclusion of the open complement `X ∖ Z` is a
*quasi-compact* morphism; equivalently, the point set of `X ∖ Z` meets every quasi-compact open
of `|X|` in a quasi-compact set.

This is the observation the source makes in passing in the prose before equation (0AEX) —
"Observe that `j` and `j'` are quasi-compact morphisms as `Z → X` is of finite presentation" —
and it is the only use that prose makes of the finite presentation of `Z`.  It is what brings
the direct images along the two open immersions of a formal glueing situation under
Stacks 03M9.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_ι_openComplement_of_isFinitePresentation`: the
  inclusion of the complement of a finitely presented closed subspace is quasi-compact.

## Implementation notes

Quasi-compactness of a morphism is étale local on the target (Stacks 03KG, available as
`AlgebraicGeometry.Space.isQuasiCompact_of_surjectiveEtale_atlas`), so it may be checked after
base change along one surjective étale chart out of a representable.  That base change is the
inclusion of the inverse image subfunctor, which is again an open subspace, and over a
representable an open subspace is represented by an open subscheme
(`AlgebraicGeometry.Space.exists_openImmersion_of_isOpenSubspace`).  The closed part becomes the
image of a closed immersion of schemes `C ⟶ V`, which is *locally of finite presentation*
precisely because the chart is étale: `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` is
a condition on étale charts, so an arbitrary base change would not deliver it, and that is why
the reduction is to an étale chart rather than to the affine test objects of
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine`.

The two point sets are complementary by
`AlgebraicGeometry.Space.range_pointsMap_ι_openComplement`, transported to the schemes along the
comparison of Stacks 03BX; so the image of the open subscheme is the complement of the image of
`C`.  That image is constructible by Chevalley's theorem, hence its complement is retrocompact,
hence the open immersion is quasi-compact as a morphism of schemes.

Chevalley's theorem in Mathlib, `AlgebraicGeometry.Scheme.Hom.isConstructible_image`, asks its
target to be quasi-compact and quasi-separated, so it does not apply to `V` directly.
Retrocompactness of the complement is therefore proved affine-locally: on an affine open `W` of
`V` the restriction `i|_W` is still a closed immersion locally of finite presentation, both
properties being local at the target, and `retroIsRetrocompact_of_affine_local` globalises from
the affine opens, which is possible because every quasi-compact open is covered by finitely many
affine opens contained in it.

One input used here is `private` elsewhere in the tree and is therefore reproved as
`retroPresheafEtale_of_isPullback`: base-change stability of "étale after every representable
base change".

## References

* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Retrocompactness of a subset of a scheme may be checked on the affine opens: every
quasi-compact open is covered by finitely many affine opens contained in it. -/
@[ega "IV 1.8.1" "Sufficiency"]
private theorem retroIsRetrocompact_of_affine_local {V' : Scheme.{u}} {E : Set V'}
    (haff : ∀ W : V'.Opens, IsAffineOpen W → IsCompact (W.ι.base ⁻¹' E)) :
    IsRetrocompact E := by
  classical
  intro K hKcompact hKopen
  let A : V'.Opens := ⟨K, hKopen⟩
  let ι := {W : V'.Opens // IsAffineOpen W ∧ (W : Set V') ⊆ K}
  let O : ι → Set V' := fun W => W.1
  have hcover : K ⊆ ⋃ W : ι, O W := by
    intro s hs
    obtain ⟨W, hWa, hsW, hWA⟩ := exists_isAffineOpen_mem_and_subset (U := A) hs
    exact Set.mem_iUnion.mpr ⟨⟨W, hWa, hWA⟩, hsW⟩
  obtain ⟨T, hT⟩ := hKcompact.elim_finite_subcover O (fun W => W.1.2) hcover
  have hcompact (W : ι) : IsCompact (O W ∩ E) := by
    simpa [O, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
      using (haff W.1 W.2.1).image W.1.ι.continuous
  have heq : E ∩ K = ⋃ W ∈ T, O W ∩ E := by
    ext s
    constructor
    · rintro ⟨hsE, hsK⟩
      obtain ⟨W, hWT, hsW⟩ := Set.mem_iUnion₂.mp (hT hsK)
      exact Set.mem_iUnion₂.mpr ⟨W, hWT, hsW, hsE⟩
    · intro hs
      obtain ⟨W, -, hsW, hsE⟩ := Set.mem_iUnion₂.mp hs
      exact ⟨hsE, W.2.2 hsW⟩
  rw [heq]
  exact T.isCompact_biUnion fun W _ => hcompact W

/-- **Stacks 09YH for the image of a closed immersion of finite presentation.** The complement
of the image of a closed immersion locally of finite presentation is retrocompact: on every
affine open of the target the image is constructible by Chevalley's theorem, so its complement
there is retrocompact, hence compact. -/
private theorem retroIsRetrocompact_compl_range {C' V' : Scheme.{u}} (i : C' ⟶ V')
    [_root_.AlgebraicGeometry.IsClosedImmersion i] [LocallyOfFinitePresentation i] :
    IsRetrocompact (Set.range ⇑i)ᶜ := by
  refine retroIsRetrocompact_of_affine_local fun W hW => ?_
  have _ : IsAffine W.toScheme := hW
  have hr : Set.range ⇑(i ∣_ W) = W.ι.base ⁻¹' Set.range ⇑i := by
    rw [morphismRestrict_base]
    exact Set.range_restrictPreimage _ _
  rw [Set.preimage_compl, ← hr]
  have hc : Topology.IsConstructible (Set.range ⇑(i ∣_ W)) := by
    simpa only [Set.image_univ] using
      (i ∣_ W).isConstructible_image (s := Set.univ) Topology.IsConstructible.univ
  exact (IsRetrocompact_of_IsConstructible hc.compl).isCompact

/-- The scheme-level input: an open immersion whose image is the complement of the image of a
closed immersion locally of finite presentation is quasi-compact.

The complement of the image of the closed immersion is retrocompact by
`retroIsRetrocompact_compl_range`, which says exactly that its intersection with every
quasi-compact open is quasi-compact; the open immersion is a homeomorphism onto that
complement, so the preimage of a quasi-compact open is quasi-compact. -/
private theorem retroQuasiCompact_of_range_eq_compl {C' V' W' : Scheme.{u}}
    (i : C' ⟶ V') (j : W' ⟶ V')
    [_root_.AlgebraicGeometry.IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j)
    (hrange : Set.range ⇑j = (Set.range ⇑i)ᶜ) :
    QuasiCompact j := by
  refine ⟨fun U hUopen hUcompact => ?_⟩
  have hemb : Topology.IsEmbedding j.base := hj.base_open.isEmbedding
  rw [hemb.isCompact_iff, Set.image_preimage_eq_inter_range, Set.inter_comm, hrange]
  exact retroIsRetrocompact_compl_range i hUcompact hUopen

/-- Étaleness after every representable base change is stable under base change. -/
private theorem retroPresheafEtale_of_isPullback
    {P₁ P₂ P₃ P₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : P₁ ⟶ P₂} {b : P₁ ⟶ P₃} {c : P₂ ⟶ P₄} {d : P₃ ⟶ P₄}
    (h : IsPullback a b c d)
    (hc : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := ⟨by
    intro _ _ _ _ _ _ _ _ hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
      (hs.map (BigFppfOver.toScheme B S hS)) hg⟩
  have _ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback h hc

/-- **The complement of a finitely presented closed subspace is retrocompact.** Let `X` be an
algebraic space over `S` and let `Z ⊆ X` be a closed subspace whose inclusion is of finite
presentation. Then the inclusion of the open complement `X \ Z` is a quasi-compact morphism.

This is the parenthetical observation of Stacks 0AEX that the two open immersions of a formal
glueing situation are quasi-compact because the closed subspace is of finite presentation.

Quasi-compactness is étale local on the target by Stacks 03KG, so it may be checked after base
change to a surjective étale chart `h_V ⟶ X`. Over the chart both subspaces become subspaces of
`h_V`: the closed one is the image of a closed immersion of schemes `C ⟶ V` which is locally of
finite presentation, because `Z ⟶ X` is, and the open one is represented by an open subscheme
`W ⊆ V`. Their point sets are complementary, so the image of `W` is the complement of the image
of `C`, which is constructible by Chevalley's theorem and therefore has retrocompact
complement. -/
theorem isQuasiCompact_ι_openComplement_of_isFinitePresentation
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (Z : Subfunctor F) (hZ : IsClosedSubspace B S hS Z)
    (hfp : IsFinitePresentation B S hS Z.ι) :
    IsQuasiCompact B S hS (openComplement B S hS Z).ι := by
  obtain ⟨V, φ, hsurj, hetale⟩ := hF.exists_atlas
  have hO := isOpenSubspace_openComplement B S hS hF Z hZ
  refine isQuasiCompact_of_surjectiveEtale_atlas B S hS (openComplement B S hS Z).ι
    hO.1 hF V φ (isSurjective_of_presheafSurjective B S hS φ hsurj)
    (fun _ _ hψ => (isMultiplicative_presheaf_etale B S hS).comp_mem _ _ hψ hetale) ?_
  have hsqT := Subfunctor.isPullback_preimage φ (openComplement B S hS Z)
  have hkey : IsQuasiCompact B S hS ((openComplement B S hS Z).preimage φ).ι := by
    obtain ⟨W, j, e, hjoi, he⟩ := exists_openImmersion_of_isOpenSubspace B S hS V _
      (isOpenSubspace_preimage B S hS φ _ hF (isAlgebraicSpace_yoneda B S hS V) hO)
    have hsqZ := hZ.2.1.isPullback φ
    have hiCI : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd φ)) :=
      hZ.2.2 φ (hZ.2.1.fst φ) (hZ.2.1.snd φ) hsqZ
    have hiFP : LocallyOfFinitePresentation
        ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd φ)) :=
      hfp.1 (hZ.2.1.pullback φ) V (hZ.2.1.fst φ) φ (hZ.2.1.snd φ)
        (retroPresheafEtale_of_isPullback B S hS hsqZ.flip hetale) hetale hsqZ.w.symm
    have hsqZpre := Subfunctor.isPullback_preimage φ Z
    have hrange_iso {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : P ⟶ Q) [IsIso g]
        (f : Q ⟶ R) :
        Set.range (pointsMap B S hS P (g ≫ f)) = Set.range (pointsMap B S hS Q f) := by
      rw [pointsMap_comp, Set.range_comp, (bijective_pointsMap_of_isIso B S hS g).2.range_eq,
        Set.image_univ]
    have hrangeZ :
        Set.range (pointsMap B S hS (yoneda.obj (hZ.2.1.pullback φ))
            (yoneda.map (hZ.2.1.snd φ))) =
          Set.range (pointsMap B S hS (Z.preimage φ).toFunctor (Z.preimage φ).ι) := by
      rw [← IsPullback.isoIsPullback_hom_snd _ _ hsqZ hsqZpre, hrange_iso]
    have hrangej : Set.range ((BigFppfOver.toScheme B S hS).map j) =
        (Set.range ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd φ)))ᶜ := by
      rw [← image_pointsToScheme_range B S hS j,
        ← image_pointsToScheme_range B S hS (hZ.2.1.snd φ), hrangeZ,
        ← Set.image_compl_eq (bijective_pointsToScheme B S hS V)]
      congr 1
      rw [← he, hrange_iso, pointsRange_preimage, range_pointsMap_ι_openComplement,
        Set.preimage_compl, pointsRange_preimage]
    refine isQuasiCompact_of_isIso_comp B S hS e.hom ?_
    rw [he]
    exact isQuasiCompact_yoneda_map B S hS j
      (retroQuasiCompact_of_range_eq_compl _ _ hjoi hrangej)
  have hqc := isQuasiCompact_isIso_comp B S hS hsqT.isoPullback.inv hkey
  rwa [hsqT.isoPullback_inv_snd] at hqc

end AlgebraicGeometry.Space

end

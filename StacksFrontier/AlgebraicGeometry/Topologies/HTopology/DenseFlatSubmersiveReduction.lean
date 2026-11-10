module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongCoproduct
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.StratificationDensePhCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.UniversallySubmersive
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.CoveringsParts0DBI

/-!
# Reducing Stacks 0ETT to the case of a family flat over a dense open

The implication (1) ⟹ (2) of Stacks 0ETT — a finite family of finite type morphisms to a
Noetherian scheme whose disjoint-union morphism is universally submersive is an h covering —
reduces to the statement that such a family is refined by a ph covering,
`AlgebraicGeometry.UniversallySubmersiveHasPHRefinement`. The Stacks proof of that refinement has
two halves. The first, steps 1 and 2 of the source, is a reduction: stratify the base by generic
flatness, replace each closed subscheme of the stratification by the scheme-theoretic closure of
its stratum, and solve the problem over each of those separately. The second, steps 3 to 5, is
the flattening blowup of Stacks 0815 followed by a valuative argument.

This file carries out the first half. It isolates the case the reduction arrives at as
`AlgebraicGeometry.DenseFlatUniversallySubmersiveHasPHRefinement` — the same statement with the
extra datum of a dense open of the base over which every member of the family is flat — and
proves that this case implies the general one. The second half is
`StacksFrontier/AlgebraicGeometry/Topologies/HTopology/SubmersiveFlatteningRefinement.lean`, which
proves that case and hence Stacks 0ETT.

## Main definitions

* `AlgebraicGeometry.DenseFlatUniversallySubmersiveHasPHRefinement`: a finite family of finite
  type morphisms to a Noetherian scheme whose disjoint-union morphism is universally submersive
  and which is flat over a dense open of the base is refined by a ph covering.

## Main results

* `AlgebraicGeometry.flat_pullback_snd_comp_left`: if the base change of `f` along `g` is flat,
  so is the base change of `p ≫ f` for `p` flat. Applied to `p` the inclusion of a summand of a
  coproduct, this splits flatness of the base change of `∐ fᵢ` into flatness of the base changes
  of the `fᵢ`.
* `AlgebraicGeometry.universallySubmersive_sigmaDesc_pullback`: the disjoint-union morphism of a
  base changed family is universally submersive when that of the original family is.
* `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement.of_denseFlat`: **steps 1 and 2 of the
  proof of Stacks 0ETT (1) ⟹ (2)** — the dense flat case implies the general case.
* `AlgebraicGeometry.IsHCovering.of_universallySubmersive_of_denseFlat` and
  `AlgebraicGeometry.universallySubmersive_sigmaDesc_iff_isHCovering_of_denseFlat`: Stacks 0ETT
  (1) ⟹ (2) and Stacks 0ETT, carrying only the dense flat case as a hypothesis.

## Implementation notes

The two base change lemmas are what makes the reduction go through, and both are pure
pullback-pasting. Flatness of the base change of a single member is read off flatness of the base
change of the coproduct through `AlgebraicGeometry.flat_pullback_snd_comp_left`, because the
inclusion `Yᵢ ⟶ ∐ Y` of a summand is an open immersion and hence flat; and the base change of
the coproduct along the closed immersion of a stratum is again a coproduct, which is the content
of `AlgebraicGeometry.isPullback_sigmaDesc_sigmaMap`, so universal submersiveness passes to it by
stability under base change. The latter needs the symmetry isomorphism of fibre products, because
`AlgebraicGeometry.isPullback_sigmaDesc_sigmaMap` presents the base change with the pulled back
scheme on the left while the covering machinery uses `CategoryTheory.Limits.pullback.snd`.

Quasi-compactness of `∐ Y ⟶ X` is obtained from Noetherianness of the source rather than
directly: `∐ Y` is covered by the finitely many opens that are the ranges of the inclusions of
the summands, each compact because each `Yᵢ ⟶ X` is quasi-compact and `X` is compact, so `∐ Y` is
a compact scheme; it is locally Noetherian because `∐ Y ⟶ X` is locally of finite type, and a
morphism out of a Noetherian scheme is quasi-compact.

The ph covering produced at the end is the two-step covering
`CategoryTheory.PreZeroHypercover.bind` of the covering by the closures of the strata with the
coverings the hypothesis supplies over each of them, which is a ph covering by Stacks 0DBI part
(2). Its refinement morphism to the original family sends a member to the member of the original
family that the inner refinement over its stratum points at, through the projection
`Yᵢ ×_X Zₖ ⟶ Yᵢ`.

No tag is attached to anything here. The two forms of Stacks 0ETT below are conditional, exactly
as `AlgebraicGeometry.isHCovering_of_universallySubmersive` and
`AlgebraicGeometry.universallySubmersive_sigmaDesc_iff_isHCovering` are; what
is proved here is only that the hypothesis they carry may be weakened to the dense flat case. The
tag sits on the unconditional forms in
`StacksFrontier/AlgebraicGeometry/Topologies/HTopology/SubmersiveFlatteningRefinement.lean`.

**Why the dense flat case still needs Stacks 0815.** It is tempting to try to close
`AlgebraicGeometry.DenseFlatUniversallySubmersiveHasPHRefinement` from the stratification
machinery alone, without any flattening: over the dense open `U` the family is flat, locally of
finite presentation and -- by surjectivity of the submersive disjoint-union morphism -- jointly
surjective, hence an fppf covering of `U`, so it is refined by a ph covering there
(`AlgebraicGeometry.IsHCovering.of_universallySubmersive_of_flat`); and over the closed
complement `Z` of `U` the base changed family is again a finite family of finite type morphisms
to a Noetherian scheme with universally submersive disjoint-union morphism, so an induction on
the base would refine it there. That route is blocked, and not for want of effort: the two pieces
cannot be glued, because `{U ⟶ X, Z ⟶ X}` is a ph covering only when `U` is closed. A ph
covering has universally submersive disjoint-union morphism (Stacks 0ETP,
`AlgebraicGeometry.isVCovering_universallySubmersive` composed with
`AlgebraicGeometry.isVCovering_of_isPHCovering`), and `U ⊔ Z ⟶ X` is not submersive as soon as
`Z` is not open: the preimage of `Z` is empty in `U` and all of `Z` in `Z`, hence open, while `Z`
itself is not. Equivalently, and directly from the definition: a proper surjective `V ⟶ X`
decomposed into opens mapping into `U` respectively into `Z` has both opens closed in `V`, hence
proper over `X`, so their images are closed and cover `X`, which forces `U` closed. This is
exactly what the blowup of Stacks 0815 buys -- a *proper surjective* base change after which the
family is flat over the whole base, rather than a decomposition of the base into an open and its
complement.

What the dense flat case still needs is therefore precisely steps 3 to 5 of the source:
Stacks 0815 (`AlgebraicGeometry.finitePresentationHasFlatteningBlowup` in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/GenericFibreFreeBlowup0811.lean`), together
with Stacks 0CM2 (`AlgebraicGeometry.nonempty_discreteValuationSpecialization`) and Stacks 0DBT
(`AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage`) — all three available. The valuative
heart of step 4 is `AlgebraicGeometry.exists_specializes_closedPoint_of_universallySubmersive` in
`StacksFrontier/AlgebraicGeometry/Topologies/HTopology/SubmersiveSpecialization.lean`, proved with
no carried hypothesis: for a universally submersive morphism of finite type and a map from the
spectrum of a discrete valuation ring into its target, the base change carries a specialization
lying over the generic and the closed point. Those steps are assembled in
`StacksFrontier/AlgebraicGeometry/Topologies/HTopology/SubmersiveFlatteningRefinement.lean`, which
proves the dense flat case — and so Stacks 0ETT — with nothing granted; no second, Stacks 080Y
blowup is needed there, the complement of the exceptional divisor serving as the dense open the
valuative argument runs over.

The reduction is stated for Stacks 0ETT and not for Stacks 0ETR, whose proof performs the same
two steps: there the base is affine but not Noetherian, so quasi-compactness of the stratum —
which is what `AlgebraicGeometry.Scheme.Opens.exists_denseOpens_closure` needs — has to come from
the finite type clause of `AlgebraicGeometry.HasFlatStratification` on the ideal sheaf cutting out
the removed part rather than from the ambient scheme, and that step is not available here.

## References

* [Stacks Project, Tag 0ETT](https://stacks.math.columbia.edu/tag/0ETT)
* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- **Flatness of a base change passes to a precomposition by a flat morphism.** If `X ×_S T` is
flat over `T` and `p : X' ⟶ X` is flat, then `X' ×_S T` is flat over `T`.

The pullback of `p ≫ f` along `g` is the pullback of `p` along the projection `X ×_S T ⟶ X`
followed by the projection `X ×_S T ⟶ T`, by
`CategoryTheory.Limits.pullbackRightPullbackFstIso`. Taking `p` to be the inclusion of a summand
of a coproduct, which is an open immersion, this splits flatness of the base change of a
disjoint-union morphism into flatness of the base changes of its members. -/
theorem flat_pullback_snd_comp_left {X X' S T : Scheme.{u}} {f : X ⟶ S} (p : X' ⟶ X) [Flat p]
    (g : T ⟶ S) (h : Flat (pullback.snd f g)) : Flat (pullback.snd (p ≫ f) g) := by
  have h1 : Flat (pullback.snd p (pullback.fst f g)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p (pullback.fst f g)) ‹Flat p›
  rw [← pullbackRightPullbackFstIso_inv_snd_snd f g p]
  infer_instance

/-- **The disjoint-union morphism of a base changed family is universally submersive** as soon as
that of the original family is.

The base change of a coproduct is the coproduct of the base changes,
`AlgebraicGeometry.isPullback_sigmaDesc_sigmaMap`, so the morphism `∐ (T ×_S Xᵢ) ⟶ T` is a base
change of `∐ Xᵢ ⟶ S` and universal submersiveness is stable under base change; the symmetry
isomorphism of fibre products turns that into the statement for
`CategoryTheory.Limits.pullback.snd`. -/
theorem universallySubmersive_sigmaDesc_pullback {S T : Scheme.{u}} {I : Type v} [Small.{u} I]
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) (g : T ⟶ S)
    (h : UniversallySubmersive (Sigma.desc f)) :
    UniversallySubmersive (Sigma.desc fun i ↦ pullback.snd (f i) g) := by
  have _ : UniversallySubmersive.{u}.IsStableUnderBaseChange := by
    rw [universallySubmersive_eq]; infer_instance
  have _ : UniversallySubmersive.{u}.RespectsIso := by
    rw [universallySubmersive_eq]; infer_instance
  have h1 : UniversallySubmersive (Sigma.desc fun i ↦ pullback.fst g (f i)) :=
    MorphismProperty.of_isPullback (isPullback_sigmaDesc_sigmaMap f (Over.mk g)).flip h
  have e : (Sigma.desc fun i ↦ pullback.snd (f i) g) =
      (Limits.Sigma.map fun i ↦ (pullbackSymmetry (f i) g).hom) ≫
        (Sigma.desc fun i ↦ pullback.fst g (f i)) :=
    Sigma.hom_ext _ _ fun i ↦ by simp
  rw [e]
  exact (MorphismProperty.cancel_left_of_respectsIso UniversallySubmersive _ _).mpr h1

/-- **The case the proof of Stacks 0ETT (1) ⟹ (2) reduces to.** A finite family of morphisms of
finite type to a Noetherian scheme whose disjoint-union morphism is universally submersive *and
which is flat over a dense open of the base* is refined by a ph covering.

This is `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement` with the extra datum the first
two steps of the Stacks proof produce, and it is all that is left of that hypothesis after
`AlgebraicGeometry.UniversallySubmersiveHasPHRefinement.of_denseFlat`. It is not proved here: its
Stacks proof is the flattening blowup of Stacks 0815 followed by the valuative argument that
recognizes the flattened family as an fppf covering, and that is
`AlgebraicGeometry.denseFlatUniversallySubmersiveHasPHRefinement` in
`StacksFrontier/AlgebraicGeometry/Topologies/HTopology/SubmersiveFlatteningRefinement.lean`. -/
def DenseFlatUniversallySubmersiveHasPHRefinement : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X] (I : Type v) [Finite I] [Small.{u} I]
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X), (∀ i, LocallyOfFiniteType (f i)) →
    (∀ i, QuasiCompact (f i)) → UniversallySubmersive (Sigma.desc f) →
    ∀ U : X.Opens, Dense (U : Set X) → (∀ i, Flat (pullback.snd (f i) U.ι)) →
    ∃ (K : Type v) (Z : K → Scheme.{u}) (g : ∀ k, Z k ⟶ X), IsPHCovering Z g ∧
      Nonempty (({ I₀ := K, X := Z, f := g } : PreZeroHypercover.{v} X).Hom
        ({ I₀ := I, X := Y, f := f } : PreZeroHypercover.{v} X))

/-- A compact scheme with a morphism of finite type to a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_compact_lft {X Y : Scheme.{u}} [IsNoetherian X]
    [CompactSpace Y] (f : Y ⟶ X) [LocallyOfFiniteType f] : IsNoetherian Y := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  exact ⟨⟩

/-- **Steps 1 and 2 of the proof of Stacks 0ETT (1) ⟹ (2).** If every universally submersive
finite family of finite type morphisms to a Noetherian scheme which is flat over a dense open of
the base is refined by a ph covering, then every such family is, with no flatness assumption.

Stratify the base by generic flatness for the disjoint-union morphism (Stacks 0H3Z) and replace
each closed subscheme of the stratification by the scheme-theoretic closure of its stratum: by
`AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_dense_flat_stratum` this gives a
finite ph covering `{Zₖ ⟶ X}` of the base by closed subschemes, each carrying a dense open over
which the disjoint-union morphism base changes flat. Over each `Zₖ` the base changed family is
again a finite family of finite type morphisms to a Noetherian scheme, its disjoint-union
morphism is again universally submersive, and it is flat over that dense open, so the hypothesis
refines it by a ph covering. Stacks 0DBI part (2) binds those refinements with `{Zₖ ⟶ X}` into a
single ph covering of `X`, which refines the original family through the projections
`Yᵢ ×_X Zₖ ⟶ Yᵢ`. -/
theorem UniversallySubmersiveHasPHRefinement.of_denseFlat
    (H : DenseFlatUniversallySubmersiveHasPHRefinement.{u, v}) :
    UniversallySubmersiveHasPHRefinement.{u, v} := by
  classical
  intro X _ I _ _ Y f _ _ hsub
  have _ : LocallyOfFiniteType (Sigma.desc f) := locallyOfFiniteType_sigmaDesc f
  have _ : ∀ i, CompactSpace (Y i) := fun i ↦ QuasiCompact.compactSpace_of_compactSpace (f i)
  -- `∐ Y` is a Noetherian scheme, so `∐ Y ⟶ X` is quasi-compact
  have _ : CompactSpace (∐ Y : Scheme.{u}) := by
    rw [← isCompact_univ_iff]
    have huniv : (Set.univ : Set (∐ Y : Scheme.{u})) = ⋃ i, Set.range (Sigma.ι Y i).base := by
      ext p
      simp only [Set.mem_univ, true_iff, Set.mem_iUnion]
      obtain ⟨i, y, hy⟩ := (sigmaOpenCover Y).exists_eq p
      exact ⟨i, y, hy⟩
    rw [huniv]
    exact isCompact_iUnion fun i ↦ isCompact_range (Sigma.ι Y i).continuous
  have _ : IsNoetherian (∐ Y : Scheme.{u}) := isNoetherian_of_compact_lft (Sigma.desc f)
  have _ : QuasiCompact (Sigma.desc f) := inferInstance
  obtain ⟨K, hK, Z, z, V, hph, hclosed, hflat, hVdense, -⟩ :=
    (HasFlatStratification.of_isNoetherian (Sigma.desc f)).exists_isPHCovering_dense_flat_stratum
  -- the hypothesis applies to the base changed family over each member of that covering
  have hinner : ∀ k, ∃ (K' : Type v) (Z' : K' → Scheme.{u}) (g' : ∀ m, Z' m ⟶ Z k),
      IsPHCovering Z' g' ∧
        Nonempty ((PreZeroHypercover.mk K' Z' g').Hom
          (PreZeroHypercover.mk I (fun i ↦ pullback (f i) (z k))
            (fun i ↦ pullback.snd (f i) (z k)))) := by
    intro k
    have _ : IsClosedImmersion (z k) := hclosed k
    have _ : CompactSpace (Z k) := QuasiCompact.compactSpace_of_compactSpace (z k)
    have _ : IsNoetherian (Z k) := isNoetherian_of_compact_lft (z k)
    refine H (Z k) I (fun i ↦ pullback (f i) (z k)) (fun i ↦ pullback.snd (f i) (z k))
      (fun i ↦ inferInstance) (fun i ↦ inferInstance)
      (universallySubmersive_sigmaDesc_pullback f (z k) hsub) (V k) (hVdense k) fun i ↦ ?_
    have h1 : Flat (pullback.snd (f i) ((V k).ι ≫ z k)) := by
      have h0 := flat_pullback_snd_comp_left (f := Sigma.desc f) (Sigma.ι Y i)
        ((V k).ι ≫ z k) (hflat k)
      rwa [Sigma.ι_comp_desc] at h0
    rw [← pullbackLeftPullbackSndIso_hom_snd (f i) (z k) (V k).ι]
    infer_instance
  choose K' Z' g' hph' hhom using hinner
  -- a refinement morphism over each member of the covering, and its factorization
  set φ : ∀ k, (PreZeroHypercover.mk (K' k) (Z' k) (g' k)).Hom
      (PreZeroHypercover.mk I (fun i ↦ pullback (f i) (z k))
        (fun i ↦ pullback.snd (f i) (z k))) := fun k ↦ (hhom k).some with hφ
  have hw : ∀ (k : K) (m : K' k),
      (φ k).h₀ m ≫ pullback.snd (f ((φ k).s₀ m)) (z k) = g' k m := fun k m ↦ (φ k).w₀ m
  -- bind the two layers of coverings
  refine ⟨Σ k : K, K' k, fun km ↦ Z' km.1 km.2, fun km ↦ g' km.1 km.2 ≫ z km.1, ?_, ⟨?_⟩⟩
  · exact isPHCovering_bind (PreZeroHypercover.mk K Z z) hph
      (fun k ↦ PreZeroHypercover.mk (K' k) (Z' k) (g' k)) hph'
  · exact
    { s₀ := fun km ↦ (φ km.1).s₀ km.2
      h₀ := fun km ↦ (φ km.1).h₀ km.2 ≫ pullback.fst (f ((φ km.1).s₀ km.2)) (z km.1)
      w₀ := fun km ↦ by
        change ((φ km.1).h₀ km.2 ≫ pullback.fst (f ((φ km.1).s₀ km.2)) (z km.1)) ≫
          f ((φ km.1).s₀ km.2) = g' km.1 km.2 ≫ z km.1
        rw [Category.assoc, pullback.condition, ← Category.assoc, hw km.1 km.2] }

/-- **Stacks 0ETT (1) ⟹ (2)**, granted only the dense flat case
`AlgebraicGeometry.DenseFlatUniversallySubmersiveHasPHRefinement`: a finite family of morphisms of
finite type to a Noetherian scheme whose disjoint-union morphism is universally submersive is an h
covering.

This is `AlgebraicGeometry.isHCovering_of_universallySubmersive` with its
hypothesis replaced by the weaker one that remains after the reduction. -/
theorem IsHCovering.of_universallySubmersive_of_denseFlat
    (H : DenseFlatUniversallySubmersiveHasPHRefinement.{u, v}) {X : Scheme.{u}} [IsNoetherian X]
    {I : Type v} [Finite I] [Small.{u} I] {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFiniteType (f i)] [∀ i, QuasiCompact (f i)]
    (hsub : UniversallySubmersive (Sigma.desc f)) : IsHCovering Y f :=
  isHCovering_of_universallySubmersive (.of_denseFlat H) f hsub

/-- **Stacks 0ETT**, granted only the dense flat case
`AlgebraicGeometry.DenseFlatUniversallySubmersiveHasPHRefinement`: for a finite family
`{X i ⟶ X}` of morphisms of finite type to a Noetherian scheme `X`, the morphism `∐ X i ⟶ X` is
universally submersive if and only if the family is an h covering.

This is `AlgebraicGeometry.universallySubmersive_sigmaDesc_iff_isHCovering`
with its hypothesis replaced by the weaker one that remains after the reduction; the implication
from the h covering condition is unconditional. -/
theorem universallySubmersive_sigmaDesc_iff_isHCovering_of_denseFlat
    (H : DenseFlatUniversallySubmersiveHasPHRefinement.{u, v}) {X : Scheme.{u}} [IsNoetherian X]
    {I : Type v} [Finite I] [Small.{u} I] {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFiniteType (f i)] [∀ i, QuasiCompact (f i)] :
    UniversallySubmersive (Sigma.desc f) ↔ IsHCovering Y f :=
  universallySubmersive_sigmaDesc_iff_isHCovering (.of_denseFlat H) f

end AlgebraicGeometry

end

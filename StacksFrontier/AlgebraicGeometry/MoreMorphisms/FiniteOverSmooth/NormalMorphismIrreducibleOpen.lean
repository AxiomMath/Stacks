module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.PullbackNormal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ConditionalStatements
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre

/-!
# Spreading out a geometrically irreducible open in a normal morphism

Let `h : Y ⟶ S` be normal and of finite presentation and let `T` be an open subscheme of the
fibre of `h` over a point `s` which is geometrically irreducible over the residue field of `s`.
Then, after an affine elementary étale neighbourhood of `s`, the open `T` spreads to a
quasi-compact open of the base change whose every fibre is geometrically integral.

This is Stacks Tag 057J. It is deduced from Tag 055W, which gives the same conclusion with
"geometrically connected" in place of "geometrically integral": the fibres of the open produced
by Tag 055W are normal, by Tag 06DG applied to the geometrically normal fibres of `h`, and a
connected Noetherian normal scheme is irreducible by Tag 033M.

## Main results

* `exists_elementaryEtaleNeighborhood_open_geometricallyIntegral_of_statement055W`: Tag 057J,
  with the statement of Tag 055W as an explicit hypothesis.

## Implementation notes

Tag 055W is not yet available, so it is carried as the hypothesis
`AlgebraicGeometry.Statement055W` and the theorem is left untagged. Everything else in the proof
is discharged.

Normality of the base change of the open along a `K`-point `q` of the elementary neighbourhood is
obtained by rewriting that base change as a normal scheme in four steps: the `K`-point of the
neighbourhood is factored through the residue field of its image in `S`, so that the base change
of `h` along it becomes a base change of the fibre of `h`; Tag 06DG makes that normal; and the
two remaining comparisons move the open and the two pullbacks into place.

## References

* [Stacks Project, Tag 057J](https://stacks.math.columbia.edu/tag/057J)
* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
* [Stacks Project, Tag 06DG](https://stacks.math.columbia.edu/tag/06DG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The base change along a `K`-point of the source of an elementary étale neighbourhood of an
open in a normal family is normal. -/
private theorem isNormal_pullback_of_isNormal_hom {Y S : Scheme.{u}} (h : Y ⟶ S)
    (hnormal : Scheme.Hom.IsNormal h) (s : S) (U : EtaleNeighborhood S s)
    (V : (pullback h U.toBase).Opens) (K : Type u) [Field K]
    (q : Spec (.of K) ⟶ U.scheme) :
    IsNormal (pullback (V.ι ≫ pullback.snd h U.toBase) q : Scheme.{u}) := by
  obtain ⟨⟨s₀, φ⟩, hqS⟩ :=
    (Scheme.SpecToEquivOfField K S).symm.surjective (q ≫ U.toBase)
  have hqS' : Spec.map φ ≫ S.fromSpecResidueField s₀ = q ≫ U.toBase := by
    simpa [Scheme.SpecToEquivOfField] using hqS
  have hKnormal : IsNormal (Spec (.of K)) := isNormal_spec_of_isIntegrallyClosed K
  have hfibre : IsNormal
      (pullback (h.fiberToSpecResidueField s₀) (Spec.map φ) : Scheme.{u}) :=
    isNormal_pullback_of_isGeometricallyNormal (h.fiberToSpecResidueField s₀) (Spec.map φ)
      (hnormal.isGeometricallyNormal_fiber s₀)
  have hbase : IsNormal (pullback (pullback.snd h U.toBase) q : Scheme.{u}) := by
    have e₁ := pullbackLeftPullbackSndIso h (S.fromSpecResidueField s₀) (Spec.map φ)
    have e₂ : pullback h (Spec.map φ ≫ S.fromSpecResidueField s₀) ≅
        pullback h (q ≫ U.toBase) :=
      pullback.congrHom (f₁ := h) (f₂ := h) (g₁ := Spec.map φ ≫ S.fromSpecResidueField s₀)
        (g₂ := q ≫ U.toBase) rfl hqS'
    have e₃ := pullbackLeftPullbackSndIso h U.toBase q
    have : IsNormal
        (pullback (pullback.snd h (S.fromSpecResidueField s₀)) (Spec.map φ) : Scheme.{u}) :=
      hfibre
    exact isNormal_of_iso (e₃ ≪≫ e₂.symm ≪≫ e₁.symm)
  have e₄ := pullbackRightPullbackFstIso (pullback.snd h U.toBase) q V.ι
  have : IsNormal (pullback V.ι (pullback.fst (pullback.snd h U.toBase) q) : Scheme.{u}) := by
    have : IsOpenImmersion
        (pullback.snd V.ι (pullback.fst (pullback.snd h U.toBase) q)) :=
      MorphismProperty.pullback_snd V.ι _ inferInstance
    exact isNormal_of_isOpenImmersion
      (pullback.snd V.ι (pullback.fst (pullback.snd h U.toBase) q))
  exact isNormal_of_iso e₄.symm

/-- **Stacks Project, Tag 057J**, conditional on Tag 055W. A geometrically irreducible open in a
fibre of a normal, finitely presented morphism spreads, after an affine elementary étale base
change, to a quasi-compact open with geometrically integral fibres. -/
theorem exists_elementaryEtaleNeighborhood_open_geometricallyIntegral_of_statement055W
    (h055W : Statement055W.{u})
    {Y S : Scheme.{u}} (h : Y ⟶ S) (s : S)
    (T : (h.fiber s).Opens) (hfp : FinitePresentation h)
    (hnormal : Scheme.Hom.IsNormal h)
    [GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary) (_ : IsAffine U.scheme)
      (V : (pullback h U.toBase).Opens),
      QuasiCompact V.ι ∧ GeometricallyIntegral (V.ι ≫ pullback.snd h U.toBase) ∧
      ∀ x : (pullback.snd h U.toBase).fiber U.point,
        ((pullback.snd h U.toBase).fiberι U.point x ∈ V) ↔
          pullback.fst h U.toBase ((pullback.snd h U.toBase).fiberι U.point x) ∈
            h.fiberι s '' (T : Set (h.fiber s)) := by
  have : Flat h := hnormal.flat
  have : GeometricallyReduced h := hnormal.geometricallyReduced
  have : GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s) := by
    refine ⟨fun K hK y Z fst snd hpull ↦ ?_⟩
    have : IrreducibleSpace Z :=
      GeometricallyIrreducible.geometrically_irreducibleSpace (K := K) y fst snd hpull
    infer_instance
  obtain ⟨U, hU, hUa, V, hVqc, hVconn, hVfiber⟩ := h055W h s T hfp
  have : LocallyOfFinitePresentation h := hfp.locallyOfFinitePresentation
  have : QuasiCompact h := hfp.quasiCompact
  have : LocallyOfFiniteType (V.ι ≫ pullback.snd h U.toBase) := by infer_instance
  have : QuasiCompact (V.ι ≫ pullback.snd h U.toBase) := by infer_instance
  refine ⟨U, hU, hUa, V, hVqc, ?_, hVfiber⟩
  rw [GeometricallyIntegral.eq_geometrically]
  intro K hK q Z fst snd hpull
  set fV := V.ι ≫ pullback.snd h U.toBase with hfV
  have : IsLocallyNoetherian (pullback fV q : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd fV q)
  have : CompactSpace (pullback fV q : Scheme.{u}) :=
    (quasiCompact_iff_compactSpace (pullback.snd fV q)).mp inferInstance
  have : IsNoetherian (pullback fV q : Scheme.{u}) := ⟨⟩
  have hnormalQ : IsNormal (pullback fV q : Scheme.{u}) :=
    isNormal_pullback_of_isNormal_hom h hnormal s U V K q
  have : ConnectedSpace (pullback fV q : Scheme.{u}) :=
    hVconn.geometrically_connectedSpace (K := K) q (pullback.fst fV q) (pullback.snd fV q)
      (IsPullback.of_hasPullback fV q)
  have : IrreducibleSpace (pullback fV q : Scheme.{u}) :=
    irreducibleSpace_of_isNormal_of_connectedSpace _ hnormalQ
  have : IsReduced (pullback fV q : Scheme.{u}) := isReduced_of_isNormal _
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨(Scheme.homeoOfIso hpull.isoPullback).irreducibleSpace_iff.mpr inferInstance,
    isReduced_of_isOpenImmersion hpull.isoPullback.hom⟩

end AlgebraicGeometry

end

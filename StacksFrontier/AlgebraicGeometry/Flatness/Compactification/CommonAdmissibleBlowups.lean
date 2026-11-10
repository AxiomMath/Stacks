module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleCommonRefinement
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleComposition
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingNormalForm
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.StrictTransformOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.SpanOverBaseSeparated

/-!
# Common admissible blowups for two open embeddings

Let `S` be a quasi-compact and quasi-separated scheme and let `U ⟶ X₁` and `U ⟶ X₂` be open
immersions of schemes over `S`, with `U`, `X₁` and `X₂` of finite type and separated over `S`.
Then there are `U`-admissible blowups `X₁' ⟶ X₁` and `X₂' ⟶ X₂` which are both open subschemes of
one scheme `X`, separated and of finite type over `S`, compatibly with `U`. This is
[Stacks, Tag 0F3X], the first step of Nagata's compactification theorem.

## Main results

* `AlgebraicGeometry.exists_graphImage_isIso_pullbackSnd`: the scheme-theoretic image `X₁₂` of
  `U` in `X₁ ×_S X₂`, with its two projections and the properties the proof needs of them.
* `AlgebraicGeometry.exists_common_isAdmissibleBlowup_pair`: two admissible blowups of a scheme
  along one open are dominated by a common one, [Stacks, Tag 080N] for a pair.
* `AlgebraicGeometry.exists_common_isAdmissibleBlowup_isOpenImmersion`: **[Stacks, Tag 0F3X]**.

## Implementation notes

The proof is the source's. Write `X₁₂` for the scheme-theoretic image of the graph
`U ⟶ X₁ ×_S X₂`. The graph is an immersion
(`Stacks.AmpleProjectiveImmersion.isImmersion_lift`, one component being an open immersion) and
quasi-compact, so [Stacks, Tag 01RG] makes `U ⟶ X₁₂` an open immersion and `X₁₂ ⟶ X₁ ×_S X₂` a
closed immersion, and [Stacks, Tag 0CNG] makes each projection `qᵢ : X₁₂ ⟶ Xᵢ` an isomorphism
over `U`.

[Stacks, Tag 081S] then gives a `U`-admissible blowup `Xᵢⁱ ⟶ Xᵢ` whose strict transform of `X₁₂`
is an open subscheme `X₁₂ⁱ ⊆ Xᵢⁱ`, and that strict transform is itself a `U`-admissible blowup of
`X₁₂` by [Stacks, Tag 080E]
(`AlgebraicGeometry.isAdmissibleBlowup_strictTransformToSource`); its admissible open is the image
of `U` because that image is exactly the inverse image of `U`
(`AlgebraicGeometry.opensRange_eq_preimage_of_isIso_pullbackSnd`). [Stacks, Tag 080N] produces a
`U`-admissible blowup `X₁₂' ⟶ X₁₂` dominating both, and [Stacks, Tag 080M]
(`Stacks.Blowup.exists_admissibleBlowup_isPullback`) extends each of the two resulting blowups
`X₁₂' ⟶ X₁₂ⁱ` from the open `X₁₂ⁱ` to a `U`-admissible blowup `Xᵢ' ⟶ Xᵢⁱ`, with `X₁₂'` an open
subscheme of `Xᵢ'`. Compositions of admissible blowups being admissible ([Stacks, Tag 080L]),
`Xᵢ' ⟶ Xᵢ` is a `U`-admissible blowup.

Finally `X₁₂' ⟶ X₁' ×_S X₂'` is a closed immersion
(`AlgebraicGeometry.isClosedImmersion_lift_of_isProper`, which is [Stacks, Tag 01W6]), so glueing
`X₁'` and `X₂'` along `X₁₂'` gives a scheme separated and of finite type over `S`
([Stacks, Tag 0F3U], through `AlgebraicGeometry.SpanGlue.isSeparated_desc`). The morphism from
`U` is the section of `X₁₂' ⟶ X₁₂` over the admissible open
(`AlgebraicGeometry.exists_section_of_isAdmissibleBlowup`).

The strict transform `X₁₂ⁱ` is replaced throughout by the open subscheme of `Xᵢⁱ` it is
isomorphic to, through `AlgebraicGeometry.Scheme.Hom.isoOpensRange`; admissibility survives that
replacement by `Stacks.Blowup.IsAdmissibleBlowup.comp_iso`. This is what lets [Stacks, Tag 080M],
whose hypothesis is phrased for an open of the blown-up scheme, be applied without an extra
transport.

The open subscheme of `Xᵢ` that the admissibility is relative to is the image `uᵢ.opensRange` of
the given open immersion, and finite type is expressed by `LocallyOfFiniteType` together with
`QuasiCompact`. Every morphism of the source's diagram appears in the statement, together with
the equations making the diagram commute.

## References

* [Stacks Project, Tag 0F3X](https://stacks.math.columbia.edu/tag/0F3X)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 0CNG](https://stacks.math.columbia.edu/tag/0CNG)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 080L](https://stacks.math.columbia.edu/tag/080L)
* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
* [Stacks Project, Tag 080N](https://stacks.math.columbia.edu/tag/080N)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 0F3U](https://stacks.math.columbia.edu/tag/0F3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Tag 0CNG: if `g : U ⟶ P` lifts the open immersion `u : U ⟶ X` along a separated `p`, then
`p` restricted to the scheme-theoretic image of `g` is an isomorphism over the image of `u`. -/
private theorem isIso_pullback_snd_imageι_comp {P X U : Scheme.{u}} (p : P ⟶ X) [IsSeparated p]
    [QuasiSeparatedSpace X] (u : U ⟶ X) [IsOpenImmersion u]
    (hU : IsCompact (u.opensRange : Set X)) (g : U ⟶ P) (hg : g ≫ p = u) :
    IsIso (pullback.snd (g.imageι ≫ p) u.opensRange.ι) := by
  have h : IsIso (pullback.snd ((u.isoOpensRange.inv ≫ g).ker.subschemeι ≫ p) u.opensRange.ι) :=
    isIso_pullback_snd_imageι_comp_of_section p u.opensRange
      (hU.isRetrocompact u.opensRange.isOpen) (u.isoOpensRange.inv ≫ g)
      (by rw [Category.assoc, hg, Scheme.Hom.isoOpensRange_inv_comp])
  rwa [Scheme.Hom.ker_comp_of_isIso] at h

/-- The restriction of `q` over `V` is an isomorphism if the pullback of `q` along `V.ι` is. -/
private theorem isIso_morphismRestrict_of_isIso_pullback_snd {Z X : Scheme.{u}} (q : Z ⟶ X)
    (V : X.Opens) [IsIso (pullback.snd q V.ι)] : IsIso (q ∣_ V) := by
  have h : IsIso ((pullbackRestrictIsoRestrict q V).hom ≫ (q ∣_ V)) := by
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]; infer_instance
  exact (isIso_comp_left_iff (pullbackRestrictIsoRestrict q V).hom (q ∣_ V)).mp h

/-- The open of the blowup onto which the strict transform of `q` embeds lies over `Z` through
the blowup morphisms. -/
private theorem isoOpensRange_symm_comp_strictTransform_comp {Z X : Scheme.{u}} (q : Z ⟶ X)
    (I : X.IdealSheafData) [IsOpenImmersion (strictTransformToBlowUp q I)] :
    ((strictTransformToBlowUp q I).isoOpensRange.symm.hom ≫
      ((Stacks.StrictTransform.ideal q (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
        pullback.fst q (blowUpToBase I))) ≫ q =
      (strictTransformToBlowUp q I).opensRange.ι ≫ blowUpToBase I := by
  rw [Category.assoc, show ((Stacks.StrictTransform.ideal q (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι ≫ pullback.fst q (blowUpToBase I)) ≫ q =
    strictTransformToBlowUp q I ≫ blowUpToBase I from by
      simp only [strictTransformToBlowUp, Category.assoc, pullback.condition],
    ← Category.assoc, Iso.symm_hom, Scheme.Hom.isoOpensRange_inv_comp]

/-- A blowup over the image of `U` in `Z`, read through the open of `blowUp I` onto which the
strict transform embeds, is admissible relative to the inverse image of the open of `X`. -/
private theorem isAdmissibleBlowup_preimage_strictTransform {Z X T : Scheme.{u}} (q : Z ⟶ X)
    (I : X.IdealSheafData) [IsOpenImmersion (strictTransformToBlowUp q I)] (V : X.Opens)
    (W : Z.Opens) (hW : W = q ⁻¹ᵁ V) (c : T ⟶ (strictTransformToBlowUp q I).opensRange.toScheme)
    (hc : Stacks.Blowup.IsAdmissibleBlowup
      (((strictTransformToBlowUp q I).isoOpensRange.symm.hom ≫
        ((Stacks.StrictTransform.ideal q (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
          pullback.fst q (blowUpToBase I))) ⁻¹ᵁ W) c) :
    Stacks.Blowup.IsAdmissibleBlowup
      ((strictTransformToBlowUp q I).opensRange.ι ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ V)) c := by
  subst hW
  rwa [← Scheme.Hom.comp_preimage, ← isoOpensRange_symm_comp_strictTransform_comp q I,
    Scheme.Hom.comp_preimage]

/-- **The scheme-theoretic image of `U` in `X₁ ×_S X₂`**, with the two projections to `X₁` and
`X₂`. The graph of the two open immersions is an immersion and quasi-compact, so the image
contains `U` as an open subscheme and is closed in `X₁ ×_S X₂`, and each projection is an
isomorphism over the image of `U`. -/
theorem exists_graphImage_isIso_pullbackSnd {S U X₁ X₂ : Scheme.{u}} (fU : U ⟶ S)
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) [QuasiCompact fU]
    [QuasiSeparatedSpace X₁] [QuasiSeparatedSpace X₂]
    [IsSeparated f₁] [QuasiCompact f₁] [LocallyOfFiniteType f₁]
    [IsSeparated f₂] [QuasiCompact f₂] [LocallyOfFiniteType f₂]
    (u₁ : U ⟶ X₁) (u₂ : U ⟶ X₂) [IsOpenImmersion u₁] [IsOpenImmersion u₂]
    (hu₁ : u₁ ≫ f₁ = fU) (hu₂ : u₂ ≫ f₂ = fU)
    (hU₁ : IsCompact (u₁.opensRange : Set X₁)) (hU₂ : IsCompact (u₂.opensRange : Set X₂)) :
    ∃ (Z : Scheme.{u}) (s : U ⟶ Z) (q₁ : Z ⟶ X₁) (q₂ : Z ⟶ X₂),
      IsOpenImmersion s ∧
      ∃ hq : q₁ ≫ f₁ = q₂ ≫ f₂,
        IsClosedImmersion (pullback.lift q₁ q₂ hq) ∧
          s ≫ q₁ = u₁ ∧ s ≫ q₂ = u₂ ∧
            IsIso (pullback.snd q₁ u₁.opensRange.ι) ∧
              IsIso (pullback.snd q₂ u₂.opensRange.ι) ∧
                IsSeparated q₁ ∧ IsSeparated q₂ ∧ QuasiCompact q₁ ∧ QuasiCompact q₂ ∧
                  LocallyOfFiniteType q₁ ∧ LocallyOfFiniteType q₂ := by
  have hgraph : u₁ ≫ f₁ = u₂ ≫ f₂ := by rw [hu₁, hu₂]
  have himm : IsImmersion (pullback.lift u₁ u₂ hgraph) :=
    Stacks.AmpleProjectiveImmersion.isImmersion_lift u₁ u₂ hgraph
  have hu₁qc : QuasiCompact u₁ := by
    have h : QuasiCompact (u₁ ≫ f₁) := by
      rw [hu₁]
      infer_instance
    exact QuasiCompact.of_comp u₁ f₁
  have hgfst : pullback.lift u₁ u₂ hgraph ≫ pullback.fst f₁ f₂ = u₁ := pullback.lift_fst _ _ _
  have hgsnd : pullback.lift u₁ u₂ hgraph ≫ pullback.snd f₁ f₂ = u₂ := pullback.lift_snd _ _ _
  have hgqc : QuasiCompact (pullback.lift u₁ u₂ hgraph) := by
    have h : QuasiCompact (pullback.lift u₁ u₂ hgraph ≫ pullback.fst f₁ f₂) := by
      rw [hgfst]
      exact hu₁qc
    exact QuasiCompact.of_comp _ (pullback.fst f₁ f₂)
  refine ⟨(pullback.lift u₁ u₂ hgraph).image, (pullback.lift u₁ u₂ hgraph).toImage,
    (pullback.lift u₁ u₂ hgraph).imageι ≫ pullback.fst f₁ f₂,
    (pullback.lift u₁ u₂ hgraph).imageι ≫ pullback.snd f₁ f₂, inferInstance,
    by simp only [Category.assoc, pullback.condition], ?_, ?_, ?_, ?_, ?_,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  · have hc : pullback.lift
        ((pullback.lift u₁ u₂ hgraph).imageι ≫ pullback.fst f₁ f₂)
        ((pullback.lift u₁ u₂ hgraph).imageι ≫ pullback.snd f₁ f₂)
        (by simp only [Category.assoc, pullback.condition]) =
        (pullback.lift u₁ u₂ hgraph).imageι := by
      apply pullback.hom_ext <;>
        simp
    rw [hc]
    infer_instance
  · rw [← Category.assoc, Scheme.Hom.toImage_imageι, hgfst]
  · rw [← Category.assoc, Scheme.Hom.toImage_imageι, hgsnd]
  · exact isIso_pullback_snd_imageι_comp (pullback.fst f₁ f₂) u₁ hU₁ _ hgfst
  · exact isIso_pullback_snd_imageι_comp (pullback.snd f₁ f₂) u₂ hU₂ _ hgsnd

/-- **[Stacks, Tag 080N] for a pair.** Two `V`-admissible blowups of a scheme are dominated by a
single `V`-admissible blowup, by blowups admissible relative to the inverse images of `V`. -/
theorem exists_common_isAdmissibleBlowup_pair {Z T₁ T₂ : Scheme.{u}} (V : Z.Opens)
    (t₁ : T₁ ⟶ Z) (t₂ : T₂ ⟶ Z)
    (h₁ : Stacks.Blowup.IsAdmissibleBlowup V t₁)
    (h₂ : Stacks.Blowup.IsAdmissibleBlowup V t₂) :
    ∃ (W : Scheme.{u}) (c : W ⟶ Z) (c₁ : W ⟶ T₁) (c₂ : W ⟶ T₂),
      Stacks.Blowup.IsAdmissibleBlowup V c ∧ c₁ ≫ t₁ = c ∧ c₂ ≫ t₂ = c ∧
        Stacks.Blowup.IsAdmissibleBlowup (t₁ ⁻¹ᵁ V) c₁ ∧
          Stacks.Blowup.IsAdmissibleBlowup (t₂ ⁻¹ᵁ V) c₂ := by
  obtain ⟨W, d, hd, c, hc, hca⟩ := Stacks.Blowup.exists_admissibleBlowup_dominating V
    (fun b : Bool => cond b T₁ T₂)
    (fun b => match b with | false => t₂ | true => t₁)
    (fun b => match b with | false => h₂ | true => h₁)
  exact ⟨W, d, c true, c false, hd, hc true, hc false, hca true, hca false⟩

/-- **Stacks Project, Tag 0F3X.** Let `S` be a quasi-compact and quasi-separated scheme and let
`u₁ : U ⟶ X₁` and `u₂ : U ⟶ X₂` be open immersions of schemes over `S`, with `U`, `X₁` and `X₂`
of finite type and separated over `S`. Then there is a commutative diagram of schemes over `S`
in which `Xᵢ' ⟶ Xᵢ` is a `U`-admissible blowup, `Xᵢ' ⟶ X` is an open immersion, and `X` is
separated and of finite type over `S`. -/
@[stacks 0F3X]
theorem exists_common_isAdmissibleBlowup_isOpenImmersion {S U X₁ X₂ : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S]
    (fU : U ⟶ S) (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [LocallyOfFiniteType fU] [QuasiCompact fU] [IsSeparated fU]
    [LocallyOfFiniteType f₁] [QuasiCompact f₁] [IsSeparated f₁]
    [LocallyOfFiniteType f₂] [QuasiCompact f₂] [IsSeparated f₂]
    (u₁ : U ⟶ X₁) (u₂ : U ⟶ X₂) [IsOpenImmersion u₁] [IsOpenImmersion u₂]
    (hu₁ : u₁ ≫ f₁ = fU) (hu₂ : u₂ ≫ f₂ = fU) :
    ∃ (X₁' X₂' X : Scheme.{u}) (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
      (j₁ : X₁' ⟶ X) (j₂ : X₂' ⟶ X)
      (v₁ : U ⟶ X₁') (v₂ : U ⟶ X₂') (v : U ⟶ X) (f : X ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup u₁.opensRange b₁ ∧
        Stacks.Blowup.IsAdmissibleBlowup u₂.opensRange b₂ ∧
          IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
            LocallyOfFiniteType f ∧ QuasiCompact f ∧ IsSeparated f ∧
              (v₁ ≫ b₁ = u₁) ∧ (v₂ ≫ b₂ = u₂) ∧
                (v₁ ≫ j₁ = v) ∧ (v₂ ≫ j₂ = v) ∧
                  (b₁ ≫ f₁ = j₁ ≫ f) ∧ (b₂ ≫ f₂ = j₂ ≫ f) ∧ (v ≫ f = fU) := by
  have _ : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace fU
  have _ : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have _ : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace f₂
  have _ : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  have _ : QuasiSeparatedSpace X₂ := quasiSeparatedSpace_of_quasiSeparated f₂
  have hU₁ : IsCompact (u₁.opensRange : Set X₁) := isCompact_range u₁.continuous
  have hU₂ : IsCompact (u₂.opensRange : Set X₂) := isCompact_range u₂.continuous
  obtain ⟨Z, s, q₁, q₂, hsoi, hq, hZclosed, hs₁, hs₂, his₁, his₂,
    hsep₁, hsep₂, hqc₁, hqc₂, hlft₁, hlft₂⟩ :=
    exists_graphImage_isIso_pullbackSnd fU f₁ f₂ u₁ u₂ hu₁ hu₂ hU₁ hU₂
  have _ : IsOpenImmersion s := hsoi
  have _ : IsSeparated q₁ := hsep₁
  have _ : IsSeparated q₂ := hsep₂
  have _ : QuasiCompact q₁ := hqc₁
  have _ : QuasiCompact q₂ := hqc₂
  have _ : LocallyOfFiniteType q₁ := hlft₁
  have _ : LocallyOfFiniteType q₂ := hlft₂
  have _ : IsIso (pullback.snd q₁ u₁.opensRange.ι) := his₁
  have _ : IsIso (pullback.snd q₂ u₂.opensRange.ι) := his₂
  have _ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q₁
  have _ : IsClosedImmersion (pullback.lift q₁ q₂ hq) := hZclosed
  -- The two projections are isomorphisms over the images of `U`.
  have _ : IsIso (q₁ ∣_ u₁.opensRange) := isIso_morphismRestrict_of_isIso_pullback_snd _ _
  have _ : IsIso (q₂ ∣_ u₂.opensRange) := isIso_morphismRestrict_of_isIso_pullback_snd _ _
  -- Tag 081S on each projection.
  obtain ⟨I₁, hI₁fp, hI₁disj, hb₁, hopen₁⟩ :=
    exists_isAdmissibleBlowup_isOpenImmersion_strictTransform q₁ u₁.opensRange hU₁
  obtain ⟨I₂, hI₂fp, hI₂disj, hb₂, hopen₂⟩ :=
    exists_isAdmissibleBlowup_isOpenImmersion_strictTransform q₂ u₂.opensRange hU₂
  have _ : IsOpenImmersion (strictTransformToBlowUp q₁ I₁) := hopen₁
  have _ : IsOpenImmersion (strictTransformToBlowUp q₂ I₂) := hopen₂
  -- The strict transforms are admissible blowups of `Z` relative to the image of `U`.
  have hr₁ : s.opensRange = q₁ ⁻¹ᵁ u₁.opensRange :=
    opensRange_eq_preimage_of_isIso_pullbackSnd s q₁ u₁ hs₁
  have hr₂ : s.opensRange = q₂ ⁻¹ᵁ u₂.opensRange :=
    opensRange_eq_preimage_of_isIso_pullbackSnd s q₂ u₂ hs₂
  have hat₁ : Stacks.Blowup.IsAdmissibleBlowup s.opensRange
      ((Stacks.StrictTransform.ideal q₁ (blowUpToBase I₁)
        (exceptionalIdeal I₁)).subschemeι ≫ pullback.fst q₁ (blowUpToBase I₁)) := by
    rw [hr₁]
    exact isAdmissibleBlowup_strictTransformToSource q₁ u₁.opensRange I₁ hI₁fp hI₁disj
  have hat₂ : Stacks.Blowup.IsAdmissibleBlowup s.opensRange
      ((Stacks.StrictTransform.ideal q₂ (blowUpToBase I₂)
        (exceptionalIdeal I₂)).subschemeι ≫ pullback.fst q₂ (blowUpToBase I₂)) := by
    rw [hr₂]
    exact isAdmissibleBlowup_strictTransformToSource q₂ u₂.opensRange I₂ hI₂fp hI₂disj
  -- Read the strict transforms as the opens of the blowups they embed onto.
  have hV₁ := Stacks.Blowup.IsAdmissibleBlowup.comp_iso hat₁
    (strictTransformToBlowUp q₁ I₁).isoOpensRange.symm
  have hV₂ := Stacks.Blowup.IsAdmissibleBlowup.comp_iso hat₂
    (strictTransformToBlowUp q₂ I₂).isoOpensRange.symm
  -- A common dominating blowup of `Z`.
  obtain ⟨W, c, c₁, c₂, hc, hc₁, hc₂, hca₁, hca₂⟩ :=
    exists_common_isAdmissibleBlowup_pair s.opensRange _ _ hV₁ hV₂
  -- The two opens of the blowups lie over `Z` through the blowup morphisms.
  have hVq₁ := isoOpensRange_symm_comp_strictTransform_comp q₁ I₁
  have hVq₂ := isoOpensRange_symm_comp_strictTransform_comp q₂ I₂
  -- Properness and compactness of the pieces.
  have _ : IsProper (blowUpToBase I₁) := hb₁.isProper
  have _ : IsProper (blowUpToBase I₂) := hb₂.isProper
  have _ : CompactSpace (blowUp I₁) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I₁)
  have _ : CompactSpace (blowUp I₂) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I₂)
  have _ : QuasiSeparatedSpace (blowUp I₁) :=
    quasiSeparatedSpace_of_quasiSeparated (blowUpToBase I₁)
  have _ : QuasiSeparatedSpace (blowUp I₂) :=
    quasiSeparatedSpace_of_quasiSeparated (blowUpToBase I₂)
  have _ : IsProper ((Stacks.StrictTransform.ideal q₁ (blowUpToBase I₁)
      (exceptionalIdeal I₁)).subschemeι ≫ pullback.fst q₁ (blowUpToBase I₁)) := hat₁.isProper
  have _ : IsProper ((Stacks.StrictTransform.ideal q₂ (blowUpToBase I₂)
      (exceptionalIdeal I₂)).subschemeι ≫ pullback.fst q₂ (blowUpToBase I₂)) := hat₂.isProper
  have _ : CompactSpace (Stacks.StrictTransform.scheme q₁ (blowUpToBase I₁)
      (exceptionalIdeal I₁)) :=
    QuasiCompact.compactSpace_of_compactSpace
      ((Stacks.StrictTransform.ideal q₁ (blowUpToBase I₁)
        (exceptionalIdeal I₁)).subschemeι ≫ pullback.fst q₁ (blowUpToBase I₁))
  have _ : CompactSpace (Stacks.StrictTransform.scheme q₂ (blowUpToBase I₂)
      (exceptionalIdeal I₂)) :=
    QuasiCompact.compactSpace_of_compactSpace
      ((Stacks.StrictTransform.ideal q₂ (blowUpToBase I₂)
        (exceptionalIdeal I₂)).subschemeι ≫ pullback.fst q₂ (blowUpToBase I₂))
  have hVc₁ : IsCompact (((strictTransformToBlowUp q₁ I₁).opensRange) : Set (blowUp I₁)) :=
    isCompact_range (strictTransformToBlowUp q₁ I₁).continuous
  have hVc₂ : IsCompact (((strictTransformToBlowUp q₂ I₂).opensRange) : Set (blowUp I₂)) :=
    isCompact_range (strictTransformToBlowUp q₂ I₂).continuous
  have hUB₁ : IsCompact ((blowUpToBase I₁ ⁻¹ᵁ u₁.opensRange : (blowUp I₁).Opens) :
      Set (blowUp I₁)) :=
    QuasiCompact.isCompact_preimage (f := blowUpToBase I₁) _ u₁.opensRange.2 hU₁
  have hUB₂ : IsCompact ((blowUpToBase I₂ ⁻¹ᵁ u₂.opensRange : (blowUp I₂).Opens) :
      Set (blowUp I₂)) :=
    QuasiCompact.isCompact_preimage (f := blowUpToBase I₂) _ u₂.opensRange.2 hU₂
  -- Tag 080M: extend the two blowups from the opens to the whole blowups of `Xᵢ`.
  have hca₁' := isAdmissibleBlowup_preimage_strictTransform q₁ I₁ u₁.opensRange _ hr₁ c₁ hca₁
  have hca₂' := isAdmissibleBlowup_preimage_strictTransform q₂ I₂ u₂.opensRange _ hr₂ c₂ hca₂
  obtain ⟨Y₁, d₁, hd₁, k₁, hk₁⟩ := Stacks.Blowup.exists_admissibleBlowup_isPullback
    (blowUpToBase I₁ ⁻¹ᵁ u₁.opensRange) (strictTransformToBlowUp q₁ I₁).opensRange
    hUB₁ hVc₁ c₁ hca₁'
  obtain ⟨Y₂, d₂, hd₂, k₂, hk₂⟩ := Stacks.Blowup.exists_admissibleBlowup_isPullback
    (blowUpToBase I₂ ⁻¹ᵁ u₂.opensRange) (strictTransformToBlowUp q₂ I₂).opensRange
    hUB₂ hVc₂ c₂ hca₂'
  have _ : IsOpenImmersion k₁ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hk₁ inferInstance
  have _ : IsOpenImmersion k₂ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hk₂ inferInstance
  -- Tag 080L: the composites are `U`-admissible blowups of `Xᵢ`.
  have hbd₁ : Stacks.Blowup.IsAdmissibleBlowup u₁.opensRange (d₁ ≫ blowUpToBase I₁) :=
    Stacks.Blowup.IsAdmissibleBlowup.comp u₁.opensRange (blowUpToBase I₁) d₁ hb₁ hd₁
  have hbd₂ : Stacks.Blowup.IsAdmissibleBlowup u₂.opensRange (d₂ ≫ blowUpToBase I₂) :=
    Stacks.Blowup.IsAdmissibleBlowup.comp u₂.opensRange (blowUpToBase I₂) d₂ hb₂ hd₂
  have _ : IsProper (d₁ ≫ blowUpToBase I₁) := hbd₁.isProper
  have _ : IsProper (d₂ ≫ blowUpToBase I₂) := hbd₂.isProper
  have _ : CompactSpace Y₁ :=
    QuasiCompact.compactSpace_of_compactSpace (d₁ ≫ blowUpToBase I₁)
  have _ : CompactSpace Y₂ :=
    QuasiCompact.compactSpace_of_compactSpace (d₂ ≫ blowUpToBase I₂)
  have _ : IsProper c := hc.isProper
  have hkc₁ : k₁ ≫ (d₁ ≫ blowUpToBase I₁) = c ≫ q₁ := by
    rw [← Category.assoc, ← hk₁.w, Category.assoc, ← hVq₁, ← Category.assoc, hc₁]
  have hkc₂ : k₂ ≫ (d₂ ≫ blowUpToBase I₂) = c ≫ q₂ := by
    rw [← Category.assoc, ← hk₂.w, Category.assoc, ← hVq₂, ← Category.assoc, hc₂]
  -- Tag 01W6: the common open stays closed in the fibre product of the two blowups.
  obtain ⟨hw, hclosed⟩ := isClosedImmersion_lift_of_isProper f₁ f₂ q₁ q₂ hq
    (d₁ ≫ blowUpToBase I₁) (d₂ ≫ blowUpToBase I₂) c k₁ k₂ hkc₁ hkc₂
  -- The section of the dominating blowup over the image of `U`.
  obtain ⟨v, hv⟩ := exists_section_of_isAdmissibleBlowup hc s le_rfl
  -- Glue the two blowups of `Xᵢ` along `W`.
  have _ : CompactSpace (SpanGlue.glued k₁ k₂) := SpanGlue.compactSpace_glued k₁ k₂
  refine ⟨Y₁, Y₂, SpanGlue.glued k₁ k₂, d₁ ≫ blowUpToBase I₁, d₂ ≫ blowUpToBase I₂,
    SpanGlue.ι₁ k₁ k₂, SpanGlue.ι₂ k₁ k₂, v ≫ k₁, v ≫ k₂, v ≫ k₁ ≫ SpanGlue.ι₁ k₁ k₂,
    SpanGlue.desc k₁ k₂ ((d₁ ≫ blowUpToBase I₁) ≫ f₁) ((d₂ ≫ blowUpToBase I₂) ≫ f₂) hw,
    hbd₁, hbd₂, inferInstance, inferInstance,
    SpanGlue.locallyOfFiniteType_desc k₁ k₂ _ _ hw, inferInstance,
    SpanGlue.isSeparated_desc k₁ k₂ _ _ hw hclosed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hkc₁, ← Category.assoc, hv, hs₁]
  · rw [Category.assoc, hkc₂, ← Category.assoc, hv, hs₂]
  · exact Category.assoc _ _ _
  · rw [Category.assoc, ← SpanGlue.glue_condition k₁ k₂]
  · exact (SpanGlue.ι₁_desc k₁ k₂ _ _ hw).symm
  · exact (SpanGlue.ι₂_desc k₁ k₂ _ _ hw).symm
  · calc (v ≫ k₁ ≫ SpanGlue.ι₁ k₁ k₂) ≫
          SpanGlue.desc k₁ k₂ ((d₁ ≫ blowUpToBase I₁) ≫ f₁)
            ((d₂ ≫ blowUpToBase I₂) ≫ f₂) hw
        = (v ≫ k₁ ≫ (d₁ ≫ blowUpToBase I₁)) ≫ f₁ := by
          simp only [Category.assoc, SpanGlue.ι₁_desc]
      _ = ((v ≫ c) ≫ q₁) ≫ f₁ := by rw [hkc₁, ← Category.assoc]
      _ = fU := by rw [hv, hs₁, hu₁]

end AlgebraicGeometry

end
